-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c304063_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:48:36.968392+00:00
-- url     : https://prove2.me/submissions/ce3c80c9-f0d6-4f43-a56b-741f7d4863c6

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
theorem collision_support_c304063_s2_s2_0 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-54312501/2000000000 : ℝ)*x 0 + (5686281101/10000000000 : ℝ)*x 1 + (6048986833/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (54312501/2000000000 : ℝ)^133 ≤ (433151821531/50000000000000 : ℝ)^101 := by
    have hnat : (54312501 : ℕ)^133*50000000000000^101 ≤ 433151821531^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54312501 2000000000 433151821531 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5686281101/10000000000 : ℝ)^133 ≤ (11887490407409/25000000000000 : ℝ)^101 := by
    have hnat : (5686281101 : ℕ)^133*25000000000000^101 ≤ 11887490407409^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5686281101 10000000000 11887490407409 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6048986833/10000000000 : ℝ)^133 ≤ (51583734710991/100000000000000 : ℝ)^101 := by
    have hnat : (6048986833 : ℕ)^133*100000000000000^101 ≤ 51583734710991^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6048986833 10000000000 51583734710991 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-54312501/2000000000 : ℝ), (5686281101/10000000000 : ℝ), (6048986833/10000000000 : ℝ)] ![(433151821531/50000000000000 : ℝ), (11887490407409/25000000000000 : ℝ), (51583734710991/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-54312501/2000000000 : ℝ)|^133 ≤ (433151821531/50000000000000 : ℝ)^101
        have hw : |(-54312501/2000000000 : ℝ)|=(54312501/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5686281101/10000000000 : ℝ)|^133 ≤ (11887490407409/25000000000000 : ℝ)^101
        have hw : |(5686281101/10000000000 : ℝ)|=(5686281101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6048986833/10000000000 : ℝ)|^133 ≤ (51583734710991/100000000000000 : ℝ)^101
        have hw : |(6048986833/10000000000 : ℝ)|=(6048986833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304063_s2_s2_1 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5685453039/10000000000 : ℝ)*x 0 + (-259030183/10000000000 : ℝ)*x 1 + (6054451541/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5685453039/10000000000 : ℝ)^133 ≤ (11885210879271/25000000000000 : ℝ)^101 := by
    have hnat : (5685453039 : ℕ)^133*25000000000000^101 ≤ 11885210879271^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5685453039 10000000000 11885210879271 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (259030183/10000000000 : ℝ)^133 ≤ (814047037699/100000000000000 : ℝ)^101 := by
    have hnat : (259030183 : ℕ)^133*100000000000000^101 ≤ 814047037699^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259030183 10000000000 814047037699 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6054451541/10000000000 : ℝ)^133 ≤ (51645109428713/100000000000000 : ℝ)^101 := by
    have hnat : (6054451541 : ℕ)^133*100000000000000^101 ≤ 51645109428713^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6054451541 10000000000 51645109428713 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5685453039/10000000000 : ℝ), (-259030183/10000000000 : ℝ), (6054451541/10000000000 : ℝ)] ![(11885210879271/25000000000000 : ℝ), (814047037699/100000000000000 : ℝ), (51645109428713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5685453039/10000000000 : ℝ)|^133 ≤ (11885210879271/25000000000000 : ℝ)^101
        have hw : |(5685453039/10000000000 : ℝ)|=(5685453039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-259030183/10000000000 : ℝ)|^133 ≤ (814047037699/100000000000000 : ℝ)^101
        have hw : |(-259030183/10000000000 : ℝ)|=(259030183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6054451541/10000000000 : ℝ)|^133 ≤ (51645109428713/100000000000000 : ℝ)^101
        have hw : |(6054451541/10000000000 : ℝ)|=(6054451541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304063_s2_s2_7 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-33530613/500000000 : ℝ)*x 0 + (2196185607/10000000000 : ℝ)*x 1 + (2181356391/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33530613/500000000 : ℝ)^133 ≤ (712197564343/25000000000000 : ℝ)^101 := by
    have hnat : (33530613 : ℕ)^133*25000000000000^101 ≤ 712197564343^101*500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33530613 500000000 712197564343 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2196185607/10000000000 : ℝ)^133 ≤ (3396479079117/25000000000000 : ℝ)^101 := by
    have hnat : (2196185607 : ℕ)^133*25000000000000^101 ≤ 3396479079117^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2196185607 10000000000 3396479079117 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2181356391/2500000000 : ℝ)^133 ≤ (83565293417353/100000000000000 : ℝ)^101 := by
    have hnat : (2181356391 : ℕ)^133*100000000000000^101 ≤ 83565293417353^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181356391 2500000000 83565293417353 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-33530613/500000000 : ℝ), (2196185607/10000000000 : ℝ), (2181356391/2500000000 : ℝ)] ![(712197564343/25000000000000 : ℝ), (3396479079117/25000000000000 : ℝ), (83565293417353/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-33530613/500000000 : ℝ)|^133 ≤ (712197564343/25000000000000 : ℝ)^101
        have hw : |(-33530613/500000000 : ℝ)|=(33530613/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2196185607/10000000000 : ℝ)|^133 ≤ (3396479079117/25000000000000 : ℝ)^101
        have hw : |(2196185607/10000000000 : ℝ)|=(2196185607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2181356391/2500000000 : ℝ)|^133 ≤ (83565293417353/100000000000000 : ℝ)^101
        have hw : |(2181356391/2500000000 : ℝ)|=(2181356391/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304063_s2_s2_8 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (498643051/2000000000 : ℝ)*x 0 + (-115811161/10000000000 : ℝ)*x 1 + (2183275023/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (498643051/2000000000 : ℝ)^133 ≤ (8027940854077/50000000000000 : ℝ)^101 := by
    have hnat : (498643051 : ℕ)^133*50000000000000^101 ≤ 8027940854077^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      498643051 2000000000 8027940854077 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (115811161/10000000000 : ℝ)^133 ≤ (282023436669/100000000000000 : ℝ)^101 := by
    have hnat : (115811161 : ℕ)^133*100000000000000^101 ≤ 282023436669^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      115811161 10000000000 282023436669 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2183275023/2500000000 : ℝ)^133 ≤ (83662094845169/100000000000000 : ℝ)^101 := by
    have hnat : (2183275023 : ℕ)^133*100000000000000^101 ≤ 83662094845169^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183275023 2500000000 83662094845169 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(498643051/2000000000 : ℝ), (-115811161/10000000000 : ℝ), (2183275023/2500000000 : ℝ)] ![(8027940854077/50000000000000 : ℝ), (282023436669/100000000000000 : ℝ), (83662094845169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(498643051/2000000000 : ℝ)|^133 ≤ (8027940854077/50000000000000 : ℝ)^101
        have hw : |(498643051/2000000000 : ℝ)|=(498643051/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-115811161/10000000000 : ℝ)|^133 ≤ (282023436669/100000000000000 : ℝ)^101
        have hw : |(-115811161/10000000000 : ℝ)|=(115811161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2183275023/2500000000 : ℝ)|^133 ≤ (83662094845169/100000000000000 : ℝ)^101
        have hw : |(2183275023/2500000000 : ℝ)|=(2183275023/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304063_s2_s2_9 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (161668199/625000000 : ℝ)*x 0 + (8688989939/10000000000 : ℝ)*x 1 + (-1663323/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (161668199/625000000 : ℝ)^133 ≤ (8426621071691/50000000000000 : ℝ)^101 := by
    have hnat : (161668199 : ℕ)^133*50000000000000^101 ≤ 8426621071691^101*625000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161668199 625000000 8426621071691 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8688989939/10000000000 : ℝ)^133 ≤ (10388260847721/12500000000000 : ℝ)^101 := by
    have hnat : (8688989939 : ℕ)^133*12500000000000^101 ≤ 10388260847721^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8688989939 10000000000 10388260847721 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1663323/625000000 : ℝ)^133 ≤ (40671069187/100000000000000 : ℝ)^101 := by
    have hnat : (1663323 : ℕ)^133*100000000000000^101 ≤ 40671069187^101*625000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1663323 625000000 40671069187 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(161668199/625000000 : ℝ), (8688989939/10000000000 : ℝ), (-1663323/625000000 : ℝ)] ![(8426621071691/50000000000000 : ℝ), (10388260847721/12500000000000 : ℝ), (40671069187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(161668199/625000000 : ℝ)|^133 ≤ (8426621071691/50000000000000 : ℝ)^101
        have hw : |(161668199/625000000 : ℝ)|=(161668199/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8688989939/10000000000 : ℝ)|^133 ≤ (10388260847721/12500000000000 : ℝ)^101
        have hw : |(8688989939/10000000000 : ℝ)|=(8688989939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1663323/625000000 : ℝ)|^133 ≤ (40671069187/100000000000000 : ℝ)^101
        have hw : |(-1663323/625000000 : ℝ)|=(1663323/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304063_s2_s2_13 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1512230653/5000000000 : ℝ)*x 0 + (936603947/1250000000 : ℝ)*x 1 + (1859671291/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1512230653/5000000000 : ℝ)^133 ≤ (20706222416229/100000000000000 : ℝ)^101 := by
    have hnat : (1512230653 : ℕ)^133*100000000000000^101 ≤ 20706222416229^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1512230653 5000000000 20706222416229 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (936603947/1250000000 : ℝ)^133 ≤ (34190058733173/50000000000000 : ℝ)^101 := by
    have hnat : (936603947 : ℕ)^133*50000000000000^101 ≤ 34190058733173^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      936603947 1250000000 34190058733173 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1859671291/10000000000 : ℝ)^133 ≤ (5456830052267/50000000000000 : ℝ)^101 := by
    have hnat : (1859671291 : ℕ)^133*50000000000000^101 ≤ 5456830052267^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1859671291 10000000000 5456830052267 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1512230653/5000000000 : ℝ), (936603947/1250000000 : ℝ), (1859671291/10000000000 : ℝ)] ![(20706222416229/100000000000000 : ℝ), (34190058733173/50000000000000 : ℝ), (5456830052267/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1512230653/5000000000 : ℝ)|^133 ≤ (20706222416229/100000000000000 : ℝ)^101
        have hw : |(1512230653/5000000000 : ℝ)|=(1512230653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(936603947/1250000000 : ℝ)|^133 ≤ (34190058733173/50000000000000 : ℝ)^101
        have hw : |(936603947/1250000000 : ℝ)|=(936603947/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1859671291/10000000000 : ℝ)|^133 ≤ (5456830052267/50000000000000 : ℝ)^101
        have hw : |(1859671291/10000000000 : ℝ)|=(1859671291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304063_s2_s2_14 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1095109/156250000 : ℝ)*x 0 + (1199267203/5000000000 : ℝ)*x 1 + (8807078309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1095109/156250000 : ℝ)^133 ≤ (36392088289/25000000000000 : ℝ)^101 := by
    have hnat : (1095109 : ℕ)^133*25000000000000^101 ≤ 36392088289^101*156250000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095109 156250000 36392088289 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1199267203/5000000000 : ℝ)^133 ≤ (7628922261593/50000000000000 : ℝ)^101 := by
    have hnat : (1199267203 : ℕ)^133*50000000000000^101 ≤ 7628922261593^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1199267203 5000000000 7628922261593 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8807078309/10000000000 : ℝ)^133 ≤ (21149146778687/25000000000000 : ℝ)^101 := by
    have hnat : (8807078309 : ℕ)^133*25000000000000^101 ≤ 21149146778687^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8807078309 10000000000 21149146778687 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1095109/156250000 : ℝ), (1199267203/5000000000 : ℝ), (8807078309/10000000000 : ℝ)] ![(36392088289/25000000000000 : ℝ), (7628922261593/50000000000000 : ℝ), (21149146778687/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1095109/156250000 : ℝ)|^133 ≤ (36392088289/25000000000000 : ℝ)^101
        have hw : |(-1095109/156250000 : ℝ)|=(1095109/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1199267203/5000000000 : ℝ)|^133 ≤ (7628922261593/50000000000000 : ℝ)^101
        have hw : |(1199267203/5000000000 : ℝ)|=(1199267203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8807078309/10000000000 : ℝ)|^133 ≤ (21149146778687/25000000000000 : ℝ)^101
        have hw : |(8807078309/10000000000 : ℝ)|=(8807078309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304063_s2_s2_15 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1044730793/5000000000 : ℝ)*x 0 + (-622340047/10000000000 : ℝ)*x 1 + (4407421367/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1044730793/5000000000 : ℝ)^133 ≤ (12723299280369/100000000000000 : ℝ)^101 := by
    have hnat : (1044730793 : ℕ)^133*100000000000000^101 ≤ 12723299280369^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044730793 5000000000 12723299280369 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (622340047/10000000000 : ℝ)^133 ≤ (1290944389233/50000000000000 : ℝ)^101 := by
    have hnat : (622340047 : ℕ)^133*50000000000000^101 ≤ 1290944389233^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      622340047 10000000000 1290944389233 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4407421367/5000000000 : ℝ)^133 ≤ (16938962384563/20000000000000 : ℝ)^101 := by
    have hnat : (4407421367 : ℕ)^133*20000000000000^101 ≤ 16938962384563^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4407421367 5000000000 16938962384563 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1044730793/5000000000 : ℝ), (-622340047/10000000000 : ℝ), (4407421367/5000000000 : ℝ)] ![(12723299280369/100000000000000 : ℝ), (1290944389233/50000000000000 : ℝ), (16938962384563/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1044730793/5000000000 : ℝ)|^133 ≤ (12723299280369/100000000000000 : ℝ)^101
        have hw : |(1044730793/5000000000 : ℝ)|=(1044730793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-622340047/10000000000 : ℝ)|^133 ≤ (1290944389233/50000000000000 : ℝ)^101
        have hw : |(-622340047/10000000000 : ℝ)|=(622340047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4407421367/5000000000 : ℝ)|^133 ≤ (16938962384563/20000000000000 : ℝ)^101
        have hw : |(4407421367/5000000000 : ℝ)|=(4407421367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304063_s2_s2_16 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (8490495727/10000000000 : ℝ)*x 0 + (179049221/625000000 : ℝ)*x 1 + (-13764443/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8490495727/10000000000 : ℝ)^133 ≤ (80615172133687/100000000000000 : ℝ)^101 := by
    have hnat : (8490495727 : ℕ)^133*100000000000000^101 ≤ 80615172133687^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8490495727 10000000000 80615172133687 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (179049221/625000000 : ℝ)^133 ≤ (9639446559613/50000000000000 : ℝ)^101 := by
    have hnat : (179049221 : ℕ)^133*50000000000000^101 ≤ 9639446559613^101*625000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179049221 625000000 9639446559613 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13764443/2500000000 : ℝ)^133 ≤ (52967369133/50000000000000 : ℝ)^101 := by
    have hnat : (13764443 : ℕ)^133*50000000000000^101 ≤ 52967369133^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13764443 2500000000 52967369133 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8490495727/10000000000 : ℝ), (179049221/625000000 : ℝ), (-13764443/2500000000 : ℝ)] ![(80615172133687/100000000000000 : ℝ), (9639446559613/50000000000000 : ℝ), (52967369133/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8490495727/10000000000 : ℝ)|^133 ≤ (80615172133687/100000000000000 : ℝ)^101
        have hw : |(8490495727/10000000000 : ℝ)|=(8490495727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(179049221/625000000 : ℝ)|^133 ≤ (9639446559613/50000000000000 : ℝ)^101
        have hw : |(179049221/625000000 : ℝ)|=(179049221/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-13764443/2500000000 : ℝ)|^133 ≤ (52967369133/50000000000000 : ℝ)^101
        have hw : |(-13764443/2500000000 : ℝ)|=(13764443/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304063_s2_s2_20 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (7778564277/10000000000 : ℝ)*x 0 + (2640006667/10000000000 : ℝ)*x 1 + (925932059/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7778564277/10000000000 : ℝ)^133 ≤ (7183447668141/10000000000000 : ℝ)^101 := by
    have hnat : (7778564277 : ℕ)^133*10000000000000^101 ≤ 7183447668141^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7778564277 10000000000 7183447668141 10000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2640006667/10000000000 : ℝ)^133 ≤ (17312156512247/100000000000000 : ℝ)^101 := by
    have hnat : (2640006667 : ℕ)^133*100000000000000^101 ≤ 17312156512247^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640006667 10000000000 17312156512247 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (925932059/5000000000 : ℝ)^133 ≤ (2170673359481/20000000000000 : ℝ)^101 := by
    have hnat : (925932059 : ℕ)^133*20000000000000^101 ≤ 2170673359481^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      925932059 5000000000 2170673359481 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7778564277/10000000000 : ℝ), (2640006667/10000000000 : ℝ), (925932059/5000000000 : ℝ)] ![(7183447668141/10000000000000 : ℝ), (17312156512247/100000000000000 : ℝ), (2170673359481/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7778564277/10000000000 : ℝ)|^133 ≤ (7183447668141/10000000000000 : ℝ)^101
        have hw : |(7778564277/10000000000 : ℝ)|=(7778564277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2640006667/10000000000 : ℝ)|^133 ≤ (17312156512247/100000000000000 : ℝ)^101
        have hw : |(2640006667/10000000000 : ℝ)|=(2640006667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(925932059/5000000000 : ℝ)|^133 ≤ (2170673359481/20000000000000 : ℝ)^101
        have hw : |(925932059/5000000000 : ℝ)|=(925932059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304063_s2_s2_21 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-16863247/1000000000 : ℝ)*x 0 + (1597647253/2000000000 : ℝ)*x 1 + (2190529/6250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16863247/1000000000 : ℝ)^133 ≤ (92514539917/20000000000000 : ℝ)^101 := by
    have hnat : (16863247 : ℕ)^133*20000000000000^101 ≤ 92514539917^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16863247 1000000000 92514539917 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1597647253/2000000000 : ℝ)^133 ≤ (14879017408459/20000000000000 : ℝ)^101 := by
    have hnat : (1597647253 : ℕ)^133*20000000000000^101 ≤ 14879017408459^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1597647253 2000000000 14879017408459 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2190529/6250000 : ℝ)^133 ≤ (2514234024979/10000000000000 : ℝ)^101 := by
    have hnat : (2190529 : ℕ)^133*10000000000000^101 ≤ 2514234024979^101*6250000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2190529 6250000 2514234024979 10000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-16863247/1000000000 : ℝ), (1597647253/2000000000 : ℝ), (2190529/6250000 : ℝ)] ![(92514539917/20000000000000 : ℝ), (14879017408459/20000000000000 : ℝ), (2514234024979/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-16863247/1000000000 : ℝ)|^133 ≤ (92514539917/20000000000000 : ℝ)^101
        have hw : |(-16863247/1000000000 : ℝ)|=(16863247/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1597647253/2000000000 : ℝ)|^133 ≤ (14879017408459/20000000000000 : ℝ)^101
        have hw : |(1597647253/2000000000 : ℝ)|=(1597647253/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2190529/6250000 : ℝ)|^133 ≤ (2514234024979/10000000000000 : ℝ)^101
        have hw : |(2190529/6250000 : ℝ)|=(2190529/6250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304063_s2_s2_22 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1050315037/1250000000 : ℝ)*x 0 + (-44204887/10000000000 : ℝ)*x 1 + (2990838559/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050315037/1250000000 : ℝ)^133 ≤ (39758512845883/50000000000000 : ℝ)^101 := by
    have hnat : (1050315037 : ℕ)^133*50000000000000^101 ≤ 39758512845883^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050315037 1250000000 39758512845883 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (44204887/10000000000 : ℝ)^133 ≤ (9917236839/12500000000000 : ℝ)^101 := by
    have hnat : (44204887 : ℕ)^133*12500000000000^101 ≤ 9917236839^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44204887 10000000000 9917236839 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2990838559/10000000000 : ℝ)^133 ≤ (20403636407181/100000000000000 : ℝ)^101 := by
    have hnat : (2990838559 : ℕ)^133*100000000000000^101 ≤ 20403636407181^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2990838559 10000000000 20403636407181 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050315037/1250000000 : ℝ), (-44204887/10000000000 : ℝ), (2990838559/10000000000 : ℝ)] ![(39758512845883/50000000000000 : ℝ), (9917236839/12500000000000 : ℝ), (20403636407181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050315037/1250000000 : ℝ)|^133 ≤ (39758512845883/50000000000000 : ℝ)^101
        have hw : |(1050315037/1250000000 : ℝ)|=(1050315037/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-44204887/10000000000 : ℝ)|^133 ≤ (9917236839/12500000000000 : ℝ)^101
        have hw : |(-44204887/10000000000 : ℝ)|=(44204887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2990838559/10000000000 : ℝ)|^133 ≤ (20403636407181/100000000000000 : ℝ)^101
        have hw : |(2990838559/10000000000 : ℝ)|=(2990838559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304063_s2_s2_23 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1902835443/10000000000 : ℝ)*x 0 + (8982151979/10000000000 : ℝ)*x 1 + (-249820947/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1902835443/10000000000 : ℝ)^133 ≤ (11248450763431/100000000000000 : ℝ)^101 := by
    have hnat : (1902835443 : ℕ)^133*100000000000000^101 ≤ 11248450763431^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1902835443 10000000000 11248450763431 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8982151979/10000000000 : ℝ)^133 ≤ (2170450277719/2500000000000 : ℝ)^101 := by
    have hnat : (8982151979 : ℕ)^133*2500000000000^101 ≤ 2170450277719^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8982151979 10000000000 2170450277719 2500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (249820947/5000000000 : ℝ)^133 ≤ (1933538115967/100000000000000 : ℝ)^101 := by
    have hnat : (249820947 : ℕ)^133*100000000000000^101 ≤ 1933538115967^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249820947 5000000000 1933538115967 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1902835443/10000000000 : ℝ), (8982151979/10000000000 : ℝ), (-249820947/5000000000 : ℝ)] ![(11248450763431/100000000000000 : ℝ), (2170450277719/2500000000000 : ℝ), (1933538115967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1902835443/10000000000 : ℝ)|^133 ≤ (11248450763431/100000000000000 : ℝ)^101
        have hw : |(1902835443/10000000000 : ℝ)|=(1902835443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8982151979/10000000000 : ℝ)|^133 ≤ (2170450277719/2500000000000 : ℝ)^101
        have hw : |(8982151979/10000000000 : ℝ)|=(8982151979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-249820947/5000000000 : ℝ)|^133 ≤ (1933538115967/100000000000000 : ℝ)^101
        have hw : |(-249820947/5000000000 : ℝ)|=(249820947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304063_s2_s2_27 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3952387263/5000000000 : ℝ)*x 0 + (508922803/2000000000 : ℝ)*x 1 + (439459159/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3952387263/5000000000 : ℝ)^133 ≤ (73373230531473/100000000000000 : ℝ)^101 := by
    have hnat : (3952387263 : ℕ)^133*100000000000000^101 ≤ 73373230531473^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3952387263 5000000000 73373230531473 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (508922803/2000000000 : ℝ)^133 ≤ (16493168870209/100000000000000 : ℝ)^101 := by
    have hnat : (508922803 : ℕ)^133*100000000000000^101 ≤ 16493168870209^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508922803 2000000000 16493168870209 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (439459159/2500000000 : ℝ)^133 ≤ (63335003653/625000000000 : ℝ)^101 := by
    have hnat : (439459159 : ℕ)^133*625000000000^101 ≤ 63335003653^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      439459159 2500000000 63335003653 625000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3952387263/5000000000 : ℝ), (508922803/2000000000 : ℝ), (439459159/2500000000 : ℝ)] ![(73373230531473/100000000000000 : ℝ), (16493168870209/100000000000000 : ℝ), (63335003653/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3952387263/5000000000 : ℝ)|^133 ≤ (73373230531473/100000000000000 : ℝ)^101
        have hw : |(3952387263/5000000000 : ℝ)|=(3952387263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(508922803/2000000000 : ℝ)|^133 ≤ (16493168870209/100000000000000 : ℝ)^101
        have hw : |(508922803/2000000000 : ℝ)|=(508922803/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(439459159/2500000000 : ℝ)|^133 ≤ (63335003653/625000000000 : ℝ)^101
        have hw : |(439459159/2500000000 : ℝ)|=(439459159/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c304063_s2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((91711/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(91711/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18257/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(18257/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22209/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(22209/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((10769/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(10769/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(86079/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(86079/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(41617/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(41617/50000 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76617/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76617/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (187821/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base27 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 1 0+(1 : ℝ)*X 2 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 0).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (91711/100000 : ℝ) ^ (33/8 : ℝ) ≤ (34991164720826830981/50000000000000000000 : ℝ) := by
    have hpowers : (91711/100000 : ℝ)^33 ≤ (34991164720826830981/50000000000000000000 : ℝ)^8 := by
      have hnat : (91711 : ℕ)^33*50000000000000000000^8 ≤ 34991164720826830981^8*100000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        91711 100000 34991164720826830981 50000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (91711/100000 : ℝ)) (X := (34991164720826830981/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s2_corner0a : (84991164720826830981/50000000000000000000 : ℝ) ≤ (11372487312138383/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (84991164720826830981/50000000000000000000 : ℝ)^8 ≤ (11372487312138383/10000000000000000 : ℝ)^33 := by
      have hnat : (84991164720826830981 : ℕ)^8*10000000000000000^33 ≤ 11372487312138383^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        84991164720826830981 50000000000000000000 11372487312138383 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11372487312138383/10000000000000000 : ℝ)) (X := (84991164720826830981/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s2_corner0b : (59991164720826830981/25000000000000000000 : ℝ) ≤ (3090985204707419/2500000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (59991164720826830981/25000000000000000000 : ℝ)^8 ≤ (3090985204707419/2500000000000000 : ℝ)^33 := by
      have hnat : (59991164720826830981 : ℕ)^8*2500000000000000^33 ≤ 3090985204707419^33*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59991164720826830981 25000000000000000000 3090985204707419 2500000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3090985204707419/2500000000000000 : ℝ)) (X := (59991164720826830981/25000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1372487312138383/9171100000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(991453506691293/9171100000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (91711/100000 : ℝ)) (alpha := (1372487312138383/9171100000000000 : ℝ)) (beta := (991453506691293/9171100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (91711/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1372487312138383/9171100000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(991453506691293/9171100000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (18257/20000 : ℝ) ^ (33/8 : ℝ) ≤ (34325558434734578411/50000000000000000000 : ℝ) := by
    have hpowers : (18257/20000 : ℝ)^33 ≤ (34325558434734578411/50000000000000000000 : ℝ)^8 := by
      have hnat : (18257 : ℕ)^33*50000000000000000000^8 ≤ 34325558434734578411^8*20000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18257 20000 34325558434734578411 50000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18257/20000 : ℝ)) (X := (34325558434734578411/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s2_corner1a : (84325558434734578411/50000000000000000000 : ℝ) ≤ (11350831848752591/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (84325558434734578411/50000000000000000000 : ℝ)^8 ≤ (11350831848752591/10000000000000000 : ℝ)^33 := by
      have hnat : (84325558434734578411 : ℕ)^8*10000000000000000^33 ≤ 11350831848752591^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        84325558434734578411 50000000000000000000 11350831848752591 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11350831848752591/10000000000000000 : ℝ)) (X := (84325558434734578411/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s2_corner1b : (59325558434734578411/25000000000000000000 : ℝ) ≤ (308263616790617/250000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (59325558434734578411/25000000000000000000 : ℝ)^8 ≤ (308263616790617/250000000000000 : ℝ)^33 := by
      have hnat : (59325558434734578411 : ℕ)^8*250000000000000^33 ≤ 308263616790617^33*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59325558434734578411 25000000000000000000 308263616790617 250000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (308263616790617/250000000000000 : ℝ)) (X := (59325558434734578411/25000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1350831848752591/9128500000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(979712822872089/9128500000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (18257/20000 : ℝ)) (alpha := (1350831848752591/9128500000000000 : ℝ)) (beta := (979712822872089/9128500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (18257/20000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1350831848752591/9128500000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(979712822872089/9128500000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (22209/25000 : ℝ) ^ (33/8 : ℝ) ≤ (15341563246819118163/25000000000000000000 : ℝ) := by
    have hpowers : (22209/25000 : ℝ)^33 ≤ (15341563246819118163/25000000000000000000 : ℝ)^8 := by
      have hnat : (22209 : ℕ)^33*25000000000000000000^8 ≤ 15341563246819118163^8*25000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22209 25000 15341563246819118163 25000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (22209/25000 : ℝ)) (X := (15341563246819118163/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s2_corner2a : (40341563246819118163/25000000000000000000 : ℝ) ≤ (11229976304568777/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (40341563246819118163/25000000000000000000 : ℝ)^8 ≤ (11229976304568777/10000000000000000 : ℝ)^33 := by
      have hnat : (40341563246819118163 : ℕ)^8*10000000000000000^33 ≤ 11229976304568777^33*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        40341563246819118163 25000000000000000000 11229976304568777 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11229976304568777/10000000000000000 : ℝ)) (X := (40341563246819118163/25000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s2_corner2b : (27841563246819118163/12500000000000000000 : ℝ) ≤ (2428517135811507/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (27841563246819118163/12500000000000000000 : ℝ)^8 ≤ (2428517135811507/2000000000000000 : ℝ)^33 := by
      have hnat : (27841563246819118163 : ℕ)^8*2000000000000000^33 ≤ 2428517135811507^33*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27841563246819118163 12500000000000000000 2428517135811507 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2428517135811507/2000000000000000 : ℝ)) (X := (27841563246819118163/12500000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1229976304568777/8883600000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(152101562414793/1480600000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (22209/25000 : ℝ)) (alpha := (1229976304568777/8883600000000000 : ℝ)) (beta := (152101562414793/1480600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (22209/25000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1229976304568777/8883600000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(152101562414793/1480600000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-54312501/2000000000 : ℝ)*X 0 0+(5686281101/10000000000 : ℝ)*X 0 1+(6048986833/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((5685453039/10000000000 : ℝ)*X 1 0+(-259030183/10000000000 : ℝ)*X 1 1+(6054451541/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-33530613/500000000 : ℝ)*X 0 0+(2196185607/10000000000 : ℝ)*X 0 1+(2181356391/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((498643051/2000000000 : ℝ)*X 1 0+(-115811161/10000000000 : ℝ)*X 1 1+(2183275023/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((161668199/625000000 : ℝ)*X 2 0+(8688989939/10000000000 : ℝ)*X 2 1+(-1663323/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((1512230653/5000000000 : ℝ)*X 0 0+(936603947/1250000000 : ℝ)*X 0 1+(1859671291/10000000000 : ℝ)*X 0 2+(1512230653/5000000000 : ℝ)*X 1 0+(936603947/1250000000 : ℝ)*X 1 1+(1859671291/10000000000 : ℝ)*X 1 2+(1512230653/5000000000 : ℝ)*X 2 0+(936603947/1250000000 : ℝ)*X 2 1+(1859671291/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-1095109/156250000 : ℝ)*X 0 0+(1199267203/5000000000 : ℝ)*X 0 1+(8807078309/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((1044730793/5000000000 : ℝ)*X 1 0+(-622340047/10000000000 : ℝ)*X 1 1+(4407421367/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((8490495727/10000000000 : ℝ)*X 2 0+(179049221/625000000 : ℝ)*X 2 1+(-13764443/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((7778564277/10000000000 : ℝ)*X 0 0+(2640006667/10000000000 : ℝ)*X 0 1+(925932059/5000000000 : ℝ)*X 0 2+(7778564277/10000000000 : ℝ)*X 1 0+(2640006667/10000000000 : ℝ)*X 1 1+(925932059/5000000000 : ℝ)*X 1 2+(7778564277/10000000000 : ℝ)*X 2 0+(2640006667/10000000000 : ℝ)*X 2 1+(925932059/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-16863247/1000000000 : ℝ)*X 0 0+(1597647253/2000000000 : ℝ)*X 0 1+(2190529/6250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((1050315037/1250000000 : ℝ)*X 1 0+(-44204887/10000000000 : ℝ)*X 1 1+(2990838559/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((1902835443/10000000000 : ℝ)*X 2 0+(8982151979/10000000000 : ℝ)*X 2 1+(-249820947/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((3952387263/5000000000 : ℝ)*X 0 0+(508922803/2000000000 : ℝ)*X 0 1+(439459159/2500000000 : ℝ)*X 0 2+(3952387263/5000000000 : ℝ)*X 1 0+(508922803/2000000000 : ℝ)*X 1 1+(439459159/2500000000 : ℝ)*X 1 2+(3952387263/5000000000 : ℝ)*X 2 0+(508922803/2000000000 : ℝ)*X 2 1+(439459159/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((10769/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(10769/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (169198443486812746260538859543013/12395344282981000000000000000000000000 : ℝ) := by norm_num
    linear_combination (835637650561/1000000000000 : ℝ)*(base7) + (603931/250000000000 : ℝ)*(base50) + (271707/250000000000 : ℝ)*(base53) + (1630271/1000000000000 : ℝ)*(base60) + (1626717622191/1000000000000 : ℝ)*(major_s2_0) + (1626717622191/1000000000000 : ℝ)*(major_s2_1) + (1626716535363/1000000000000 : ℝ)*(major_s2_2) + (9130737/1000000000000 : ℝ)*(sp_s2_0) + (1657640189623/1000000000000 : ℝ)*(sp_s2_7) + (103608661821/62500000000 : ℝ)*(sp_s2_8) + (414431630319/250000000000 : ℝ)*(sp_s2_9) + (1908161005031/1000000000000 : ℝ)*(sp_s2_13) + (11158597/125000000000 : ℝ)*(sp_s2_14) + (102771/7812500000 : ℝ)*(sp_s2_23) + (1072523354469/1000000000000 : ℝ)*(f.failure) + (414434918991/250000000000 : ℝ)*(f.sum) + (172842882120592968017/270313142000000000000000000000000 : ℝ)*base63 + (1044725850065741/1480600000000000000000000000 : ℝ)*base64 + (2376887634582301/9128500000000000000000000000 : ℝ)*base66 + (1461493550231097/2961200000000000000000000000 : ℝ)*base69 + (110164792846454242533/135787306600000000000000000000000 : ℝ)*base70 + (308728752313333/9171100000000000000000000000 : ℝ)*base73 + (2380623107252981/9128500000000000000000000000 : ℝ)*base75 + (1557879014009767/9171100000000000000000000000 : ℝ)*base76 + (161415846824345118303/418591931750000000000000000000000 : ℝ)*base78 + (9729/12500000000000000 : ℝ)*base86 + (9729/12500000000000000 : ℝ)*base88 + (9729/12500000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(86079/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(86079/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1632156869859924106549489920429/154941803537262500000000000000000000 : ℝ) := by norm_num
    linear_combination (210310159187/250000000000 : ℝ)*(base7) + (2229061/500000000000 : ℝ)*(base13) + (1223531/500000000000 : ℝ)*(base40) + (5880921/1000000000000 : ℝ)*(base53) + (315119817537/200000000000 : ℝ)*(major_s2_0) + (315119817537/200000000000 : ℝ)*(major_s2_1) + (393898301691/250000000000 : ℝ)*(major_s2_2) + (3151309/1000000000000 : ℝ)*(sp_s2_1) + (10197689/125000000000 : ℝ)*(sp_s2_8) + (792844394071/500000000000 : ℝ)*(sp_s2_14) + (396402128361/250000000000 : ℝ)*(sp_s2_15) + (317139825437/200000000000 : ℝ)*(sp_s2_16) + (1879965841499/1000000000000 : ℝ)*(sp_s2_20) + (47403323/500000000000 : ℝ)*(sp_s2_27) + (259705002849/250000000000 : ℝ)*(f.failure) + (317139825437/200000000000 : ℝ)*(f.sum) + (1461997544710906309/3378914275000000000000000000000 : ℝ)*base62 + (19348042186169/185075000000000000000000000 : ℝ)*base65 + (289362461171673/1825700000000000000000000000 : ℝ)*base67 + (185256511706451/740300000000000000000000000 : ℝ)*base68 + (5009424814266047371/67893653300000000000000000000000 : ℝ)*base71 + (1874275156792413/1834220000000000000000000000 : ℝ)*base72 + (294574581182613/1825700000000000000000000000 : ℝ)*base74 + (115002422703889/366844000000000000000000000 : ℝ)*base77 + (9464136042843949963/41859193175000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (717/1562500000000000 : ℝ)*base86 + (717/1562500000000000 : ℝ)*base88 + (717/1562500000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(41617/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(41617/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (24341006419575927960516052043611/2479068856596200000000000000000000000 : ℝ) := by norm_num
    linear_combination (844459160311/1000000000000 : ℝ)*(base7) + (283461/1000000000000 : ℝ)*(base27) + (79123571803/1000000000000 : ℝ)*(base40) + (3186033/500000000000 : ℝ)*(base43) + (288677/500000000000 : ℝ)*(base49) + (699951/1000000000000 : ℝ)*(base59) + (1525257491909/1000000000000 : ℝ)*(major_s2_0) + (762625559921/500000000000 : ℝ)*(major_s2_1) + (1525257491909/1000000000000 : ℝ)*(major_s2_2) + (9800801/125000000000 : ℝ)*(sp_s2_9) + (1516185874771/1000000000000 : ℝ)*(sp_s2_21) + (758096123419/500000000000 : ℝ)*(sp_s2_22) + (1516107468363/1000000000000 : ℝ)*(sp_s2_23) + (925043897227/500000000000 : ℝ)*(sp_s2_27) + (251407229401/250000000000 : ℝ)*(f.failure) + (758096123419/500000000000 : ℝ)*(f.sum) + (349095179788016499097/810939426000000000000000000000000 : ℝ)*base63 + (492969189677663/1480600000000000000000000000 : ℝ)*base64 + (4251449705044769/4564250000000000000000000000 : ℝ)*base67 + (4484743041922573/8883600000000000000000000000 : ℝ)*base69 + (87089758659642557051/135787306600000000000000000000000 : ℝ)*base70 + (6941278051935877/9171100000000000000000000000 : ℝ)*base73 + (1691435871239593/2282125000000000000000000000 : ℝ)*base75 + (2786158222992743/9171100000000000000000000000 : ℝ)*base76 + (823061717658717001663/837183863500000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base84 + (1033/1562500000000000 : ℝ)*base86 + (1059/3125000000000000 : ℝ)*base89 + (1033/1562500000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((91711/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(91711/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18257/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(18257/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22209/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(22209/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((10769/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(10769/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(86079/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(86079/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(41617/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(41617/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c304063_s2 p hpa hpb X hX hprev1

#print axioms solution
