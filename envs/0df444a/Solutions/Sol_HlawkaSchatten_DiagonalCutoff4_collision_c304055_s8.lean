-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c304055_s8
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:45:35.190677+00:00
-- url     : https://prove2.me/submissions/9f19337a-a9b6-402a-85c4-f1368284538e

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
theorem collision_support_c304055_s8_s8_0 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2643512281/10000000000 : ℝ)*x 0 + (1368746297/2500000000 : ℝ)*x 1 + (23702279/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643512281/10000000000 : ℝ)^133 ≤ (17342434835953/100000000000000 : ℝ)^101 := by
    have hnat : (2643512281 : ℕ)^133*100000000000000^101 ≤ 17342434835953^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643512281 10000000000 17342434835953 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1368746297/2500000000 : ℝ)^133 ≤ (45237060611661/100000000000000 : ℝ)^101 := by
    have hnat : (1368746297 : ℕ)^133*100000000000000^101 ≤ 45237060611661^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1368746297 2500000000 45237060611661 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (23702279/50000000 : ℝ)^133 ≤ (37420504532519/100000000000000 : ℝ)^101 := by
    have hnat : (23702279 : ℕ)^133*100000000000000^101 ≤ 37420504532519^101*50000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23702279 50000000 37420504532519 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2643512281/10000000000 : ℝ), (1368746297/2500000000 : ℝ), (23702279/50000000 : ℝ)] ![(17342434835953/100000000000000 : ℝ), (45237060611661/100000000000000 : ℝ), (37420504532519/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2643512281/10000000000 : ℝ)|^133 ≤ (17342434835953/100000000000000 : ℝ)^101
        have hw : |(-2643512281/10000000000 : ℝ)|=(2643512281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1368746297/2500000000 : ℝ)|^133 ≤ (45237060611661/100000000000000 : ℝ)^101
        have hw : |(1368746297/2500000000 : ℝ)|=(1368746297/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(23702279/50000000 : ℝ)|^133 ≤ (37420504532519/100000000000000 : ℝ)^101
        have hw : |(23702279/50000000 : ℝ)|=(23702279/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304055_s8_s8_1 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4738385943/10000000000 : ℝ)*x 0 + (-956305319/5000000000 : ℝ)*x 1 + (6021598997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4738385943/10000000000 : ℝ)^133 ≤ (7479798017947/20000000000000 : ℝ)^101 := by
    have hnat : (4738385943 : ℕ)^133*20000000000000^101 ≤ 7479798017947^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4738385943 10000000000 7479798017947 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (956305319/5000000000 : ℝ)^133 ≤ (566230302471/5000000000000 : ℝ)^101 := by
    have hnat : (956305319 : ℕ)^133*5000000000000^101 ≤ 566230302471^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      956305319 5000000000 566230302471 5000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6021598997/10000000000 : ℝ)^133 ≤ (51276403834061/100000000000000 : ℝ)^101 := by
    have hnat : (6021598997 : ℕ)^133*100000000000000^101 ≤ 51276403834061^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6021598997 10000000000 51276403834061 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4738385943/10000000000 : ℝ), (-956305319/5000000000 : ℝ), (6021598997/10000000000 : ℝ)] ![(7479798017947/20000000000000 : ℝ), (566230302471/5000000000000 : ℝ), (51276403834061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4738385943/10000000000 : ℝ)|^133 ≤ (7479798017947/20000000000000 : ℝ)^101
        have hw : |(4738385943/10000000000 : ℝ)|=(4738385943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-956305319/5000000000 : ℝ)|^133 ≤ (566230302471/5000000000000 : ℝ)^101
        have hw : |(-956305319/5000000000 : ℝ)|=(956305319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6021598997/10000000000 : ℝ)|^133 ≤ (51276403834061/100000000000000 : ℝ)^101
        have hw : |(6021598997/10000000000 : ℝ)|=(6021598997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304055_s8_s8_2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4740182451/10000000000 : ℝ)*x 0 + (1367959607/2500000000 : ℝ)*x 1 + (-2647802929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4740182451/10000000000 : ℝ)^133 ≤ (37417663126301/100000000000000 : ℝ)^101 := by
    have hnat : (4740182451 : ℕ)^133*100000000000000^101 ≤ 37417663126301^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4740182451 10000000000 37417663126301 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1367959607/2500000000 : ℝ)^133 ≤ (904056519429/2000000000000 : ℝ)^101 := by
    have hnat : (1367959607 : ℕ)^133*2000000000000^101 ≤ 904056519429^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1367959607 2500000000 904056519429 2000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2647802929/10000000000 : ℝ)^133 ≤ (2172438861227/12500000000000 : ℝ)^101 := by
    have hnat : (2647802929 : ℕ)^133*12500000000000^101 ≤ 2172438861227^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647802929 10000000000 2172438861227 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4740182451/10000000000 : ℝ), (1367959607/2500000000 : ℝ), (-2647802929/10000000000 : ℝ)] ![(37417663126301/100000000000000 : ℝ), (904056519429/2000000000000 : ℝ), (2172438861227/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4740182451/10000000000 : ℝ)|^133 ≤ (37417663126301/100000000000000 : ℝ)^101
        have hw : |(4740182451/10000000000 : ℝ)|=(4740182451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1367959607/2500000000 : ℝ)|^133 ≤ (904056519429/2000000000000 : ℝ)^101
        have hw : |(1367959607/2500000000 : ℝ)|=(1367959607/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2647802929/10000000000 : ℝ)|^133 ≤ (2172438861227/12500000000000 : ℝ)^101
        have hw : |(-2647802929/10000000000 : ℝ)|=(2647802929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304055_s8_s8_6 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5672847261/10000000000 : ℝ)*x 0 + (1043187829/2500000000 : ℝ)*x 1 + (3052952011/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5672847261/10000000000 : ℝ)^133 ≤ (47402088376133/100000000000000 : ℝ)^101 := by
    have hnat : (5672847261 : ℕ)^133*100000000000000^101 ≤ 47402088376133^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5672847261 10000000000 47402088376133 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043187829/2500000000 : ℝ)^133 ≤ (31634452714893/100000000000000 : ℝ)^101 := by
    have hnat : (1043187829 : ℕ)^133*100000000000000^101 ≤ 31634452714893^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043187829 2500000000 31634452714893 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3052952011/10000000000 : ℝ)^133 ≤ (4192691776327/20000000000000 : ℝ)^101 := by
    have hnat : (3052952011 : ℕ)^133*20000000000000^101 ≤ 4192691776327^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3052952011 10000000000 4192691776327 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5672847261/10000000000 : ℝ), (1043187829/2500000000 : ℝ), (3052952011/10000000000 : ℝ)] ![(47402088376133/100000000000000 : ℝ), (31634452714893/100000000000000 : ℝ), (4192691776327/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5672847261/10000000000 : ℝ)|^133 ≤ (47402088376133/100000000000000 : ℝ)^101
        have hw : |(5672847261/10000000000 : ℝ)|=(5672847261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043187829/2500000000 : ℝ)|^133 ≤ (31634452714893/100000000000000 : ℝ)^101
        have hw : |(1043187829/2500000000 : ℝ)|=(1043187829/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3052952011/10000000000 : ℝ)|^133 ≤ (4192691776327/20000000000000 : ℝ)^101
        have hw : |(3052952011/10000000000 : ℝ)|=(3052952011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304055_s8_s8_7 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-647845497/2500000000 : ℝ)*x 0 + (2639798633/5000000000 : ℝ)*x 1 + (249250743/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (647845497/2500000000 : ℝ)^133 ≤ (3378699823443/20000000000000 : ℝ)^101 := by
    have hnat : (647845497 : ℕ)^133*20000000000000^101 ≤ 3378699823443^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647845497 2500000000 3378699823443 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2639798633/5000000000 : ℝ)^133 ≤ (21561647548817/50000000000000 : ℝ)^101 := by
    have hnat : (2639798633 : ℕ)^133*50000000000000^101 ≤ 21561647548817^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639798633 5000000000 21561647548817 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (249250743/500000000 : ℝ)^133 ≤ (19991602886039/50000000000000 : ℝ)^101 := by
    have hnat : (249250743 : ℕ)^133*50000000000000^101 ≤ 19991602886039^101*500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249250743 500000000 19991602886039 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-647845497/2500000000 : ℝ), (2639798633/5000000000 : ℝ), (249250743/500000000 : ℝ)] ![(3378699823443/20000000000000 : ℝ), (21561647548817/50000000000000 : ℝ), (19991602886039/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-647845497/2500000000 : ℝ)|^133 ≤ (3378699823443/20000000000000 : ℝ)^101
        have hw : |(-647845497/2500000000 : ℝ)|=(647845497/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2639798633/5000000000 : ℝ)|^133 ≤ (21561647548817/50000000000000 : ℝ)^101
        have hw : |(2639798633/5000000000 : ℝ)|=(2639798633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(249250743/500000000 : ℝ)|^133 ≤ (19991602886039/50000000000000 : ℝ)^101
        have hw : |(249250743/500000000 : ℝ)|=(249250743/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304055_s8_s8_8 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (942860921/2000000000 : ℝ)*x 0 + (-106616433/625000000 : ℝ)*x 1 + (6184440711/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (942860921/2000000000 : ℝ)^133 ≤ (37148903659277/100000000000000 : ℝ)^101 := by
    have hnat : (942860921 : ℕ)^133*100000000000000^101 ≤ 37148903659277^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      942860921 2000000000 37148903659277 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (106616433/625000000 : ℝ)^133 ≤ (9740913739529/100000000000000 : ℝ)^101 := by
    have hnat : (106616433 : ℕ)^133*100000000000000^101 ≤ 9740913739529^101*625000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106616433 625000000 9740913739529 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6184440711/10000000000 : ℝ)^133 ≤ (53110182585203/100000000000000 : ℝ)^101 := by
    have hnat : (6184440711 : ℕ)^133*100000000000000^101 ≤ 53110182585203^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6184440711 10000000000 53110182585203 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(942860921/2000000000 : ℝ), (-106616433/625000000 : ℝ), (6184440711/10000000000 : ℝ)] ![(37148903659277/100000000000000 : ℝ), (9740913739529/100000000000000 : ℝ), (53110182585203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(942860921/2000000000 : ℝ)|^133 ≤ (37148903659277/100000000000000 : ℝ)^101
        have hw : |(942860921/2000000000 : ℝ)|=(942860921/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-106616433/625000000 : ℝ)|^133 ≤ (9740913739529/100000000000000 : ℝ)^101
        have hw : |(-106616433/625000000 : ℝ)|=(106616433/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6184440711/10000000000 : ℝ)|^133 ≤ (53110182585203/100000000000000 : ℝ)^101
        have hw : |(6184440711/10000000000 : ℝ)|=(6184440711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304055_s8_s8_9 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (943220309/2000000000 : ℝ)*x 0 + (227287579/400000000 : ℝ)*x 1 + (-1203424819/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (943220309/2000000000 : ℝ)^133 ≤ (37167551065233/100000000000000 : ℝ)^101 := by
    have hnat : (943220309 : ℕ)^133*100000000000000^101 ≤ 37167551065233^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      943220309 2000000000 37167551065233 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (227287579/400000000 : ℝ)^133 ≤ (4750491124261/10000000000000 : ℝ)^101 := by
    have hnat : (227287579 : ℕ)^133*10000000000000^101 ≤ 4750491124261^101*400000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      227287579 400000000 4750491124261 10000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1203424819/5000000000 : ℝ)^133 ≤ (3831884419719/25000000000000 : ℝ)^101 := by
    have hnat : (1203424819 : ℕ)^133*25000000000000^101 ≤ 3831884419719^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1203424819 5000000000 3831884419719 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(943220309/2000000000 : ℝ), (227287579/400000000 : ℝ), (-1203424819/5000000000 : ℝ)] ![(37167551065233/100000000000000 : ℝ), (4750491124261/10000000000000 : ℝ), (3831884419719/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(943220309/2000000000 : ℝ)|^133 ≤ (37167551065233/100000000000000 : ℝ)^101
        have hw : |(943220309/2000000000 : ℝ)|=(943220309/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(227287579/400000000 : ℝ)|^133 ≤ (4750491124261/10000000000000 : ℝ)^101
        have hw : |(227287579/400000000 : ℝ)|=(227287579/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1203424819/5000000000 : ℝ)|^133 ≤ (3831884419719/25000000000000 : ℝ)^101
        have hw : |(-1203424819/5000000000 : ℝ)|=(1203424819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304055_s8_s8_13 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (222568847/400000000 : ℝ)*x 0 + (915099183/2000000000 : ℝ)*x 1 + (2727798999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (222568847/400000000 : ℝ)^133 ≤ (361019331477/781250000000 : ℝ)^101 := by
    have hnat : (222568847 : ℕ)^133*781250000000^101 ≤ 361019331477^101*400000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222568847 400000000 361019331477 781250000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (915099183/2000000000 : ℝ)^133 ≤ (27902573241/78125000000 : ℝ)^101 := by
    have hnat : (915099183 : ℕ)^133*78125000000^101 ≤ 27902573241^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      915099183 2000000000 27902573241 78125000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2727798999/10000000000 : ℝ)^133 ≤ (903711590233/5000000000000 : ℝ)^101 := by
    have hnat : (2727798999 : ℕ)^133*5000000000000^101 ≤ 903711590233^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2727798999 10000000000 903711590233 5000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(222568847/400000000 : ℝ), (915099183/2000000000 : ℝ), (2727798999/10000000000 : ℝ)] ![(361019331477/781250000000 : ℝ), (27902573241/78125000000 : ℝ), (903711590233/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(222568847/400000000 : ℝ)|^133 ≤ (361019331477/781250000000 : ℝ)^101
        have hw : |(222568847/400000000 : ℝ)|=(222568847/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(915099183/2000000000 : ℝ)|^133 ≤ (27902573241/78125000000 : ℝ)^101
        have hw : |(915099183/2000000000 : ℝ)|=(915099183/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2727798999/10000000000 : ℝ)|^133 ≤ (903711590233/5000000000000 : ℝ)^101
        have hw : |(2727798999/10000000000 : ℝ)|=(2727798999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304055_s8_s8_14 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2381521731/10000000000 : ℝ)*x 0 + (1084735169/2000000000 : ℝ)*x 1 + (2502994397/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2381521731/10000000000 : ℝ)^133 ≤ (15115493349923/100000000000000 : ℝ)^101 := by
    have hnat : (2381521731 : ℕ)^133*100000000000000^101 ≤ 15115493349923^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2381521731 10000000000 15115493349923 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1084735169/2000000000 : ℝ)^133 ≤ (22339814540873/50000000000000 : ℝ)^101 := by
    have hnat : (1084735169 : ℕ)^133*50000000000000^101 ≤ 22339814540873^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084735169 2000000000 22339814540873 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2502994397/5000000000 : ℝ)^133 ≤ (20102438776673/50000000000000 : ℝ)^101 := by
    have hnat : (2502994397 : ℕ)^133*50000000000000^101 ≤ 20102438776673^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2502994397 5000000000 20102438776673 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2381521731/10000000000 : ℝ), (1084735169/2000000000 : ℝ), (2502994397/5000000000 : ℝ)] ![(15115493349923/100000000000000 : ℝ), (22339814540873/50000000000000 : ℝ), (20102438776673/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2381521731/10000000000 : ℝ)|^133 ≤ (15115493349923/100000000000000 : ℝ)^101
        have hw : |(-2381521731/10000000000 : ℝ)|=(2381521731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1084735169/2000000000 : ℝ)|^133 ≤ (22339814540873/50000000000000 : ℝ)^101
        have hw : |(1084735169/2000000000 : ℝ)|=(1084735169/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2502994397/5000000000 : ℝ)|^133 ≤ (20102438776673/50000000000000 : ℝ)^101
        have hw : |(2502994397/5000000000 : ℝ)|=(2502994397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304055_s8_s8_15 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4586071651/10000000000 : ℝ)*x 0 + (-1882175843/10000000000 : ℝ)*x 1 + (1236496743/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4586071651/10000000000 : ℝ)^133 ≤ (8956010096127/25000000000000 : ℝ)^101 := by
    have hnat : (4586071651 : ℕ)^133*25000000000000^101 ≤ 8956010096127^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4586071651 10000000000 8956010096127 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1882175843/10000000000 : ℝ)^133 ≤ (88703253801/800000000000 : ℝ)^101 := by
    have hnat : (1882175843 : ℕ)^133*800000000000^101 ≤ 88703253801^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1882175843 10000000000 88703253801 800000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1236496743/2000000000 : ℝ)^133 ≤ (53088052871447/100000000000000 : ℝ)^101 := by
    have hnat : (1236496743 : ℕ)^133*100000000000000^101 ≤ 53088052871447^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1236496743 2000000000 53088052871447 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4586071651/10000000000 : ℝ), (-1882175843/10000000000 : ℝ), (1236496743/2000000000 : ℝ)] ![(8956010096127/25000000000000 : ℝ), (88703253801/800000000000 : ℝ), (53088052871447/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4586071651/10000000000 : ℝ)|^133 ≤ (8956010096127/25000000000000 : ℝ)^101
        have hw : |(4586071651/10000000000 : ℝ)|=(4586071651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1882175843/10000000000 : ℝ)|^133 ≤ (88703253801/800000000000 : ℝ)^101
        have hw : |(-1882175843/10000000000 : ℝ)|=(1882175843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1236496743/2000000000 : ℝ)|^133 ≤ (53088052871447/100000000000000 : ℝ)^101
        have hw : |(1236496743/2000000000 : ℝ)|=(1236496743/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304055_s8_s8_16 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2502888249/5000000000 : ℝ)*x 0 + (5420527531/10000000000 : ℝ)*x 1 + (-2385874989/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2502888249/5000000000 : ℝ)^133 ≤ (40202632337847/100000000000000 : ℝ)^101 := by
    have hnat : (2502888249 : ℕ)^133*100000000000000^101 ≤ 40202632337847^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2502888249 5000000000 40202632337847 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5420527531/10000000000 : ℝ)^133 ≤ (44645479593631/100000000000000 : ℝ)^101 := by
    have hnat : (5420527531 : ℕ)^133*100000000000000^101 ≤ 44645479593631^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420527531 10000000000 44645479593631 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2385874989/10000000000 : ℝ)^133 ≤ (7575944024857/50000000000000 : ℝ)^101 := by
    have hnat : (2385874989 : ℕ)^133*50000000000000^101 ≤ 7575944024857^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2385874989 10000000000 7575944024857 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2502888249/5000000000 : ℝ), (5420527531/10000000000 : ℝ), (-2385874989/10000000000 : ℝ)] ![(40202632337847/100000000000000 : ℝ), (44645479593631/100000000000000 : ℝ), (7575944024857/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2502888249/5000000000 : ℝ)|^133 ≤ (40202632337847/100000000000000 : ℝ)^101
        have hw : |(2502888249/5000000000 : ℝ)|=(2502888249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5420527531/10000000000 : ℝ)|^133 ≤ (44645479593631/100000000000000 : ℝ)^101
        have hw : |(5420527531/10000000000 : ℝ)|=(5420527531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2385874989/10000000000 : ℝ)|^133 ≤ (7575944024857/50000000000000 : ℝ)^101
        have hw : |(-2385874989/10000000000 : ℝ)|=(2385874989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304055_s8_s8_20 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1496817841/2500000000 : ℝ)*x 0 + (2054483049/5000000000 : ℝ)*x 1 + (2731777633/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1496817841/2500000000 : ℝ)^133 ≤ (50891823599937/100000000000000 : ℝ)^101 := by
    have hnat : (1496817841 : ℕ)^133*100000000000000^101 ≤ 50891823599937^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1496817841 2500000000 50891823599937 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2054483049/5000000000 : ℝ)^133 ≤ (30999221994759/100000000000000 : ℝ)^101 := by
    have hnat : (2054483049 : ℕ)^133*100000000000000^101 ≤ 30999221994759^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2054483049 5000000000 30999221994759 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2731777633/10000000000 : ℝ)^133 ≤ (724358175559/4000000000000 : ℝ)^101 := by
    have hnat : (2731777633 : ℕ)^133*4000000000000^101 ≤ 724358175559^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2731777633 10000000000 724358175559 4000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1496817841/2500000000 : ℝ), (2054483049/5000000000 : ℝ), (2731777633/10000000000 : ℝ)] ![(50891823599937/100000000000000 : ℝ), (30999221994759/100000000000000 : ℝ), (724358175559/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1496817841/2500000000 : ℝ)|^133 ≤ (50891823599937/100000000000000 : ℝ)^101
        have hw : |(1496817841/2500000000 : ℝ)|=(1496817841/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2054483049/5000000000 : ℝ)|^133 ≤ (30999221994759/100000000000000 : ℝ)^101
        have hw : |(2054483049/5000000000 : ℝ)|=(2054483049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2731777633/10000000000 : ℝ)|^133 ≤ (724358175559/4000000000000 : ℝ)^101
        have hw : |(2731777633/10000000000 : ℝ)|=(2731777633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304055_s8_s8_21 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2398213617/10000000000 : ℝ)*x 0 + (1420769271/2500000000 : ℝ)*x 1 + (590266643/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2398213617/10000000000 : ℝ)^133 ≤ (15255157398829/100000000000000 : ℝ)^101 := by
    have hnat : (2398213617 : ℕ)^133*100000000000000^101 ≤ 15255157398829^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2398213617 10000000000 15255157398829 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1420769271/2500000000 : ℝ)^133 ≤ (23757341644393/50000000000000 : ℝ)^101 := by
    have hnat : (1420769271 : ℕ)^133*50000000000000^101 ≤ 23757341644393^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1420769271 2500000000 23757341644393 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (590266643/1250000000 : ℝ)^133 ≤ (7446031860667/20000000000000 : ℝ)^101 := by
    have hnat : (590266643 : ℕ)^133*20000000000000^101 ≤ 7446031860667^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      590266643 1250000000 7446031860667 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2398213617/10000000000 : ℝ), (1420769271/2500000000 : ℝ), (590266643/1250000000 : ℝ)] ![(15255157398829/100000000000000 : ℝ), (23757341644393/50000000000000 : ℝ), (7446031860667/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2398213617/10000000000 : ℝ)|^133 ≤ (15255157398829/100000000000000 : ℝ)^101
        have hw : |(-2398213617/10000000000 : ℝ)|=(2398213617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1420769271/2500000000 : ℝ)|^133 ≤ (23757341644393/50000000000000 : ℝ)^101
        have hw : |(1420769271/2500000000 : ℝ)|=(1420769271/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(590266643/1250000000 : ℝ)|^133 ≤ (7446031860667/20000000000000 : ℝ)^101
        have hw : |(590266643/1250000000 : ℝ)|=(590266643/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304055_s8_s8_22 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2493643859/5000000000 : ℝ)*x 0 + (-1708125389/10000000000 : ℝ)*x 1 + (1185697139/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2493643859/5000000000 : ℝ)^133 ≤ (40007213169899/100000000000000 : ℝ)^101 := by
    have hnat : (2493643859 : ℕ)^133*100000000000000^101 ≤ 40007213169899^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2493643859 5000000000 40007213169899 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1708125389/10000000000 : ℝ)^133 ≤ (9757929765717/100000000000000 : ℝ)^101 := by
    have hnat : (1708125389 : ℕ)^133*100000000000000^101 ≤ 9757929765717^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1708125389 10000000000 9757929765717 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1185697139/2000000000 : ℝ)^133 ≤ (2511742852471/5000000000000 : ℝ)^101 := by
    have hnat : (1185697139 : ℕ)^133*5000000000000^101 ≤ 2511742852471^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1185697139 2000000000 2511742852471 5000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2493643859/5000000000 : ℝ), (-1708125389/10000000000 : ℝ), (1185697139/2000000000 : ℝ)] ![(40007213169899/100000000000000 : ℝ), (9757929765717/100000000000000 : ℝ), (2511742852471/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2493643859/5000000000 : ℝ)|^133 ≤ (40007213169899/100000000000000 : ℝ)^101
        have hw : |(2493643859/5000000000 : ℝ)|=(2493643859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1708125389/10000000000 : ℝ)|^133 ≤ (9757929765717/100000000000000 : ℝ)^101
        have hw : |(-1708125389/10000000000 : ℝ)|=(1708125389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1185697139/2000000000 : ℝ)|^133 ≤ (2511742852471/5000000000000 : ℝ)^101
        have hw : |(1185697139/2000000000 : ℝ)|=(1185697139/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304055_s8_s8_23 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2285569173/5000000000 : ℝ)*x 0 + (5679928369/10000000000 : ℝ)*x 1 + (-646562891/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2285569173/5000000000 : ℝ)^133 ≤ (2229406845283/6250000000000 : ℝ)^101 := by
    have hnat : (2285569173 : ℕ)^133*6250000000000^101 ≤ 2229406845283^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2285569173 5000000000 2229406845283 6250000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5679928369/10000000000 : ℝ)^133 ≤ (23740009999113/50000000000000 : ℝ)^101 := by
    have hnat : (5679928369 : ℕ)^133*50000000000000^101 ≤ 23740009999113^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5679928369 10000000000 23740009999113 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (646562891/2500000000 : ℝ)^133 ≤ (16849470462907/100000000000000 : ℝ)^101 := by
    have hnat : (646562891 : ℕ)^133*100000000000000^101 ≤ 16849470462907^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      646562891 2500000000 16849470462907 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2285569173/5000000000 : ℝ), (5679928369/10000000000 : ℝ), (-646562891/2500000000 : ℝ)] ![(2229406845283/6250000000000 : ℝ), (23740009999113/50000000000000 : ℝ), (16849470462907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2285569173/5000000000 : ℝ)|^133 ≤ (2229406845283/6250000000000 : ℝ)^101
        have hw : |(2285569173/5000000000 : ℝ)|=(2285569173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5679928369/10000000000 : ℝ)|^133 ≤ (23740009999113/50000000000000 : ℝ)^101
        have hw : |(5679928369/10000000000 : ℝ)|=(5679928369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-646562891/2500000000 : ℝ)|^133 ≤ (16849470462907/100000000000000 : ℝ)^101
        have hw : |(-646562891/2500000000 : ℝ)|=(646562891/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304055_s8_s8_27 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (6021290647/10000000000 : ℝ)*x 0 + (1877522567/5000000000 : ℝ)*x 1 + (153925841/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6021290647/10000000000 : ℝ)^133 ≤ (51272946220719/100000000000000 : ℝ)^101 := by
    have hnat : (6021290647 : ℕ)^133*100000000000000^101 ≤ 51272946220719^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6021290647 10000000000 51272946220719 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1877522567/5000000000 : ℝ)^133 ≤ (860378974291/3125000000000 : ℝ)^101 := by
    have hnat : (1877522567 : ℕ)^133*3125000000000^101 ≤ 860378974291^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1877522567 5000000000 860378974291 3125000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (153925841/500000000 : ℝ)^133 ≤ (21194926593137/100000000000000 : ℝ)^101 := by
    have hnat : (153925841 : ℕ)^133*100000000000000^101 ≤ 21194926593137^101*500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      153925841 500000000 21194926593137 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6021290647/10000000000 : ℝ), (1877522567/5000000000 : ℝ), (153925841/500000000 : ℝ)] ![(51272946220719/100000000000000 : ℝ), (860378974291/3125000000000 : ℝ), (21194926593137/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6021290647/10000000000 : ℝ)|^133 ≤ (51272946220719/100000000000000 : ℝ)^101
        have hw : |(6021290647/10000000000 : ℝ)|=(6021290647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1877522567/5000000000 : ℝ)|^133 ≤ (860378974291/3125000000000 : ℝ)^101
        have hw : |(1877522567/5000000000 : ℝ)|=(1877522567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(153925841/500000000 : ℝ)|^133 ≤ (21194926593137/100000000000000 : ℝ)^101
        have hw : |(153925841/500000000 : ℝ)|=(153925841/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c304055_s8 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev7 : (0 : ℝ) ≤ ((7001/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7001/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(35929/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(35929/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(35643/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(35643/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((2459/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2459/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2553/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2553/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9987/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(9987/50000 : ℝ)*X 1 2) := by
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
  have main2 : (76617/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76617/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  rcases hprev7 with ⟨ratio_s7_0,ratio_s7_1,ratio_s7_2⟩
  have s8_pow0 : (7001/20000 : ℝ) ^ (33/8 : ℝ) ≤ (329212712341904749/25000000000000000000 : ℝ) := by
    have hpowers : (7001/20000 : ℝ)^33 ≤ (329212712341904749/25000000000000000000 : ℝ)^8 := by
      have hnat : (7001 : ℕ)^33*25000000000000000000^8 ≤ 329212712341904749^8*20000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7001 20000 329212712341904749 25000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7001/20000 : ℝ)) (X := (329212712341904749/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s8_corner0a : (25329212712341904749/25000000000000000000 : ℝ) ≤ (2507941409232343/2500000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (25329212712341904749/25000000000000000000 : ℝ)^8 ≤ (2507941409232343/2500000000000000 : ℝ)^33 := by
      have hnat : (25329212712341904749 : ℕ)^8*2500000000000000^33 ≤ 2507941409232343^33*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25329212712341904749 25000000000000000000 2507941409232343 2500000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2507941409232343/2500000000000000 : ℝ)) (X := (25329212712341904749/25000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s8_corner0b : (12829212712341904749/12500000000000000000 : ℝ) ≤ (10063220016994093/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (12829212712341904749/12500000000000000000 : ℝ)^8 ≤ (10063220016994093/10000000000000000 : ℝ)^33 := by
      have hnat : (12829212712341904749 : ℕ)^8*10000000000000000^33 ≤ 10063220016994093^33*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12829212712341904749 12500000000000000000 10063220016994093 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10063220016994093/10000000000000000 : ℝ)) (X := (12829212712341904749/12500000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s8_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(7941409232343/875125000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(31454380064721/3500500000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (7001/20000 : ℝ)) (alpha := (7941409232343/875125000000000 : ℝ)) (beta := (31454380064721/3500500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s8_pow0,s8_corner0a]) (by linarith only [s8_pow0,s8_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (7001/20000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s7_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(7941409232343/875125000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(31454380064721/3500500000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s8_pow1 : (35929/100000 : ℝ) ^ (33/8 : ℝ) ≤ (733130292652328637/50000000000000000000 : ℝ) := by
    have hpowers : (35929/100000 : ℝ)^33 ≤ (733130292652328637/50000000000000000000 : ℝ)^8 := by
      have hnat : (35929 : ℕ)^33*50000000000000000000^8 ≤ 733130292652328637^8*100000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        35929 100000 733130292652328637 50000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (35929/100000 : ℝ)) (X := (733130292652328637/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s8_corner1a : (50733130292652328637/50000000000000000000 : ℝ) ≤ (10035349968598677/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (50733130292652328637/50000000000000000000 : ℝ)^8 ≤ (10035349968598677/10000000000000000 : ℝ)^33 := by
      have hnat : (50733130292652328637 : ℕ)^8*10000000000000000^33 ≤ 10035349968598677^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50733130292652328637 50000000000000000000 10035349968598677 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10035349968598677/10000000000000000 : ℝ)) (X := (50733130292652328637/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s8_corner1b : (25733130292652328637/25000000000000000000 : ℝ) ≤ (10070315035097369/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (25733130292652328637/25000000000000000000 : ℝ)^8 ≤ (10070315035097369/10000000000000000 : ℝ)^33 := by
      have hnat : (25733130292652328637 : ℕ)^8*10000000000000000^33 ≤ 10070315035097369^33*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25733130292652328637 25000000000000000000 10070315035097369 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10070315035097369/10000000000000000 : ℝ)) (X := (25733130292652328637/25000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s8_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(35349968598677/3592900000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(8741266624673/898225000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (35929/100000 : ℝ)) (alpha := (35349968598677/3592900000000000 : ℝ)) (beta := (8741266624673/898225000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s8_pow1,s8_corner1a]) (by linarith only [s8_pow1,s8_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (35929/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s7_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(35349968598677/3592900000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(8741266624673/898225000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s8_pow2 : (35643/100000 : ℝ) ^ (33/8 : ℝ) ≤ (354677625596561473/25000000000000000000 : ℝ) := by
    have hpowers : (35643/100000 : ℝ)^33 ≤ (354677625596561473/25000000000000000000 : ℝ)^8 := by
      have hnat : (35643 : ℕ)^33*25000000000000000000^8 ≤ 354677625596561473^8*100000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        35643 100000 354677625596561473 25000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (35643/100000 : ℝ)) (X := (354677625596561473/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s8_corner2a : (25354677625596561473/25000000000000000000 : ℝ) ≤ (10034209678641547/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (25354677625596561473/25000000000000000000 : ℝ)^8 ≤ (10034209678641547/10000000000000000 : ℝ)^33 := by
      have hnat : (25354677625596561473 : ℕ)^8*10000000000000000^33 ≤ 10034209678641547^33*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25354677625596561473 25000000000000000000 10034209678641547 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10034209678641547/10000000000000000 : ℝ)) (X := (25354677625596561473/25000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s8_corner2b : (12854677625596561473/12500000000000000000 : ℝ) ≤ (10068058719675709/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (12854677625596561473/12500000000000000000 : ℝ)^8 ≤ (10068058719675709/10000000000000000 : ℝ)^33 := by
      have hnat : (12854677625596561473 : ℕ)^8*10000000000000000^33 ≤ 10068058719675709^33*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12854677625596561473 12500000000000000000 10068058719675709 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10068058719675709/10000000000000000 : ℝ)) (X := (12854677625596561473/12500000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s8_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(11403226213849/1188100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(5641506839027/594050000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (35643/100000 : ℝ)) (alpha := (11403226213849/1188100000000000 : ℝ)) (beta := (5641506839027/594050000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s8_pow2,s8_corner2a]) (by linarith only [s8_pow2,s8_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (35643/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s7_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(11403226213849/1188100000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(5641506839027/594050000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s8_0 : ((-2643512281/10000000000 : ℝ)*X 0 0+(1368746297/2500000000 : ℝ)*X 0 1+(23702279/50000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304055_s8_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s8_1 : ((4738385943/10000000000 : ℝ)*X 1 0+(-956305319/5000000000 : ℝ)*X 1 1+(6021598997/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304055_s8_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s8_2 : ((4740182451/10000000000 : ℝ)*X 2 0+(1367959607/2500000000 : ℝ)*X 2 1+(-2647802929/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304055_s8_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s8_6 : ((5672847261/10000000000 : ℝ)*X 0 0+(1043187829/2500000000 : ℝ)*X 0 1+(3052952011/10000000000 : ℝ)*X 0 2+(5672847261/10000000000 : ℝ)*X 1 0+(1043187829/2500000000 : ℝ)*X 1 1+(3052952011/10000000000 : ℝ)*X 1 2+(5672847261/10000000000 : ℝ)*X 2 0+(1043187829/2500000000 : ℝ)*X 2 1+(3052952011/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304055_s8_s8_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s8_7 : ((-647845497/2500000000 : ℝ)*X 0 0+(2639798633/5000000000 : ℝ)*X 0 1+(249250743/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304055_s8_s8_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s8_8 : ((942860921/2000000000 : ℝ)*X 1 0+(-106616433/625000000 : ℝ)*X 1 1+(6184440711/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304055_s8_s8_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s8_9 : ((943220309/2000000000 : ℝ)*X 2 0+(227287579/400000000 : ℝ)*X 2 1+(-1203424819/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304055_s8_s8_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s8_13 : ((222568847/400000000 : ℝ)*X 0 0+(915099183/2000000000 : ℝ)*X 0 1+(2727798999/10000000000 : ℝ)*X 0 2+(222568847/400000000 : ℝ)*X 1 0+(915099183/2000000000 : ℝ)*X 1 1+(2727798999/10000000000 : ℝ)*X 1 2+(222568847/400000000 : ℝ)*X 2 0+(915099183/2000000000 : ℝ)*X 2 1+(2727798999/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304055_s8_s8_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s8_14 : ((-2381521731/10000000000 : ℝ)*X 0 0+(1084735169/2000000000 : ℝ)*X 0 1+(2502994397/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304055_s8_s8_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s8_15 : ((4586071651/10000000000 : ℝ)*X 1 0+(-1882175843/10000000000 : ℝ)*X 1 1+(1236496743/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304055_s8_s8_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s8_16 : ((2502888249/5000000000 : ℝ)*X 2 0+(5420527531/10000000000 : ℝ)*X 2 1+(-2385874989/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304055_s8_s8_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s8_20 : ((1496817841/2500000000 : ℝ)*X 0 0+(2054483049/5000000000 : ℝ)*X 0 1+(2731777633/10000000000 : ℝ)*X 0 2+(1496817841/2500000000 : ℝ)*X 1 0+(2054483049/5000000000 : ℝ)*X 1 1+(2731777633/10000000000 : ℝ)*X 1 2+(1496817841/2500000000 : ℝ)*X 2 0+(2054483049/5000000000 : ℝ)*X 2 1+(2731777633/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304055_s8_s8_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s8_21 : ((-2398213617/10000000000 : ℝ)*X 0 0+(1420769271/2500000000 : ℝ)*X 0 1+(590266643/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304055_s8_s8_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s8_22 : ((2493643859/5000000000 : ℝ)*X 1 0+(-1708125389/10000000000 : ℝ)*X 1 1+(1185697139/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304055_s8_s8_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s8_23 : ((2285569173/5000000000 : ℝ)*X 2 0+(5679928369/10000000000 : ℝ)*X 2 1+(-646562891/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304055_s8_s8_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s8_27 : ((6021290647/10000000000 : ℝ)*X 0 0+(1877522567/5000000000 : ℝ)*X 0 1+(153925841/500000000 : ℝ)*X 0 2+(6021290647/10000000000 : ℝ)*X 1 0+(1877522567/5000000000 : ℝ)*X 1 1+(153925841/500000000 : ℝ)*X 1 2+(6021290647/10000000000 : ℝ)*X 2 0+(1877522567/5000000000 : ℝ)*X 2 1+(153925841/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304055_s8_s8_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s8_0 : (0 : ℝ) ≤ ((2459/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2459/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (6044188505498216503420379499441/373566751931125000000000000000000000 : ℝ) := by norm_num
    linear_combination (261207006777/100000000000 : ℝ)*(base49) + (3370167/1000000000000 : ℝ)*(base60) + (18383519516017/1000000000000 : ℝ)*(major_s8_0) + (18383519516017/1000000000000 : ℝ)*(major_s8_1) + (18383519516017/1000000000000 : ℝ)*(major_s8_2) + (40672339/250000000000 : ℝ)*(sp_s8_0) + (8303263/62500000000 : ℝ)*(sp_s8_1) + (7650567/50000000000 : ℝ)*(sp_s8_6) + (24646295288797/1000000000000 : ℝ)*(sp_s8_7) + (24646019228193/1000000000000 : ℝ)*(sp_s8_8) + (3080756661623/125000000000 : ℝ)*(sp_s8_9) + (12120422649307/1000000000000 : ℝ)*(sp_s8_13) + (38237219/125000000000 : ℝ)*(sp_s8_15) + (404685169/1000000000000 : ℝ)*(sp_s8_23) + (12120575660647/1000000000000 : ℝ)*(f.failure) + (12323228989077/500000000000 : ℝ)*(f.sum) + (1632534453616370971/10671811225000000000000000000000 : ℝ)*base62 + (85890302899771/148512500000000000000000000 : ℝ)*base65 + (186259614303067/1796450000000000000000000000 : ℝ)*base66 + (159729746661373/1188100000000000000000000000 : ℝ)*base69 + (1494118463503517623/5198680062500000000000000000000 : ℝ)*base71 + (1190058519050657/3500500000000000000000000000 : ℝ)*base73 + (1301965742684999/3592900000000000000000000000 : ℝ)*base75 + (156246765537003/437562500000000000000000000 : ℝ)*base77 + (49090323635795807317/125769464500000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (6027/12500000000000000 : ℝ)*base86 + (6027/12500000000000000 : ℝ)*base88 + (6027/12500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s8_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2553/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2553/12500 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (300077616866074656695682279/20794720250000000000000000000000 : ℝ) := by norm_num
    linear_combination (620286504781/250000000000 : ℝ)*(base49) + (3840641/1000000000000 : ℝ)*(base60) + (17848298696149/1000000000000 : ℝ)*(major_s8_0) + (17848298696149/1000000000000 : ℝ)*(major_s8_1) + (17848298696149/1000000000000 : ℝ)*(major_s8_2) + (212653953/1000000000000 : ℝ)*(sp_s8_1) + (95506949/500000000000 : ℝ)*(sp_s8_2) + (200879907/1000000000000 : ℝ)*(sp_s8_7) + (31124031/200000000000 : ℝ)*(sp_s8_8) + (747771765027/31250000000 : ℝ)*(sp_s8_14) + (23928529086663/1000000000000 : ℝ)*(sp_s8_15) + (23928706346873/1000000000000 : ℝ)*(sp_s8_16) + (1470937606379/125000000000 : ℝ)*(sp_s8_20) + (194370333/1000000000000 : ℝ)*(sp_s8_27) + (2353539044273/200000000000 : ℝ)*(f.failure) + (23928897360771/1000000000000 : ℝ)*(f.sum) + (1967958628288279877/2667952806250000000000000000000 : ℝ)*base63 + (461028380868477/594050000000000000000000000 : ℝ)*base64 + (416667853591797/898225000000000000000000000 : ℝ)*base66 + (234267508945041/1188100000000000000000000000 : ℝ)*base69 + (2329612404449609113/10397360125000000000000000000000 : ℝ)*base70 + (1376028327825921/3500500000000000000000000000 : ℝ)*base72 + (871986452290917/3592900000000000000000000000 : ℝ)*base74 + (602485257072411/1750250000000000000000000000 : ℝ)*base76 + (10735177059351162351/125769464500000000000000000000000 : ℝ)*base79 + (693/2500000000000000 : ℝ)*base86 + (693/2500000000000000 : ℝ)*base88 + (693/2500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s8_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9987/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(9987/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (20496961325215449/2500000000000000000000 : ℝ) := by norm_num
    linear_combination (31904363317/12500000000 : ℝ)*(base49) + (17846583606501/1000000000000 : ℝ)*(major_s8_0) + (17846583606501/1000000000000 : ℝ)*(major_s8_1) + (17846583606501/1000000000000 : ℝ)*(major_s8_2) + (74914921/1000000000000 : ℝ)*(sp_s8_0) + (15013117/250000000000 : ℝ)*(sp_s8_1) + (10820943/125000000000 : ℝ)*(sp_s8_2) + (106261703/1000000000000 : ℝ)*(sp_s8_9) + (46733127/1000000000000 : ℝ)*(sp_s8_14) + (14116537/1000000000000 : ℝ)*(sp_s8_20) + (23926478399229/1000000000000 : ℝ)*(sp_s8_21) + (2392653999481/100000000000 : ℝ)*(sp_s8_22) + (2392640721803/100000000000 : ℝ)*(sp_s8_23) + (11766550316253/1000000000000 : ℝ)*(sp_s8_27) + (1176656443279/100000000000 : ℝ)*(f.failure) + (11963300023639/500000000000 : ℝ)*(f.sum) + (305557545992589751/688503950000000000000000000000 : ℝ)*base62 + (24759539520287/37128125000000000000000000 : ℝ)*base65 + (9964328596609/57950000000000000000000000 : ℝ)*base67 + (49279021417319/1188100000000000000000000000 : ℝ)*base69 + (2575809747798653349/20794720250000000000000000000000 : ℝ)*base70 + (532666136404871/3500500000000000000000000000 : ℝ)*base73 + (59826349685547/115900000000000000000000000 : ℝ)*base75 + (1165964722014811/1750250000000000000000000000 : ℝ)*base77 + (3213275445488417971/4057079500000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base84 + (311/1250000000000000 : ℝ)*base87 + (311/1250000000000000 : ℝ)*base89 + (311/1250000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s8_0,ratio_s8_1,ratio_s8_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev7 : (0 : ℝ) ≤ ((7001/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7001/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(35929/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(35929/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(35643/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(35643/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((2459/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2459/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2553/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2553/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9987/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(9987/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c304055_s8 p hpa hpb X hX hprev7

#print axioms solution
