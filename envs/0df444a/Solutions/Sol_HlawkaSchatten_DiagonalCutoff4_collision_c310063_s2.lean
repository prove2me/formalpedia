-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c310063_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:28:13.198176+00:00
-- url     : https://prove2.me/submissions/26122379-207c-4ae3-8934-4edb82e317e1

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
theorem collision_support_c310063_s2_s2_0 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-431094973/5000000000 : ℝ)*x 0 + (1115262911/2000000000 : ℝ)*x 1 + (5729415857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (431094973/5000000000 : ℝ)^71 ≤ (169051943747/4000000000000 : ℝ)^55 := by
    have hnat : (431094973 : ℕ)^71*4000000000000^55 ≤ 169051943747^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431094973 5000000000 169051943747 4000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1115262911/2000000000 : ℝ)^71 ≤ (11762439042841/25000000000000 : ℝ)^55 := by
    have hnat : (1115262911 : ℕ)^71*25000000000000^55 ≤ 11762439042841^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1115262911 2000000000 11762439042841 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5729415857/10000000000 : ℝ)^71 ≤ (48723945222067/100000000000000 : ℝ)^55 := by
    have hnat : (5729415857 : ℕ)^71*100000000000000^55 ≤ 48723945222067^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5729415857 10000000000 48723945222067 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-431094973/5000000000 : ℝ), (1115262911/2000000000 : ℝ), (5729415857/10000000000 : ℝ)] ![(169051943747/4000000000000 : ℝ), (11762439042841/25000000000000 : ℝ), (48723945222067/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-431094973/5000000000 : ℝ)|^71 ≤ (169051943747/4000000000000 : ℝ)^55
        have hw : |(-431094973/5000000000 : ℝ)|=(431094973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1115262911/2000000000 : ℝ)|^71 ≤ (11762439042841/25000000000000 : ℝ)^55
        have hw : |(1115262911/2000000000 : ℝ)|=(1115262911/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5729415857/10000000000 : ℝ)|^71 ≤ (48723945222067/100000000000000 : ℝ)^55
        have hw : |(5729415857/10000000000 : ℝ)|=(5729415857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310063_s2_s2_1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (697037513/1250000000 : ℝ)*x 0 + (-107738577/1250000000 : ℝ)*x 1 + (1145918469/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (697037513/1250000000 : ℝ)^71 ≤ (9409919754361/20000000000000 : ℝ)^55 := by
    have hnat : (697037513 : ℕ)^71*20000000000000^55 ≤ 9409919754361^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      697037513 1250000000 9409919754361 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (107738577/1250000000 : ℝ)^71 ≤ (66008101213/1562500000000 : ℝ)^55 := by
    have hnat : (107738577 : ℕ)^71*1562500000000^55 ≤ 66008101213^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107738577 1250000000 66008101213 1562500000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1145918469/2000000000 : ℝ)^71 ≤ (48725882736237/100000000000000 : ℝ)^55 := by
    have hnat : (1145918469 : ℕ)^71*100000000000000^55 ≤ 48725882736237^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1145918469 2000000000 48725882736237 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(697037513/1250000000 : ℝ), (-107738577/1250000000 : ℝ), (1145918469/2000000000 : ℝ)] ![(9409919754361/20000000000000 : ℝ), (66008101213/1562500000000 : ℝ), (48725882736237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(697037513/1250000000 : ℝ)|^71 ≤ (9409919754361/20000000000000 : ℝ)^55
        have hw : |(697037513/1250000000 : ℝ)|=(697037513/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-107738577/1250000000 : ℝ)|^71 ≤ (66008101213/1562500000000 : ℝ)^55
        have hw : |(-107738577/1250000000 : ℝ)|=(107738577/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1145918469/2000000000 : ℝ)|^71 ≤ (48725882736237/100000000000000 : ℝ)^55
        have hw : |(1145918469/2000000000 : ℝ)|=(1145918469/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310063_s2_s2_2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5633251143/10000000000 : ℝ)*x 0 + (570759253/1000000000 : ℝ)*x 1 + (-400621757/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5633251143/10000000000 : ℝ)^71 ≤ (47670825637523/100000000000000 : ℝ)^55 := by
    have hnat : (5633251143 : ℕ)^71*100000000000000^55 ≤ 47670825637523^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5633251143 10000000000 47670825637523 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (570759253/1000000000 : ℝ)^71 ≤ (48484499092507/100000000000000 : ℝ)^55 := by
    have hnat : (570759253 : ℕ)^71*100000000000000^55 ≤ 48484499092507^55*1000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      570759253 1000000000 48484499092507 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (400621757/5000000000 : ℝ)^71 ≤ (384467525133/10000000000000 : ℝ)^55 := by
    have hnat : (400621757 : ℕ)^71*10000000000000^55 ≤ 384467525133^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      400621757 5000000000 384467525133 10000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5633251143/10000000000 : ℝ), (570759253/1000000000 : ℝ), (-400621757/5000000000 : ℝ)] ![(47670825637523/100000000000000 : ℝ), (48484499092507/100000000000000 : ℝ), (384467525133/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5633251143/10000000000 : ℝ)|^71 ≤ (47670825637523/100000000000000 : ℝ)^55
        have hw : |(5633251143/10000000000 : ℝ)|=(5633251143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(570759253/1000000000 : ℝ)|^71 ≤ (48484499092507/100000000000000 : ℝ)^55
        have hw : |(570759253/1000000000 : ℝ)|=(570759253/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-400621757/5000000000 : ℝ)|^71 ≤ (384467525133/10000000000000 : ℝ)^55
        have hw : |(-400621757/5000000000 : ℝ)|=(400621757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310063_s2_s2_6 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (279426623/625000000 : ℝ)*x 0 + (53746223/125000000 : ℝ)*x 1 + (252208481/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (279426623/625000000 : ℝ)^71 ≤ (17686927336733/50000000000000 : ℝ)^55 := by
    have hnat : (279426623 : ℕ)^71*50000000000000^55 ≤ 17686927336733^55*625000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      279426623 625000000 17686927336733 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (53746223/125000000 : ℝ)^71 ≤ (33635795249887/100000000000000 : ℝ)^55 := by
    have hnat : (53746223 : ℕ)^71*100000000000000^55 ≤ 33635795249887^55*125000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53746223 125000000 33635795249887 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (252208481/625000000 : ℝ)^71 ≤ (30990350060963/100000000000000 : ℝ)^55 := by
    have hnat : (252208481 : ℕ)^71*100000000000000^55 ≤ 30990350060963^55*625000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      252208481 625000000 30990350060963 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(279426623/625000000 : ℝ), (53746223/125000000 : ℝ), (252208481/625000000 : ℝ)] ![(17686927336733/50000000000000 : ℝ), (33635795249887/100000000000000 : ℝ), (30990350060963/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(279426623/625000000 : ℝ)|^71 ≤ (17686927336733/50000000000000 : ℝ)^55
        have hw : |(279426623/625000000 : ℝ)|=(279426623/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(53746223/125000000 : ℝ)|^71 ≤ (33635795249887/100000000000000 : ℝ)^55
        have hw : |(53746223/125000000 : ℝ)|=(53746223/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(252208481/625000000 : ℝ)|^71 ≤ (30990350060963/100000000000000 : ℝ)^55
        have hw : |(252208481/625000000 : ℝ)|=(252208481/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310063_s2_s2_7 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-520461753/5000000000 : ℝ)*x 0 + (3570309001/10000000000 : ℝ)*x 1 + (3715071733/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (520461753/5000000000 : ℝ)^71 ≤ (5389854193489/100000000000000 : ℝ)^55 := by
    have hnat : (520461753 : ℕ)^71*100000000000000^55 ≤ 5389854193489^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520461753 5000000000 5389854193489 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3570309001/10000000000 : ℝ)^71 ≤ (3307454436933/12500000000000 : ℝ)^55 := by
    have hnat : (3570309001 : ℕ)^71*12500000000000^55 ≤ 3307454436933^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3570309001 10000000000 3307454436933 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3715071733/5000000000 : ℝ)^71 ≤ (68150510291443/100000000000000 : ℝ)^55 := by
    have hnat : (3715071733 : ℕ)^71*100000000000000^55 ≤ 68150510291443^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3715071733 5000000000 68150510291443 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-520461753/5000000000 : ℝ), (3570309001/10000000000 : ℝ), (3715071733/5000000000 : ℝ)] ![(5389854193489/100000000000000 : ℝ), (3307454436933/12500000000000 : ℝ), (68150510291443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-520461753/5000000000 : ℝ)|^71 ≤ (5389854193489/100000000000000 : ℝ)^55
        have hw : |(-520461753/5000000000 : ℝ)|=(520461753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3570309001/10000000000 : ℝ)|^71 ≤ (3307454436933/12500000000000 : ℝ)^55
        have hw : |(3570309001/10000000000 : ℝ)|=(3570309001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3715071733/5000000000 : ℝ)|^71 ≤ (68150510291443/100000000000000 : ℝ)^55
        have hw : |(3715071733/5000000000 : ℝ)|=(3715071733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310063_s2_s2_8 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4064104833/10000000000 : ℝ)*x 0 + (-182945939/10000000000 : ℝ)*x 1 + (464396603/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4064104833/10000000000 : ℝ)^71 ≤ (125103433281/400000000000 : ℝ)^55 := by
    have hnat : (4064104833 : ℕ)^71*400000000000^55 ≤ 125103433281^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4064104833 10000000000 125103433281 400000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (182945939/10000000000 : ℝ)^71 ≤ (571237449343/100000000000000 : ℝ)^55 := by
    have hnat : (182945939 : ℕ)^71*100000000000000^55 ≤ 571237449343^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      182945939 10000000000 571237449343 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (464396603/625000000 : ℝ)^71 ≤ (8519113027909/12500000000000 : ℝ)^55 := by
    have hnat : (464396603 : ℕ)^71*12500000000000^55 ≤ 8519113027909^55*625000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      464396603 625000000 8519113027909 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4064104833/10000000000 : ℝ), (-182945939/10000000000 : ℝ), (464396603/625000000 : ℝ)] ![(125103433281/400000000000 : ℝ), (571237449343/100000000000000 : ℝ), (8519113027909/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4064104833/10000000000 : ℝ)|^71 ≤ (125103433281/400000000000 : ℝ)^55
        have hw : |(4064104833/10000000000 : ℝ)|=(4064104833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-182945939/10000000000 : ℝ)|^71 ≤ (571237449343/100000000000000 : ℝ)^55
        have hw : |(-182945939/10000000000 : ℝ)|=(182945939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(464396603/625000000 : ℝ)|^71 ≤ (8519113027909/12500000000000 : ℝ)^55
        have hw : |(464396603/625000000 : ℝ)|=(464396603/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310063_s2_s2_9 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3799407299/10000000000 : ℝ)*x 0 + (7685037439/10000000000 : ℝ)*x 1 + (-31613469/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3799407299/10000000000 : ℝ)^71 ≤ (28671563316871/100000000000000 : ℝ)^55 := by
    have hnat : (3799407299 : ℕ)^71*100000000000000^55 ≤ 28671563316871^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3799407299 10000000000 28671563316871 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7685037439/10000000000 : ℝ)^71 ≤ (14236700914629/20000000000000 : ℝ)^55 := by
    have hnat : (7685037439 : ℕ)^71*20000000000000^55 ≤ 14236700914629^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7685037439 10000000000 14236700914629 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (31613469/5000000000 : ℝ)^71 ≤ (144932102887/100000000000000 : ℝ)^55 := by
    have hnat : (31613469 : ℕ)^71*100000000000000^55 ≤ 144932102887^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31613469 5000000000 144932102887 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3799407299/10000000000 : ℝ), (7685037439/10000000000 : ℝ), (-31613469/5000000000 : ℝ)] ![(28671563316871/100000000000000 : ℝ), (14236700914629/20000000000000 : ℝ), (144932102887/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3799407299/10000000000 : ℝ)|^71 ≤ (28671563316871/100000000000000 : ℝ)^55
        have hw : |(3799407299/10000000000 : ℝ)|=(3799407299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7685037439/10000000000 : ℝ)|^71 ≤ (14236700914629/20000000000000 : ℝ)^55
        have hw : |(7685037439/10000000000 : ℝ)|=(7685037439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-31613469/5000000000 : ℝ)|^71 ≤ (144932102887/100000000000000 : ℝ)^55
        have hw : |(-31613469/5000000000 : ℝ)|=(31613469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310063_s2_s2_13 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (765673853/2000000000 : ℝ)*x 0 + (3408398001/5000000000 : ℝ)*x 1 + (105569697/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (765673853/2000000000 : ℝ)^71 ≤ (289540120423/1000000000000 : ℝ)^55 := by
    have hnat : (765673853 : ℕ)^71*1000000000000^55 ≤ 289540120423^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      765673853 2000000000 289540120423 1000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3408398001/5000000000 : ℝ)^71 ≤ (7622146753921/12500000000000 : ℝ)^55 := by
    have hnat : (3408398001 : ℕ)^71*12500000000000^55 ≤ 7622146753921^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3408398001 5000000000 7622146753921 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105569697/625000000 : ℝ)^71 ≤ (5034406956623/50000000000000 : ℝ)^55 := by
    have hnat : (105569697 : ℕ)^71*50000000000000^55 ≤ 5034406956623^55*625000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105569697 625000000 5034406956623 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(765673853/2000000000 : ℝ), (3408398001/5000000000 : ℝ), (105569697/625000000 : ℝ)] ![(289540120423/1000000000000 : ℝ), (7622146753921/12500000000000 : ℝ), (5034406956623/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(765673853/2000000000 : ℝ)|^71 ≤ (289540120423/1000000000000 : ℝ)^55
        have hw : |(765673853/2000000000 : ℝ)|=(765673853/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3408398001/5000000000 : ℝ)|^71 ≤ (7622146753921/12500000000000 : ℝ)^55
        have hw : |(3408398001/5000000000 : ℝ)|=(3408398001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(105569697/625000000 : ℝ)|^71 ≤ (5034406956623/50000000000000 : ℝ)^55
        have hw : |(105569697/625000000 : ℝ)|=(105569697/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310063_s2_s2_14 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-31820649/2000000000 : ℝ)*x 0 + (796747089/2000000000 : ℝ)*x 1 + (7505429391/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (31820649/2000000000 : ℝ)^71 ≤ (238506997577/50000000000000 : ℝ)^55 := by
    have hnat : (31820649 : ℕ)^71*50000000000000^55 ≤ 238506997577^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31820649 2000000000 238506997577 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (796747089/2000000000 : ℝ)^71 ≤ (30479747119797/100000000000000 : ℝ)^55 := by
    have hnat : (796747089 : ℕ)^71*100000000000000^55 ≤ 30479747119797^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      796747089 2000000000 30479747119797 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7505429391/10000000000 : ℝ)^71 ≤ (69043238870827/100000000000000 : ℝ)^55 := by
    have hnat : (7505429391 : ℕ)^71*100000000000000^55 ≤ 69043238870827^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7505429391 10000000000 69043238870827 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-31820649/2000000000 : ℝ), (796747089/2000000000 : ℝ), (7505429391/10000000000 : ℝ)] ![(238506997577/50000000000000 : ℝ), (30479747119797/100000000000000 : ℝ), (69043238870827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-31820649/2000000000 : ℝ)|^71 ≤ (238506997577/50000000000000 : ℝ)^55
        have hw : |(-31820649/2000000000 : ℝ)|=(31820649/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(796747089/2000000000 : ℝ)|^71 ≤ (30479747119797/100000000000000 : ℝ)^55
        have hw : |(796747089/2000000000 : ℝ)|=(796747089/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7505429391/10000000000 : ℝ)|^71 ≤ (69043238870827/100000000000000 : ℝ)^55
        have hw : |(7505429391/10000000000 : ℝ)|=(7505429391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310063_s2_s2_15 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (86622387/250000000 : ℝ)*x 0 + (-1057189991/10000000000 : ℝ)*x 1 + (750563321/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (86622387/250000000 : ℝ)^71 ≤ (254555107379/1000000000000 : ℝ)^55 := by
    have hnat : (86622387 : ℕ)^71*1000000000000^55 ≤ 254555107379^55*250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86622387 250000000 254555107379 1000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1057189991/10000000000 : ℝ)^71 ≤ (85919218393/1562500000000 : ℝ)^55 := by
    have hnat : (1057189991 : ℕ)^71*1562500000000^55 ≤ 85919218393^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057189991 10000000000 85919218393 1562500000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (750563321/1000000000 : ℝ)^71 ≤ (69045659273667/100000000000000 : ℝ)^55 := by
    have hnat : (750563321 : ℕ)^71*100000000000000^55 ≤ 69045659273667^55*1000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      750563321 1000000000 69045659273667 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(86622387/250000000 : ℝ), (-1057189991/10000000000 : ℝ), (750563321/1000000000 : ℝ)] ![(254555107379/1000000000000 : ℝ), (85919218393/1562500000000 : ℝ), (69045659273667/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(86622387/250000000 : ℝ)|^71 ≤ (254555107379/1000000000000 : ℝ)^55
        have hw : |(86622387/250000000 : ℝ)|=(86622387/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1057189991/10000000000 : ℝ)|^71 ≤ (85919218393/1562500000000 : ℝ)^55
        have hw : |(-1057189991/10000000000 : ℝ)|=(1057189991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(750563321/1000000000 : ℝ)|^71 ≤ (69045659273667/100000000000000 : ℝ)^55
        have hw : |(750563321/1000000000 : ℝ)|=(750563321/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310063_s2_s2_16 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (924716141/1250000000 : ℝ)*x 0 + (4136468203/10000000000 : ℝ)*x 1 + (-46189349/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (924716141/1250000000 : ℝ)^71 ≤ (33883477149007/50000000000000 : ℝ)^55 := by
    have hnat : (924716141 : ℕ)^71*50000000000000^55 ≤ 33883477149007^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      924716141 1250000000 33883477149007 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4136468203/10000000000 : ℝ)^71 ≤ (31996596308117/100000000000000 : ℝ)^55 := by
    have hnat : (4136468203 : ℕ)^71*100000000000000^55 ≤ 31996596308117^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4136468203 10000000000 31996596308117 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (46189349/5000000000 : ℝ)^71 ≤ (59112346351/25000000000000 : ℝ)^55 := by
    have hnat : (46189349 : ℕ)^71*25000000000000^55 ≤ 59112346351^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46189349 5000000000 59112346351 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(924716141/1250000000 : ℝ), (4136468203/10000000000 : ℝ), (-46189349/5000000000 : ℝ)] ![(33883477149007/50000000000000 : ℝ), (31996596308117/100000000000000 : ℝ), (59112346351/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(924716141/1250000000 : ℝ)|^71 ≤ (33883477149007/50000000000000 : ℝ)^55
        have hw : |(924716141/1250000000 : ℝ)|=(924716141/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4136468203/10000000000 : ℝ)|^71 ≤ (31996596308117/100000000000000 : ℝ)^55
        have hw : |(4136468203/10000000000 : ℝ)|=(4136468203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-46189349/5000000000 : ℝ)|^71 ≤ (59112346351/25000000000000 : ℝ)^55
        have hw : |(-46189349/5000000000 : ℝ)|=(46189349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310063_s2_s2_20 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7404488697/10000000000 : ℝ)*x 0 + (779101331/2500000000 : ℝ)*x 1 + (1674056393/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7404488697/10000000000 : ℝ)^71 ≤ (33923449704631/50000000000000 : ℝ)^55 := by
    have hnat : (7404488697 : ℕ)^71*50000000000000^55 ≤ 33923449704631^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7404488697 10000000000 33923449704631 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (779101331/2500000000 : ℝ)^71 ≤ (22200014848229/100000000000000 : ℝ)^55 := by
    have hnat : (779101331 : ℕ)^71*100000000000000^55 ≤ 22200014848229^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      779101331 2500000000 22200014848229 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1674056393/10000000000 : ℝ)^71 ≤ (4976542860657/50000000000000 : ℝ)^55 := by
    have hnat : (1674056393 : ℕ)^71*50000000000000^55 ≤ 4976542860657^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1674056393 10000000000 4976542860657 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7404488697/10000000000 : ℝ), (779101331/2500000000 : ℝ), (1674056393/10000000000 : ℝ)] ![(33923449704631/50000000000000 : ℝ), (22200014848229/100000000000000 : ℝ), (4976542860657/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7404488697/10000000000 : ℝ)|^71 ≤ (33923449704631/50000000000000 : ℝ)^55
        have hw : |(7404488697/10000000000 : ℝ)|=(7404488697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(779101331/2500000000 : ℝ)|^71 ≤ (22200014848229/100000000000000 : ℝ)^55
        have hw : |(779101331/2500000000 : ℝ)|=(779101331/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1674056393/10000000000 : ℝ)|^71 ≤ (4976542860657/50000000000000 : ℝ)^55
        have hw : |(1674056393/10000000000 : ℝ)|=(1674056393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310063_s2_s2_21 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-134717977/10000000000 : ℝ)*x 0 + (6846136487/10000000000 : ℝ)*x 1 + (2377316079/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134717977/10000000000 : ℝ)^71 ≤ (192410356811/50000000000000 : ℝ)^55 := by
    have hnat : (134717977 : ℕ)^71*50000000000000^55 ≤ 192410356811^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134717977 10000000000 192410356811 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6846136487/10000000000 : ℝ)^71 ≤ (6131619103081/10000000000000 : ℝ)^55 := by
    have hnat : (6846136487 : ℕ)^71*10000000000000^55 ≤ 6131619103081^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6846136487 10000000000 6131619103081 10000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2377316079/5000000000 : ℝ)^71 ≤ (7659797646577/20000000000000 : ℝ)^55 := by
    have hnat : (2377316079 : ℕ)^71*20000000000000^55 ≤ 7659797646577^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2377316079 5000000000 7659797646577 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-134717977/10000000000 : ℝ), (6846136487/10000000000 : ℝ), (2377316079/5000000000 : ℝ)] ![(192410356811/50000000000000 : ℝ), (6131619103081/10000000000000 : ℝ), (7659797646577/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-134717977/10000000000 : ℝ)|^71 ≤ (192410356811/50000000000000 : ℝ)^55
        have hw : |(-134717977/10000000000 : ℝ)|=(134717977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6846136487/10000000000 : ℝ)|^71 ≤ (6131619103081/10000000000000 : ℝ)^55
        have hw : |(6846136487/10000000000 : ℝ)|=(6846136487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2377316079/5000000000 : ℝ)|^71 ≤ (7659797646577/20000000000000 : ℝ)^55
        have hw : |(2377316079/5000000000 : ℝ)|=(2377316079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310063_s2_s2_22 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7382321839/10000000000 : ℝ)*x 0 + (-75785217/10000000000 : ℝ)*x 1 + (832006001/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7382321839/10000000000 : ℝ)^71 ≤ (6758481243243/10000000000000 : ℝ)^55 := by
    have hnat : (7382321839 : ℕ)^71*10000000000000^55 ≤ 6758481243243^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7382321839 10000000000 6758481243243 10000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (75785217/10000000000 : ℝ)^71 ≤ (7324809663/4000000000000 : ℝ)^55 := by
    have hnat : (75785217 : ℕ)^71*4000000000000^55 ≤ 7324809663^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      75785217 10000000000 7324809663 4000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (832006001/2000000000 : ℝ)^71 ≤ (16116033658737/50000000000000 : ℝ)^55 := by
    have hnat : (832006001 : ℕ)^71*50000000000000^55 ≤ 16116033658737^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      832006001 2000000000 16116033658737 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7382321839/10000000000 : ℝ), (-75785217/10000000000 : ℝ), (832006001/2000000000 : ℝ)] ![(6758481243243/10000000000000 : ℝ), (7324809663/4000000000000 : ℝ), (16116033658737/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7382321839/10000000000 : ℝ)|^71 ≤ (6758481243243/10000000000000 : ℝ)^55
        have hw : |(7382321839/10000000000 : ℝ)|=(7382321839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-75785217/10000000000 : ℝ)|^71 ≤ (7324809663/4000000000000 : ℝ)^55
        have hw : |(-75785217/10000000000 : ℝ)|=(75785217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(832006001/2000000000 : ℝ)|^71 ≤ (16116033658737/50000000000000 : ℝ)^55
        have hw : |(832006001/2000000000 : ℝ)|=(832006001/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310063_s2_s2_23 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3394350341/10000000000 : ℝ)*x 0 + (1518842829/2000000000 : ℝ)*x 1 + (-999132117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3394350341/10000000000 : ℝ)^71 ≤ (24788458081707/100000000000000 : ℝ)^55 := by
    have hnat : (3394350341 : ℕ)^71*100000000000000^55 ≤ 24788458081707^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3394350341 10000000000 24788458081707 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1518842829/2000000000 : ℝ)^71 ≤ (17524846373517/25000000000000 : ℝ)^55 := by
    have hnat : (1518842829 : ℕ)^71*25000000000000^55 ≤ 17524846373517^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1518842829 2000000000 17524846373517 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (999132117/10000000000 : ℝ)^71 ≤ (5112156405409/100000000000000 : ℝ)^55 := by
    have hnat : (999132117 : ℕ)^71*100000000000000^55 ≤ 5112156405409^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      999132117 10000000000 5112156405409 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3394350341/10000000000 : ℝ), (1518842829/2000000000 : ℝ), (-999132117/10000000000 : ℝ)] ![(24788458081707/100000000000000 : ℝ), (17524846373517/25000000000000 : ℝ), (5112156405409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3394350341/10000000000 : ℝ)|^71 ≤ (24788458081707/100000000000000 : ℝ)^55
        have hw : |(3394350341/10000000000 : ℝ)|=(3394350341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1518842829/2000000000 : ℝ)|^71 ≤ (17524846373517/25000000000000 : ℝ)^55
        have hw : |(1518842829/2000000000 : ℝ)|=(1518842829/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-999132117/10000000000 : ℝ)|^71 ≤ (5112156405409/100000000000000 : ℝ)^55
        have hw : |(-999132117/10000000000 : ℝ)|=(999132117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310063_s2_s2_27 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1510300417/2000000000 : ℝ)*x 0 + (2549466777/10000000000 : ℝ)*x 1 + (1046436841/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1510300417/2000000000 : ℝ)^71 ≤ (34795424782329/50000000000000 : ℝ)^55 := by
    have hnat : (1510300417 : ℕ)^71*50000000000000^55 ≤ 34795424782329^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1510300417 2000000000 34795424782329 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2549466777/10000000000 : ℝ)^71 ≤ (8565448007269/50000000000000 : ℝ)^55 := by
    have hnat : (2549466777 : ℕ)^71*50000000000000^55 ≤ 8565448007269^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2549466777 10000000000 8565448007269 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1046436841/5000000000 : ℝ)^71 ≤ (2655650880923/20000000000000 : ℝ)^55 := by
    have hnat : (1046436841 : ℕ)^71*20000000000000^55 ≤ 2655650880923^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046436841 5000000000 2655650880923 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1510300417/2000000000 : ℝ), (2549466777/10000000000 : ℝ), (1046436841/5000000000 : ℝ)] ![(34795424782329/50000000000000 : ℝ), (8565448007269/50000000000000 : ℝ), (2655650880923/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1510300417/2000000000 : ℝ)|^71 ≤ (34795424782329/50000000000000 : ℝ)^55
        have hw : |(1510300417/2000000000 : ℝ)|=(1510300417/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2549466777/10000000000 : ℝ)|^71 ≤ (8565448007269/50000000000000 : ℝ)^55
        have hw : |(2549466777/10000000000 : ℝ)|=(2549466777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1046436841/5000000000 : ℝ)|^71 ≤ (2655650880923/20000000000000 : ℝ)^55
        have hw : |(1046436841/5000000000 : ℝ)|=(1046436841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c310063_s2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((18933/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(18933/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1893/2500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1893/2500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1827/2500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(1827/2500 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((15703/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15703/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(63347/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(63347/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(12163/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(12163/20000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (2431/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (2431/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (18111/10000 : ℝ) := by
    linarith only [f.Tcap]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  have s2_pow0 : (18933/25000 : ℝ) ^ (35/8 : ℝ) ≤ (29637904187285145027/100000000000000000000 : ℝ) := by
    have hpowers : (18933/25000 : ℝ)^35 ≤ (29637904187285145027/100000000000000000000 : ℝ)^8 := by
      have hnat : (18933 : ℕ)^35*100000000000000000000^8 ≤ 29637904187285145027^8*25000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18933 25000 29637904187285145027 100000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18933/25000 : ℝ)) (X := (29637904187285145027/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner0a : (129637904187285145027/100000000000000000000 : ℝ) ≤ (5305634382375287/5000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (129637904187285145027/100000000000000000000 : ℝ)^8 ≤ (5305634382375287/5000000000000000 : ℝ)^35 := by
      have hnat : (129637904187285145027 : ℕ)^8*5000000000000000^35 ≤ 5305634382375287^35*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        129637904187285145027 100000000000000000000 5305634382375287 5000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5305634382375287/5000000000000000 : ℝ)) (X := (129637904187285145027/100000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner0b : (79637904187285145027/50000000000000000000 : ℝ) ≤ (1390322930722873/1250000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (79637904187285145027/50000000000000000000 : ℝ)^8 ≤ (1390322930722873/1250000000000000 : ℝ)^35 := by
      have hnat : (79637904187285145027 : ℕ)^8*1250000000000000^35 ≤ 1390322930722873^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        79637904187285145027 50000000000000000000 1390322930722873 1250000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1390322930722873/1250000000000000 : ℝ)) (X := (79637904187285145027/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(101878127458429/1262200000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(51131468103241/757320000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (18933/25000 : ℝ)) (alpha := (101878127458429/1262200000000000 : ℝ)) (beta := (51131468103241/757320000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (18933/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(101878127458429/1262200000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(51131468103241/757320000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (1893/2500 : ℝ) ^ (35/8 : ℝ) ≤ (370217045955810869/1250000000000000000 : ℝ) := by
    have hpowers : (1893/2500 : ℝ)^35 ≤ (370217045955810869/1250000000000000000 : ℝ)^8 := by
      have hnat : (1893 : ℕ)^35*1250000000000000000^8 ≤ 370217045955810869^8*2500^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1893 2500 370217045955810869 1250000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1893/2500 : ℝ)) (X := (370217045955810869/1250000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner1a : (1620217045955810869/1250000000000000000 : ℝ) ≤ (10610884442933439/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (1620217045955810869/1250000000000000000 : ℝ)^8 ≤ (10610884442933439/10000000000000000 : ℝ)^35 := by
      have hnat : (1620217045955810869 : ℕ)^8*10000000000000000^35 ≤ 10610884442933439^35*1250000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1620217045955810869 1250000000000000000 10610884442933439 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10610884442933439/10000000000000000 : ℝ)) (X := (1620217045955810869/1250000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner1b : (995217045955810869/625000000000000000 : ℝ) ≤ (2780481914907199/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (995217045955810869/625000000000000000 : ℝ)^8 ≤ (2780481914907199/2500000000000000 : ℝ)^35 := by
      have hnat : (995217045955810869 : ℕ)^8*2500000000000000^35 ≤ 2780481914907199^35*625000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        995217045955810869 625000000000000000 2780481914907199 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2780481914907199/2500000000000000 : ℝ)) (X := (995217045955810869/625000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(610884442933439/7572000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(511043216695357/7572000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (1893/2500 : ℝ)) (alpha := (610884442933439/7572000000000000 : ℝ)) (beta := (511043216695357/7572000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1893/2500 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(610884442933439/7572000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(511043216695357/7572000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (1827/2500 : ℝ) ^ (35/8 : ℝ) ≤ (5071642147908970411/20000000000000000000 : ℝ) := by
    have hpowers : (1827/2500 : ℝ)^35 ≤ (5071642147908970411/20000000000000000000 : ℝ)^8 := by
      have hnat : (1827 : ℕ)^35*20000000000000000000^8 ≤ 5071642147908970411^8*2500^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1827 2500 5071642147908970411 20000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1827/2500 : ℝ)) (X := (5071642147908970411/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner2a : (25071642147908970411/20000000000000000000 : ℝ) ≤ (5265079419593201/5000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (25071642147908970411/20000000000000000000 : ℝ)^8 ≤ (5265079419593201/5000000000000000 : ℝ)^35 := by
      have hnat : (25071642147908970411 : ℕ)^8*5000000000000000^35 ≤ 5265079419593201^35*20000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25071642147908970411 20000000000000000000 5265079419593201 5000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5265079419593201/5000000000000000 : ℝ)) (X := (25071642147908970411/20000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner2b : (15071642147908970411/10000000000000000000 : ℝ) ≤ (10983036247196843/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (15071642147908970411/10000000000000000000 : ℝ)^8 ≤ (10983036247196843/10000000000000000 : ℝ)^35 := by
      have hnat : (15071642147908970411 : ℕ)^8*10000000000000000^35 ≤ 10983036247196843^35*10000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15071642147908970411 10000000000000000000 10983036247196843 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10983036247196843/10000000000000000 : ℝ)) (X := (15071642147908970411/10000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(29453268843689/406000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(452877408010441/7308000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (1827/2500 : ℝ)) (alpha := (29453268843689/406000000000000 : ℝ)) (beta := (452877408010441/7308000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1827/2500 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(29453268843689/406000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(452877408010441/7308000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-431094973/5000000000 : ℝ)*X 0 0+(1115262911/2000000000 : ℝ)*X 0 1+(5729415857/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310063_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((697037513/1250000000 : ℝ)*X 1 0+(-107738577/1250000000 : ℝ)*X 1 1+(1145918469/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310063_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((5633251143/10000000000 : ℝ)*X 2 0+(570759253/1000000000 : ℝ)*X 2 1+(-400621757/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310063_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((279426623/625000000 : ℝ)*X 0 0+(53746223/125000000 : ℝ)*X 0 1+(252208481/625000000 : ℝ)*X 0 2+(279426623/625000000 : ℝ)*X 1 0+(53746223/125000000 : ℝ)*X 1 1+(252208481/625000000 : ℝ)*X 1 2+(279426623/625000000 : ℝ)*X 2 0+(53746223/125000000 : ℝ)*X 2 1+(252208481/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310063_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-520461753/5000000000 : ℝ)*X 0 0+(3570309001/10000000000 : ℝ)*X 0 1+(3715071733/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310063_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((4064104833/10000000000 : ℝ)*X 1 0+(-182945939/10000000000 : ℝ)*X 1 1+(464396603/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310063_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((3799407299/10000000000 : ℝ)*X 2 0+(7685037439/10000000000 : ℝ)*X 2 1+(-31613469/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310063_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((765673853/2000000000 : ℝ)*X 0 0+(3408398001/5000000000 : ℝ)*X 0 1+(105569697/625000000 : ℝ)*X 0 2+(765673853/2000000000 : ℝ)*X 1 0+(3408398001/5000000000 : ℝ)*X 1 1+(105569697/625000000 : ℝ)*X 1 2+(765673853/2000000000 : ℝ)*X 2 0+(3408398001/5000000000 : ℝ)*X 2 1+(105569697/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310063_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-31820649/2000000000 : ℝ)*X 0 0+(796747089/2000000000 : ℝ)*X 0 1+(7505429391/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310063_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((86622387/250000000 : ℝ)*X 1 0+(-1057189991/10000000000 : ℝ)*X 1 1+(750563321/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310063_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((924716141/1250000000 : ℝ)*X 2 0+(4136468203/10000000000 : ℝ)*X 2 1+(-46189349/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310063_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((7404488697/10000000000 : ℝ)*X 0 0+(779101331/2500000000 : ℝ)*X 0 1+(1674056393/10000000000 : ℝ)*X 0 2+(7404488697/10000000000 : ℝ)*X 1 0+(779101331/2500000000 : ℝ)*X 1 1+(1674056393/10000000000 : ℝ)*X 1 2+(7404488697/10000000000 : ℝ)*X 2 0+(779101331/2500000000 : ℝ)*X 2 1+(1674056393/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310063_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-134717977/10000000000 : ℝ)*X 0 0+(6846136487/10000000000 : ℝ)*X 0 1+(2377316079/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310063_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((7382321839/10000000000 : ℝ)*X 1 0+(-75785217/10000000000 : ℝ)*X 1 1+(832006001/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310063_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((3394350341/10000000000 : ℝ)*X 2 0+(1518842829/2000000000 : ℝ)*X 2 1+(-999132117/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310063_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((1510300417/2000000000 : ℝ)*X 0 0+(2549466777/10000000000 : ℝ)*X 0 1+(1046436841/5000000000 : ℝ)*X 0 2+(1510300417/2000000000 : ℝ)*X 1 0+(2549466777/10000000000 : ℝ)*X 1 1+(1046436841/5000000000 : ℝ)*X 1 2+(1510300417/2000000000 : ℝ)*X 2 0+(2549466777/10000000000 : ℝ)*X 2 1+(1046436841/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310063_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((15703/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15703/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (15854089593029648112520113/995560250000000000000000000000 : ℝ) := by norm_num
    linear_combination (31480752813/62500000000 : ℝ)*(base7) + (832113/500000000000 : ℝ)*(base50) + (90822109567/1000000000000 : ℝ)*(base60) + (2211300377379/1000000000000 : ℝ)*(major_s2_0) + (2211300377379/1000000000000 : ℝ)*(major_s2_1) + (2211300377379/1000000000000 : ℝ)*(major_s2_2) + (6829921/500000000000 : ℝ)*(sp_s2_0) + (495419/250000000000 : ℝ)*(sp_s2_6) + (2751666198827/1000000000000 : ℝ)*(sp_s2_7) + (1375884955043/500000000000 : ℝ)*(sp_s2_8) + (2751769927493/1000000000000 : ℝ)*(sp_s2_9) + (467609173689/250000000000 : ℝ)*(sp_s2_13) + (11258603/125000000000 : ℝ)*(sp_s2_14) + (17407/1000000000000 : ℝ)*(sp_s2_15) + (5338854029/3906250000 : ℝ)*(f.failure) + (2751769927493/1000000000000 : ℝ)*(f.sum) + (14943663941837093/17668000000000000000000000000 : ℝ)*base62 + (12356152162801/28000000000000000000000000 : ℝ)*base64 + (846920245920099/2524000000000000000000000000 : ℝ)*base66 + (11191050598361/14000000000000000000000000 : ℝ)*base68 + (27938152189887971/176708000000000000000000000000 : ℝ)*base70 + (150284946906751/252440000000000000000000000 : ℝ)*base72 + (2491974422133873/2524000000000000000000000000 : ℝ)*base74 + (889990111947789/1262200000000000000000000000 : ℝ)*base76 + (1188015560962747111/15928964000000000000000000000000 : ℝ)*base79 + (2601/3125000000000000 : ℝ)*base87 + (2601/3125000000000000 : ℝ)*base89 + (2601/3125000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(63347/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(63347/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (366736017108795220818527891/48503695380000000000000000000000 : ℝ) := by norm_num
    linear_combination (539711760809/1000000000000 : ℝ)*(base7) + (28733/100000000000 : ℝ)*(base49) + (105363876853/50000000000 : ℝ)*(major_s2_0) + (105363876853/50000000000 : ℝ)*(major_s2_1) + (105363876853/50000000000 : ℝ)*(major_s2_2) + (166701/62500000000 : ℝ)*(sp_s2_1) + (294223/500000000000 : ℝ)*(sp_s2_2) + (5555133/125000000000 : ℝ)*(sp_s2_8) + (2586272777047/1000000000000 : ℝ)*(sp_s2_14) + (2586228607077/1000000000000 : ℝ)*(sp_s2_15) + (258627512691/100000000000 : ℝ)*(sp_s2_16) + (921063682253/500000000000 : ℝ)*(sp_s2_20) + (2938309/1000000000000 : ℝ)*(sp_s2_21) + (37244733/1000000000000 : ℝ)*(sp_s2_27) + (130245284843/100000000000 : ℝ)*(f.failure) + (646568928839/250000000000 : ℝ)*(f.sum) + (13174849828759543/76855800000000000000000000000 : ℝ)*base63 + (35912052917353/365400000000000000000000000 : ℝ)*base65 + (113649802892341/378600000000000000000000000 : ℝ)*base67 + (3855690866973/20300000000000000000000000 : ℝ)*base68 + (252128043167509343/2306039400000000000000000000000 : ℝ)*base71 + (78222802702093/189330000000000000000000000 : ℝ)*base72 + (132738540411767/378600000000000000000000000 : ℝ)*base75 + (2589019453223/15777500000000000000000000 : ℝ)*base77 + (30248980215382977/796448200000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (3499/10000000000000000 : ℝ)*base87 + (3499/10000000000000000 : ℝ)*base89 + (3499/10000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(12163/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(12163/20000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (174141988792825205638235557/17322748350000000000000000000000 : ℝ) := by norm_num
    linear_combination (530950822703/1000000000000 : ℝ)*(base7) + (73351517537/500000000000 : ℝ)*(base40) + (542239/500000000000 : ℝ)*(base49) + (403346802733/200000000000 : ℝ)*(major_s2_0) + (403346802733/200000000000 : ℝ)*(major_s2_1) + (403346802733/200000000000 : ℝ)*(major_s2_2) + (10325909/1000000000000 : ℝ)*(sp_s2_1) + (3640711/200000000000 : ℝ)*(sp_s2_2) + (657833/10000000000 : ℝ)*(sp_s2_9) + (7541527/1000000000000 : ℝ)*(sp_s2_20) + (2466439387853/1000000000000 : ℝ)*(sp_s2_21) + (308303632743/125000000000 : ℝ)*(sp_s2_22) + (1233177700499/500000000000 : ℝ)*(sp_s2_23) + (444358389513/250000000000 : ℝ)*(sp_s2_27) + (311622569219/250000000000 : ℝ)*(f.failure) + (2466439387853/1000000000000 : ℝ)*(f.sum) + (17306034084773531/43917600000000000000000000000 : ℝ)*base62 + (76554918593261/208800000000000000000000000 : ℝ)*base64 + (1340219081879/1514400000000000000000000000 : ℝ)*base66 + (6304243017269/11600000000000000000000000 : ℝ)*base68 + (435969964138627591/1317736800000000000000000000000 : ℝ)*base70 + (43699377870107/151464000000000000000000000 : ℝ)*base72 + (923468849546893/1514400000000000000000000000 : ℝ)*base74 + (149025830995271/252440000000000000000000000 : ℝ)*base76 + (1171922653721330777/3185792800000000000000000000000 : ℝ)*base79 + (24667/25000000000000000 : ℝ)*base87 + (24667/25000000000000000 : ℝ)*base89 + (24667/25000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((18933/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(18933/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1893/2500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1893/2500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1827/2500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(1827/2500 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((15703/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15703/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(63347/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(63347/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(12163/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(12163/20000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c310063_s2 p hpa hpb X hX hprev1

#print axioms solution
