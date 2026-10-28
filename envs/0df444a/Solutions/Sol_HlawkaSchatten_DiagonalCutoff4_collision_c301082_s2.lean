-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c301082_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:43:11.831777+00:00
-- url     : https://prove2.me/submissions/c2a88cb1-fc8f-4536-90ac-e4c534d6de9d

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
theorem collision_support_c301082_s2_s2_0 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2026144163/5000000000 : ℝ)*x 0 + (105741129/312500000 : ℝ)*x 1 + (5575736817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2026144163/5000000000 : ℝ)^65 ≤ (7542972049709/25000000000000 : ℝ)^49 := by
    have hnat : (2026144163 : ℕ)^65*25000000000000^49 ≤ 7542972049709^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2026144163 5000000000 7542972049709 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (105741129/312500000 : ℝ)^65 ≤ (190027571139/800000000000 : ℝ)^49 := by
    have hnat : (105741129 : ℕ)^65*800000000000^49 ≤ 190027571139^49*312500000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105741129 312500000 190027571139 800000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5575736817/10000000000 : ℝ)^65 ≤ (46074665389431/100000000000000 : ℝ)^49 := by
    have hnat : (5575736817 : ℕ)^65*100000000000000^49 ≤ 46074665389431^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5575736817 10000000000 46074665389431 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2026144163/5000000000 : ℝ), (105741129/312500000 : ℝ), (5575736817/10000000000 : ℝ)] ![(7542972049709/25000000000000 : ℝ), (190027571139/800000000000 : ℝ), (46074665389431/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2026144163/5000000000 : ℝ)|^65 ≤ (7542972049709/25000000000000 : ℝ)^49
        have hw : |(-2026144163/5000000000 : ℝ)|=(2026144163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(105741129/312500000 : ℝ)|^65 ≤ (190027571139/800000000000 : ℝ)^49
        have hw : |(105741129/312500000 : ℝ)|=(105741129/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5575736817/10000000000 : ℝ)|^65 ≤ (46074665389431/100000000000000 : ℝ)^49
        have hw : |(5575736817/10000000000 : ℝ)|=(5575736817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301082_s2_s2_1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (445835243/1000000000 : ℝ)*x 0 + (-3464728963/10000000000 : ℝ)*x 1 + (1282239661/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (445835243/1000000000 : ℝ)^65 ≤ (17123364495077/50000000000000 : ℝ)^49 := by
    have hnat : (445835243 : ℕ)^65*50000000000000^49 ≤ 17123364495077^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      445835243 1000000000 17123364495077 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3464728963/10000000000 : ℝ)^65 ≤ (24510783294109/100000000000000 : ℝ)^49 := by
    have hnat : (3464728963 : ℕ)^65*100000000000000^49 ≤ 24510783294109^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3464728963 10000000000 24510783294109 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1282239661/2500000000 : ℝ)^65 ≤ (4124248769607/10000000000000 : ℝ)^49 := by
    have hnat : (1282239661 : ℕ)^65*10000000000000^49 ≤ 4124248769607^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1282239661 2500000000 4124248769607 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(445835243/1000000000 : ℝ), (-3464728963/10000000000 : ℝ), (1282239661/2500000000 : ℝ)] ![(17123364495077/50000000000000 : ℝ), (24510783294109/100000000000000 : ℝ), (4124248769607/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(445835243/1000000000 : ℝ)|^65 ≤ (17123364495077/50000000000000 : ℝ)^49
        have hw : |(445835243/1000000000 : ℝ)|=(445835243/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3464728963/10000000000 : ℝ)|^65 ≤ (24510783294109/100000000000000 : ℝ)^49
        have hw : |(-3464728963/10000000000 : ℝ)|=(3464728963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1282239661/2500000000 : ℝ)|^65 ≤ (4124248769607/10000000000000 : ℝ)^49
        have hw : |(1282239661/2500000000 : ℝ)|=(1282239661/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301082_s2_s2_2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5927009709/10000000000 : ℝ)*x 0 + (264044721/500000000 : ℝ)*x 1 + (-1370880957/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5927009709/10000000000 : ℝ)^65 ≤ (24982133510437/50000000000000 : ℝ)^49 := by
    have hnat : (5927009709 : ℕ)^65*50000000000000^49 ≤ 24982133510437^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5927009709 10000000000 24982133510437 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (264044721/500000000 : ℝ)^65 ≤ (21435469208699/50000000000000 : ℝ)^49 := by
    have hnat : (264044721 : ℕ)^65*50000000000000^49 ≤ 21435469208699^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264044721 500000000 21435469208699 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1370880957/10000000000 : ℝ)^65 ≤ (3582397275321/50000000000000 : ℝ)^49 := by
    have hnat : (1370880957 : ℕ)^65*50000000000000^49 ≤ 3582397275321^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1370880957 10000000000 3582397275321 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5927009709/10000000000 : ℝ), (264044721/500000000 : ℝ), (-1370880957/10000000000 : ℝ)] ![(24982133510437/50000000000000 : ℝ), (21435469208699/50000000000000 : ℝ), (3582397275321/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5927009709/10000000000 : ℝ)|^65 ≤ (24982133510437/50000000000000 : ℝ)^49
        have hw : |(5927009709/10000000000 : ℝ)|=(5927009709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(264044721/500000000 : ℝ)|^65 ≤ (21435469208699/50000000000000 : ℝ)^49
        have hw : |(264044721/500000000 : ℝ)|=(264044721/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1370880957/10000000000 : ℝ)|^65 ≤ (3582397275321/50000000000000 : ℝ)^49
        have hw : |(-1370880957/10000000000 : ℝ)|=(1370880957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301082_s2_s2_6 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (216832423/2000000000 : ℝ)*x 0 + (5640884207/10000000000 : ℝ)*x 1 + (5747013601/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (216832423/2000000000 : ℝ)^65 ≤ (524835199469/10000000000000 : ℝ)^49 := by
    have hnat : (216832423 : ℕ)^65*10000000000000^49 ≤ 524835199469^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216832423 2000000000 524835199469 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5640884207/10000000000 : ℝ)^65 ≤ (46790149077109/100000000000000 : ℝ)^49 := by
    have hnat : (5640884207 : ℕ)^65*100000000000000^49 ≤ 46790149077109^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5640884207 10000000000 46790149077109 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5747013601/10000000000 : ℝ)^65 ≤ (47961498911111/100000000000000 : ℝ)^49 := by
    have hnat : (5747013601 : ℕ)^65*100000000000000^49 ≤ 47961498911111^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5747013601 10000000000 47961498911111 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(216832423/2000000000 : ℝ), (5640884207/10000000000 : ℝ), (5747013601/10000000000 : ℝ)] ![(524835199469/10000000000000 : ℝ), (46790149077109/100000000000000 : ℝ), (47961498911111/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(216832423/2000000000 : ℝ)|^65 ≤ (524835199469/10000000000000 : ℝ)^49
        have hw : |(216832423/2000000000 : ℝ)|=(216832423/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5640884207/10000000000 : ℝ)|^65 ≤ (46790149077109/100000000000000 : ℝ)^49
        have hw : |(5640884207/10000000000 : ℝ)|=(5640884207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5747013601/10000000000 : ℝ)|^65 ≤ (47961498911111/100000000000000 : ℝ)^49
        have hw : |(5747013601/10000000000 : ℝ)|=(5747013601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301082_s2_s2_7 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-151152317/400000000 : ℝ)*x 0 + (17562289/62500000 : ℝ)*x 1 + (6278679613/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (151152317/400000000 : ℝ)^65 ≤ (27500983613331/100000000000000 : ℝ)^49 := by
    have hnat : (151152317 : ℕ)^65*100000000000000^49 ≤ 27500983613331^49*400000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      151152317 400000000 27500983613331 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (17562289/62500000 : ℝ)^65 ≤ (18564580307869/100000000000000 : ℝ)^49 := by
    have hnat : (17562289 : ℕ)^65*100000000000000^49 ≤ 18564580307869^49*62500000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17562289 62500000 18564580307869 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6278679613/10000000000 : ℝ)^65 ≤ (10786887213393/20000000000000 : ℝ)^49 := by
    have hnat : (6278679613 : ℕ)^65*20000000000000^49 ≤ 10786887213393^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6278679613 10000000000 10786887213393 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-151152317/400000000 : ℝ), (17562289/62500000 : ℝ), (6278679613/10000000000 : ℝ)] ![(27500983613331/100000000000000 : ℝ), (18564580307869/100000000000000 : ℝ), (10786887213393/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-151152317/400000000 : ℝ)|^65 ≤ (27500983613331/100000000000000 : ℝ)^49
        have hw : |(-151152317/400000000 : ℝ)|=(151152317/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(17562289/62500000 : ℝ)|^65 ≤ (18564580307869/100000000000000 : ℝ)^49
        have hw : |(17562289/62500000 : ℝ)|=(17562289/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6278679613/10000000000 : ℝ)|^65 ≤ (10786887213393/20000000000000 : ℝ)^49
        have hw : |(6278679613/10000000000 : ℝ)|=(6278679613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301082_s2_s2_8 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4499018589/10000000000 : ℝ)*x 0 + (-1283993851/5000000000 : ℝ)*x 1 + (582834733/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4499018589/10000000000 : ℝ)^65 ≤ (34661721333647/100000000000000 : ℝ)^49 := by
    have hnat : (4499018589 : ℕ)^65*100000000000000^49 ≤ 34661721333647^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4499018589 10000000000 34661721333647 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1283993851/5000000000 : ℝ)^65 ≤ (16474299634619/100000000000000 : ℝ)^49 := by
    have hnat : (1283993851 : ℕ)^65*100000000000000^49 ≤ 16474299634619^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1283993851 5000000000 16474299634619 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (582834733/1000000000 : ℝ)^65 ≤ (305399868881/625000000000 : ℝ)^49 := by
    have hnat : (582834733 : ℕ)^65*625000000000^49 ≤ 305399868881^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      582834733 1000000000 305399868881 625000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4499018589/10000000000 : ℝ), (-1283993851/5000000000 : ℝ), (582834733/1000000000 : ℝ)] ![(34661721333647/100000000000000 : ℝ), (16474299634619/100000000000000 : ℝ), (305399868881/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4499018589/10000000000 : ℝ)|^65 ≤ (34661721333647/100000000000000 : ℝ)^49
        have hw : |(4499018589/10000000000 : ℝ)|=(4499018589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1283993851/5000000000 : ℝ)|^65 ≤ (16474299634619/100000000000000 : ℝ)^49
        have hw : |(-1283993851/5000000000 : ℝ)|=(1283993851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(582834733/1000000000 : ℝ)|^65 ≤ (305399868881/625000000000 : ℝ)^49
        have hw : |(582834733/1000000000 : ℝ)|=(582834733/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301082_s2_s2_9 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5526002031/10000000000 : ℝ)*x 0 + (1513793657/2500000000 : ℝ)*x 1 + (-723163571/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5526002031/10000000000 : ℝ)^65 ≤ (45530284018127/100000000000000 : ℝ)^49 := by
    have hnat : (5526002031 : ℕ)^65*100000000000000^49 ≤ 45530284018127^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5526002031 10000000000 45530284018127 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1513793657/2500000000 : ℝ)^65 ≤ (51402514167479/100000000000000 : ℝ)^49 := by
    have hnat : (1513793657 : ℕ)^65*100000000000000^49 ≤ 51402514167479^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1513793657 2500000000 51402514167479 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (723163571/10000000000 : ℝ)^65 ≤ (122688071843/4000000000000 : ℝ)^49 := by
    have hnat : (723163571 : ℕ)^65*4000000000000^49 ≤ 122688071843^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      723163571 10000000000 122688071843 4000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5526002031/10000000000 : ℝ), (1513793657/2500000000 : ℝ), (-723163571/10000000000 : ℝ)] ![(45530284018127/100000000000000 : ℝ), (51402514167479/100000000000000 : ℝ), (122688071843/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5526002031/10000000000 : ℝ)|^65 ≤ (45530284018127/100000000000000 : ℝ)^49
        have hw : |(5526002031/10000000000 : ℝ)|=(5526002031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1513793657/2500000000 : ℝ)|^65 ≤ (51402514167479/100000000000000 : ℝ)^49
        have hw : |(1513793657/2500000000 : ℝ)|=(1513793657/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-723163571/10000000000 : ℝ)|^65 ≤ (122688071843/4000000000000 : ℝ)^49
        have hw : |(-723163571/10000000000 : ℝ)|=(723163571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301082_s2_s2_13 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (174804661/5000000000 : ℝ)*x 0 + (3596627119/5000000000 : ℝ)*x 1 + (2228562417/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (174804661/5000000000 : ℝ)^65 ≤ (584774296533/50000000000000 : ℝ)^49 := by
    have hnat : (174804661 : ℕ)^65*50000000000000^49 ≤ 584774296533^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174804661 5000000000 584774296533 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3596627119/5000000000 : ℝ)^65 ≤ (32298115346617/50000000000000 : ℝ)^49 := by
    have hnat : (3596627119 : ℕ)^65*50000000000000^49 ≤ 32298115346617^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3596627119 5000000000 32298115346617 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2228562417/5000000000 : ℝ)^65 ≤ (8558555175217/25000000000000 : ℝ)^49 := by
    have hnat : (2228562417 : ℕ)^65*25000000000000^49 ≤ 8558555175217^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2228562417 5000000000 8558555175217 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(174804661/5000000000 : ℝ), (3596627119/5000000000 : ℝ), (2228562417/5000000000 : ℝ)] ![(584774296533/50000000000000 : ℝ), (32298115346617/50000000000000 : ℝ), (8558555175217/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(174804661/5000000000 : ℝ)|^65 ≤ (584774296533/50000000000000 : ℝ)^49
        have hw : |(174804661/5000000000 : ℝ)|=(174804661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3596627119/5000000000 : ℝ)|^65 ≤ (32298115346617/50000000000000 : ℝ)^49
        have hw : |(3596627119/5000000000 : ℝ)|=(3596627119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2228562417/5000000000 : ℝ)|^65 ≤ (8558555175217/25000000000000 : ℝ)^49
        have hw : |(2228562417/5000000000 : ℝ)|=(2228562417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301082_s2_s2_14 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3489975593/10000000000 : ℝ)*x 0 + (1457369631/5000000000 : ℝ)*x 1 + (6438547071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3489975593/10000000000 : ℝ)^65 ≤ (4949597691239/20000000000000 : ℝ)^49 := by
    have hnat : (3489975593 : ℕ)^65*20000000000000^49 ≤ 4949597691239^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3489975593 10000000000 4949597691239 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1457369631/5000000000 : ℝ)^65 ≤ (19488352519707/100000000000000 : ℝ)^49 := by
    have hnat : (1457369631 : ℕ)^65*100000000000000^49 ≤ 19488352519707^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1457369631 5000000000 19488352519707 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6438547071/10000000000 : ℝ)^65 ≤ (5576365901119/10000000000000 : ℝ)^49 := by
    have hnat : (6438547071 : ℕ)^65*10000000000000^49 ≤ 5576365901119^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6438547071 10000000000 5576365901119 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3489975593/10000000000 : ℝ), (1457369631/5000000000 : ℝ), (6438547071/10000000000 : ℝ)] ![(4949597691239/20000000000000 : ℝ), (19488352519707/100000000000000 : ℝ), (5576365901119/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3489975593/10000000000 : ℝ)|^65 ≤ (4949597691239/20000000000000 : ℝ)^49
        have hw : |(-3489975593/10000000000 : ℝ)|=(3489975593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1457369631/5000000000 : ℝ)|^65 ≤ (19488352519707/100000000000000 : ℝ)^49
        have hw : |(1457369631/5000000000 : ℝ)|=(1457369631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6438547071/10000000000 : ℝ)|^65 ≤ (5576365901119/10000000000000 : ℝ)^49
        have hw : |(6438547071/10000000000 : ℝ)|=(6438547071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301082_s2_s2_15 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1206192761/2500000000 : ℝ)*x 0 + (-3435070343/10000000000 : ℝ)*x 1 + (4796806633/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1206192761/2500000000 : ℝ)^65 ≤ (38029635690347/100000000000000 : ℝ)^49 := by
    have hnat : (1206192761 : ℕ)^65*100000000000000^49 ≤ 38029635690347^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1206192761 2500000000 38029635690347 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3435070343/10000000000 : ℝ)^65 ≤ (4846569102919/20000000000000 : ℝ)^49 := by
    have hnat : (3435070343 : ℕ)^65*20000000000000^49 ≤ 4846569102919^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3435070343 10000000000 4846569102919 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4796806633/10000000000 : ℝ)^65 ≤ (3773751877181/10000000000000 : ℝ)^49 := by
    have hnat : (4796806633 : ℕ)^65*10000000000000^49 ≤ 3773751877181^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4796806633 10000000000 3773751877181 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1206192761/2500000000 : ℝ), (-3435070343/10000000000 : ℝ), (4796806633/10000000000 : ℝ)] ![(38029635690347/100000000000000 : ℝ), (4846569102919/20000000000000 : ℝ), (3773751877181/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1206192761/2500000000 : ℝ)|^65 ≤ (38029635690347/100000000000000 : ℝ)^49
        have hw : |(1206192761/2500000000 : ℝ)|=(1206192761/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3435070343/10000000000 : ℝ)|^65 ≤ (4846569102919/20000000000000 : ℝ)^49
        have hw : |(-3435070343/10000000000 : ℝ)|=(3435070343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4796806633/10000000000 : ℝ)|^65 ≤ (3773751877181/10000000000000 : ℝ)^49
        have hw : |(4796806633/10000000000 : ℝ)|=(4796806633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301082_s2_s2_16 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3340492063/5000000000 : ℝ)*x 0 + (2469663001/5000000000 : ℝ)*x 1 + (-140823759/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3340492063/5000000000 : ℝ)^65 ≤ (58565988983449/100000000000000 : ℝ)^49 := by
    have hnat : (3340492063 : ℕ)^65*100000000000000^49 ≤ 58565988983449^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3340492063 5000000000 58565988983449 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2469663001/5000000000 : ℝ)^65 ≤ (39232033084311/100000000000000 : ℝ)^49 := by
    have hnat : (2469663001 : ℕ)^65*100000000000000^49 ≤ 39232033084311^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2469663001 5000000000 39232033084311 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (140823759/2500000000 : ℝ)^65 ≤ (440395584663/20000000000000 : ℝ)^49 := by
    have hnat : (140823759 : ℕ)^65*20000000000000^49 ≤ 440395584663^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140823759 2500000000 440395584663 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3340492063/5000000000 : ℝ), (2469663001/5000000000 : ℝ), (-140823759/2500000000 : ℝ)] ![(58565988983449/100000000000000 : ℝ), (39232033084311/100000000000000 : ℝ), (440395584663/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3340492063/5000000000 : ℝ)|^65 ≤ (58565988983449/100000000000000 : ℝ)^49
        have hw : |(3340492063/5000000000 : ℝ)|=(3340492063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2469663001/5000000000 : ℝ)|^65 ≤ (39232033084311/100000000000000 : ℝ)^49
        have hw : |(2469663001/5000000000 : ℝ)|=(2469663001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-140823759/2500000000 : ℝ)|^65 ≤ (440395584663/20000000000000 : ℝ)^49
        have hw : |(-140823759/2500000000 : ℝ)|=(140823759/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301082_s2_s2_20 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (215963221/10000000000 : ℝ)*x 0 + (2654431939/5000000000 : ℝ)*x 1 + (1619345907/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215963221/10000000000 : ℝ)^65 ≤ (308655354601/50000000000000 : ℝ)^49 := by
    have hnat : (215963221 : ℕ)^65*50000000000000^49 ≤ 308655354601^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215963221 10000000000 308655354601 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2654431939/5000000000 : ℝ)^65 ≤ (1079309996339/2500000000000 : ℝ)^49 := by
    have hnat : (2654431939 : ℕ)^65*2500000000000^49 ≤ 1079309996339^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2654431939 5000000000 1079309996339 2500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1619345907/2500000000 : ℝ)^65 ≤ (14052572355331/25000000000000 : ℝ)^49 := by
    have hnat : (1619345907 : ℕ)^65*25000000000000^49 ≤ 14052572355331^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1619345907 2500000000 14052572355331 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(215963221/10000000000 : ℝ), (2654431939/5000000000 : ℝ), (1619345907/2500000000 : ℝ)] ![(308655354601/50000000000000 : ℝ), (1079309996339/2500000000000 : ℝ), (14052572355331/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(215963221/10000000000 : ℝ)|^65 ≤ (308655354601/50000000000000 : ℝ)^49
        have hw : |(215963221/10000000000 : ℝ)|=(215963221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2654431939/5000000000 : ℝ)|^65 ≤ (1079309996339/2500000000000 : ℝ)^49
        have hw : |(2654431939/5000000000 : ℝ)|=(2654431939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1619345907/2500000000 : ℝ)|^65 ≤ (14052572355331/25000000000000 : ℝ)^49
        have hw : |(1619345907/2500000000 : ℝ)|=(1619345907/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301082_s2_s2_21 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-778726653/2000000000 : ℝ)*x 0 + (3470794983/10000000000 : ℝ)*x 1 + (5643351189/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (778726653/2000000000 : ℝ)^65 ≤ (14307489291899/50000000000000 : ℝ)^49 := by
    have hnat : (778726653 : ℕ)^65*50000000000000^49 ≤ 14307489291899^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      778726653 2000000000 14307489291899 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3470794983/10000000000 : ℝ)^65 ≤ (24567725345907/100000000000000 : ℝ)^49 := by
    have hnat : (3470794983 : ℕ)^65*100000000000000^49 ≤ 24567725345907^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3470794983 10000000000 24567725345907 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5643351189/10000000000 : ℝ)^65 ≤ (46817296056103/100000000000000 : ℝ)^49 := by
    have hnat : (5643351189 : ℕ)^65*100000000000000^49 ≤ 46817296056103^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5643351189 10000000000 46817296056103 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-778726653/2000000000 : ℝ), (3470794983/10000000000 : ℝ), (5643351189/10000000000 : ℝ)] ![(14307489291899/50000000000000 : ℝ), (24567725345907/100000000000000 : ℝ), (46817296056103/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-778726653/2000000000 : ℝ)|^65 ≤ (14307489291899/50000000000000 : ℝ)^49
        have hw : |(-778726653/2000000000 : ℝ)|=(778726653/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3470794983/10000000000 : ℝ)|^65 ≤ (24567725345907/100000000000000 : ℝ)^49
        have hw : |(3470794983/10000000000 : ℝ)|=(3470794983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5643351189/10000000000 : ℝ)|^65 ≤ (46817296056103/100000000000000 : ℝ)^49
        have hw : |(5643351189/10000000000 : ℝ)|=(5643351189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301082_s2_s2_22 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4421112931/10000000000 : ℝ)*x 0 + (-1716046729/5000000000 : ℝ)*x 1 + (207720859/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4421112931/10000000000 : ℝ)^65 ≤ (33867787609319/100000000000000 : ℝ)^49 := by
    have hnat : (4421112931 : ℕ)^65*100000000000000^49 ≤ 33867787609319^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4421112931 10000000000 33867787609319 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1716046729/5000000000 : ℝ)^65 ≤ (24204991573729/100000000000000 : ℝ)^49 := by
    have hnat : (1716046729 : ℕ)^65*100000000000000^49 ≤ 24204991573729^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1716046729 5000000000 24204991573729 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (207720859/400000000 : ℝ)^65 ≤ (4192722080543/10000000000000 : ℝ)^49 := by
    have hnat : (207720859 : ℕ)^65*10000000000000^49 ≤ 4192722080543^49*400000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207720859 400000000 4192722080543 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4421112931/10000000000 : ℝ), (-1716046729/5000000000 : ℝ), (207720859/400000000 : ℝ)] ![(33867787609319/100000000000000 : ℝ), (24204991573729/100000000000000 : ℝ), (4192722080543/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4421112931/10000000000 : ℝ)|^65 ≤ (33867787609319/100000000000000 : ℝ)^49
        have hw : |(4421112931/10000000000 : ℝ)|=(4421112931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1716046729/5000000000 : ℝ)|^65 ≤ (24204991573729/100000000000000 : ℝ)^49
        have hw : |(-1716046729/5000000000 : ℝ)|=(1716046729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(207720859/400000000 : ℝ)|^65 ≤ (4192722080543/10000000000000 : ℝ)^49
        have hw : |(207720859/400000000 : ℝ)|=(207720859/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301082_s2_s2_23 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6738486267/10000000000 : ℝ)*x 0 + (2336897551/5000000000 : ℝ)*x 1 + (-93378043/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6738486267/10000000000 : ℝ)^65 ≤ (11847117659937/20000000000000 : ℝ)^49 := by
    have hnat : (6738486267 : ℕ)^65*20000000000000^49 ≤ 11847117659937^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6738486267 10000000000 11847117659937 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2336897551/5000000000 : ℝ)^65 ≤ (18229581906049/50000000000000 : ℝ)^49 := by
    have hnat : (2336897551 : ℕ)^65*50000000000000^49 ≤ 18229581906049^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2336897551 5000000000 18229581906049 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (93378043/1000000000 : ℝ)^65 ≤ (4305247878483/100000000000000 : ℝ)^49 := by
    have hnat : (93378043 : ℕ)^65*100000000000000^49 ≤ 4305247878483^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      93378043 1000000000 4305247878483 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6738486267/10000000000 : ℝ), (2336897551/5000000000 : ℝ), (-93378043/1000000000 : ℝ)] ![(11847117659937/20000000000000 : ℝ), (18229581906049/50000000000000 : ℝ), (4305247878483/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6738486267/10000000000 : ℝ)|^65 ≤ (11847117659937/20000000000000 : ℝ)^49
        have hw : |(6738486267/10000000000 : ℝ)|=(6738486267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2336897551/5000000000 : ℝ)|^65 ≤ (18229581906049/50000000000000 : ℝ)^49
        have hw : |(2336897551/5000000000 : ℝ)|=(2336897551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-93378043/1000000000 : ℝ)|^65 ≤ (4305247878483/100000000000000 : ℝ)^49
        have hw : |(-93378043/1000000000 : ℝ)|=(93378043/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301082_s2_s2_27 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6459073/625000000 : ℝ)*x 0 + (6912097191/10000000000 : ℝ)*x 1 + (973923199/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6459073/625000000 : ℝ)^65 ≤ (23221759927/10000000000000 : ℝ)^49 := by
    have hnat : (6459073 : ℕ)^65*10000000000000^49 ≤ 23221759927^49*625000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6459073 625000000 23221759927 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6912097191/10000000000 : ℝ)^65 ≤ (2450741635529/4000000000000 : ℝ)^49 := by
    have hnat : (6912097191 : ℕ)^65*4000000000000^49 ≤ 2450741635529^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6912097191 10000000000 2450741635529 4000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (973923199/2000000000 : ℝ)^65 ≤ (38499241503309/100000000000000 : ℝ)^49 := by
    have hnat : (973923199 : ℕ)^65*100000000000000^49 ≤ 38499241503309^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      973923199 2000000000 38499241503309 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6459073/625000000 : ℝ), (6912097191/10000000000 : ℝ), (973923199/2000000000 : ℝ)] ![(23221759927/10000000000000 : ℝ), (2450741635529/4000000000000 : ℝ), (38499241503309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6459073/625000000 : ℝ)|^65 ≤ (23221759927/10000000000000 : ℝ)^49
        have hw : |(6459073/625000000 : ℝ)|=(6459073/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6912097191/10000000000 : ℝ)|^65 ≤ (2450741635529/4000000000000 : ℝ)^49
        have hw : |(6912097191/10000000000 : ℝ)|=(6912097191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(973923199/2000000000 : ℝ)|^65 ≤ (38499241503309/100000000000000 : ℝ)^49
        have hw : |(973923199/2000000000 : ℝ)|=(973923199/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c301082_s2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((72757/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(72757/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((10757/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(10757/12500 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(73799/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(73799/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((9211/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9211/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((46423/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(46423/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(3311/10000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(3311/10000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4759/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4759/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4759/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4759/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base31 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 1 2+(1 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 2).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base60 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s2_pow0 : (72757/100000 : ℝ) ^ (129/32 : ℝ) ≤ (27744871690885602967/100000000000000000000 : ℝ) := by
    have hpowers : (72757/100000 : ℝ)^129 ≤ (27744871690885602967/100000000000000000000 : ℝ)^32 := by
      have hnat : (72757 : ℕ)^129*100000000000000000000^32 ≤ 27744871690885602967^32*100000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        72757 100000 27744871690885602967 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (72757/100000 : ℝ)) (X := (27744871690885602967/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s2_corner0a : (127744871690885602967/100000000000000000000 : ℝ) ≤ (1328280477484183/1250000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (127744871690885602967/100000000000000000000 : ℝ)^32 ≤ (1328280477484183/1250000000000000 : ℝ)^129 := by
      have hnat : (127744871690885602967 : ℕ)^32*1250000000000000^129 ≤ 1328280477484183^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        127744871690885602967 100000000000000000000 1328280477484183 1250000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1328280477484183/1250000000000000 : ℝ)) (X := (127744871690885602967/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s2_corner0b : (77744871690885602967/50000000000000000000 : ℝ) ≤ (2789291673312483/2500000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (77744871690885602967/50000000000000000000 : ℝ)^32 ≤ (2789291673312483/2500000000000000 : ℝ)^129 := by
      have hnat : (77744871690885602967 : ℕ)^32*2500000000000000^129 ≤ 2789291673312483^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        77744871690885602967 50000000000000000000 2789291673312483 2500000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2789291673312483/2500000000000000 : ℝ)) (X := (77744871690885602967/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(78280477484183/909462500000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(132730718344117/1818925000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (72757/100000 : ℝ)) (alpha := (78280477484183/909462500000000 : ℝ)) (beta := (132730718344117/1818925000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (72757/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(78280477484183/909462500000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(132730718344117/1818925000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (10757/12500 : ℝ) ^ (129/32 : ℝ) ≤ (6823332683617571421/12500000000000000000 : ℝ) := by
    have hpowers : (10757/12500 : ℝ)^129 ≤ (6823332683617571421/12500000000000000000 : ℝ)^32 := by
      have hnat : (10757 : ℕ)^129*12500000000000000000^32 ≤ 6823332683617571421^32*12500^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10757 12500 6823332683617571421 12500000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10757/12500 : ℝ)) (X := (6823332683617571421/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s2_corner1a : (19323332683617571421/12500000000000000000 : ℝ) ≤ (6963160559169/6250000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (19323332683617571421/12500000000000000000 : ℝ)^32 ≤ (6963160559169/6250000000000 : ℝ)^129 := by
      have hnat : (19323332683617571421 : ℕ)^32*6250000000000^129 ≤ 6963160559169^129*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19323332683617571421 12500000000000000000 6963160559169 6250000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6963160559169/6250000000000 : ℝ)) (X := (19323332683617571421/12500000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s2_corner1b : (13073332683617571421/6250000000000000000 : ℝ) ≤ (3002240272577441/2500000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (13073332683617571421/6250000000000000000 : ℝ)^32 ≤ (3002240272577441/2500000000000000 : ℝ)^129 := by
      have hnat : (13073332683617571421 : ℕ)^32*2500000000000000^129 ≤ 3002240272577441^129*6250000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13073332683617571421 6250000000000000000 3002240272577441 2500000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3002240272577441/2500000000000000 : ℝ)) (X := (13073332683617571421/6250000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(713160559169/5378500000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(216976048909841/2151400000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (10757/12500 : ℝ)) (alpha := (713160559169/5378500000000 : ℝ)) (beta := (216976048909841/2151400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (10757/12500 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(713160559169/5378500000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(216976048909841/2151400000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (73799/100000 : ℝ) ^ (129/32 : ℝ) ≤ (14690902954658853971/50000000000000000000 : ℝ) := by
    have hpowers : (73799/100000 : ℝ)^129 ≤ (14690902954658853971/50000000000000000000 : ℝ)^32 := by
      have hnat : (73799 : ℕ)^129*50000000000000000000^32 ≤ 14690902954658853971^32*100000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        73799 100000 14690902954658853971 50000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (73799/100000 : ℝ)) (X := (14690902954658853971/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s2_corner2a : (64690902954658853971/50000000000000000000 : ℝ) ≤ (5329929909960827/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (64690902954658853971/50000000000000000000 : ℝ)^32 ≤ (5329929909960827/5000000000000000 : ℝ)^129 := by
      have hnat : (64690902954658853971 : ℕ)^32*5000000000000000^129 ≤ 5329929909960827^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        64690902954658853971 50000000000000000000 5329929909960827 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5329929909960827/5000000000000000 : ℝ)) (X := (64690902954658853971/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s2_corner2b : (39690902954658853971/25000000000000000000 : ℝ) ≤ (11214984826460349/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (39690902954658853971/25000000000000000000 : ℝ)^32 ≤ (11214984826460349/10000000000000000 : ℝ)^129 := by
      have hnat : (39690902954658853971 : ℕ)^32*10000000000000000^129 ≤ 11214984826460349^129*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        39690902954658853971 25000000000000000000 11214984826460349 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11214984826460349/10000000000000000 : ℝ)) (X := (39690902954658853971/25000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(29993628178257/335450000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(111025001307739/1475980000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (73799/100000 : ℝ)) (alpha := (29993628178257/335450000000000 : ℝ)) (beta := (111025001307739/1475980000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (73799/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(29993628178257/335450000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(111025001307739/1475980000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-2026144163/5000000000 : ℝ)*X 0 0+(105741129/312500000 : ℝ)*X 0 1+(5575736817/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301082_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((445835243/1000000000 : ℝ)*X 1 0+(-3464728963/10000000000 : ℝ)*X 1 1+(1282239661/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301082_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((5927009709/10000000000 : ℝ)*X 2 0+(264044721/500000000 : ℝ)*X 2 1+(-1370880957/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301082_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((216832423/2000000000 : ℝ)*X 0 0+(5640884207/10000000000 : ℝ)*X 0 1+(5747013601/10000000000 : ℝ)*X 0 2+(216832423/2000000000 : ℝ)*X 1 0+(5640884207/10000000000 : ℝ)*X 1 1+(5747013601/10000000000 : ℝ)*X 1 2+(216832423/2000000000 : ℝ)*X 2 0+(5640884207/10000000000 : ℝ)*X 2 1+(5747013601/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301082_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-151152317/400000000 : ℝ)*X 0 0+(17562289/62500000 : ℝ)*X 0 1+(6278679613/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301082_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((4499018589/10000000000 : ℝ)*X 1 0+(-1283993851/5000000000 : ℝ)*X 1 1+(582834733/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301082_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((5526002031/10000000000 : ℝ)*X 2 0+(1513793657/2500000000 : ℝ)*X 2 1+(-723163571/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301082_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((174804661/5000000000 : ℝ)*X 0 0+(3596627119/5000000000 : ℝ)*X 0 1+(2228562417/5000000000 : ℝ)*X 0 2+(174804661/5000000000 : ℝ)*X 1 0+(3596627119/5000000000 : ℝ)*X 1 1+(2228562417/5000000000 : ℝ)*X 1 2+(174804661/5000000000 : ℝ)*X 2 0+(3596627119/5000000000 : ℝ)*X 2 1+(2228562417/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301082_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-3489975593/10000000000 : ℝ)*X 0 0+(1457369631/5000000000 : ℝ)*X 0 1+(6438547071/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301082_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((1206192761/2500000000 : ℝ)*X 1 0+(-3435070343/10000000000 : ℝ)*X 1 1+(4796806633/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301082_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((3340492063/5000000000 : ℝ)*X 2 0+(2469663001/5000000000 : ℝ)*X 2 1+(-140823759/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301082_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((215963221/10000000000 : ℝ)*X 0 0+(2654431939/5000000000 : ℝ)*X 0 1+(1619345907/2500000000 : ℝ)*X 0 2+(215963221/10000000000 : ℝ)*X 1 0+(2654431939/5000000000 : ℝ)*X 1 1+(1619345907/2500000000 : ℝ)*X 1 2+(215963221/10000000000 : ℝ)*X 2 0+(2654431939/5000000000 : ℝ)*X 2 1+(1619345907/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301082_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-778726653/2000000000 : ℝ)*X 0 0+(3470794983/10000000000 : ℝ)*X 0 1+(5643351189/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301082_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((4421112931/10000000000 : ℝ)*X 1 0+(-1716046729/5000000000 : ℝ)*X 1 1+(207720859/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301082_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((6738486267/10000000000 : ℝ)*X 2 0+(2336897551/5000000000 : ℝ)*X 2 1+(-93378043/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301082_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((6459073/625000000 : ℝ)*X 0 0+(6912097191/10000000000 : ℝ)*X 0 1+(973923199/2000000000 : ℝ)*X 0 2+(6459073/625000000 : ℝ)*X 1 0+(6912097191/10000000000 : ℝ)*X 1 1+(973923199/2000000000 : ℝ)*X 1 2+(6459073/625000000 : ℝ)*X 2 0+(6912097191/10000000000 : ℝ)*X 2 1+(973923199/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301082_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((9211/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9211/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (276100660611999565472963132907/18631796635210000000000000000000000 : ℝ) := by norm_num
    linear_combination (10020797/1000000000000 : ℝ)*(base19) + (68842301497/200000000000 : ℝ)*(base49) + (61319/500000000000 : ℝ)*(base50) + (134292590683/125000000000 : ℝ)*(base60) + (1238251307279/250000000000 : ℝ)*(major_s2_0) + (1238251307279/250000000000 : ℝ)*(major_s2_1) + (1238251307279/250000000000 : ℝ)*(major_s2_2) + (4194001/1000000000000 : ℝ)*(sp_s2_6) + (3278640737741/500000000000 : ℝ)*(sp_s2_7) + (3278825461417/500000000000 : ℝ)*(sp_s2_8) + (6557660943631/1000000000000 : ℝ)*(sp_s2_9) + (669668076199/200000000000 : ℝ)*(sp_s2_13) + (5294787/15625000000 : ℝ)*(sp_s2_14) + (20300891/500000000000 : ℝ)*(sp_s2_21) + (669668914999/200000000000 : ℝ)*(f.failure) + (6557660943631/1000000000000 : ℝ)*(f.sum) + (21255197513254537/36084356500000000000000000000 : ℝ)*base63 + (891893031201019/737990000000000000000000000 : ℝ)*base64 + (106093855144931/107570000000000000000000000 : ℝ)*base66 + (246883567112207/335450000000000000000000000 : ℝ)*base68 + (181411945427153867177/268469692150000000000000000000000 : ℝ)*base70 + (1193148466352891/3637850000000000000000000000 : ℝ)*base72 + (227089884147551/537850000000000000000000000 : ℝ)*base75 + (2030932770144813/3637850000000000000000000000 : ℝ)*base76 + (141916560627845291/631166975000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1981/5000000000000000 : ℝ)*base86 + (1981/5000000000000000 : ℝ)*base88 + (1981/5000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((46423/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(46423/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (45220467212230703090488182507/3726359327042000000000000000000000 : ℝ) := by norm_num
    linear_combination (947987/200000000000 : ℝ)*(base31) + (5775443/1000000000000 : ℝ)*(base49) + (1630532417877/1000000000000 : ℝ)*(base60) + (158489465333/25000000000 : ℝ)*(major_s2_0) + (158489465333/25000000000 : ℝ)*(major_s2_1) + (158489465333/25000000000 : ℝ)*(major_s2_2) + (1159843/20000000000 : ℝ)*(sp_s2_2) + (4905343/1000000000000 : ℝ)*(sp_s2_6) + (151853291/500000000000 : ℝ)*(sp_s2_7) + (4196574823561/500000000000 : ℝ)*(sp_s2_14) + (1049181669213/125000000000 : ℝ)*(sp_s2_15) + (8393311320301/1000000000000 : ℝ)*(sp_s2_16) + (535711272819/125000000000 : ℝ)*(sp_s2_20) + (21010313/250000000000 : ℝ)*(sp_s2_23) + (428569982783/100000000000 : ℝ)*(f.failure) + (1049181669213/125000000000 : ℝ)*(f.sum) + (73310238640838023/721687130000000000000000000000 : ℝ)*base62 + (243953075798241/737990000000000000000000000 : ℝ)*base65 + (39107372082761/107570000000000000000000000 : ℝ)*base67 + (1733178977907/13418000000000000000000000 : ℝ)*base69 + (13044117631405482577/53693938430000000000000000000000 : ℝ)*base71 + (275133791698109/727570000000000000000000000 : ℝ)*base73 + (12849849261433/21514000000000000000000000 : ℝ)*base75 + (583526877442057/727570000000000000000000000 : ℝ)*base77 + (9634755248270737/50493358000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (1877/2500000000000000 : ℝ)*base86 + (1877/2500000000000000 : ℝ)*base88 + (1877/2500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(3311/10000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(3311/10000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (318282276705571032990582626631/37263593270420000000000000000000000 : ℝ) := by norm_num
    linear_combination (755521/500000000000 : ℝ)*(base40) + (102271/250000000000 : ℝ)*(base49) + (54620789249/62500000000 : ℝ)*(base60) + (1177629823959/200000000000 : ℝ)*(major_s2_0) + (1177629823959/200000000000 : ℝ)*(major_s2_1) + (1177629823959/200000000000 : ℝ)*(major_s2_2) + (18474779/200000000000 : ℝ)*(sp_s2_0) + (7056699/20000000000 : ℝ)*(sp_s2_1) + (70305641/1000000000000 : ℝ)*(sp_s2_13) + (30973549/1000000000000 : ℝ)*(sp_s2_16) + (7795679831119/1000000000000 : ℝ)*(sp_s2_21) + (487213710629/62500000000 : ℝ)*(sp_s2_22) + (1559148246293/200000000000 : ℝ)*(sp_s2_23) + (995113220451/250000000000 : ℝ)*(sp_s2_27) + (995130796861/250000000000 : ℝ)*(f.failure) + (3897886102507/500000000000 : ℝ)*(f.sum) + (1577699132719845923/2886748520000000000000000000000 : ℝ)*base62 + (1433949096227577/1475980000000000000000000000 : ℝ)*base64 + (1938278875343/5378500000000000000000000 : ℝ)*base66 + (5552783981817/13418000000000000000000000 : ℝ)*base68 + (135528502396172450451/107387876860000000000000000000000 : ℝ)*base70 + (2211290261907/45473125000000000000000000 : ℝ)*base72 + (90201228728003/430280000000000000000000000 : ℝ)*base74 + (319099804124031/363785000000000000000000000 : ℝ)*base76 + (5788905671811679/126233395000000000000000000000 : ℝ)*base78 + (2109/6250000000000000 : ℝ)*base86 + (2109/6250000000000000 : ℝ)*base88 + (2109/6250000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((72757/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(72757/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((10757/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(10757/12500 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(73799/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(73799/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((9211/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9211/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((46423/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(46423/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(3311/10000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(3311/10000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c301082_s2 p hpa hpb X hX hprev1

#print axioms solution
