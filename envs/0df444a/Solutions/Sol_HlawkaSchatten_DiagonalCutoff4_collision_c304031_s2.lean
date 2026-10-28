-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c304031_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:38:51.738199+00:00
-- url     : https://prove2.me/submissions/b91be966-54c5-4eb3-a718-583aff7d1b80

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
theorem collision_support_c304031_s2_s2_2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (768154359/2500000000 : ℝ)*x 0 + (6164404827/10000000000 : ℝ)*x 1 + (-3518228139/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (768154359/2500000000 : ℝ)^17 ≤ (21370702349667/100000000000000 : ℝ)^13 := by
    have hnat : (768154359 : ℕ)^17*100000000000000^13 ≤ 21370702349667^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      768154359 2500000000 21370702349667 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6164404827/10000000000 : ℝ)^17 ≤ (53118068601137/100000000000000 : ℝ)^13 := by
    have hnat : (6164404827 : ℕ)^17*100000000000000^13 ≤ 53118068601137^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6164404827 10000000000 53118068601137 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3518228139/10000000000 : ℝ)^17 ≤ (3188903628997/12500000000000 : ℝ)^13 := by
    have hnat : (3518228139 : ℕ)^17*12500000000000^13 ≤ 3188903628997^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3518228139 10000000000 3188903628997 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(768154359/2500000000 : ℝ), (6164404827/10000000000 : ℝ), (-3518228139/10000000000 : ℝ)] ![(21370702349667/100000000000000 : ℝ), (53118068601137/100000000000000 : ℝ), (3188903628997/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(768154359/2500000000 : ℝ)|^17 ≤ (21370702349667/100000000000000 : ℝ)^13
        have hw : |(768154359/2500000000 : ℝ)|=(768154359/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6164404827/10000000000 : ℝ)|^17 ≤ (53118068601137/100000000000000 : ℝ)^13
        have hw : |(6164404827/10000000000 : ℝ)|=(6164404827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3518228139/10000000000 : ℝ)|^17 ≤ (3188903628997/12500000000000 : ℝ)^13
        have hw : |(-3518228139/10000000000 : ℝ)|=(3518228139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304031_s2_s2_6 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2127948727/5000000000 : ℝ)*x 0 + (2449667537/5000000000 : ℝ)*x 1 + (1885904409/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2127948727/5000000000 : ℝ)^17 ≤ (32721604221387/100000000000000 : ℝ)^13 := by
    have hnat : (2127948727 : ℕ)^17*100000000000000^13 ≤ 32721604221387^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2127948727 5000000000 32721604221387 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2449667537/5000000000 : ℝ)^17 ≤ (39336410276151/100000000000000 : ℝ)^13 := by
    have hnat : (2449667537 : ℕ)^17*100000000000000^13 ≤ 39336410276151^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2449667537 5000000000 39336410276151 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1885904409/5000000000 : ℝ)^17 ≤ (6985496371547/25000000000000 : ℝ)^13 := by
    have hnat : (1885904409 : ℕ)^17*25000000000000^13 ≤ 6985496371547^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1885904409 5000000000 6985496371547 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2127948727/5000000000 : ℝ), (2449667537/5000000000 : ℝ), (1885904409/5000000000 : ℝ)] ![(32721604221387/100000000000000 : ℝ), (39336410276151/100000000000000 : ℝ), (6985496371547/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2127948727/5000000000 : ℝ)|^17 ≤ (32721604221387/100000000000000 : ℝ)^13
        have hw : |(2127948727/5000000000 : ℝ)|=(2127948727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2449667537/5000000000 : ℝ)|^17 ≤ (39336410276151/100000000000000 : ℝ)^13
        have hw : |(2449667537/5000000000 : ℝ)|=(2449667537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1885904409/5000000000 : ℝ)|^17 ≤ (6985496371547/25000000000000 : ℝ)^13
        have hw : |(1885904409/5000000000 : ℝ)|=(1885904409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304031_s2_s2_7 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-167876773/500000000 : ℝ)*x 0 + (1326639307/2500000000 : ℝ)*x 1 + (4217495299/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167876773/500000000 : ℝ)^17 ≤ (23998317522063/100000000000000 : ℝ)^13 := by
    have hnat : (167876773 : ℕ)^17*100000000000000^13 ≤ 23998317522063^13*500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167876773 500000000 23998317522063 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1326639307/2500000000 : ℝ)^17 ≤ (43665645400683/100000000000000 : ℝ)^13 := by
    have hnat : (1326639307 : ℕ)^17*100000000000000^13 ≤ 43665645400683^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326639307 2500000000 43665645400683 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4217495299/10000000000 : ℝ)^17 ≤ (32336037066733/100000000000000 : ℝ)^13 := by
    have hnat : (4217495299 : ℕ)^17*100000000000000^13 ≤ 32336037066733^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4217495299 10000000000 32336037066733 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-167876773/500000000 : ℝ), (1326639307/2500000000 : ℝ), (4217495299/10000000000 : ℝ)] ![(23998317522063/100000000000000 : ℝ), (43665645400683/100000000000000 : ℝ), (32336037066733/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-167876773/500000000 : ℝ)|^17 ≤ (23998317522063/100000000000000 : ℝ)^13
        have hw : |(-167876773/500000000 : ℝ)|=(167876773/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1326639307/2500000000 : ℝ)|^17 ≤ (43665645400683/100000000000000 : ℝ)^13
        have hw : |(1326639307/2500000000 : ℝ)|=(1326639307/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4217495299/10000000000 : ℝ)|^17 ≤ (32336037066733/100000000000000 : ℝ)^13
        have hw : |(4217495299/10000000000 : ℝ)|=(4217495299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304031_s2_s2_8 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5652997611/10000000000 : ℝ)*x 0 + (41780701/5000000000 : ℝ)*x 1 + (6098609271/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5652997611/10000000000 : ℝ)^17 ≤ (11857602937081/25000000000000 : ℝ)^13 := by
    have hnat : (5652997611 : ℕ)^17*25000000000000^13 ≤ 11857602937081^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5652997611 10000000000 11857602937081 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41780701/5000000000 : ℝ)^17 ≤ (95850165333/50000000000000 : ℝ)^13 := by
    have hnat : (41780701 : ℕ)^17*50000000000000^13 ≤ 95850165333^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41780701 5000000000 95850165333 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6098609271/10000000000 : ℝ)^17 ≤ (52377887899437/100000000000000 : ℝ)^13 := by
    have hnat : (6098609271 : ℕ)^17*100000000000000^13 ≤ 52377887899437^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6098609271 10000000000 52377887899437 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5652997611/10000000000 : ℝ), (41780701/5000000000 : ℝ), (6098609271/10000000000 : ℝ)] ![(11857602937081/25000000000000 : ℝ), (95850165333/50000000000000 : ℝ), (52377887899437/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5652997611/10000000000 : ℝ)|^17 ≤ (11857602937081/25000000000000 : ℝ)^13
        have hw : |(5652997611/10000000000 : ℝ)|=(5652997611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(41780701/5000000000 : ℝ)|^17 ≤ (95850165333/50000000000000 : ℝ)^13
        have hw : |(41780701/5000000000 : ℝ)|=(41780701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6098609271/10000000000 : ℝ)|^17 ≤ (52377887899437/100000000000000 : ℝ)^13
        have hw : |(6098609271/10000000000 : ℝ)|=(6098609271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304031_s2_s2_9 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1178621807/5000000000 : ℝ)*x 0 + (223543091/312500000 : ℝ)*x 1 + (-592200081/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1178621807/5000000000 : ℝ)^17 ≤ (15111172048947/100000000000000 : ℝ)^13 := by
    have hnat : (1178621807 : ℕ)^17*100000000000000^13 ≤ 15111172048947^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1178621807 5000000000 15111172048947 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (223543091/312500000 : ℝ)^17 ≤ (64527591411703/100000000000000 : ℝ)^13 := by
    have hnat : (223543091 : ℕ)^17*100000000000000^13 ≤ 64527591411703^13*312500000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223543091 312500000 64527591411703 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (592200081/2000000000 : ℝ)^17 ≤ (5090309131091/25000000000000 : ℝ)^13 := by
    have hnat : (592200081 : ℕ)^17*25000000000000^13 ≤ 5090309131091^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      592200081 2000000000 5090309131091 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1178621807/5000000000 : ℝ), (223543091/312500000 : ℝ), (-592200081/2000000000 : ℝ)] ![(15111172048947/100000000000000 : ℝ), (64527591411703/100000000000000 : ℝ), (5090309131091/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1178621807/5000000000 : ℝ)|^17 ≤ (15111172048947/100000000000000 : ℝ)^13
        have hw : |(1178621807/5000000000 : ℝ)|=(1178621807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(223543091/312500000 : ℝ)|^17 ≤ (64527591411703/100000000000000 : ℝ)^13
        have hw : |(223543091/312500000 : ℝ)|=(223543091/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-592200081/2000000000 : ℝ)|^17 ≤ (5090309131091/25000000000000 : ℝ)^13
        have hw : |(-592200081/2000000000 : ℝ)|=(592200081/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304031_s2_s2_12 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1789371287/5000000000 : ℝ)*x 0 + (5439881277/10000000000 : ℝ)*x 1 + (1930422949/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1789371287/5000000000 : ℝ)^17 ≤ (26086556525569/100000000000000 : ℝ)^13 := by
    have hnat : (1789371287 : ℕ)^17*100000000000000^13 ≤ 26086556525569^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1789371287 5000000000 26086556525569 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5439881277/10000000000 : ℝ)^17 ≤ (704778012279/1562500000000 : ℝ)^13 := by
    have hnat : (5439881277 : ℕ)^17*1562500000000^13 ≤ 704778012279^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439881277 10000000000 704778012279 1562500000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1930422949/5000000000 : ℝ)^17 ≤ (2880765067833/10000000000000 : ℝ)^13 := by
    have hnat : (1930422949 : ℕ)^17*10000000000000^13 ≤ 2880765067833^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1930422949 5000000000 2880765067833 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1789371287/5000000000 : ℝ), (5439881277/10000000000 : ℝ), (1930422949/5000000000 : ℝ)] ![(26086556525569/100000000000000 : ℝ), (704778012279/1562500000000 : ℝ), (2880765067833/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1789371287/5000000000 : ℝ)|^17 ≤ (26086556525569/100000000000000 : ℝ)^13
        have hw : |(1789371287/5000000000 : ℝ)|=(1789371287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5439881277/10000000000 : ℝ)|^17 ≤ (704778012279/1562500000000 : ℝ)^13
        have hw : |(5439881277/10000000000 : ℝ)|=(5439881277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1930422949/5000000000 : ℝ)|^17 ≤ (2880765067833/10000000000000 : ℝ)^13
        have hw : |(1930422949/5000000000 : ℝ)|=(1930422949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304031_s2_s2_13 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-3674666373/10000000000 : ℝ)*x 0 + (841451797/2000000000 : ℝ)*x 1 + (1258633219/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3674666373/10000000000 : ℝ)^17 ≤ (3375583264819/12500000000000 : ℝ)^13 := by
    have hnat : (3674666373 : ℕ)^17*12500000000000^13 ≤ 3375583264819^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3674666373 10000000000 3375583264819 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (841451797/2000000000 : ℝ)^17 ≤ (32233443750537/100000000000000 : ℝ)^13 := by
    have hnat : (841451797 : ℕ)^17*100000000000000^13 ≤ 32233443750537^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      841451797 2000000000 32233443750537 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1258633219/2500000000 : ℝ)^17 ≤ (1630475604497/4000000000000 : ℝ)^13 := by
    have hnat : (1258633219 : ℕ)^17*4000000000000^13 ≤ 1630475604497^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1258633219 2500000000 1630475604497 4000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3674666373/10000000000 : ℝ), (841451797/2000000000 : ℝ), (1258633219/2500000000 : ℝ)] ![(3375583264819/12500000000000 : ℝ), (32233443750537/100000000000000 : ℝ), (1630475604497/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3674666373/10000000000 : ℝ)|^17 ≤ (3375583264819/12500000000000 : ℝ)^13
        have hw : |(-3674666373/10000000000 : ℝ)|=(3674666373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(841451797/2000000000 : ℝ)|^17 ≤ (32233443750537/100000000000000 : ℝ)^13
        have hw : |(841451797/2000000000 : ℝ)|=(841451797/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1258633219/2500000000 : ℝ)|^17 ≤ (1630475604497/4000000000000 : ℝ)^13
        have hw : |(1258633219/2500000000 : ℝ)|=(1258633219/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304031_s2_s2_14 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (7965082533/10000000000 : ℝ)*x 0 + (-70084631/10000000000 : ℝ)*x 1 + (3525705639/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7965082533/10000000000 : ℝ)^17 ≤ (14853106164167/20000000000000 : ℝ)^13 := by
    have hnat : (7965082533 : ℕ)^17*20000000000000^13 ≤ 14853106164167^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7965082533 10000000000 14853106164167 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (70084631/10000000000 : ℝ)^17 ≤ (152313183723/100000000000000 : ℝ)^13 := by
    have hnat : (70084631 : ℕ)^17*100000000000000^13 ≤ 152313183723^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70084631 10000000000 152313183723 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3525705639/10000000000 : ℝ)^17 ≤ (6395538995581/25000000000000 : ℝ)^13 := by
    have hnat : (3525705639 : ℕ)^17*25000000000000^13 ≤ 6395538995581^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3525705639 10000000000 6395538995581 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7965082533/10000000000 : ℝ), (-70084631/10000000000 : ℝ), (3525705639/10000000000 : ℝ)] ![(14853106164167/20000000000000 : ℝ), (152313183723/100000000000000 : ℝ), (6395538995581/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7965082533/10000000000 : ℝ)|^17 ≤ (14853106164167/20000000000000 : ℝ)^13
        have hw : |(7965082533/10000000000 : ℝ)|=(7965082533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-70084631/10000000000 : ℝ)|^17 ≤ (152313183723/100000000000000 : ℝ)^13
        have hw : |(-70084631/10000000000 : ℝ)|=(70084631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3525705639/10000000000 : ℝ)|^17 ≤ (6395538995581/25000000000000 : ℝ)^13
        have hw : |(3525705639/10000000000 : ℝ)|=(3525705639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304031_s2_s2_15 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2037621481/10000000000 : ℝ)*x 0 + (6800185169/10000000000 : ℝ)*x 1 + (-3686368903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2037621481/10000000000 : ℝ)^17 ≤ (3122382740559/25000000000000 : ℝ)^13 := by
    have hnat : (2037621481 : ℕ)^17*25000000000000^13 ≤ 3122382740559^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2037621481 10000000000 3122382740559 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6800185169/10000000000 : ℝ)^17 ≤ (3774580358321/6250000000000 : ℝ)^13 := by
    have hnat : (6800185169 : ℕ)^17*6250000000000^13 ≤ 3774580358321^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6800185169 10000000000 3774580358321 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3686368903/10000000000 : ℝ)^17 ≤ (42370598889/156250000000 : ℝ)^13 := by
    have hnat : (3686368903 : ℕ)^17*156250000000^13 ≤ 42370598889^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3686368903 10000000000 42370598889 156250000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2037621481/10000000000 : ℝ), (6800185169/10000000000 : ℝ), (-3686368903/10000000000 : ℝ)] ![(3122382740559/25000000000000 : ℝ), (3774580358321/6250000000000 : ℝ), (42370598889/156250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2037621481/10000000000 : ℝ)|^17 ≤ (3122382740559/25000000000000 : ℝ)^13
        have hw : |(2037621481/10000000000 : ℝ)|=(2037621481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6800185169/10000000000 : ℝ)|^17 ≤ (3774580358321/6250000000000 : ℝ)^13
        have hw : |(6800185169/10000000000 : ℝ)|=(6800185169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3686368903/10000000000 : ℝ)|^17 ≤ (42370598889/156250000000 : ℝ)^13
        have hw : |(-3686368903/10000000000 : ℝ)|=(3686368903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304031_s2_s2_19 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2522287999/10000000000 : ℝ)*x 0 + (481697593/1000000000 : ℝ)*x 1 + (2715829323/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2522287999/10000000000 : ℝ)^17 ≤ (8254703918079/50000000000000 : ℝ)^13 := by
    have hnat : (2522287999 : ℕ)^17*50000000000000^13 ≤ 8254703918079^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2522287999 10000000000 8254703918079 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (481697593/1000000000 : ℝ)^17 ≤ (9618484099447/25000000000000 : ℝ)^13 := by
    have hnat : (481697593 : ℕ)^17*25000000000000^13 ≤ 9618484099447^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      481697593 1000000000 9618484099447 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2715829323/5000000000 : ℝ)^17 ≤ (56270819677/125000000000 : ℝ)^13 := by
    have hnat : (2715829323 : ℕ)^17*125000000000^13 ≤ 56270819677^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715829323 5000000000 56270819677 125000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2522287999/10000000000 : ℝ), (481697593/1000000000 : ℝ), (2715829323/5000000000 : ℝ)] ![(8254703918079/50000000000000 : ℝ), (9618484099447/25000000000000 : ℝ), (56270819677/125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2522287999/10000000000 : ℝ)|^17 ≤ (8254703918079/50000000000000 : ℝ)^13
        have hw : |(2522287999/10000000000 : ℝ)|=(2522287999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(481697593/1000000000 : ℝ)|^17 ≤ (9618484099447/25000000000000 : ℝ)^13
        have hw : |(481697593/1000000000 : ℝ)|=(481697593/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2715829323/5000000000 : ℝ)|^17 ≤ (56270819677/125000000000 : ℝ)^13
        have hw : |(2715829323/5000000000 : ℝ)|=(2715829323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304031_s2_s2_20 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1386236793/5000000000 : ℝ)*x 0 + (6175143597/10000000000 : ℝ)*x 1 + (3785850227/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1386236793/5000000000 : ℝ)^17 ≤ (18682801825697/100000000000000 : ℝ)^13 := by
    have hnat : (1386236793 : ℕ)^17*100000000000000^13 ≤ 18682801825697^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1386236793 5000000000 18682801825697 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6175143597/10000000000 : ℝ)^17 ≤ (3327444264077/6250000000000 : ℝ)^13 := by
    have hnat : (6175143597 : ℕ)^17*6250000000000^13 ≤ 3327444264077^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6175143597 10000000000 3327444264077 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3785850227/10000000000 : ℝ)^17 ≤ (28078089927687/100000000000000 : ℝ)^13 := by
    have hnat : (3785850227 : ℕ)^17*100000000000000^13 ≤ 28078089927687^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3785850227 10000000000 28078089927687 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1386236793/5000000000 : ℝ), (6175143597/10000000000 : ℝ), (3785850227/10000000000 : ℝ)] ![(18682801825697/100000000000000 : ℝ), (3327444264077/6250000000000 : ℝ), (28078089927687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1386236793/5000000000 : ℝ)|^17 ≤ (18682801825697/100000000000000 : ℝ)^13
        have hw : |(-1386236793/5000000000 : ℝ)|=(1386236793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6175143597/10000000000 : ℝ)|^17 ≤ (3327444264077/6250000000000 : ℝ)^13
        have hw : |(6175143597/10000000000 : ℝ)|=(6175143597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3785850227/10000000000 : ℝ)|^17 ≤ (28078089927687/100000000000000 : ℝ)^13
        have hw : |(3785850227/10000000000 : ℝ)|=(3785850227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304031_s2_s2_21 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1445295591/2000000000 : ℝ)*x 0 + (16462757/5000000000 : ℝ)*x 1 + (554597971/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1445295591/2000000000 : ℝ)^17 ≤ (32695615074209/50000000000000 : ℝ)^13 := by
    have hnat : (1445295591 : ℕ)^17*50000000000000^13 ≤ 32695615074209^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1445295591 2000000000 32695615074209 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16462757/5000000000 : ℝ)^17 ≤ (56714803163/100000000000000 : ℝ)^13 := by
    have hnat : (16462757 : ℕ)^17*100000000000000^13 ≤ 56714803163^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16462757 5000000000 56714803163 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (554597971/1250000000 : ℝ)^17 ≤ (17276027520489/50000000000000 : ℝ)^13 := by
    have hnat : (554597971 : ℕ)^17*50000000000000^13 ≤ 17276027520489^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      554597971 1250000000 17276027520489 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1445295591/2000000000 : ℝ), (16462757/5000000000 : ℝ), (554597971/1250000000 : ℝ)] ![(32695615074209/50000000000000 : ℝ), (56714803163/100000000000000 : ℝ), (17276027520489/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1445295591/2000000000 : ℝ)|^17 ≤ (32695615074209/50000000000000 : ℝ)^13
        have hw : |(1445295591/2000000000 : ℝ)|=(1445295591/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(16462757/5000000000 : ℝ)|^17 ≤ (56714803163/100000000000000 : ℝ)^13
        have hw : |(16462757/5000000000 : ℝ)|=(16462757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(554597971/1250000000 : ℝ)|^17 ≤ (17276027520489/50000000000000 : ℝ)^13
        have hw : |(554597971/1250000000 : ℝ)|=(554597971/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304031_s2_s2_22 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2329060891/10000000000 : ℝ)*x 0 + (7003789107/10000000000 : ℝ)*x 1 + (-795091047/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2329060891/10000000000 : ℝ)^17 ≤ (14875352161459/100000000000000 : ℝ)^13 := by
    have hnat : (2329060891 : ℕ)^17*100000000000000^13 ≤ 14875352161459^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2329060891 10000000000 14875352161459 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7003789107/10000000000 : ℝ)^17 ≤ (62768714280507/100000000000000 : ℝ)^13 := by
    have hnat : (7003789107 : ℕ)^17*100000000000000^13 ≤ 62768714280507^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7003789107 10000000000 62768714280507 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (795091047/2500000000 : ℝ)^17 ≤ (11177966766669/50000000000000 : ℝ)^13 := by
    have hnat : (795091047 : ℕ)^17*50000000000000^13 ≤ 11177966766669^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      795091047 2500000000 11177966766669 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2329060891/10000000000 : ℝ), (7003789107/10000000000 : ℝ), (-795091047/2500000000 : ℝ)] ![(14875352161459/100000000000000 : ℝ), (62768714280507/100000000000000 : ℝ), (11177966766669/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2329060891/10000000000 : ℝ)|^17 ≤ (14875352161459/100000000000000 : ℝ)^13
        have hw : |(2329060891/10000000000 : ℝ)|=(2329060891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7003789107/10000000000 : ℝ)|^17 ≤ (62768714280507/100000000000000 : ℝ)^13
        have hw : |(7003789107/10000000000 : ℝ)|=(7003789107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-795091047/2500000000 : ℝ)|^17 ≤ (11177966766669/50000000000000 : ℝ)^13
        have hw : |(-795091047/2500000000 : ℝ)|=(795091047/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304031_s2_s2_25 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1371128281/2500000000 : ℝ)*x 0 + (4014923709/10000000000 : ℝ)*x 1 + (3367283337/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1371128281/2500000000 : ℝ)^17 ≤ (45590344498557/100000000000000 : ℝ)^13 := by
    have hnat : (1371128281 : ℕ)^17*100000000000000^13 ≤ 45590344498557^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1371128281 2500000000 45590344498557 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4014923709/10000000000 : ℝ)^17 ≤ (947505788819/3125000000000 : ℝ)^13 := by
    have hnat : (4014923709 : ℕ)^17*3125000000000^13 ≤ 947505788819^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4014923709 10000000000 947505788819 3125000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3367283337/10000000000 : ℝ)^17 ≤ (12044735118163/50000000000000 : ℝ)^13 := by
    have hnat : (3367283337 : ℕ)^17*50000000000000^13 ≤ 12044735118163^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3367283337 10000000000 12044735118163 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1371128281/2500000000 : ℝ), (4014923709/10000000000 : ℝ), (3367283337/10000000000 : ℝ)] ![(45590344498557/100000000000000 : ℝ), (947505788819/3125000000000 : ℝ), (12044735118163/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1371128281/2500000000 : ℝ)|^17 ≤ (45590344498557/100000000000000 : ℝ)^13
        have hw : |(1371128281/2500000000 : ℝ)|=(1371128281/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4014923709/10000000000 : ℝ)|^17 ≤ (947505788819/3125000000000 : ℝ)^13
        have hw : |(4014923709/10000000000 : ℝ)|=(4014923709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3367283337/10000000000 : ℝ)|^17 ≤ (12044735118163/50000000000000 : ℝ)^13
        have hw : |(3367283337/10000000000 : ℝ)|=(3367283337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c304031_s2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((1483/2000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1483/2000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(54357/100000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(54357/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4209/5000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(4209/5000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((55967/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(55967/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(1877/10000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(1877/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6339/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(6339/10000 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
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
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  have s2_pow0 : (1483/2000 : ℝ) ^ (33/8 : ℝ) ≤ (291211496327538639/1000000000000000000 : ℝ) := by
    have hpowers : (1483/2000 : ℝ)^33 ≤ (291211496327538639/1000000000000000000 : ℝ)^8 := by
      have hnat : (1483 : ℕ)^33*1000000000000000000^8 ≤ 291211496327538639^8*2000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1483 2000 291211496327538639 1000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1483/2000 : ℝ)) (X := (291211496327538639/1000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s2_corner0a : (1291211496327538639/1000000000000000000 : ℝ) ≤ (2659796838281097/2500000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (1291211496327538639/1000000000000000000 : ℝ)^8 ≤ (2659796838281097/2500000000000000 : ℝ)^33 := by
      have hnat : (1291211496327538639 : ℕ)^8*2500000000000000^33 ≤ 2659796838281097^33*1000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1291211496327538639 1000000000000000000 2659796838281097 2500000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2659796838281097/2500000000000000 : ℝ)) (X := (1291211496327538639/1000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s2_corner0b : (791211496327538639/500000000000000000 : ℝ) ≤ (5588440494082531/5000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (791211496327538639/500000000000000000 : ℝ)^8 ≤ (5588440494082531/5000000000000000 : ℝ)^33 := by
      have hnat : (791211496327538639 : ℕ)^8*5000000000000000^33 ≤ 5588440494082531^33*500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        791211496327538639 500000000000000000 5588440494082531 5000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5588440494082531/5000000000000000 : ℝ)) (X := (791211496327538639/500000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(159796838281097/1853750000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(268846817520337/3707500000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (1483/2000 : ℝ)) (alpha := (159796838281097/1853750000000000 : ℝ)) (beta := (268846817520337/3707500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1483/2000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(159796838281097/1853750000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(268846817520337/3707500000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (54357/100000 : ℝ) ^ (33/8 : ℝ) ≤ (8089633638248728097/100000000000000000000 : ℝ) := by
    have hpowers : (54357/100000 : ℝ)^33 ≤ (8089633638248728097/100000000000000000000 : ℝ)^8 := by
      have hnat : (54357 : ℕ)^33*100000000000000000000^8 ≤ 8089633638248728097^8*100000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        54357 100000 8089633638248728097 100000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (54357/100000 : ℝ)) (X := (8089633638248728097/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s2_corner1a : (108089633638248728097/100000000000000000000 : ℝ) ≤ (10190372779937811/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (108089633638248728097/100000000000000000000 : ℝ)^8 ≤ (10190372779937811/10000000000000000 : ℝ)^33 := by
      have hnat : (108089633638248728097 : ℕ)^8*10000000000000000^33 ≤ 10190372779937811^33*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        108089633638248728097 100000000000000000000 10190372779937811 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10190372779937811/10000000000000000 : ℝ)) (X := (108089633638248728097/100000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s2_corner1b : (58089633638248728097/50000000000000000000 : ℝ) ≤ (5185119428096827/5000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (58089633638248728097/50000000000000000000 : ℝ)^8 ≤ (5185119428096827/5000000000000000 : ℝ)^33 := by
      have hnat : (58089633638248728097 : ℕ)^8*5000000000000000^33 ≤ 5185119428096827^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        58089633638248728097 50000000000000000000 5185119428096827 5000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5185119428096827/5000000000000000 : ℝ)) (X := (58089633638248728097/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(190372779937811/5435700000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(179866076255843/5435700000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (54357/100000 : ℝ)) (alpha := (190372779937811/5435700000000000 : ℝ)) (beta := (179866076255843/5435700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (54357/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(190372779937811/5435700000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(179866076255843/5435700000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (4209/5000 : ℝ) ^ (33/8 : ℝ) ≤ (49145844345683816367/100000000000000000000 : ℝ) := by
    have hpowers : (4209/5000 : ℝ)^33 ≤ (49145844345683816367/100000000000000000000 : ℝ)^8 := by
      have hnat : (4209 : ℕ)^33*100000000000000000000^8 ≤ 49145844345683816367^8*5000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4209 5000 49145844345683816367 100000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4209/5000 : ℝ)) (X := (49145844345683816367/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s2_corner2a : (149145844345683816367/100000000000000000000 : ℝ) ≤ (5508807004551473/5000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (149145844345683816367/100000000000000000000 : ℝ)^8 ≤ (5508807004551473/5000000000000000 : ℝ)^33 := by
      have hnat : (149145844345683816367 : ℕ)^8*5000000000000000^33 ≤ 5508807004551473^33*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        149145844345683816367 100000000000000000000 5508807004551473 5000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5508807004551473/5000000000000000 : ℝ)) (X := (149145844345683816367/100000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s2_corner2b : (99145844345683816367/50000000000000000000 : ℝ) ≤ (11805212823862591/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (99145844345683816367/50000000000000000000 : ℝ)^8 ≤ (11805212823862591/10000000000000000 : ℝ)^33 := by
      have hnat : (99145844345683816367 : ℕ)^8*10000000000000000^33 ≤ 11805212823862591^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        99145844345683816367 50000000000000000000 11805212823862591 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11805212823862591/10000000000000000 : ℝ)) (X := (99145844345683816367/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(7374014558717/61000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(52506587650643/561200000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (4209/5000 : ℝ)) (alpha := (7374014558717/61000000000000 : ℝ)) (beta := (52506587650643/561200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (4209/5000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(7374014558717/61000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(52506587650643/561200000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_2 : ((768154359/2500000000 : ℝ)*X 2 0+(6164404827/10000000000 : ℝ)*X 2 1+(-3518228139/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304031_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((2127948727/5000000000 : ℝ)*X 0 0+(2449667537/5000000000 : ℝ)*X 0 1+(1885904409/5000000000 : ℝ)*X 0 2+(2127948727/5000000000 : ℝ)*X 1 0+(2449667537/5000000000 : ℝ)*X 1 1+(1885904409/5000000000 : ℝ)*X 1 2+(2127948727/5000000000 : ℝ)*X 2 0+(2449667537/5000000000 : ℝ)*X 2 1+(1885904409/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304031_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-167876773/500000000 : ℝ)*X 0 0+(1326639307/2500000000 : ℝ)*X 0 1+(4217495299/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304031_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((5652997611/10000000000 : ℝ)*X 1 0+(41780701/5000000000 : ℝ)*X 1 1+(6098609271/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304031_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((1178621807/5000000000 : ℝ)*X 2 0+(223543091/312500000 : ℝ)*X 2 1+(-592200081/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304031_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_12 : ((1789371287/5000000000 : ℝ)*X 0 0+(5439881277/10000000000 : ℝ)*X 0 1+(1930422949/5000000000 : ℝ)*X 0 2+(1789371287/5000000000 : ℝ)*X 1 0+(5439881277/10000000000 : ℝ)*X 1 1+(1930422949/5000000000 : ℝ)*X 1 2+(1789371287/5000000000 : ℝ)*X 2 0+(5439881277/10000000000 : ℝ)*X 2 1+(1930422949/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304031_s2_s2_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((-3674666373/10000000000 : ℝ)*X 0 0+(841451797/2000000000 : ℝ)*X 0 1+(1258633219/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304031_s2_s2_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((7965082533/10000000000 : ℝ)*X 1 0+(-70084631/10000000000 : ℝ)*X 1 1+(3525705639/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304031_s2_s2_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((2037621481/10000000000 : ℝ)*X 2 0+(6800185169/10000000000 : ℝ)*X 2 1+(-3686368903/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304031_s2_s2_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_19 : ((2522287999/10000000000 : ℝ)*X 0 0+(481697593/1000000000 : ℝ)*X 0 1+(2715829323/5000000000 : ℝ)*X 0 2+(2522287999/10000000000 : ℝ)*X 1 0+(481697593/1000000000 : ℝ)*X 1 1+(2715829323/5000000000 : ℝ)*X 1 2+(2522287999/10000000000 : ℝ)*X 2 0+(481697593/1000000000 : ℝ)*X 2 1+(2715829323/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304031_s2_s2_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((-1386236793/5000000000 : ℝ)*X 0 0+(6175143597/10000000000 : ℝ)*X 0 1+(3785850227/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304031_s2_s2_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((1445295591/2000000000 : ℝ)*X 1 0+(16462757/5000000000 : ℝ)*X 1 1+(554597971/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304031_s2_s2_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((2329060891/10000000000 : ℝ)*X 2 0+(7003789107/10000000000 : ℝ)*X 2 1+(-795091047/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304031_s2_s2_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_25 : ((1371128281/2500000000 : ℝ)*X 0 0+(4014923709/10000000000 : ℝ)*X 0 1+(3367283337/10000000000 : ℝ)*X 0 2+(1371128281/2500000000 : ℝ)*X 1 0+(4014923709/10000000000 : ℝ)*X 1 1+(3367283337/10000000000 : ℝ)*X 1 2+(1371128281/2500000000 : ℝ)*X 2 0+(4014923709/10000000000 : ℝ)*X 2 1+(3367283337/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304031_s2_s2_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((55967/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(55967/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (673601248846216314210238062879/47124099038750000000000000000000000 : ℝ) := by norm_num
    linear_combination (325163893369/1000000000000 : ℝ)*(base7) + (4563217/1000000000000 : ℝ)*(base40) + (31012012033/125000000000 : ℝ)*(base49) + (1100194580327/1000000000000 : ℝ)*(base50) + (29310711387/1000000000000 : ℝ)*(base60) + (1046169374823/250000000000 : ℝ)*(major_s2_0) + (1046169374823/250000000000 : ℝ)*(major_s2_1) + (1046169374823/250000000000 : ℝ)*(major_s2_2) + (1081335957429/200000000000 : ℝ)*(sp_s2_7) + (1081348774897/200000000000 : ℝ)*(sp_s2_8) + (5406422722211/1000000000000 : ℝ)*(sp_s2_9) + (308419489401/100000000000 : ℝ)*(sp_s2_12) + (3204367/50000000000 : ℝ)*(sp_s2_20) + (160576137/500000000000 : ℝ)*(sp_s2_22) + (2759031000641/1000000000000 : ℝ)*(f.failure) + (1081348774897/200000000000 : ℝ)*(f.sum) + (52136254279344719/276314750000000000000000000000 : ℝ)*base63 + (75764094783111/140300000000000000000000000 : ℝ)*base64 + (184585071755899/905950000000000000000000000 : ℝ)*base66 + (1883530860679/3812500000000000000000000 : ℝ)*base69 + (709132972124275681/5201622500000000000000000000000 : ℝ)*base70 + (801810688254923/1853750000000000000000000000 : ℝ)*base72 + (108192741311481/452975000000000000000000000 : ℝ)*base74 + (173100618522081/463437500000000000000000000 : ℝ)*base77 + (21783162099881354137/33588096250000000000000000000000 : ℝ)*base78 + (2719/12500000000000000 : ℝ)*base87 + (2719/12500000000000000 : ℝ)*base89 + (2719/12500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(1877/10000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(1877/10000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (37289040020722634577057172953/4097747742500000000000000000000000 : ℝ) := by norm_num
    linear_combination (2156313/1000000000000 : ℝ)*(base24) + (229985411889/500000000000 : ℝ)*(base40) + (7760823/1000000000000 : ℝ)*(base50) + (215563693499/1000000000000 : ℝ)*(base60) + (1902992569821/1000000000000 : ℝ)*(major_s2_0) + (1902992569821/1000000000000 : ℝ)*(major_s2_1) + (1902992569821/1000000000000 : ℝ)*(major_s2_2) + (55983249/1000000000000 : ℝ)*(sp_s2_2) + (3754087/100000000000 : ℝ)*(sp_s2_6) + (31891323139/12500000000 : ℝ)*(sp_s2_13) + (2551201341967/1000000000000 : ℝ)*(sp_s2_14) + (1275623855779/500000000000 : ℝ)*(sp_s2_15) + (78414919647/62500000000 : ℝ)*(sp_s2_19) + (104509153/1000000000000 : ℝ)*(sp_s2_21) + (1254676255223/1000000000000 : ℝ)*(f.failure) + (31891323139/12500000000 : ℝ)*(f.sum) + (72969768860985013/1105259000000000000000000000000 : ℝ)*base63 + (123288216212103/561200000000000000000000000 : ℝ)*base65 + (266006646740021/1811900000000000000000000000 : ℝ)*base67 + (6239340640257/61000000000000000000000000 : ℝ)*base69 + (382231181319164587/20806490000000000000000000000000 : ℝ)*base70 + (1600394886817927/3707500000000000000000000000 : ℝ)*base73 + (90508653839377/1811900000000000000000000000 : ℝ)*base74 + (375561972269119/926875000000000000000000000 : ℝ)*base76 + (2987754509403843097/16794048125000000000000000000000 : ℝ)*base79 + (10357/12500000000000000 : ℝ)*base87 + (10357/12500000000000000 : ℝ)*base89 + (10357/12500000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6339/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(6339/10000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (108360797387397904238150151/6717619250000000000000000000000 : ℝ) := by norm_num
    linear_combination (59754046201/200000000000 : ℝ)*(base7) + (533540519789/1000000000000 : ℝ)*(base40) + (485935295541/1000000000000 : ℝ)*(base49) + (245812833999/200000000000 : ℝ)*(base50) + (452642839/97656250 : ℝ)*(major_s2_0) + (452642839/97656250 : ℝ)*(major_s2_1) + (452642839/97656250 : ℝ)*(major_s2_2) + (55940369/500000000000 : ℝ)*(sp_s2_2) + (22695727/500000000000 : ℝ)*(sp_s2_6) + (224460651/500000000000 : ℝ)*(sp_s2_9) + (6027091072379/1000000000000 : ℝ)*(sp_s2_20) + (6027091072379/1000000000000 : ℝ)*(sp_s2_21) + (6026530270339/1000000000000 : ℝ)*(sp_s2_22) + (670940530883/200000000000 : ℝ)*(sp_s2_25) + (3055977814863/1000000000000 : ℝ)*(f.failure) + (6027091072379/1000000000000 : ℝ)*(f.sum) + (39527417132711729/82894425000000000000000000000 : ℝ)*base62 + (268985044023/1403000000000000000000000 : ℝ)*base65 + (24402670721293/135892500000000000000000000 : ℝ)*base66 + (634963528351/3050000000000000000000000 : ℝ)*base69 + (156680120070826173/520162250000000000000000000000 : ℝ)*base70 + (142390630059407/370750000000000000000000000 : ℝ)*base73 + (70254479831393/543570000000000000000000000 : ℝ)*base74 + (878086640333/185375000000000000000000000 : ℝ)*base76 + (7724874739095089701/20152857750000000000000000000000 : ℝ)*base78 + (12383/12500000000000000 : ℝ)*base86 + (12383/12500000000000000 : ℝ)*base88 + (12383/12500000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((1483/2000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1483/2000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(54357/100000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(54357/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4209/5000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(4209/5000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((55967/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(55967/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(1877/10000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(1877/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6339/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(6339/10000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c304031_s2 p hpa hpb X hX hprev1

#print axioms solution
