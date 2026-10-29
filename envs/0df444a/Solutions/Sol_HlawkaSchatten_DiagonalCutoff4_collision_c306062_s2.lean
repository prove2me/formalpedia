-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c306062_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:58:53.673326+00:00
-- url     : https://prove2.me/submissions/b2e7f6a7-6019-4e48-a14f-0af5575edf57

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
theorem collision_support_c306062_s2_s2_0 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-628132237/5000000000 : ℝ)*x 0 + (78400649/156250000 : ℝ)*x 1 + (-1230477093/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (628132237/5000000000 : ℝ)^135 ≤ (3297265679797/50000000000000 : ℝ)^103 := by
    have hnat : (628132237 : ℕ)^135*50000000000000^103 ≤ 3297265679797^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      628132237 5000000000 3297265679797 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (78400649/156250000 : ℝ)^135 ≤ (10124905590881/25000000000000 : ℝ)^103 := by
    have hnat : (78400649 : ℕ)^135*25000000000000^103 ≤ 10124905590881^103*156250000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      78400649 156250000 10124905590881 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1230477093/2000000000 : ℝ)^135 ≤ (26452923132541/50000000000000 : ℝ)^103 := by
    have hnat : (1230477093 : ℕ)^135*50000000000000^103 ≤ 26452923132541^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1230477093 2000000000 26452923132541 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-628132237/5000000000 : ℝ), (78400649/156250000 : ℝ), (-1230477093/2000000000 : ℝ)] ![(3297265679797/50000000000000 : ℝ), (10124905590881/25000000000000 : ℝ), (26452923132541/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-628132237/5000000000 : ℝ)|^135 ≤ (3297265679797/50000000000000 : ℝ)^103
        have hw : |(-628132237/5000000000 : ℝ)|=(628132237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(78400649/156250000 : ℝ)|^135 ≤ (10124905590881/25000000000000 : ℝ)^103
        have hw : |(78400649/156250000 : ℝ)|=(78400649/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1230477093/2000000000 : ℝ)|^135 ≤ (26452923132541/50000000000000 : ℝ)^103
        have hw : |(-1230477093/2000000000 : ℝ)|=(1230477093/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306062_s2_s2_1 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1005154309/2000000000 : ℝ)*x 0 + (-156656753/1250000000 : ℝ)*x 1 + (-768323587/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1005154309/2000000000 : ℝ)^135 ≤ (20292826007877/50000000000000 : ℝ)^103 := by
    have hnat : (1005154309 : ℕ)^135*50000000000000^103 ≤ 20292826007877^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005154309 2000000000 20292826007877 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (156656753/1250000000 : ℝ)^135 ≤ (164345666377/2500000000000 : ℝ)^103 := by
    have hnat : (156656753 : ℕ)^135*2500000000000^103 ≤ 164345666377^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      156656753 1250000000 164345666377 2500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (768323587/1250000000 : ℝ)^135 ≤ (52840521315391/100000000000000 : ℝ)^103 := by
    have hnat : (768323587 : ℕ)^135*100000000000000^103 ≤ 52840521315391^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      768323587 1250000000 52840521315391 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1005154309/2000000000 : ℝ), (-156656753/1250000000 : ℝ), (-768323587/1250000000 : ℝ)] ![(20292826007877/50000000000000 : ℝ), (164345666377/2500000000000 : ℝ), (52840521315391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1005154309/2000000000 : ℝ)|^135 ≤ (20292826007877/50000000000000 : ℝ)^103
        have hw : |(1005154309/2000000000 : ℝ)|=(1005154309/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-156656753/1250000000 : ℝ)|^135 ≤ (164345666377/2500000000000 : ℝ)^103
        have hw : |(-156656753/1250000000 : ℝ)|=(156656753/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-768323587/1250000000 : ℝ)|^135 ≤ (52840521315391/100000000000000 : ℝ)^103
        have hw : |(-768323587/1250000000 : ℝ)|=(768323587/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306062_s2_s2_2 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2696564399/5000000000 : ℝ)*x 0 + (1368295537/2500000000 : ℝ)*x 1 + (869387743/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2696564399/5000000000 : ℝ)^135 ≤ (8903467736647/20000000000000 : ℝ)^103 := by
    have hnat : (2696564399 : ℕ)^135*20000000000000^103 ≤ 8903467736647^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696564399 5000000000 8903467736647 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1368295537/2500000000 : ℝ)^135 ≤ (56731777257/125000000000 : ℝ)^103 := by
    have hnat : (1368295537 : ℕ)^135*125000000000^103 ≤ 56731777257^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1368295537 2500000000 56731777257 125000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (869387743/5000000000 : ℝ)^135 ≤ (10097239487397/100000000000000 : ℝ)^103 := by
    have hnat : (869387743 : ℕ)^135*100000000000000^103 ≤ 10097239487397^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      869387743 5000000000 10097239487397 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2696564399/5000000000 : ℝ), (1368295537/2500000000 : ℝ), (869387743/5000000000 : ℝ)] ![(8903467736647/20000000000000 : ℝ), (56731777257/125000000000 : ℝ), (10097239487397/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2696564399/5000000000 : ℝ)|^135 ≤ (8903467736647/20000000000000 : ℝ)^103
        have hw : |(2696564399/5000000000 : ℝ)|=(2696564399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1368295537/2500000000 : ℝ)|^135 ≤ (56731777257/125000000000 : ℝ)^103
        have hw : |(1368295537/2500000000 : ℝ)|=(1368295537/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(869387743/5000000000 : ℝ)|^135 ≤ (10097239487397/100000000000000 : ℝ)^103
        have hw : |(869387743/5000000000 : ℝ)|=(869387743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306062_s2_s2_7 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-48142913/312500000 : ℝ)*x 0 + (2785295579/10000000000 : ℝ)*x 1 + (-3918698897/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (48142913/312500000 : ℝ)^135 ≤ (8616121387751/100000000000000 : ℝ)^103 := by
    have hnat : (48142913 : ℕ)^135*100000000000000^103 ≤ 8616121387751^103*312500000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48142913 312500000 8616121387751 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2785295579/10000000000 : ℝ)^135 ≤ (2340529561413/12500000000000 : ℝ)^103 := by
    have hnat : (2785295579 : ℕ)^135*12500000000000^103 ≤ 2340529561413^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2785295579 10000000000 2340529561413 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3918698897/5000000000 : ℝ)^135 ≤ (9082455262163/12500000000000 : ℝ)^103 := by
    have hnat : (3918698897 : ℕ)^135*12500000000000^103 ≤ 9082455262163^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3918698897 5000000000 9082455262163 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-48142913/312500000 : ℝ), (2785295579/10000000000 : ℝ), (-3918698897/5000000000 : ℝ)] ![(8616121387751/100000000000000 : ℝ), (2340529561413/12500000000000 : ℝ), (9082455262163/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-48142913/312500000 : ℝ)|^135 ≤ (8616121387751/100000000000000 : ℝ)^103
        have hw : |(-48142913/312500000 : ℝ)|=(48142913/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2785295579/10000000000 : ℝ)|^135 ≤ (2340529561413/12500000000000 : ℝ)^103
        have hw : |(2785295579/10000000000 : ℝ)|=(2785295579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3918698897/5000000000 : ℝ)|^135 ≤ (9082455262163/12500000000000 : ℝ)^103
        have hw : |(-3918698897/5000000000 : ℝ)|=(3918698897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306062_s2_s2_8 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1597533687/5000000000 : ℝ)*x 0 + (-127342753/1250000000 : ℝ)*x 1 + (-7830409797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1597533687/5000000000 : ℝ)^135 ≤ (11207327680541/50000000000000 : ℝ)^103 := by
    have hnat : (1597533687 : ℕ)^135*50000000000000^103 ≤ 11207327680541^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1597533687 5000000000 11207327680541 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (127342753/1250000000 : ℝ)^135 ≤ (250530152903/5000000000000 : ℝ)^103 := by
    have hnat : (127342753 : ℕ)^135*5000000000000^103 ≤ 250530152903^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127342753 1250000000 250530152903 5000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7830409797/10000000000 : ℝ)^135 ≤ (18143685389477/25000000000000 : ℝ)^103 := by
    have hnat : (7830409797 : ℕ)^135*25000000000000^103 ≤ 18143685389477^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7830409797 10000000000 18143685389477 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1597533687/5000000000 : ℝ), (-127342753/1250000000 : ℝ), (-7830409797/10000000000 : ℝ)] ![(11207327680541/50000000000000 : ℝ), (250530152903/5000000000000 : ℝ), (18143685389477/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1597533687/5000000000 : ℝ)|^135 ≤ (11207327680541/50000000000000 : ℝ)^103
        have hw : |(1597533687/5000000000 : ℝ)|=(1597533687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-127342753/1250000000 : ℝ)|^135 ≤ (250530152903/5000000000000 : ℝ)^103
        have hw : |(-127342753/1250000000 : ℝ)|=(127342753/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7830409797/10000000000 : ℝ)|^135 ≤ (18143685389477/25000000000000 : ℝ)^103
        have hw : |(-7830409797/10000000000 : ℝ)|=(7830409797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306062_s2_s2_9 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3582986031/10000000000 : ℝ)*x 0 + (7143535779/10000000000 : ℝ)*x 1 + (836937829/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3582986031/10000000000 : ℝ)^135 ≤ (325587837647/1250000000000 : ℝ)^103 := by
    have hnat : (3582986031 : ℕ)^135*1250000000000^103 ≤ 325587837647^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3582986031 10000000000 325587837647 1250000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7143535779/10000000000 : ℝ)^135 ≤ (64346812954877/100000000000000 : ℝ)^103 := by
    have hnat : (7143535779 : ℕ)^135*100000000000000^103 ≤ 64346812954877^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7143535779 10000000000 64346812954877 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (836937829/5000000000 : ℝ)^135 ≤ (1921232004933/20000000000000 : ℝ)^103 := by
    have hnat : (836937829 : ℕ)^135*20000000000000^103 ≤ 1921232004933^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      836937829 5000000000 1921232004933 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3582986031/10000000000 : ℝ), (7143535779/10000000000 : ℝ), (836937829/5000000000 : ℝ)] ![(325587837647/1250000000000 : ℝ), (64346812954877/100000000000000 : ℝ), (1921232004933/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3582986031/10000000000 : ℝ)|^135 ≤ (325587837647/1250000000000 : ℝ)^103
        have hw : |(3582986031/10000000000 : ℝ)|=(3582986031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7143535779/10000000000 : ℝ)|^135 ≤ (64346812954877/100000000000000 : ℝ)^103
        have hw : |(7143535779/10000000000 : ℝ)|=(7143535779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(836937829/5000000000 : ℝ)|^135 ≤ (1921232004933/20000000000000 : ℝ)^103
        have hw : |(836937829/5000000000 : ℝ)|=(836937829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306062_s2_s2_13 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1995912739/5000000000 : ℝ)*x 0 + (380835253/500000000 : ℝ)*x 1 + (-739299/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1995912739/5000000000 : ℝ)^135 ≤ (30009839758473/100000000000000 : ℝ)^103 := by
    have hnat : (1995912739 : ℕ)^135*100000000000000^103 ≤ 30009839758473^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1995912739 5000000000 30009839758473 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (380835253/500000000 : ℝ)^135 ≤ (8748721916717/12500000000000 : ℝ)^103 := by
    have hnat : (380835253 : ℕ)^135*12500000000000^103 ≤ 8748721916717^103*500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      380835253 500000000 8748721916717 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (739299/10000000000 : ℝ)^135 ≤ (192449489/50000000000000 : ℝ)^103 := by
    have hnat : (739299 : ℕ)^135*50000000000000^103 ≤ 192449489^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      739299 10000000000 192449489 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1995912739/5000000000 : ℝ), (380835253/500000000 : ℝ), (-739299/10000000000 : ℝ)] ![(30009839758473/100000000000000 : ℝ), (8748721916717/12500000000000 : ℝ), (192449489/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1995912739/5000000000 : ℝ)|^135 ≤ (30009839758473/100000000000000 : ℝ)^103
        have hw : |(1995912739/5000000000 : ℝ)|=(1995912739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(380835253/500000000 : ℝ)|^135 ≤ (8748721916717/12500000000000 : ℝ)^103
        have hw : |(380835253/500000000 : ℝ)|=(380835253/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-739299/10000000000 : ℝ)|^135 ≤ (192449489/50000000000000 : ℝ)^103
        have hw : |(-739299/10000000000 : ℝ)|=(739299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306062_s2_s2_14 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-251602491/2500000000 : ℝ)*x 0 + (1577200893/5000000000 : ℝ)*x 1 + (-7867633893/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (251602491/2500000000 : ℝ)^135 ≤ (2465627323049/50000000000000 : ℝ)^103 := by
    have hnat : (251602491 : ℕ)^135*50000000000000^103 ≤ 2465627323049^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      251602491 2500000000 2465627323049 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1577200893/5000000000 : ℝ)^135 ≤ (2755184929317/12500000000000 : ℝ)^103 := by
    have hnat : (1577200893 : ℕ)^135*12500000000000^103 ≤ 2755184929317^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1577200893 5000000000 2755184929317 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7867633893/10000000000 : ℝ)^135 ≤ (36513632951393/50000000000000 : ℝ)^103 := by
    have hnat : (7867633893 : ℕ)^135*50000000000000^103 ≤ 36513632951393^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7867633893 10000000000 36513632951393 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-251602491/2500000000 : ℝ), (1577200893/5000000000 : ℝ), (-7867633893/10000000000 : ℝ)] ![(2465627323049/50000000000000 : ℝ), (2755184929317/12500000000000 : ℝ), (36513632951393/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-251602491/2500000000 : ℝ)|^135 ≤ (2465627323049/50000000000000 : ℝ)^103
        have hw : |(-251602491/2500000000 : ℝ)|=(251602491/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1577200893/5000000000 : ℝ)|^135 ≤ (2755184929317/12500000000000 : ℝ)^103
        have hw : |(1577200893/5000000000 : ℝ)|=(1577200893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7867633893/10000000000 : ℝ)|^135 ≤ (36513632951393/50000000000000 : ℝ)^103
        have hw : |(-7867633893/10000000000 : ℝ)|=(7867633893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306062_s2_s2_15 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2757813803/10000000000 : ℝ)*x 0 + (-1535040151/10000000000 : ℝ)*x 1 + (-7860620199/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2757813803/10000000000 : ℝ)^135 ≤ (4620616054093/25000000000000 : ℝ)^103 := by
    have hnat : (2757813803 : ℕ)^135*25000000000000^103 ≤ 4620616054093^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2757813803 10000000000 4620616054093 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1535040151/10000000000 : ℝ)^135 ≤ (8575584610793/100000000000000 : ℝ)^103 := by
    have hnat : (1535040151 : ℕ)^135*100000000000000^103 ≤ 8575584610793^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1535040151 10000000000 8575584610793 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7860620199/10000000000 : ℝ)^135 ≤ (36470975578677/50000000000000 : ℝ)^103 := by
    have hnat : (7860620199 : ℕ)^135*50000000000000^103 ≤ 36470975578677^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7860620199 10000000000 36470975578677 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2757813803/10000000000 : ℝ), (-1535040151/10000000000 : ℝ), (-7860620199/10000000000 : ℝ)] ![(4620616054093/25000000000000 : ℝ), (8575584610793/100000000000000 : ℝ), (36470975578677/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2757813803/10000000000 : ℝ)|^135 ≤ (4620616054093/25000000000000 : ℝ)^103
        have hw : |(2757813803/10000000000 : ℝ)|=(2757813803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1535040151/10000000000 : ℝ)|^135 ≤ (8575584610793/100000000000000 : ℝ)^103
        have hw : |(-1535040151/10000000000 : ℝ)|=(1535040151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7860620199/10000000000 : ℝ)|^135 ≤ (36470975578677/50000000000000 : ℝ)^103
        have hw : |(-7860620199/10000000000 : ℝ)|=(7860620199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306062_s2_s2_16 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (7039427681/10000000000 : ℝ)*x 0 + (3705609729/10000000000 : ℝ)*x 1 + (420189031/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7039427681/10000000000 : ℝ)^135 ≤ (7890060406901/12500000000000 : ℝ)^103 := by
    have hnat : (7039427681 : ℕ)^135*12500000000000^103 ≤ 7890060406901^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7039427681 10000000000 7890060406901 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3705609729/10000000000 : ℝ)^135 ≤ (13610785020723/50000000000000 : ℝ)^103 := by
    have hnat : (3705609729 : ℕ)^135*50000000000000^103 ≤ 13610785020723^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3705609729 10000000000 13610785020723 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (420189031/2500000000 : ℝ)^135 ≤ (4828973346867/50000000000000 : ℝ)^103 := by
    have hnat : (420189031 : ℕ)^135*50000000000000^103 ≤ 4828973346867^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420189031 2500000000 4828973346867 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7039427681/10000000000 : ℝ), (3705609729/10000000000 : ℝ), (420189031/2500000000 : ℝ)] ![(7890060406901/12500000000000 : ℝ), (13610785020723/50000000000000 : ℝ), (4828973346867/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7039427681/10000000000 : ℝ)|^135 ≤ (7890060406901/12500000000000 : ℝ)^103
        have hw : |(7039427681/10000000000 : ℝ)|=(7039427681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3705609729/10000000000 : ℝ)|^135 ≤ (13610785020723/50000000000000 : ℝ)^103
        have hw : |(3705609729/10000000000 : ℝ)|=(3705609729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(420189031/2500000000 : ℝ)|^135 ≤ (4828973346867/50000000000000 : ℝ)^103
        have hw : |(420189031/2500000000 : ℝ)|=(420189031/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306062_s2_s2_20 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (7780057709/10000000000 : ℝ)*x 0 + (947465587/2500000000 : ℝ)*x 1 + (-57251/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7780057709/10000000000 : ℝ)^135 ≤ (14392737293983/20000000000000 : ℝ)^103 := by
    have hnat : (7780057709 : ℕ)^135*20000000000000^103 ≤ 14392737293983^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7780057709 10000000000 14392737293983 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (947465587/2500000000 : ℝ)^135 ≤ (7008907649211/25000000000000 : ℝ)^103 := by
    have hnat : (947465587 : ℕ)^135*25000000000000^103 ≤ 7008907649211^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      947465587 2500000000 7008907649211 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (57251/500000000 : ℝ)^135 ≤ (136582999/20000000000000 : ℝ)^103 := by
    have hnat : (57251 : ℕ)^135*20000000000000^103 ≤ 136582999^103*500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      57251 500000000 136582999 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7780057709/10000000000 : ℝ), (947465587/2500000000 : ℝ), (-57251/500000000 : ℝ)] ![(14392737293983/20000000000000 : ℝ), (7008907649211/25000000000000 : ℝ), (136582999/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7780057709/10000000000 : ℝ)|^135 ≤ (14392737293983/20000000000000 : ℝ)^103
        have hw : |(7780057709/10000000000 : ℝ)|=(7780057709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(947465587/2500000000 : ℝ)|^135 ≤ (7008907649211/25000000000000 : ℝ)^103
        have hw : |(947465587/2500000000 : ℝ)|=(947465587/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-57251/500000000 : ℝ)|^135 ≤ (136582999/20000000000000 : ℝ)^103
        have hw : |(-57251/500000000 : ℝ)|=(57251/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306062_s2_s2_21 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-174716681/5000000000 : ℝ)*x 0 + (6538307483/10000000000 : ℝ)*x 1 + (-159660001/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (174716681/5000000000 : ℝ)^135 ≤ (616293203257/50000000000000 : ℝ)^103 := by
    have hnat : (174716681 : ℕ)^135*50000000000000^103 ≤ 616293203257^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174716681 5000000000 616293203257 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6538307483/10000000000 : ℝ)^135 ≤ (57297303569163/100000000000000 : ℝ)^103 := by
    have hnat : (6538307483 : ℕ)^135*100000000000000^103 ≤ 57297303569163^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6538307483 10000000000 57297303569163 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (159660001/312500000 : ℝ)^135 ≤ (41470110010103/100000000000000 : ℝ)^103 := by
    have hnat : (159660001 : ℕ)^135*100000000000000^103 ≤ 41470110010103^103*312500000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      159660001 312500000 41470110010103 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-174716681/5000000000 : ℝ), (6538307483/10000000000 : ℝ), (-159660001/312500000 : ℝ)] ![(616293203257/50000000000000 : ℝ), (57297303569163/100000000000000 : ℝ), (41470110010103/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-174716681/5000000000 : ℝ)|^135 ≤ (616293203257/50000000000000 : ℝ)^103
        have hw : |(-174716681/5000000000 : ℝ)|=(174716681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6538307483/10000000000 : ℝ)|^135 ≤ (57297303569163/100000000000000 : ℝ)^103
        have hw : |(6538307483/10000000000 : ℝ)|=(6538307483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-159660001/312500000 : ℝ)|^135 ≤ (41470110010103/100000000000000 : ℝ)^103
        have hw : |(-159660001/312500000 : ℝ)|=(159660001/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306062_s2_s2_22 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3381350649/5000000000 : ℝ)*x 0 + (-561215411/10000000000 : ℝ)*x 1 + (-4762125641/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3381350649/5000000000 : ℝ)^135 ≤ (29944152178317/50000000000000 : ℝ)^103 := by
    have hnat : (3381350649 : ℕ)^135*50000000000000^103 ≤ 29944152178317^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3381350649 5000000000 29944152178317 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (561215411/10000000000 : ℝ)^135 ≤ (458711523299/20000000000000 : ℝ)^103 := by
    have hnat : (561215411 : ℕ)^135*20000000000000^103 ≤ 458711523299^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561215411 10000000000 458711523299 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4762125641/10000000000 : ℝ)^135 ≤ (4727267251293/12500000000000 : ℝ)^103 := by
    have hnat : (4762125641 : ℕ)^135*12500000000000^103 ≤ 4727267251293^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4762125641 10000000000 4727267251293 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3381350649/5000000000 : ℝ), (-561215411/10000000000 : ℝ), (-4762125641/10000000000 : ℝ)] ![(29944152178317/50000000000000 : ℝ), (458711523299/20000000000000 : ℝ), (4727267251293/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3381350649/5000000000 : ℝ)|^135 ≤ (29944152178317/50000000000000 : ℝ)^103
        have hw : |(3381350649/5000000000 : ℝ)|=(3381350649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-561215411/10000000000 : ℝ)|^135 ≤ (458711523299/20000000000000 : ℝ)^103
        have hw : |(-561215411/10000000000 : ℝ)|=(561215411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4762125641/10000000000 : ℝ)|^135 ≤ (4727267251293/12500000000000 : ℝ)^103
        have hw : |(-4762125641/10000000000 : ℝ)|=(4762125641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306062_s2_s2_23 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1723246909/5000000000 : ℝ)*x 0 + (3527020991/5000000000 : ℝ)*x 1 + (1977703441/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1723246909/5000000000 : ℝ)^135 ≤ (12377135080143/50000000000000 : ℝ)^103 := by
    have hnat : (1723246909 : ℕ)^135*50000000000000^103 ≤ 12377135080143^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1723246909 5000000000 12377135080143 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3527020991/5000000000 : ℝ)^135 ≤ (63292292893681/100000000000000 : ℝ)^103 := by
    have hnat : (3527020991 : ℕ)^135*100000000000000^103 ≤ 63292292893681^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3527020991 5000000000 63292292893681 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1977703441/10000000000 : ℝ)^135 ≤ (5976718466669/50000000000000 : ℝ)^103 := by
    have hnat : (1977703441 : ℕ)^135*50000000000000^103 ≤ 5976718466669^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1977703441 10000000000 5976718466669 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1723246909/5000000000 : ℝ), (3527020991/5000000000 : ℝ), (1977703441/10000000000 : ℝ)] ![(12377135080143/50000000000000 : ℝ), (63292292893681/100000000000000 : ℝ), (5976718466669/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1723246909/5000000000 : ℝ)|^135 ≤ (12377135080143/50000000000000 : ℝ)^103
        have hw : |(1723246909/5000000000 : ℝ)|=(1723246909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3527020991/5000000000 : ℝ)|^135 ≤ (63292292893681/100000000000000 : ℝ)^103
        have hw : |(3527020991/5000000000 : ℝ)|=(3527020991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1977703441/10000000000 : ℝ)|^135 ≤ (5976718466669/50000000000000 : ℝ)^103
        have hw : |(1977703441/10000000000 : ℝ)|=(1977703441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306062_s2_s2_27 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1659485937/2000000000 : ℝ)*x 0 + (1546269813/5000000000 : ℝ)*x 1 + (-23741671/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1659485937/2000000000 : ℝ)^135 ≤ (78299863309139/100000000000000 : ℝ)^103 := by
    have hnat : (1659485937 : ℕ)^135*100000000000000^103 ≤ 78299863309139^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1659485937 2000000000 78299863309139 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1546269813/5000000000 : ℝ)^135 ≤ (4295330796447/20000000000000 : ℝ)^103 := by
    have hnat : (1546269813 : ℕ)^135*20000000000000^103 ≤ 4295330796447^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1546269813 5000000000 4295330796447 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (23741671/2500000000 : ℝ)^135 ≤ (223482696347/100000000000000 : ℝ)^103 := by
    have hnat : (23741671 : ℕ)^135*100000000000000^103 ≤ 223482696347^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23741671 2500000000 223482696347 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1659485937/2000000000 : ℝ), (1546269813/5000000000 : ℝ), (-23741671/2500000000 : ℝ)] ![(78299863309139/100000000000000 : ℝ), (4295330796447/20000000000000 : ℝ), (223482696347/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1659485937/2000000000 : ℝ)|^135 ≤ (78299863309139/100000000000000 : ℝ)^103
        have hw : |(1659485937/2000000000 : ℝ)|=(1659485937/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1546269813/5000000000 : ℝ)|^135 ≤ (4295330796447/20000000000000 : ℝ)^103
        have hw : |(1546269813/5000000000 : ℝ)|=(1546269813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-23741671/2500000000 : ℝ)|^135 ≤ (223482696347/100000000000000 : ℝ)^103
        have hw : |(-23741671/2500000000 : ℝ)|=(23741671/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c306062_s2 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev1 : (0 : ℝ) ≤ ((86979/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(86979/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(86569/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(86569/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-35827/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-35827/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((9443/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9443/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(75537/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(75537/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-29307/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-29307/50000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (38461/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (38461/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (38461/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (38461/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (38461/50000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (38461/50000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (92997/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  have s2_pow0 : (86979/100000 : ℝ) ^ (67/16 : ℝ) ≤ (13939200071938109233/25000000000000000000 : ℝ) := by
    have hpowers : (86979/100000 : ℝ)^67 ≤ (13939200071938109233/25000000000000000000 : ℝ)^16 := by
      have hnat : (86979 : ℕ)^67*25000000000000000000^16 ≤ 13939200071938109233^16*100000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        86979 100000 13939200071938109233 25000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (86979/100000 : ℝ)) (X := (13939200071938109233/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s2_corner0a : (38939200071938109233/25000000000000000000 : ℝ) ≤ (2779057324773877/2500000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (38939200071938109233/25000000000000000000 : ℝ)^16 ≤ (2779057324773877/2500000000000000 : ℝ)^67 := by
      have hnat : (38939200071938109233 : ℕ)^16*2500000000000000^67 ≤ 2779057324773877^67*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        38939200071938109233 25000000000000000000 2779057324773877 2500000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2779057324773877/2500000000000000 : ℝ)) (X := (38939200071938109233/25000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s2_corner0b : (26439200071938109233/12500000000000000000 : ℝ) ≤ (11958941128403019/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (26439200071938109233/12500000000000000000 : ℝ)^16 ≤ (11958941128403019/10000000000000000 : ℝ)^67 := by
      have hnat : (26439200071938109233 : ℕ)^16*10000000000000000^67 ≤ 11958941128403019^67*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26439200071938109233 12500000000000000000 11958941128403019 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11958941128403019/10000000000000000 : ℝ)) (X := (26439200071938109233/12500000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(93019108257959/724825000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(842711829307511/8697900000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (86979/100000 : ℝ)) (alpha := (93019108257959/724825000000000 : ℝ)) (beta := (842711829307511/8697900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (86979/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(93019108257959/724825000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(842711829307511/8697900000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (86569/100000 : ℝ) ^ (67/16 : ℝ) ≤ (54664458873996378029/100000000000000000000 : ℝ) := by
    have hpowers : (86569/100000 : ℝ)^67 ≤ (54664458873996378029/100000000000000000000 : ℝ)^16 := by
      have hnat : (86569 : ℕ)^67*100000000000000000000^16 ≤ 54664458873996378029^16*100000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        86569 100000 54664458873996378029 100000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (86569/100000 : ℝ)) (X := (54664458873996378029/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s2_corner1a : (154664458873996378029/100000000000000000000 : ℝ) ≤ (5548781107050601/5000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (154664458873996378029/100000000000000000000 : ℝ)^16 ≤ (5548781107050601/5000000000000000 : ℝ)^67 := by
      have hnat : (154664458873996378029 : ℕ)^16*5000000000000000^67 ≤ 5548781107050601^67*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        154664458873996378029 100000000000000000000 5548781107050601 5000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5548781107050601/5000000000000000 : ℝ)) (X := (154664458873996378029/100000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s2_corner1b : (104664458873996378029/50000000000000000000 : ℝ) ≤ (1491165846456447/1250000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (104664458873996378029/50000000000000000000 : ℝ)^16 ≤ (1491165846456447/1250000000000000 : ℝ)^67 := by
      have hnat : (104664458873996378029 : ℕ)^16*1250000000000000^67 ≤ 1491165846456447^67*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        104664458873996378029 50000000000000000000 1491165846456447 1250000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1491165846456447/1250000000000000 : ℝ)) (X := (104664458873996378029/50000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(548781107050601/4328450000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(59411754110741/618350000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (86569/100000 : ℝ)) (alpha := (548781107050601/4328450000000000 : ℝ)) (beta := (59411754110741/618350000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (86569/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(548781107050601/4328450000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(59411754110741/618350000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (35827/50000 : ℝ) ^ (67/16 : ℝ) ≤ (24763917011033388749/100000000000000000000 : ℝ) := by
    have hpowers : (35827/50000 : ℝ)^67 ≤ (24763917011033388749/100000000000000000000 : ℝ)^16 := by
      have hnat : (35827 : ℕ)^67*100000000000000000000^16 ≤ 24763917011033388749^16*50000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        35827 50000 24763917011033388749 100000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (35827/50000 : ℝ)) (X := (24763917011033388749/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s2_corner2a : (124763917011033388749/100000000000000000000 : ℝ) ≤ (5271286624446797/5000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (124763917011033388749/100000000000000000000 : ℝ)^16 ≤ (5271286624446797/5000000000000000 : ℝ)^67 := by
      have hnat : (124763917011033388749 : ℕ)^16*5000000000000000^67 ≤ 5271286624446797^67*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        124763917011033388749 100000000000000000000 5271286624446797 5000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5271286624446797/5000000000000000 : ℝ)) (X := (124763917011033388749/100000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s2_corner2b : (74763917011033388749/50000000000000000000 : ℝ) ≤ (11008411791517293/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (74763917011033388749/50000000000000000000 : ℝ)^16 ≤ (11008411791517293/10000000000000000 : ℝ)^67 := by
      have hnat : (74763917011033388749 : ℕ)^16*10000000000000000^67 ≤ 11008411791517293^67*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        74763917011033388749 50000000000000000000 11008411791517293 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11008411791517293/10000000000000000 : ℝ)) (X := (74763917011033388749/50000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(271286624446797/3582700000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(465838542623699/7165400000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (35827/50000 : ℝ)) (alpha := (271286624446797/3582700000000000 : ℝ)) (beta := (465838542623699/7165400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (35827/50000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(271286624446797/3582700000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(465838542623699/7165400000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-628132237/5000000000 : ℝ)*X 0 0+(78400649/156250000 : ℝ)*X 0 1+(-1230477093/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306062_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((1005154309/2000000000 : ℝ)*X 1 0+(-156656753/1250000000 : ℝ)*X 1 1+(-768323587/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306062_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((2696564399/5000000000 : ℝ)*X 2 0+(1368295537/2500000000 : ℝ)*X 2 1+(869387743/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306062_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-48142913/312500000 : ℝ)*X 0 0+(2785295579/10000000000 : ℝ)*X 0 1+(-3918698897/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306062_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((1597533687/5000000000 : ℝ)*X 1 0+(-127342753/1250000000 : ℝ)*X 1 1+(-7830409797/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306062_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((3582986031/10000000000 : ℝ)*X 2 0+(7143535779/10000000000 : ℝ)*X 2 1+(836937829/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306062_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((1995912739/5000000000 : ℝ)*X 0 0+(380835253/500000000 : ℝ)*X 0 1+(-739299/10000000000 : ℝ)*X 0 2+(1995912739/5000000000 : ℝ)*X 1 0+(380835253/500000000 : ℝ)*X 1 1+(-739299/10000000000 : ℝ)*X 1 2+(1995912739/5000000000 : ℝ)*X 2 0+(380835253/500000000 : ℝ)*X 2 1+(-739299/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306062_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-251602491/2500000000 : ℝ)*X 0 0+(1577200893/5000000000 : ℝ)*X 0 1+(-7867633893/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306062_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((2757813803/10000000000 : ℝ)*X 1 0+(-1535040151/10000000000 : ℝ)*X 1 1+(-7860620199/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306062_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((7039427681/10000000000 : ℝ)*X 2 0+(3705609729/10000000000 : ℝ)*X 2 1+(420189031/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306062_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((7780057709/10000000000 : ℝ)*X 0 0+(947465587/2500000000 : ℝ)*X 0 1+(-57251/500000000 : ℝ)*X 0 2+(7780057709/10000000000 : ℝ)*X 1 0+(947465587/2500000000 : ℝ)*X 1 1+(-57251/500000000 : ℝ)*X 1 2+(7780057709/10000000000 : ℝ)*X 2 0+(947465587/2500000000 : ℝ)*X 2 1+(-57251/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306062_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-174716681/5000000000 : ℝ)*X 0 0+(6538307483/10000000000 : ℝ)*X 0 1+(-159660001/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306062_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((3381350649/5000000000 : ℝ)*X 1 0+(-561215411/10000000000 : ℝ)*X 1 1+(-4762125641/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306062_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((1723246909/5000000000 : ℝ)*X 2 0+(3527020991/5000000000 : ℝ)*X 2 1+(1977703441/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306062_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((1659485937/2000000000 : ℝ)*X 0 0+(1546269813/5000000000 : ℝ)*X 0 1+(-23741671/2500000000 : ℝ)*X 0 2+(1659485937/2000000000 : ℝ)*X 1 0+(1546269813/5000000000 : ℝ)*X 1 1+(-23741671/2500000000 : ℝ)*X 1 2+(1659485937/2000000000 : ℝ)*X 2 0+(1546269813/5000000000 : ℝ)*X 2 1+(-23741671/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306062_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((9443/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9443/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (5653716173089735059447349167381/817472807036900000000000000000000000 : ℝ) := by norm_num
    linear_combination (2953206273/4000000000 : ℝ)*(base7) + (561051/1000000000000 : ℝ)*(base49) + (14613795301/1000000000000 : ℝ)*(base60) + (2309662106323/1000000000000 : ℝ)*(major_s2_0) + (2309662106323/1000000000000 : ℝ)*(major_s2_1) + (2309662106323/1000000000000 : ℝ)*(major_s2_2) + (7356199/500000000000 : ℝ)*(sp_s2_0) + (8070811/1000000000000 : ℝ)*(sp_s2_1) + (2663557185521/1000000000000 : ℝ)*(sp_s2_7) + (332950889173/125000000000 : ℝ)*(sp_s2_8) + (1331809175299/500000000000 : ℝ)*(sp_s2_9) + (2236272918647/1000000000000 : ℝ)*(sp_s2_13) + (46452679/1000000000000 : ℝ)*(sp_s2_14) + (1583201/500000000000 : ℝ)*(sp_s2_15) + (1497971350397/1000000000000 : ℝ)*(f.failure) + (1331809175299/500000000000 : ℝ)*(f.sum) + (6518775509665421711/28195523300000000000000000000000 : ℝ)*base63 + (145233809776567/651400000000000000000000000 : ℝ)*base65 + (21768043391417/618350000000000000000000000 : ℝ)*base66 + (251455658729911/325700000000000000000000000 : ℝ)*base69 + (26534408990508683/18886040200000000000000000000000 : ℝ)*base71 + (6659260639628497/8697900000000000000000000000 : ℝ)*base72 + (1429788792562743/4328450000000000000000000000 : ℝ)*base75 + (73442054361921/362412500000000000000000000 : ℝ)*base77 + (1717690072256125243/21513385860000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (5921/50000000000000000 : ℝ)*base87 + (5921/50000000000000000 : ℝ)*base89 + (5921/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(75537/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(75537/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (96832618948295440273558530370989/8992200877405900000000000000000000000 : ℝ) := by norm_num
    linear_combination (741594643773/1000000000000 : ℝ)*(base7) + (90929/500000000000 : ℝ)*(base40) + (631141/1000000000000 : ℝ)*(base59) + (2268642616687/1000000000000 : ℝ)*(major_s2_0) + (2268642616687/1000000000000 : ℝ)*(major_s2_1) + (2268642616687/1000000000000 : ℝ)*(major_s2_2) + (83889/31250000000 : ℝ)*(sp_s2_0) + (109661/100000000000 : ℝ)*(sp_s2_2) + (89186953/1000000000000 : ℝ)*(sp_s2_8) + (130306883101/50000000000 : ℝ)*(sp_s2_14) + (521210231903/200000000000 : ℝ)*(sp_s2_15) + (1303069624929/500000000000 : ℝ)*(sp_s2_16) + (138308953683/62500000000 : ℝ)*(sp_s2_20) + (18834993/1000000000000 : ℝ)*(sp_s2_27) + (1471367450149/1000000000000 : ℝ)*(f.failure) + (651535086617/250000000000 : ℝ)*(f.sum) + (157214229134225543039/310150756300000000000000000000000 : ℝ)*base63 + (5982735222783813/7165400000000000000000000000 : ℝ)*base65 + (158357703593013/618350000000000000000000000 : ℝ)*base66 + (2834415241476059/3582700000000000000000000000 : ℝ)*base69 + (96261283254948044137/207746442200000000000000000000000 : ℝ)*base71 + (1694590578801523/8697900000000000000000000000 : ℝ)*base72 + (195207833405957/270528125000000000000000000 : ℝ)*base75 + (392090794812503/724825000000000000000000000 : ℝ)*base77 + (3089093380303827541/21513385860000000000000000000000 : ℝ)*base79 + (13143/50000000000000000 : ℝ)*base86 + (13143/50000000000000000 : ℝ)*base88 + (13143/50000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-29307/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-29307/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (439925942747484225726740887749/35968803509623600000000000000000000 : ℝ) := by norm_num
    linear_combination (10881342533/25000000000 : ℝ)*(base7) + (20188711/1000000000000 : ℝ)*(base11) + (91210463399/1000000000000 : ℝ)*(base39) + (260767/1000000000000 : ℝ)*(base59) + (1091179798287/500000000000 : ℝ)*(major_s2_0) + (1091179798287/500000000000 : ℝ)*(major_s2_1) + (1091179798287/500000000000 : ℝ)*(major_s2_2) + (8095289/250000000000 : ℝ)*(sp_s2_0) + (22138171/100000000000 : ℝ)*(sp_s2_9) + (4892931/500000000000 : ℝ)*(sp_s2_20) + (334925856641/125000000000 : ℝ)*(sp_s2_21) + (535891884599/200000000000 : ℝ)*(sp_s2_22) + (669809510321/250000000000 : ℝ)*(sp_s2_23) + (92532550947/50000000000 : ℝ)*(sp_s2_27) + (707703551741/500000000000 : ℝ)*(f.failure) + (535891884599/200000000000 : ℝ)*(f.sum) + (47087156967541311081/155075378150000000000000000000000 : ℝ)*base62 + (2186939183715507/3582700000000000000000000000 : ℝ)*base64 + (169546108080197/309175000000000000000000000 : ℝ)*base67 + (1221424984796941/1791350000000000000000000000 : ℝ)*base68 + (47669827644082164573/103873221100000000000000000000000 : ℝ)*base70 + (259792194845697/724825000000000000000000000 : ℝ)*base73 + (569584799147563/2164225000000000000000000000 : ℝ)*base74 + (129749293546861/724825000000000000000000000 : ℝ)*base77 + (620152410410662863/3585564310000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (18913/25000000000000000 : ℝ)*base87 + (18913/25000000000000000 : ℝ)*base89 + (18913/25000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev1 : (0 : ℝ) ≤ ((86979/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(86979/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(86569/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(86569/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-35827/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-35827/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((9443/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9443/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(75537/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(75537/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-29307/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-29307/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c306062_s2 p hpa hpb X hX hprev1

#print axioms solution
