-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c306086_s0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:01:00.697365+00:00
-- url     : https://prove2.me/submissions/d9f2233a-af74-4b6c-8ec1-169214ee2fe4

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
theorem collision_support_c306086_s0_s0_1 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (6596266659/10000000000 : ℝ)*x 0 + (3110692947/10000000000 : ℝ)*x 1 + (2972873051/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6596266659/10000000000 : ℝ)^135 ≤ (28981966127607/50000000000000 : ℝ)^103 := by
    have hnat : (6596266659 : ℕ)^135*50000000000000^103 ≤ 28981966127607^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6596266659 10000000000 28981966127607 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3110692947/10000000000 : ℝ)^135 ≤ (676313755791/3125000000000 : ℝ)^103 := by
    have hnat : (3110692947 : ℕ)^135*3125000000000^103 ≤ 676313755791^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3110692947 10000000000 676313755791 3125000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2972873051/10000000000 : ℝ)^135 ≤ (10197013773023/50000000000000 : ℝ)^103 := by
    have hnat : (2972873051 : ℕ)^135*50000000000000^103 ≤ 10197013773023^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2972873051 10000000000 10197013773023 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6596266659/10000000000 : ℝ), (3110692947/10000000000 : ℝ), (2972873051/10000000000 : ℝ)] ![(28981966127607/50000000000000 : ℝ), (676313755791/3125000000000 : ℝ), (10197013773023/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6596266659/10000000000 : ℝ)|^135 ≤ (28981966127607/50000000000000 : ℝ)^103
        have hw : |(6596266659/10000000000 : ℝ)|=(6596266659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3110692947/10000000000 : ℝ)|^135 ≤ (676313755791/3125000000000 : ℝ)^103
        have hw : |(3110692947/10000000000 : ℝ)|=(3110692947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2972873051/10000000000 : ℝ)|^135 ≤ (10197013773023/50000000000000 : ℝ)^103
        have hw : |(2972873051/10000000000 : ℝ)|=(2972873051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306086_s0_s0_2 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (6146903293/10000000000 : ℝ)*x 0 + (-1737728541/5000000000 : ℝ)*x 1 + (-3163915579/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6146903293/10000000000 : ℝ)^135 ≤ (13211016520231/25000000000000 : ℝ)^103 := by
    have hnat : (6146903293 : ℕ)^135*25000000000000^103 ≤ 13211016520231^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6146903293 10000000000 13211016520231 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1737728541/5000000000 : ℝ)^135 ≤ (6256820605059/25000000000000 : ℝ)^103 := by
    have hnat : (1737728541 : ℕ)^135*25000000000000^103 ≤ 6256820605059^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1737728541 5000000000 6256820605059 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3163915579/10000000000 : ℝ)^135 ≤ (2212865148389/10000000000000 : ℝ)^103 := by
    have hnat : (3163915579 : ℕ)^135*10000000000000^103 ≤ 2212865148389^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3163915579 10000000000 2212865148389 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6146903293/10000000000 : ℝ), (-1737728541/5000000000 : ℝ), (-3163915579/10000000000 : ℝ)] ![(13211016520231/25000000000000 : ℝ), (6256820605059/25000000000000 : ℝ), (2212865148389/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6146903293/10000000000 : ℝ)|^135 ≤ (13211016520231/25000000000000 : ℝ)^103
        have hw : |(6146903293/10000000000 : ℝ)|=(6146903293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1737728541/5000000000 : ℝ)|^135 ≤ (6256820605059/25000000000000 : ℝ)^103
        have hw : |(-1737728541/5000000000 : ℝ)|=(1737728541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3163915579/10000000000 : ℝ)|^135 ≤ (2212865148389/10000000000000 : ℝ)^103
        have hw : |(-3163915579/10000000000 : ℝ)|=(3163915579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306086_s0_s0_6 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3639860631/10000000000 : ℝ)*x 0 + (-560043933/2500000000 : ℝ)*x 1 + (6715012727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3639860631/10000000000 : ℝ)^135 ≤ (3323783672653/12500000000000 : ℝ)^103 := by
    have hnat : (3639860631 : ℕ)^135*12500000000000^103 ≤ 3323783672653^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3639860631 10000000000 3323783672653 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (560043933/2500000000 : ℝ)^135 ≤ (14074338100511/100000000000000 : ℝ)^103 := by
    have hnat : (560043933 : ℕ)^135*100000000000000^103 ≤ 14074338100511^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560043933 2500000000 14074338100511 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6715012727/10000000000 : ℝ)^135 ≤ (29667696252787/50000000000000 : ℝ)^103 := by
    have hnat : (6715012727 : ℕ)^135*50000000000000^103 ≤ 29667696252787^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6715012727 10000000000 29667696252787 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3639860631/10000000000 : ℝ), (-560043933/2500000000 : ℝ), (6715012727/10000000000 : ℝ)] ![(3323783672653/12500000000000 : ℝ), (14074338100511/100000000000000 : ℝ), (29667696252787/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3639860631/10000000000 : ℝ)|^135 ≤ (3323783672653/12500000000000 : ℝ)^103
        have hw : |(3639860631/10000000000 : ℝ)|=(3639860631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-560043933/2500000000 : ℝ)|^135 ≤ (14074338100511/100000000000000 : ℝ)^103
        have hw : |(-560043933/2500000000 : ℝ)|=(560043933/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6715012727/10000000000 : ℝ)|^135 ≤ (29667696252787/50000000000000 : ℝ)^103
        have hw : |(6715012727/10000000000 : ℝ)|=(6715012727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306086_s0_s0_7 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (10039049/625000000 : ℝ)*x 0 + (-8597606989/10000000000 : ℝ)*x 1 + (264774711/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10039049/625000000 : ℝ)^135 ≤ (222517976963/50000000000000 : ℝ)^103 := by
    have hnat : (10039049 : ℕ)^135*50000000000000^103 ≤ 222517976963^103*625000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10039049 625000000 222517976963 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8597606989/10000000000 : ℝ)^135 ≤ (82033273782473/100000000000000 : ℝ)^103 := by
    have hnat : (8597606989 : ℕ)^135*100000000000000^103 ≤ 82033273782473^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8597606989 10000000000 82033273782473 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (264774711/1000000000 : ℝ)^135 ≤ (2190211281697/12500000000000 : ℝ)^103 := by
    have hnat : (264774711 : ℕ)^135*12500000000000^103 ≤ 2190211281697^103*1000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264774711 1000000000 2190211281697 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(10039049/625000000 : ℝ), (-8597606989/10000000000 : ℝ), (264774711/1000000000 : ℝ)] ![(222517976963/50000000000000 : ℝ), (82033273782473/100000000000000 : ℝ), (2190211281697/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(10039049/625000000 : ℝ)|^135 ≤ (222517976963/50000000000000 : ℝ)^103
        have hw : |(10039049/625000000 : ℝ)|=(10039049/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-8597606989/10000000000 : ℝ)|^135 ≤ (82033273782473/100000000000000 : ℝ)^103
        have hw : |(-8597606989/10000000000 : ℝ)|=(8597606989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(264774711/1000000000 : ℝ)|^135 ≤ (2190211281697/12500000000000 : ℝ)^103
        have hw : |(264774711/1000000000 : ℝ)|=(264774711/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306086_s0_s0_8 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1558530581/5000000000 : ℝ)*x 0 + (908546519/1250000000 : ℝ)*x 1 + (2043235873/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1558530581/5000000000 : ℝ)^135 ≤ (21700129110349/100000000000000 : ℝ)^103 := by
    have hnat : (1558530581 : ℕ)^135*100000000000000^103 ≤ 21700129110349^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1558530581 5000000000 21700129110349 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (908546519/1250000000 : ℝ)^135 ≤ (13164928379779/20000000000000 : ℝ)^103 := by
    have hnat : (908546519 : ℕ)^135*20000000000000^103 ≤ 13164928379779^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      908546519 1250000000 13164928379779 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2043235873/10000000000 : ℝ)^135 ≤ (1559403622721/12500000000000 : ℝ)^103 := by
    have hnat : (2043235873 : ℕ)^135*12500000000000^103 ≤ 1559403622721^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2043235873 10000000000 1559403622721 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1558530581/5000000000 : ℝ), (908546519/1250000000 : ℝ), (2043235873/10000000000 : ℝ)] ![(21700129110349/100000000000000 : ℝ), (13164928379779/20000000000000 : ℝ), (1559403622721/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1558530581/5000000000 : ℝ)|^135 ≤ (21700129110349/100000000000000 : ℝ)^103
        have hw : |(1558530581/5000000000 : ℝ)|=(1558530581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(908546519/1250000000 : ℝ)|^135 ≤ (13164928379779/20000000000000 : ℝ)^103
        have hw : |(908546519/1250000000 : ℝ)|=(908546519/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2043235873/10000000000 : ℝ)|^135 ≤ (1559403622721/12500000000000 : ℝ)^103
        have hw : |(2043235873/10000000000 : ℝ)|=(2043235873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306086_s0_s0_9 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4889622517/5000000000 : ℝ)*x 0 + (-8000201/5000000000 : ℝ)*x 1 + (-332230013/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4889622517/5000000000 : ℝ)^135 ≤ (48558291247869/50000000000000 : ℝ)^103 := by
    have hnat : (4889622517 : ℕ)^135*50000000000000^103 ≤ 48558291247869^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4889622517 5000000000 48558291247869 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8000201/5000000000 : ℝ)^135 ≤ (21652665469/100000000000000 : ℝ)^103 := by
    have hnat : (8000201 : ℕ)^135*100000000000000^103 ≤ 21652665469^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8000201 5000000000 21652665469 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (332230013/5000000000 : ℝ)^135 ≤ (1430882412211/50000000000000 : ℝ)^103 := by
    have hnat : (332230013 : ℕ)^135*50000000000000^103 ≤ 1430882412211^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332230013 5000000000 1430882412211 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4889622517/5000000000 : ℝ), (-8000201/5000000000 : ℝ), (-332230013/5000000000 : ℝ)] ![(48558291247869/50000000000000 : ℝ), (21652665469/100000000000000 : ℝ), (1430882412211/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4889622517/5000000000 : ℝ)|^135 ≤ (48558291247869/50000000000000 : ℝ)^103
        have hw : |(4889622517/5000000000 : ℝ)|=(4889622517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-8000201/5000000000 : ℝ)|^135 ≤ (21652665469/100000000000000 : ℝ)^103
        have hw : |(-8000201/5000000000 : ℝ)|=(8000201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-332230013/5000000000 : ℝ)|^135 ≤ (1430882412211/50000000000000 : ℝ)^103
        have hw : |(-332230013/5000000000 : ℝ)|=(332230013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306086_s0_s0_13 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (153221309/400000000 : ℝ)*x 0 + (-662669031/5000000000 : ℝ)*x 1 + (3578067531/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (153221309/400000000 : ℝ)^135 ≤ (14215308992959/50000000000000 : ℝ)^103 := by
    have hnat : (153221309 : ℕ)^135*50000000000000^103 ≤ 14215308992959^103*400000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      153221309 400000000 14215308992959 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (662669031/5000000000 : ℝ)^135 ≤ (3536889287987/50000000000000 : ℝ)^103 := by
    have hnat : (662669031 : ℕ)^135*50000000000000^103 ≤ 3536889287987^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      662669031 5000000000 3536889287987 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3578067531/5000000000 : ℝ)^135 ≤ (64495603424527/100000000000000 : ℝ)^103 := by
    have hnat : (3578067531 : ℕ)^135*100000000000000^103 ≤ 64495603424527^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3578067531 5000000000 64495603424527 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(153221309/400000000 : ℝ), (-662669031/5000000000 : ℝ), (3578067531/5000000000 : ℝ)] ![(14215308992959/50000000000000 : ℝ), (3536889287987/50000000000000 : ℝ), (64495603424527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(153221309/400000000 : ℝ)|^135 ≤ (14215308992959/50000000000000 : ℝ)^103
        have hw : |(153221309/400000000 : ℝ)|=(153221309/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-662669031/5000000000 : ℝ)|^135 ≤ (3536889287987/50000000000000 : ℝ)^103
        have hw : |(-662669031/5000000000 : ℝ)|=(662669031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3578067531/5000000000 : ℝ)|^135 ≤ (64495603424527/100000000000000 : ℝ)^103
        have hw : |(3578067531/5000000000 : ℝ)|=(3578067531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306086_s0_s0_14 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (241709/10000000000 : ℝ)*x 0 + (-702699477/2000000000 : ℝ)*x 1 + (1999411089/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (241709/10000000000 : ℝ)^135 ≤ (22228801/25000000000000 : ℝ)^103 := by
    have hnat : (241709 : ℕ)^135*25000000000000^103 ≤ 22228801^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      241709 10000000000 22228801 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (702699477/2000000000 : ℝ)^135 ≤ (25386930889419/100000000000000 : ℝ)^103 := by
    have hnat : (702699477 : ℕ)^135*100000000000000^103 ≤ 25386930889419^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      702699477 2000000000 25386930889419 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1999411089/2500000000 : ℝ)^135 ≤ (74612980182403/100000000000000 : ℝ)^103 := by
    have hnat : (1999411089 : ℕ)^135*100000000000000^103 ≤ 74612980182403^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1999411089 2500000000 74612980182403 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(241709/10000000000 : ℝ), (-702699477/2000000000 : ℝ), (1999411089/2500000000 : ℝ)] ![(22228801/25000000000000 : ℝ), (25386930889419/100000000000000 : ℝ), (74612980182403/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(241709/10000000000 : ℝ)|^135 ≤ (22228801/25000000000000 : ℝ)^103
        have hw : |(241709/10000000000 : ℝ)|=(241709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-702699477/2000000000 : ℝ)|^135 ≤ (25386930889419/100000000000000 : ℝ)^103
        have hw : |(-702699477/2000000000 : ℝ)|=(702699477/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1999411089/2500000000 : ℝ)|^135 ≤ (74612980182403/100000000000000 : ℝ)^103
        have hw : |(1999411089/2500000000 : ℝ)|=(1999411089/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306086_s0_s0_15 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (8515037829/10000000000 : ℝ)*x 0 + (2664949993/10000000000 : ℝ)*x 1 + (11550479/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8515037829/10000000000 : ℝ)^135 ≤ (81002230149911/100000000000000 : ℝ)^103 := by
    have hnat : (8515037829 : ℕ)^135*100000000000000^103 ≤ 81002230149911^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8515037829 10000000000 81002230149911 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2664949993/10000000000 : ℝ)^135 ≤ (883552519867/5000000000000 : ℝ)^103 := by
    have hnat : (2664949993 : ℕ)^135*5000000000000^103 ≤ 883552519867^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2664949993 10000000000 883552519867 5000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (11550479/312500000 : ℝ)^135 ≤ (1326719434777/100000000000000 : ℝ)^103 := by
    have hnat : (11550479 : ℕ)^135*100000000000000^103 ≤ 1326719434777^103*312500000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11550479 312500000 1326719434777 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8515037829/10000000000 : ℝ), (2664949993/10000000000 : ℝ), (11550479/312500000 : ℝ)] ![(81002230149911/100000000000000 : ℝ), (883552519867/5000000000000 : ℝ), (1326719434777/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8515037829/10000000000 : ℝ)|^135 ≤ (81002230149911/100000000000000 : ℝ)^103
        have hw : |(8515037829/10000000000 : ℝ)|=(8515037829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2664949993/10000000000 : ℝ)|^135 ≤ (883552519867/5000000000000 : ℝ)^103
        have hw : |(2664949993/10000000000 : ℝ)|=(2664949993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(11550479/312500000 : ℝ)|^135 ≤ (1326719434777/100000000000000 : ℝ)^103
        have hw : |(11550479/312500000 : ℝ)|=(11550479/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306086_s0_s0_16 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (317669579/400000000 : ℝ)*x 0 + (-1991546263/10000000000 : ℝ)*x 1 + (-89278061/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (317669579/400000000 : ℝ)^135 ≤ (462063307149/625000000000 : ℝ)^103 := by
    have hnat : (317669579 : ℕ)^135*625000000000^103 ≤ 462063307149^103*400000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      317669579 400000000 462063307149 625000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1991546263/10000000000 : ℝ)^135 ≤ (12063217127787/100000000000000 : ℝ)^103 := by
    have hnat : (1991546263 : ℕ)^135*100000000000000^103 ≤ 12063217127787^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1991546263 10000000000 12063217127787 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (89278061/400000000 : ℝ)^135 ≤ (14006653711193/100000000000000 : ℝ)^103 := by
    have hnat : (89278061 : ℕ)^135*100000000000000^103 ≤ 14006653711193^103*400000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89278061 400000000 14006653711193 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(317669579/400000000 : ℝ), (-1991546263/10000000000 : ℝ), (-89278061/400000000 : ℝ)] ![(462063307149/625000000000 : ℝ), (12063217127787/100000000000000 : ℝ), (14006653711193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(317669579/400000000 : ℝ)|^135 ≤ (462063307149/625000000000 : ℝ)^103
        have hw : |(317669579/400000000 : ℝ)|=(317669579/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1991546263/10000000000 : ℝ)|^135 ≤ (12063217127787/100000000000000 : ℝ)^103
        have hw : |(-1991546263/10000000000 : ℝ)|=(1991546263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-89278061/400000000 : ℝ)|^135 ≤ (14006653711193/100000000000000 : ℝ)^103
        have hw : |(-89278061/400000000 : ℝ)|=(89278061/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306086_s0_s0_20 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (594371551/2500000000 : ℝ)*x 0 + (-650976287/5000000000 : ℝ)*x 1 + (8262952643/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (594371551/2500000000 : ℝ)^135 ≤ (950978300067/6250000000000 : ℝ)^103 := by
    have hnat : (594371551 : ℕ)^135*6250000000000^103 ≤ 950978300067^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      594371551 2500000000 950978300067 6250000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (650976287/5000000000 : ℝ)^135 ≤ (6910634661691/100000000000000 : ℝ)^103 := by
    have hnat : (650976287 : ℕ)^135*100000000000000^103 ≤ 6910634661691^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      650976287 5000000000 6910634661691 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8262952643/10000000000 : ℝ)^135 ≤ (77873712530339/100000000000000 : ℝ)^103 := by
    have hnat : (8262952643 : ℕ)^135*100000000000000^103 ≤ 77873712530339^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8262952643 10000000000 77873712530339 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(594371551/2500000000 : ℝ), (-650976287/5000000000 : ℝ), (8262952643/10000000000 : ℝ)] ![(950978300067/6250000000000 : ℝ), (6910634661691/100000000000000 : ℝ), (77873712530339/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(594371551/2500000000 : ℝ)|^135 ≤ (950978300067/6250000000000 : ℝ)^103
        have hw : |(594371551/2500000000 : ℝ)|=(594371551/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-650976287/5000000000 : ℝ)|^135 ≤ (6910634661691/100000000000000 : ℝ)^103
        have hw : |(-650976287/5000000000 : ℝ)|=(650976287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8262952643/10000000000 : ℝ)|^135 ≤ (77873712530339/100000000000000 : ℝ)^103
        have hw : |(8262952643/10000000000 : ℝ)|=(8262952643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306086_s0_s0_21 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5803641/1250000000 : ℝ)*x 0 + (-8831601819/10000000000 : ℝ)*x 1 + (2344633987/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5803641/1250000000 : ℝ)^135 ≤ (21870057399/25000000000000 : ℝ)^103 := by
    have hnat : (5803641 : ℕ)^135*25000000000000^103 ≤ 21870057399^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5803641 1250000000 21870057399 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8831601819/10000000000 : ℝ)^135 ≤ (1699436894961/2000000000000 : ℝ)^103 := by
    have hnat : (8831601819 : ℕ)^135*2000000000000^103 ≤ 1699436894961^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8831601819 10000000000 1699436894961 2000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2344633987/10000000000 : ℝ)^135 ≤ (14940675012253/100000000000000 : ℝ)^103 := by
    have hnat : (2344633987 : ℕ)^135*100000000000000^103 ≤ 14940675012253^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2344633987 10000000000 14940675012253 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5803641/1250000000 : ℝ), (-8831601819/10000000000 : ℝ), (2344633987/10000000000 : ℝ)] ![(21870057399/25000000000000 : ℝ), (1699436894961/2000000000000 : ℝ), (14940675012253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5803641/1250000000 : ℝ)|^135 ≤ (21870057399/25000000000000 : ℝ)^103
        have hw : |(5803641/1250000000 : ℝ)|=(5803641/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-8831601819/10000000000 : ℝ)|^135 ≤ (1699436894961/2000000000000 : ℝ)^103
        have hw : |(-8831601819/10000000000 : ℝ)|=(8831601819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2344633987/10000000000 : ℝ)|^135 ≤ (14940675012253/100000000000000 : ℝ)^103
        have hw : |(2344633987/10000000000 : ℝ)|=(2344633987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306086_s0_s0_22 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1103719329/1250000000 : ℝ)*x 0 + (328122987/2500000000 : ℝ)*x 1 + (1465136917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1103719329/1250000000 : ℝ)^135 ≤ (21237137890941/25000000000000 : ℝ)^103 := by
    have hnat : (1103719329 : ℕ)^135*25000000000000^103 ≤ 21237137890941^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103719329 1250000000 21237137890941 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (328122987/2500000000 : ℝ)^135 ≤ (3492024331367/50000000000000 : ℝ)^103 := by
    have hnat : (328122987 : ℕ)^135*50000000000000^103 ≤ 3492024331367^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328122987 2500000000 3492024331367 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1465136917/10000000000 : ℝ)^135 ≤ (806739976327/10000000000000 : ℝ)^103 := by
    have hnat : (1465136917 : ℕ)^135*10000000000000^103 ≤ 806739976327^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1465136917 10000000000 806739976327 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1103719329/1250000000 : ℝ), (328122987/2500000000 : ℝ), (1465136917/10000000000 : ℝ)] ![(21237137890941/25000000000000 : ℝ), (3492024331367/50000000000000 : ℝ), (806739976327/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1103719329/1250000000 : ℝ)|^135 ≤ (21237137890941/25000000000000 : ℝ)^103
        have hw : |(1103719329/1250000000 : ℝ)|=(1103719329/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(328122987/2500000000 : ℝ)|^135 ≤ (3492024331367/50000000000000 : ℝ)^103
        have hw : |(328122987/2500000000 : ℝ)|=(328122987/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1465136917/10000000000 : ℝ)|^135 ≤ (806739976327/10000000000000 : ℝ)^103
        have hw : |(1465136917/10000000000 : ℝ)|=(1465136917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306086_s0_s0_23 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1530386781/5000000000 : ℝ)*x 0 + (-54087467/250000000 : ℝ)*x 1 + (-361483827/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1530386781/5000000000 : ℝ)^135 ≤ (21187974360641/100000000000000 : ℝ)^103 := by
    have hnat : (1530386781 : ℕ)^135*100000000000000^103 ≤ 21187974360641^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1530386781 5000000000 21187974360641 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (54087467/250000000 : ℝ)^135 ≤ (6723158660193/50000000000000 : ℝ)^103 := by
    have hnat : (54087467 : ℕ)^135*50000000000000^103 ≤ 6723158660193^103*250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54087467 250000000 6723158660193 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (361483827/500000000 : ℝ)^135 ≤ (4085356768311/6250000000000 : ℝ)^103 := by
    have hnat : (361483827 : ℕ)^135*6250000000000^103 ≤ 4085356768311^103*500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      361483827 500000000 4085356768311 6250000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1530386781/5000000000 : ℝ), (-54087467/250000000 : ℝ), (-361483827/500000000 : ℝ)] ![(21187974360641/100000000000000 : ℝ), (6723158660193/50000000000000 : ℝ), (4085356768311/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1530386781/5000000000 : ℝ)|^135 ≤ (21187974360641/100000000000000 : ℝ)^103
        have hw : |(1530386781/5000000000 : ℝ)|=(1530386781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-54087467/250000000 : ℝ)|^135 ≤ (6723158660193/50000000000000 : ℝ)^103
        have hw : |(-54087467/250000000 : ℝ)|=(54087467/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-361483827/500000000 : ℝ)|^135 ≤ (4085356768311/6250000000000 : ℝ)^103
        have hw : |(-361483827/500000000 : ℝ)|=(361483827/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306086_s0_s0_27 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (7783668517/10000000000 : ℝ)*x 0 + (-397703663/5000000000 : ℝ)*x 1 + (425698441/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7783668517/10000000000 : ℝ)^135 ≤ (14401493033357/20000000000000 : ℝ)^103 := by
    have hnat : (7783668517 : ℕ)^135*20000000000000^103 ≤ 14401493033357^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7783668517 10000000000 14401493033357 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (397703663/5000000000 : ℝ)^135 ≤ (1811320034547/50000000000000 : ℝ)^103 := by
    have hnat : (397703663 : ℕ)^135*50000000000000^103 ≤ 1811320034547^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397703663 5000000000 1811320034547 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (425698441/1250000000 : ℝ)^135 ≤ (12184947372079/50000000000000 : ℝ)^103 := by
    have hnat : (425698441 : ℕ)^135*50000000000000^103 ≤ 12184947372079^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425698441 1250000000 12184947372079 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7783668517/10000000000 : ℝ), (-397703663/5000000000 : ℝ), (425698441/1250000000 : ℝ)] ![(14401493033357/20000000000000 : ℝ), (1811320034547/50000000000000 : ℝ), (12184947372079/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7783668517/10000000000 : ℝ)|^135 ≤ (14401493033357/20000000000000 : ℝ)^103
        have hw : |(7783668517/10000000000 : ℝ)|=(7783668517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-397703663/5000000000 : ℝ)|^135 ≤ (1811320034547/50000000000000 : ℝ)^103
        have hw : |(-397703663/5000000000 : ℝ)|=(397703663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(425698441/1250000000 : ℝ)|^135 ≤ (12184947372079/50000000000000 : ℝ)^103
        have hw : |(425698441/1250000000 : ℝ)|=(425698441/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c306086_s0 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]]) : (0 : ℝ) ≤ ((90383/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(90383/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-5951/6250 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-5951/6250 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(94049/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(94049/100000 : ℝ)*X 1 2) := by
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
  have main1 : (38461/50000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (38461/50000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (38461/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (38461/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base7 : ((1 : ℝ)*T) ≤ (92997/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base54 : ((-1 : ℝ)*N 2+(1 : ℝ)*P 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 2]
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
  have s0_pow0 : (1 : ℝ) ^ (67/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^67 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^67*1^16 ≤ 1^16*1^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (2360031261787197/2000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2360031261787197/2000000000000000 : ℝ)^67 := by
      have hnat : (2 : ℕ)^16*2000000000000000^67 ≤ 2360031261787197^67*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2360031261787197 2000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2360031261787197/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12999881816832461/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12999881816832461/10000000000000000 : ℝ)^67 := by
      have hnat : (3 : ℕ)^16*10000000000000000^67 ≤ 12999881816832461^67*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12999881816832461 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12999881816832461/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(360031261787197/2000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(299931376974119/2500000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (360031261787197/2000000000000000 : ℝ)) (beta := (299931376974119/2500000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(360031261787197/2000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(299931376974119/2500000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (67/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^67 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^67*1^16 ≤ 1^16*1^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (2360031261787197/2000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2360031261787197/2000000000000000 : ℝ)^67 := by
      have hnat : (2 : ℕ)^16*2000000000000000^67 ≤ 2360031261787197^67*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2360031261787197 2000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2360031261787197/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12999881816832461/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12999881816832461/10000000000000000 : ℝ)^67 := by
      have hnat : (3 : ℕ)^16*10000000000000000^67 ≤ 12999881816832461^67*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12999881816832461 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12999881816832461/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(360031261787197/2000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(299931376974119/2500000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (360031261787197/2000000000000000 : ℝ)) (beta := (299931376974119/2500000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(360031261787197/2000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(299931376974119/2500000000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (67/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^67 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^67*1^16 ≤ 1^16*1^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (2360031261787197/2000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2360031261787197/2000000000000000 : ℝ)^67 := by
      have hnat : (2 : ℕ)^16*2000000000000000^67 ≤ 2360031261787197^67*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2360031261787197 2000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2360031261787197/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12999881816832461/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12999881816832461/10000000000000000 : ℝ)^67 := by
      have hnat : (3 : ℕ)^16*10000000000000000^67 ≤ 12999881816832461^67*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12999881816832461 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12999881816832461/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(360031261787197/2000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(299931376974119/2500000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (360031261787197/2000000000000000 : ℝ)) (beta := (299931376974119/2500000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(360031261787197/2000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(299931376974119/2500000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((6596266659/10000000000 : ℝ)*X 1 0+(3110692947/10000000000 : ℝ)*X 1 1+(2972873051/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306086_s0_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((6146903293/10000000000 : ℝ)*X 2 0+(-1737728541/5000000000 : ℝ)*X 2 1+(-3163915579/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306086_s0_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((3639860631/10000000000 : ℝ)*X 0 0+(-560043933/2500000000 : ℝ)*X 0 1+(6715012727/10000000000 : ℝ)*X 0 2+(3639860631/10000000000 : ℝ)*X 1 0+(-560043933/2500000000 : ℝ)*X 1 1+(6715012727/10000000000 : ℝ)*X 1 2+(3639860631/10000000000 : ℝ)*X 2 0+(-560043933/2500000000 : ℝ)*X 2 1+(6715012727/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306086_s0_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((10039049/625000000 : ℝ)*X 0 0+(-8597606989/10000000000 : ℝ)*X 0 1+(264774711/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306086_s0_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((1558530581/5000000000 : ℝ)*X 1 0+(908546519/1250000000 : ℝ)*X 1 1+(2043235873/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306086_s0_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((4889622517/5000000000 : ℝ)*X 2 0+(-8000201/5000000000 : ℝ)*X 2 1+(-332230013/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306086_s0_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((153221309/400000000 : ℝ)*X 0 0+(-662669031/5000000000 : ℝ)*X 0 1+(3578067531/5000000000 : ℝ)*X 0 2+(153221309/400000000 : ℝ)*X 1 0+(-662669031/5000000000 : ℝ)*X 1 1+(3578067531/5000000000 : ℝ)*X 1 2+(153221309/400000000 : ℝ)*X 2 0+(-662669031/5000000000 : ℝ)*X 2 1+(3578067531/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306086_s0_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((241709/10000000000 : ℝ)*X 0 0+(-702699477/2000000000 : ℝ)*X 0 1+(1999411089/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306086_s0_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((8515037829/10000000000 : ℝ)*X 1 0+(2664949993/10000000000 : ℝ)*X 1 1+(11550479/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306086_s0_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((317669579/400000000 : ℝ)*X 2 0+(-1991546263/10000000000 : ℝ)*X 2 1+(-89278061/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306086_s0_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((594371551/2500000000 : ℝ)*X 0 0+(-650976287/5000000000 : ℝ)*X 0 1+(8262952643/10000000000 : ℝ)*X 0 2+(594371551/2500000000 : ℝ)*X 1 0+(-650976287/5000000000 : ℝ)*X 1 1+(8262952643/10000000000 : ℝ)*X 1 2+(594371551/2500000000 : ℝ)*X 2 0+(-650976287/5000000000 : ℝ)*X 2 1+(8262952643/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306086_s0_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((5803641/1250000000 : ℝ)*X 0 0+(-8831601819/10000000000 : ℝ)*X 0 1+(2344633987/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306086_s0_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((1103719329/1250000000 : ℝ)*X 1 0+(328122987/2500000000 : ℝ)*X 1 1+(1465136917/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306086_s0_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((1530386781/5000000000 : ℝ)*X 2 0+(-54087467/250000000 : ℝ)*X 2 1+(-361483827/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306086_s0_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((7783668517/10000000000 : ℝ)*X 0 0+(-397703663/5000000000 : ℝ)*X 0 1+(425698441/1250000000 : ℝ)*X 0 2+(7783668517/10000000000 : ℝ)*X 1 0+(-397703663/5000000000 : ℝ)*X 1 1+(425698441/1250000000 : ℝ)*X 1 2+(7783668517/10000000000 : ℝ)*X 2 0+(-397703663/5000000000 : ℝ)*X 2 1+(425698441/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306086_s0_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((90383/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(90383/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1562770684727286623667/200000000000000000000000000 : ℝ) := by norm_num
    linear_combination (26185734067/1000000000000 : ℝ)*(base1) + (303431331337/500000000000 : ℝ)*(base7) + (222350317993/1000000000000 : ℝ)*(base43) + (118289887043/125000000000 : ℝ)*(base54) + (800306421363/500000000000 : ℝ)*(major_s0_0) + (1378262524733/1000000000000 : ℝ)*(major_s0_1) + (654293746381/1000000000000 : ℝ)*(major_s0_2) + (11586359/200000000000 : ℝ)*(sp_s0_6) + (795355304927/500000000000 : ℝ)*(sp_s0_7) + (89343759689/50000000000 : ℝ)*(sp_s0_8) + (618161785737/1000000000000 : ℝ)*(sp_s0_9) + (336195541687/500000000000 : ℝ)*(sp_s0_13) + (8798741/200000000000 : ℝ)*(sp_s0_16) + (13990537/1000000000000 : ℝ)*(sp_s0_20) + (259526293361/250000000000 : ℝ)*(f.failure) + (89343759689/50000000000 : ℝ)*(f.sum) + (128956571038807/10000000000000000000000000000 : ℝ)*base62 + (331009693913339/2500000000000000000000000000 : ℝ)*base64 + (673552081556599/2000000000000000000000000000 : ℝ)*base66 + (267670570284057/2000000000000000000000000000 : ℝ)*base69 + (755947867379123/5000000000000000000000000000 : ℝ)*base70 + (537576563295803/1250000000000000000000000000 : ℝ)*base72 + (2070081619385227/2500000000000000000000000000 : ℝ)*base75 + (69514026189511/1000000000000000000000000000 : ℝ)*base77 + (1050528303149419/10000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (4573/12500000000000000 : ℝ)*base87 + (4573/12500000000000000 : ℝ)*base89 + (17073/12500000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-5951/6250 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-5951/6250 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (34746984742570107433881/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11987172131/12500000000 : ℝ)*(base7) + (73534161293/125000000000 : ℝ)*(base33) + (20955675337/500000000000 : ℝ)*(base54) + (959223142363/1000000000000 : ℝ)*(major_s0_0) + (1547496432707/1000000000000 : ℝ)*(major_s0_1) + (1505585082033/1000000000000 : ℝ)*(major_s0_2) + (10057767/500000000000 : ℝ)*(sp_s0_1) + (1821773/62500000000 : ℝ)*(sp_s0_2) + (2344297/200000000000 : ℝ)*(sp_s0_13) + (748395192347/500000000000 : ℝ)*(sp_s0_14) + (227121513633/250000000000 : ℝ)*(sp_s0_15) + (866576595309/1000000000000 : ℝ)*(sp_s0_16) + (960353152173/500000000000 : ℝ)*(sp_s0_20) + (2184857/200000000000 : ℝ)*(sp_s0_22) + (501827803013/500000000000 : ℝ)*(f.failure) + (748395192347/500000000000 : ℝ)*(f.sum) + (1585495372098037/10000000000000000000000000000 : ℝ)*base63 + (1592408466903927/2500000000000000000000000000 : ℝ)*base64 + (1613766742252279/2000000000000000000000000000 : ℝ)*base67 + (4003581531501/2000000000000000000000000000 : ℝ)*base69 + (1217824502983153/10000000000000000000000000000 : ℝ)*base70 + (930528797753197/2500000000000000000000000000 : ℝ)*base73 + (310532912110133/2500000000000000000000000000 : ℝ)*base75 + (686536034873489/2000000000000000000000000000 : ℝ)*base76 + (3458620886274183/10000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (6209/25000000000000000 : ℝ)*base87 + (6209/25000000000000000 : ℝ)*base89 + (6209/25000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(94049/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(94049/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (15384587978655306116907/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (174015020727/250000000000 : ℝ)*(base7) + (962731/500000000000 : ℝ)*(base24) + (162282969413/1000000000000 : ℝ)*(base33) + (1092289829401/1000000000000 : ℝ)*(base43) + (77277/125000000000 : ℝ)*(base59) + (710483055409/500000000000 : ℝ)*(major_s0_0) + (49095925083/100000000000 : ℝ)*(major_s0_1) + (1583249080231/1000000000000 : ℝ)*(major_s0_2) + (9113649/1000000000000 : ℝ)*(sp_s0_1) + (78910757/1000000000000 : ℝ)*(sp_s0_7) + (38483777137/62500000000 : ℝ)*(sp_s0_21) + (1545817091287/1000000000000 : ℝ)*(sp_s0_22) + (226767225037/500000000000 : ℝ)*(sp_s0_23) + (107681480471/62500000000 : ℝ)*(sp_s0_27) + (256710901157/250000000000 : ℝ)*(f.failure) + (1708109174349/1000000000000 : ℝ)*(f.sum) + (183521302182477/2000000000000000000000000000 : ℝ)*base62 + (2397952522708511/2500000000000000000000000000 : ℝ)*base65 + (23923335077649/200000000000000000000000000 : ℝ)*base66 + (513202664202507/2000000000000000000000000000 : ℝ)*base69 + (3201424334409887/5000000000000000000000000000 : ℝ)*base71 + (167935450209671/1250000000000000000000000000 : ℝ)*base73 + (34538538573123/250000000000000000000000000 : ℝ)*base74 + (142689623398573/1000000000000000000000000000 : ℝ)*base77 + (451446433897459/5000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base85 + (9101/12500000000000000 : ℝ)*base87 + (9101/12500000000000000 : ℝ)*base89 + (9101/12500000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]]) : (0 : ℝ) ≤ ((90383/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(90383/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-5951/6250 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-5951/6250 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(94049/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(94049/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c306086_s0 p hpa hpb X hX

#print axioms solution
