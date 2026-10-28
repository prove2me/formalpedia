-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c304061_s8
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:48:25.314169+00:00
-- url     : https://prove2.me/submissions/b6eb426b-6de7-4b14-8155-6ff4870151c7

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
theorem collision_support_c304061_s8_s8_0 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1328835873/5000000000 : ℝ)*x 0 + (2279767137/5000000000 : ℝ)*x 1 + (5634794331/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328835873/5000000000 : ℝ)^133 ≤ (17464860862813/100000000000000 : ℝ)^101 := by
    have hnat : (1328835873 : ℕ)^133*100000000000000^101 ≤ 17464860862813^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328835873 5000000000 17464860862813 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2279767137/5000000000 : ℝ)^133 ≤ (17775658249599/50000000000000 : ℝ)^101 := by
    have hnat : (2279767137 : ℕ)^133*50000000000000^101 ≤ 17775658249599^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2279767137 5000000000 17775658249599 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5634794331/10000000000 : ℝ)^133 ≤ (46983822626329/100000000000000 : ℝ)^101 := by
    have hnat : (5634794331 : ℕ)^133*100000000000000^101 ≤ 46983822626329^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5634794331 10000000000 46983822626329 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1328835873/5000000000 : ℝ), (2279767137/5000000000 : ℝ), (5634794331/10000000000 : ℝ)] ![(17464860862813/100000000000000 : ℝ), (17775658249599/50000000000000 : ℝ), (46983822626329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1328835873/5000000000 : ℝ)|^133 ≤ (17464860862813/100000000000000 : ℝ)^101
        have hw : |(-1328835873/5000000000 : ℝ)|=(1328835873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2279767137/5000000000 : ℝ)|^133 ≤ (17775658249599/50000000000000 : ℝ)^101
        have hw : |(2279767137/5000000000 : ℝ)|=(2279767137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5634794331/10000000000 : ℝ)|^133 ≤ (46983822626329/100000000000000 : ℝ)^101
        have hw : |(5634794331/10000000000 : ℝ)|=(5634794331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304061_s8_s8_1 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2355325881/5000000000 : ℝ)*x 0 + (-2698585133/10000000000 : ℝ)*x 1 + (1091910609/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2355325881/5000000000 : ℝ)^133 ≤ (37111003912019/100000000000000 : ℝ)^101 := by
    have hnat : (2355325881 : ℕ)^133*100000000000000^101 ≤ 37111003912019^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2355325881 5000000000 37111003912019 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2698585133/10000000000 : ℝ)^133 ≤ (17819767112271/100000000000000 : ℝ)^101 := by
    have hnat : (2698585133 : ℕ)^133*100000000000000^101 ≤ 17819767112271^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698585133 10000000000 17819767112271 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1091910609/2000000000 : ℝ)^133 ≤ (22534614484393/50000000000000 : ℝ)^101 := by
    have hnat : (1091910609 : ℕ)^133*50000000000000^101 ≤ 22534614484393^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091910609 2000000000 22534614484393 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2355325881/5000000000 : ℝ), (-2698585133/10000000000 : ℝ), (1091910609/2000000000 : ℝ)] ![(37111003912019/100000000000000 : ℝ), (17819767112271/100000000000000 : ℝ), (22534614484393/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2355325881/5000000000 : ℝ)|^133 ≤ (37111003912019/100000000000000 : ℝ)^101
        have hw : |(2355325881/5000000000 : ℝ)|=(2355325881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2698585133/10000000000 : ℝ)|^133 ≤ (17819767112271/100000000000000 : ℝ)^101
        have hw : |(-2698585133/10000000000 : ℝ)|=(2698585133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1091910609/2000000000 : ℝ)|^133 ≤ (22534614484393/50000000000000 : ℝ)^101
        have hw : |(1091910609/2000000000 : ℝ)|=(1091910609/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304061_s8_s8_2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1182895309/2500000000 : ℝ)*x 0 + (3014861531/5000000000 : ℝ)*x 1 + (-477498121/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1182895309/2500000000 : ℝ)^133 ≤ (7465656361201/20000000000000 : ℝ)^101 := by
    have hnat : (1182895309 : ℕ)^133*20000000000000^101 ≤ 7465656361201^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1182895309 2500000000 7465656361201 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3014861531/5000000000 : ℝ)^133 ≤ (6420940176513/12500000000000 : ℝ)^101 := by
    have hnat : (3014861531 : ℕ)^133*12500000000000^101 ≤ 6420940176513^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3014861531 5000000000 6420940176513 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (477498121/2500000000 : ℝ)^133 ≤ (5652098382607/50000000000000 : ℝ)^101 := by
    have hnat : (477498121 : ℕ)^133*50000000000000^101 ≤ 5652098382607^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      477498121 2500000000 5652098382607 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1182895309/2500000000 : ℝ), (3014861531/5000000000 : ℝ), (-477498121/2500000000 : ℝ)] ![(7465656361201/20000000000000 : ℝ), (6420940176513/12500000000000 : ℝ), (5652098382607/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1182895309/2500000000 : ℝ)|^133 ≤ (7465656361201/20000000000000 : ℝ)^101
        have hw : |(1182895309/2500000000 : ℝ)|=(1182895309/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3014861531/5000000000 : ℝ)|^133 ≤ (6420940176513/12500000000000 : ℝ)^101
        have hw : |(3014861531/5000000000 : ℝ)|=(3014861531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-477498121/2500000000 : ℝ)|^133 ≤ (5652098382607/50000000000000 : ℝ)^101
        have hw : |(-477498121/2500000000 : ℝ)|=(477498121/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304061_s8_s8_6 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5722365987/10000000000 : ℝ)*x 0 + (1653009401/5000000000 : ℝ)*x 1 + (1941340847/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5722365987/10000000000 : ℝ)^133 ≤ (11986928596667/25000000000000 : ℝ)^101 := by
    have hnat : (5722365987 : ℕ)^133*25000000000000^101 ≤ 11986928596667^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5722365987 10000000000 11986928596667 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1653009401/5000000000 : ℝ)^133 ≤ (11640617492747/50000000000000 : ℝ)^101 := by
    have hnat : (1653009401 : ℕ)^133*50000000000000^101 ≤ 11640617492747^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1653009401 5000000000 11640617492747 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1941340847/5000000000 : ℝ)^133 ≤ (7192762652867/25000000000000 : ℝ)^101 := by
    have hnat : (1941340847 : ℕ)^133*25000000000000^101 ≤ 7192762652867^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1941340847 5000000000 7192762652867 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5722365987/10000000000 : ℝ), (1653009401/5000000000 : ℝ), (1941340847/5000000000 : ℝ)] ![(11986928596667/25000000000000 : ℝ), (11640617492747/50000000000000 : ℝ), (7192762652867/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5722365987/10000000000 : ℝ)|^133 ≤ (11986928596667/25000000000000 : ℝ)^101
        have hw : |(5722365987/10000000000 : ℝ)|=(5722365987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1653009401/5000000000 : ℝ)|^133 ≤ (11640617492747/50000000000000 : ℝ)^101
        have hw : |(1653009401/5000000000 : ℝ)|=(1653009401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1941340847/5000000000 : ℝ)|^133 ≤ (7192762652867/25000000000000 : ℝ)^101
        have hw : |(1941340847/5000000000 : ℝ)|=(1941340847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304061_s8_s8_7 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-664503003/2500000000 : ℝ)*x 0 + (4500789083/10000000000 : ℝ)*x 1 + (568926397/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664503003/2500000000 : ℝ)^133 ≤ (3493561085937/20000000000000 : ℝ)^101 := by
    have hnat : (664503003 : ℕ)^133*20000000000000^101 ≤ 3493561085937^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664503003 2500000000 3493561085937 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4500789083/10000000000 : ℝ)^133 ≤ (34949383914131/100000000000000 : ℝ)^101 := by
    have hnat : (4500789083 : ℕ)^133*100000000000000^101 ≤ 34949383914131^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4500789083 10000000000 34949383914131 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (568926397/1000000000 : ℝ)^133 ≤ (11895702661657/25000000000000 : ℝ)^101 := by
    have hnat : (568926397 : ℕ)^133*25000000000000^101 ≤ 11895702661657^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      568926397 1000000000 11895702661657 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-664503003/2500000000 : ℝ), (4500789083/10000000000 : ℝ), (568926397/1000000000 : ℝ)] ![(3493561085937/20000000000000 : ℝ), (34949383914131/100000000000000 : ℝ), (11895702661657/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-664503003/2500000000 : ℝ)|^133 ≤ (3493561085937/20000000000000 : ℝ)^101
        have hw : |(-664503003/2500000000 : ℝ)|=(664503003/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4500789083/10000000000 : ℝ)|^133 ≤ (34949383914131/100000000000000 : ℝ)^101
        have hw : |(4500789083/10000000000 : ℝ)|=(4500789083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(568926397/1000000000 : ℝ)|^133 ≤ (11895702661657/25000000000000 : ℝ)^101
        have hw : |(568926397/1000000000 : ℝ)|=(568926397/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304061_s8_s8_8 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2325734197/5000000000 : ℝ)*x 0 + (-2518710487/10000000000 : ℝ)*x 1 + (5657138253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2325734197/5000000000 : ℝ)^133 ≤ (36498253065131/100000000000000 : ℝ)^101 := by
    have hnat : (2325734197 : ℕ)^133*100000000000000^101 ≤ 36498253065131^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2325734197 5000000000 36498253065131 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2518710487/10000000000 : ℝ)^133 ≤ (4068108770101/25000000000000 : ℝ)^101 := by
    have hnat : (2518710487 : ℕ)^133*25000000000000^101 ≤ 4068108770101^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2518710487 10000000000 4068108770101 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5657138253/10000000000 : ℝ)^133 ≤ (23614655925469/50000000000000 : ℝ)^101 := by
    have hnat : (5657138253 : ℕ)^133*50000000000000^101 ≤ 23614655925469^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5657138253 10000000000 23614655925469 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2325734197/5000000000 : ℝ), (-2518710487/10000000000 : ℝ), (5657138253/10000000000 : ℝ)] ![(36498253065131/100000000000000 : ℝ), (4068108770101/25000000000000 : ℝ), (23614655925469/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2325734197/5000000000 : ℝ)|^133 ≤ (36498253065131/100000000000000 : ℝ)^101
        have hw : |(2325734197/5000000000 : ℝ)|=(2325734197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2518710487/10000000000 : ℝ)|^133 ≤ (4068108770101/25000000000000 : ℝ)^101
        have hw : |(-2518710487/10000000000 : ℝ)|=(2518710487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5657138253/10000000000 : ℝ)|^133 ≤ (23614655925469/50000000000000 : ℝ)^101
        have hw : |(5657138253/10000000000 : ℝ)|=(5657138253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304061_s8_s8_9 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2336202173/5000000000 : ℝ)*x 0 + (777117001/1250000000 : ℝ)*x 1 + (-857342513/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2336202173/5000000000 : ℝ)^133 ≤ (36714731290117/100000000000000 : ℝ)^101 := by
    have hnat : (2336202173 : ℕ)^133*100000000000000^101 ≤ 36714731290117^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2336202173 5000000000 36714731290117 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (777117001/1250000000 : ℝ)^133 ≤ (13369490846891/25000000000000 : ℝ)^101 := by
    have hnat : (777117001 : ℕ)^133*25000000000000^101 ≤ 13369490846891^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      777117001 1250000000 13369490846891 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (857342513/5000000000 : ℝ)^133 ≤ (9807305311509/100000000000000 : ℝ)^101 := by
    have hnat : (857342513 : ℕ)^133*100000000000000^101 ≤ 9807305311509^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      857342513 5000000000 9807305311509 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2336202173/5000000000 : ℝ), (777117001/1250000000 : ℝ), (-857342513/5000000000 : ℝ)] ![(36714731290117/100000000000000 : ℝ), (13369490846891/25000000000000 : ℝ), (9807305311509/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2336202173/5000000000 : ℝ)|^133 ≤ (36714731290117/100000000000000 : ℝ)^101
        have hw : |(2336202173/5000000000 : ℝ)|=(2336202173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(777117001/1250000000 : ℝ)|^133 ≤ (13369490846891/25000000000000 : ℝ)^101
        have hw : |(777117001/1250000000 : ℝ)|=(777117001/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-857342513/5000000000 : ℝ)|^133 ≤ (9807305311509/100000000000000 : ℝ)^101
        have hw : |(-857342513/5000000000 : ℝ)|=(857342513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304061_s8_s8_13 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5721387611/10000000000 : ℝ)*x 0 + (3418902687/10000000000 : ℝ)*x 1 + (1887731299/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5721387611/10000000000 : ℝ)^133 ≤ (383495356301/800000000000 : ℝ)^101 := by
    have hnat : (5721387611 : ℕ)^133*800000000000^101 ≤ 383495356301^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5721387611 10000000000 383495356301 800000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3418902687/10000000000 : ℝ)^133 ≤ (3041706485003/12500000000000 : ℝ)^101 := by
    have hnat : (3418902687 : ℕ)^133*12500000000000^101 ≤ 3041706485003^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3418902687 10000000000 3041706485003 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1887731299/5000000000 : ℝ)^133 ≤ (27729428561863/100000000000000 : ℝ)^101 := by
    have hnat : (1887731299 : ℕ)^133*100000000000000^101 ≤ 27729428561863^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1887731299 5000000000 27729428561863 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5721387611/10000000000 : ℝ), (3418902687/10000000000 : ℝ), (1887731299/5000000000 : ℝ)] ![(383495356301/800000000000 : ℝ), (3041706485003/12500000000000 : ℝ), (27729428561863/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5721387611/10000000000 : ℝ)|^133 ≤ (383495356301/800000000000 : ℝ)^101
        have hw : |(5721387611/10000000000 : ℝ)|=(5721387611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3418902687/10000000000 : ℝ)|^133 ≤ (3041706485003/12500000000000 : ℝ)^101
        have hw : |(3418902687/10000000000 : ℝ)|=(3418902687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1887731299/5000000000 : ℝ)|^133 ≤ (27729428561863/100000000000000 : ℝ)^101
        have hw : |(1887731299/5000000000 : ℝ)|=(1887731299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304061_s8_s8_14 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-607782063/2500000000 : ℝ)*x 0 + (2325051213/5000000000 : ℝ)*x 1 + (5725690373/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (607782063/2500000000 : ℝ)^133 ≤ (15531462198973/100000000000000 : ℝ)^101 := by
    have hnat : (607782063 : ℕ)^133*100000000000000^101 ≤ 15531462198973^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      607782063 2500000000 15531462198973 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2325051213/5000000000 : ℝ)^133 ≤ (18242069817287/50000000000000 : ℝ)^101 := by
    have hnat : (2325051213 : ℕ)^133*50000000000000^101 ≤ 18242069817287^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2325051213 5000000000 18242069817287 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5725690373/10000000000 : ℝ)^133 ≤ (47984398155867/100000000000000 : ℝ)^101 := by
    have hnat : (5725690373 : ℕ)^133*100000000000000^101 ≤ 47984398155867^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5725690373 10000000000 47984398155867 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-607782063/2500000000 : ℝ), (2325051213/5000000000 : ℝ), (5725690373/10000000000 : ℝ)] ![(15531462198973/100000000000000 : ℝ), (18242069817287/50000000000000 : ℝ), (47984398155867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-607782063/2500000000 : ℝ)|^133 ≤ (15531462198973/100000000000000 : ℝ)^101
        have hw : |(-607782063/2500000000 : ℝ)|=(607782063/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2325051213/5000000000 : ℝ)|^133 ≤ (18242069817287/50000000000000 : ℝ)^101
        have hw : |(2325051213/5000000000 : ℝ)|=(2325051213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5725690373/10000000000 : ℝ)|^133 ≤ (47984398155867/100000000000000 : ℝ)^101
        have hw : |(5725690373/10000000000 : ℝ)|=(5725690373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304061_s8_s8_15 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1144814083/2500000000 : ℝ)*x 0 + (-164257307/625000000 : ℝ)*x 1 + (5639590351/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1144814083/2500000000 : ℝ)^133 ≤ (35753951701863/100000000000000 : ℝ)^101 := by
    have hnat : (1144814083 : ℕ)^133*100000000000000^101 ≤ 35753951701863^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1144814083 2500000000 35753951701863 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (164257307/625000000 : ℝ)^133 ≤ (3441911695583/20000000000000 : ℝ)^101 := by
    have hnat : (164257307 : ℕ)^133*20000000000000^101 ≤ 3441911695583^101*625000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164257307 625000000 3441911695583 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5639590351/10000000000 : ℝ)^133 ≤ (4703648980747/10000000000000 : ℝ)^101 := by
    have hnat : (5639590351 : ℕ)^133*10000000000000^101 ≤ 4703648980747^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5639590351 10000000000 4703648980747 10000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1144814083/2500000000 : ℝ), (-164257307/625000000 : ℝ), (5639590351/10000000000 : ℝ)] ![(35753951701863/100000000000000 : ℝ), (3441911695583/20000000000000 : ℝ), (4703648980747/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1144814083/2500000000 : ℝ)|^133 ≤ (35753951701863/100000000000000 : ℝ)^101
        have hw : |(1144814083/2500000000 : ℝ)|=(1144814083/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-164257307/625000000 : ℝ)|^133 ≤ (3441911695583/20000000000000 : ℝ)^101
        have hw : |(-164257307/625000000 : ℝ)|=(164257307/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5639590351/10000000000 : ℝ)|^133 ≤ (4703648980747/10000000000000 : ℝ)^101
        have hw : |(5639590351/10000000000 : ℝ)|=(5639590351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304061_s8_s8_16 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4960408403/10000000000 : ℝ)*x 0 + (5937619287/10000000000 : ℝ)*x 1 + (-866116473/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4960408403/10000000000 : ℝ)^133 ≤ (19861759330937/50000000000000 : ℝ)^101 := by
    have hnat : (4960408403 : ℕ)^133*50000000000000^101 ≤ 19861759330937^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4960408403 10000000000 19861759330937 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5937619287/10000000000 : ℝ)^133 ≤ (12584198944529/25000000000000 : ℝ)^101 := by
    have hnat : (5937619287 : ℕ)^133*25000000000000^101 ≤ 12584198944529^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5937619287 10000000000 12584198944529 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (866116473/5000000000 : ℝ)^133 ≤ (24849213857/250000000000 : ℝ)^101 := by
    have hnat : (866116473 : ℕ)^133*250000000000^101 ≤ 24849213857^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      866116473 5000000000 24849213857 250000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4960408403/10000000000 : ℝ), (5937619287/10000000000 : ℝ), (-866116473/5000000000 : ℝ)] ![(19861759330937/50000000000000 : ℝ), (12584198944529/25000000000000 : ℝ), (24849213857/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4960408403/10000000000 : ℝ)|^133 ≤ (19861759330937/50000000000000 : ℝ)^101
        have hw : |(4960408403/10000000000 : ℝ)|=(4960408403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5937619287/10000000000 : ℝ)|^133 ≤ (12584198944529/25000000000000 : ℝ)^101
        have hw : |(5937619287/10000000000 : ℝ)|=(5937619287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-866116473/5000000000 : ℝ)|^133 ≤ (24849213857/250000000000 : ℝ)^101
        have hw : |(-866116473/5000000000 : ℝ)|=(866116473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304061_s8_s8_20 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5992510369/10000000000 : ℝ)*x 0 + (198166291/625000000 : ℝ)*x 1 + (3701392181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5992510369/10000000000 : ℝ)^133 ≤ (25475236146297/50000000000000 : ℝ)^101 := by
    have hnat : (5992510369 : ℕ)^133*50000000000000^101 ≤ 25475236146297^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5992510369 10000000000 25475236146297 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (198166291/625000000 : ℝ)^133 ≤ (4406849299101/20000000000000 : ℝ)^101 := by
    have hnat : (198166291 : ℕ)^133*20000000000000^101 ≤ 4406849299101^101*625000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      198166291 625000000 4406849299101 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3701392181/10000000000 : ℝ)^133 ≤ (337691014923/1250000000000 : ℝ)^101 := by
    have hnat : (3701392181 : ℕ)^133*1250000000000^101 ≤ 337691014923^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3701392181 10000000000 337691014923 1250000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5992510369/10000000000 : ℝ), (198166291/625000000 : ℝ), (3701392181/10000000000 : ℝ)] ![(25475236146297/50000000000000 : ℝ), (4406849299101/20000000000000 : ℝ), (337691014923/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5992510369/10000000000 : ℝ)|^133 ≤ (25475236146297/50000000000000 : ℝ)^101
        have hw : |(5992510369/10000000000 : ℝ)|=(5992510369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(198166291/625000000 : ℝ)|^133 ≤ (4406849299101/20000000000000 : ℝ)^101
        have hw : |(198166291/625000000 : ℝ)|=(198166291/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3701392181/10000000000 : ℝ)|^133 ≤ (337691014923/1250000000000 : ℝ)^101
        have hw : |(3701392181/10000000000 : ℝ)|=(3701392181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304061_s8_s8_21 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-489053797/2000000000 : ℝ)*x 0 + (2343536037/5000000000 : ℝ)*x 1 + (568018887/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (489053797/2000000000 : ℝ)^133 ≤ (7825266616187/50000000000000 : ℝ)^101 := by
    have hnat : (489053797 : ℕ)^133*50000000000000^101 ≤ 7825266616187^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      489053797 2000000000 7825266616187 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2343536037/5000000000 : ℝ)^133 ≤ (9216644799951/25000000000000 : ℝ)^101 := by
    have hnat : (2343536037 : ℕ)^133*25000000000000^101 ≤ 9216644799951^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2343536037 5000000000 9216644799951 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (568018887/1000000000 : ℝ)^133 ≤ (11870721886813/25000000000000 : ℝ)^101 := by
    have hnat : (568018887 : ℕ)^133*25000000000000^101 ≤ 11870721886813^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      568018887 1000000000 11870721886813 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-489053797/2000000000 : ℝ), (2343536037/5000000000 : ℝ), (568018887/1000000000 : ℝ)] ![(7825266616187/50000000000000 : ℝ), (9216644799951/25000000000000 : ℝ), (11870721886813/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-489053797/2000000000 : ℝ)|^133 ≤ (7825266616187/50000000000000 : ℝ)^101
        have hw : |(-489053797/2000000000 : ℝ)|=(489053797/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2343536037/5000000000 : ℝ)|^133 ≤ (9216644799951/25000000000000 : ℝ)^101
        have hw : |(2343536037/5000000000 : ℝ)|=(2343536037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(568018887/1000000000 : ℝ)|^133 ≤ (11870721886813/25000000000000 : ℝ)^101
        have hw : |(568018887/1000000000 : ℝ)|=(568018887/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304061_s8_s8_22 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (30783321/62500000 : ℝ)*x 0 + (-2487939523/10000000000 : ℝ)*x 1 + (216781743/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (30783321/62500000 : ℝ)^133 ≤ (19677017196361/50000000000000 : ℝ)^101 := by
    have hnat : (30783321 : ℕ)^133*50000000000000^101 ≤ 19677017196361^101*62500000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30783321 62500000 19677017196361 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2487939523/10000000000 : ℝ)^133 ≤ (16011157598733/100000000000000 : ℝ)^101 := by
    have hnat : (2487939523 : ℕ)^133*100000000000000^101 ≤ 16011157598733^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2487939523 10000000000 16011157598733 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216781743/400000000 : ℝ)^133 ≤ (22317403998587/50000000000000 : ℝ)^101 := by
    have hnat : (216781743 : ℕ)^133*50000000000000^101 ≤ 22317403998587^101*400000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216781743 400000000 22317403998587 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(30783321/62500000 : ℝ), (-2487939523/10000000000 : ℝ), (216781743/400000000 : ℝ)] ![(19677017196361/50000000000000 : ℝ), (16011157598733/100000000000000 : ℝ), (22317403998587/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(30783321/62500000 : ℝ)|^133 ≤ (19677017196361/50000000000000 : ℝ)^101
        have hw : |(30783321/62500000 : ℝ)|=(30783321/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2487939523/10000000000 : ℝ)|^133 ≤ (16011157598733/100000000000000 : ℝ)^101
        have hw : |(-2487939523/10000000000 : ℝ)|=(2487939523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216781743/400000000 : ℝ)|^133 ≤ (22317403998587/50000000000000 : ℝ)^101
        have hw : |(216781743/400000000 : ℝ)|=(216781743/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304061_s8_s8_23 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4582038839/10000000000 : ℝ)*x 0 + (6183695359/10000000000 : ℝ)*x 1 + (-1885755367/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4582038839/10000000000 : ℝ)^133 ≤ (1789128149543/5000000000000 : ℝ)^101 := by
    have hnat : (4582038839 : ℕ)^133*5000000000000^101 ≤ 1789128149543^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4582038839 10000000000 1789128149543 5000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6183695359/10000000000 : ℝ)^133 ≤ (2655087694101/5000000000000 : ℝ)^101 := by
    have hnat : (6183695359 : ℕ)^133*5000000000000^101 ≤ 2655087694101^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6183695359 10000000000 2655087694101 5000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1885755367/10000000000 : ℝ)^133 ≤ (11115683107397/100000000000000 : ℝ)^101 := by
    have hnat : (1885755367 : ℕ)^133*100000000000000^101 ≤ 11115683107397^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1885755367 10000000000 11115683107397 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4582038839/10000000000 : ℝ), (6183695359/10000000000 : ℝ), (-1885755367/10000000000 : ℝ)] ![(1789128149543/5000000000000 : ℝ), (2655087694101/5000000000000 : ℝ), (11115683107397/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4582038839/10000000000 : ℝ)|^133 ≤ (1789128149543/5000000000000 : ℝ)^101
        have hw : |(4582038839/10000000000 : ℝ)|=(4582038839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6183695359/10000000000 : ℝ)|^133 ≤ (2655087694101/5000000000000 : ℝ)^101
        have hw : |(6183695359/10000000000 : ℝ)|=(6183695359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1885755367/10000000000 : ℝ)|^133 ≤ (11115683107397/100000000000000 : ℝ)^101
        have hw : |(-1885755367/10000000000 : ℝ)|=(1885755367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304061_s8_s8_27 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (6029425833/10000000000 : ℝ)*x 0 + (3170269309/10000000000 : ℝ)*x 1 + (3658641001/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6029425833/10000000000 : ℝ)^133 ≤ (5136418707657/10000000000000 : ℝ)^101 := by
    have hnat : (6029425833 : ℕ)^133*10000000000000^101 ≤ 5136418707657^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6029425833 10000000000 5136418707657 10000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3170269309/10000000000 : ℝ)^133 ≤ (22030665265421/100000000000000 : ℝ)^101 := by
    have hnat : (3170269309 : ℕ)^133*100000000000000^101 ≤ 22030665265421^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3170269309 10000000000 22030665265421 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3658641001/10000000000 : ℝ)^133 ≤ (13302573821049/50000000000000 : ℝ)^101 := by
    have hnat : (3658641001 : ℕ)^133*50000000000000^101 ≤ 13302573821049^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3658641001 10000000000 13302573821049 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6029425833/10000000000 : ℝ), (3170269309/10000000000 : ℝ), (3658641001/10000000000 : ℝ)] ![(5136418707657/10000000000000 : ℝ), (22030665265421/100000000000000 : ℝ), (13302573821049/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6029425833/10000000000 : ℝ)|^133 ≤ (5136418707657/10000000000000 : ℝ)^101
        have hw : |(6029425833/10000000000 : ℝ)|=(6029425833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3170269309/10000000000 : ℝ)|^133 ≤ (22030665265421/100000000000000 : ℝ)^101
        have hw : |(3170269309/10000000000 : ℝ)|=(3170269309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3658641001/10000000000 : ℝ)|^133 ≤ (13302573821049/50000000000000 : ℝ)^101
        have hw : |(3658641001/10000000000 : ℝ)|=(3658641001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c304061_s8 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev7 : (0 : ℝ) ≤ ((32811/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(32811/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(38137/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(38137/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(34949/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(34949/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((3979/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3979/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3961/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(3961/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3653/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(3653/20000 : ℝ)*X 1 2) := by
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
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  rcases hprev7 with ⟨ratio_s7_0,ratio_s7_1,ratio_s7_2⟩
  have s8_pow0 : (32811/100000 : ℝ) ^ (33/8 : ℝ) ≤ (1008278021903594861/100000000000000000000 : ℝ) := by
    have hpowers : (32811/100000 : ℝ)^33 ≤ (1008278021903594861/100000000000000000000 : ℝ)^8 := by
      have hnat : (32811 : ℕ)^33*100000000000000000000^8 ≤ 1008278021903594861^8*100000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        32811 100000 1008278021903594861 100000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (32811/100000 : ℝ)) (X := (1008278021903594861/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s8_corner0a : (101008278021903594861/100000000000000000000 : ℝ) ≤ (1253043787156453/1250000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (101008278021903594861/100000000000000000000 : ℝ)^8 ≤ (1253043787156453/1250000000000000 : ℝ)^33 := by
      have hnat : (101008278021903594861 : ℕ)^8*1250000000000000^33 ≤ 1253043787156453^33*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101008278021903594861 100000000000000000000 1253043787156453 1250000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1253043787156453/1250000000000000 : ℝ)) (X := (101008278021903594861/100000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s8_corner0b : (51008278021903594861/50000000000000000000 : ℝ) ≤ (10048517142484269/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (51008278021903594861/50000000000000000000 : ℝ)^8 ≤ (10048517142484269/10000000000000000 : ℝ)^33 := by
      have hnat : (51008278021903594861 : ℕ)^8*10000000000000000^33 ≤ 10048517142484269^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51008278021903594861 50000000000000000000 10048517142484269 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10048517142484269/10000000000000000 : ℝ)) (X := (51008278021903594861/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s8_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(3043787156453/410137500000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(4833369046529/656220000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (32811/100000 : ℝ)) (alpha := (3043787156453/410137500000000 : ℝ)) (beta := (4833369046529/656220000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s8_pow0,s8_corner0a]) (by linarith only [s8_pow0,s8_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (32811/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s7_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(3043787156453/410137500000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(4833369046529/656220000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s8_pow1 : (38137/100000 : ℝ) ^ (33/8 : ℝ) ≤ (93761474277829803/5000000000000000000 : ℝ) := by
    have hpowers : (38137/100000 : ℝ)^33 ≤ (93761474277829803/5000000000000000000 : ℝ)^8 := by
      have hnat : (38137 : ℕ)^33*5000000000000000000^8 ≤ 93761474277829803^8*100000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        38137 100000 93761474277829803 5000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (38137/100000 : ℝ)) (X := (93761474277829803/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s8_corner1a : (5093761474277829803/5000000000000000000 : ℝ) ≤ (19619415432531/19531250000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (5093761474277829803/5000000000000000000 : ℝ)^8 ≤ (19619415432531/19531250000000 : ℝ)^33 := by
      have hnat : (5093761474277829803 : ℕ)^8*19531250000000^33 ≤ 19619415432531^33*5000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5093761474277829803 5000000000000000000 19619415432531 19531250000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (19619415432531/19531250000000 : ℝ)) (X := (5093761474277829803/5000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s8_corner1b : (2593761474277829803/2500000000000000000 : ℝ) ≤ (10089656245728583/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (2593761474277829803/2500000000000000000 : ℝ)^8 ≤ (10089656245728583/10000000000000000 : ℝ)^33 := by
      have hnat : (2593761474277829803 : ℕ)^8*10000000000000000^33 ≤ 10089656245728583^33*2500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2593761474277829803 2500000000000000000 10089656245728583 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10089656245728583/10000000000000000 : ℝ)) (X := (2593761474277829803/2500000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s8_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(8015039321/677148437500 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(44515544272711/3813700000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (38137/100000 : ℝ)) (alpha := (8015039321/677148437500 : ℝ)) (beta := (44515544272711/3813700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s8_pow1,s8_corner1a]) (by linarith only [s8_pow1,s8_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (38137/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s7_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(8015039321/677148437500 : ℝ)*((1 : ℝ)*pair X 1 0)+(44515544272711/3813700000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s8_pow2 : (34949/100000 : ℝ) ^ (33/8 : ℝ) ≤ (261636514483104681/20000000000000000000 : ℝ) := by
    have hpowers : (34949/100000 : ℝ)^33 ≤ (261636514483104681/20000000000000000000 : ℝ)^8 := by
      have hnat : (34949 : ℕ)^33*20000000000000000000^8 ≤ 261636514483104681^8*100000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        34949 100000 261636514483104681 20000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (34949/100000 : ℝ)) (X := (261636514483104681/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s8_corner2a : (20261636514483104681/20000000000000000000 : ℝ) ≤ (2507889390638961/2500000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (20261636514483104681/20000000000000000000 : ℝ)^8 ≤ (2507889390638961/2500000000000000 : ℝ)^33 := by
      have hnat : (20261636514483104681 : ℕ)^8*2500000000000000^33 ≤ 2507889390638961^33*20000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20261636514483104681 20000000000000000000 2507889390638961 2500000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2507889390638961/2500000000000000 : ℝ)) (X := (20261636514483104681/20000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s8_corner2b : (10261636514483104681/10000000000000000000 : ℝ) ≤ (10062807906583139/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (10261636514483104681/10000000000000000000 : ℝ)^8 ≤ (10062807906583139/10000000000000000 : ℝ)^33 := by
      have hnat : (10261636514483104681 : ℕ)^8*10000000000000000^33 ≤ 10062807906583139^33*10000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10261636514483104681 10000000000000000000 10062807906583139 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10062807906583139/10000000000000000 : ℝ)) (X := (10261636514483104681/10000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s8_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(7889390638961/873725000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(6250068805459/698980000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (34949/100000 : ℝ)) (alpha := (7889390638961/873725000000000 : ℝ)) (beta := (6250068805459/698980000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s8_pow2,s8_corner2a]) (by linarith only [s8_pow2,s8_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (34949/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s7_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(7889390638961/873725000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(6250068805459/698980000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s8_0 : ((-1328835873/5000000000 : ℝ)*X 0 0+(2279767137/5000000000 : ℝ)*X 0 1+(5634794331/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304061_s8_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s8_1 : ((2355325881/5000000000 : ℝ)*X 1 0+(-2698585133/10000000000 : ℝ)*X 1 1+(1091910609/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304061_s8_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s8_2 : ((1182895309/2500000000 : ℝ)*X 2 0+(3014861531/5000000000 : ℝ)*X 2 1+(-477498121/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304061_s8_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s8_6 : ((5722365987/10000000000 : ℝ)*X 0 0+(1653009401/5000000000 : ℝ)*X 0 1+(1941340847/5000000000 : ℝ)*X 0 2+(5722365987/10000000000 : ℝ)*X 1 0+(1653009401/5000000000 : ℝ)*X 1 1+(1941340847/5000000000 : ℝ)*X 1 2+(5722365987/10000000000 : ℝ)*X 2 0+(1653009401/5000000000 : ℝ)*X 2 1+(1941340847/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304061_s8_s8_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s8_7 : ((-664503003/2500000000 : ℝ)*X 0 0+(4500789083/10000000000 : ℝ)*X 0 1+(568926397/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304061_s8_s8_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s8_8 : ((2325734197/5000000000 : ℝ)*X 1 0+(-2518710487/10000000000 : ℝ)*X 1 1+(5657138253/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304061_s8_s8_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s8_9 : ((2336202173/5000000000 : ℝ)*X 2 0+(777117001/1250000000 : ℝ)*X 2 1+(-857342513/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304061_s8_s8_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s8_13 : ((5721387611/10000000000 : ℝ)*X 0 0+(3418902687/10000000000 : ℝ)*X 0 1+(1887731299/5000000000 : ℝ)*X 0 2+(5721387611/10000000000 : ℝ)*X 1 0+(3418902687/10000000000 : ℝ)*X 1 1+(1887731299/5000000000 : ℝ)*X 1 2+(5721387611/10000000000 : ℝ)*X 2 0+(3418902687/10000000000 : ℝ)*X 2 1+(1887731299/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304061_s8_s8_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s8_14 : ((-607782063/2500000000 : ℝ)*X 0 0+(2325051213/5000000000 : ℝ)*X 0 1+(5725690373/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304061_s8_s8_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s8_15 : ((1144814083/2500000000 : ℝ)*X 1 0+(-164257307/625000000 : ℝ)*X 1 1+(5639590351/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304061_s8_s8_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s8_16 : ((4960408403/10000000000 : ℝ)*X 2 0+(5937619287/10000000000 : ℝ)*X 2 1+(-866116473/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304061_s8_s8_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s8_20 : ((5992510369/10000000000 : ℝ)*X 0 0+(198166291/625000000 : ℝ)*X 0 1+(3701392181/10000000000 : ℝ)*X 0 2+(5992510369/10000000000 : ℝ)*X 1 0+(198166291/625000000 : ℝ)*X 1 1+(3701392181/10000000000 : ℝ)*X 1 2+(5992510369/10000000000 : ℝ)*X 2 0+(198166291/625000000 : ℝ)*X 2 1+(3701392181/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304061_s8_s8_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s8_21 : ((-489053797/2000000000 : ℝ)*X 0 0+(2343536037/5000000000 : ℝ)*X 0 1+(568018887/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304061_s8_s8_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s8_22 : ((30783321/62500000 : ℝ)*X 1 0+(-2487939523/10000000000 : ℝ)*X 1 1+(216781743/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304061_s8_s8_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s8_23 : ((4582038839/10000000000 : ℝ)*X 2 0+(6183695359/10000000000 : ℝ)*X 2 1+(-1885755367/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304061_s8_s8_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s8_27 : ((6029425833/10000000000 : ℝ)*X 0 0+(3170269309/10000000000 : ℝ)*X 0 1+(3658641001/10000000000 : ℝ)*X 0 2+(6029425833/10000000000 : ℝ)*X 1 0+(3170269309/10000000000 : ℝ)*X 1 1+(3658641001/10000000000 : ℝ)*X 1 2+(6029425833/10000000000 : ℝ)*X 2 0+(3170269309/10000000000 : ℝ)*X 2 1+(3658641001/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304061_s8_s8_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s8_0 : (0 : ℝ) ≤ ((3979/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3979/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1507607176343368682764504355827/145773805921810000000000000000000000 : ℝ) := by norm_num
    linear_combination (863087/1000000000000 : ℝ)*(base50) + (3150963108241/1000000000000 : ℝ)*(base59) + (19422659353477/1000000000000 : ℝ)*(major_s8_0) + (19422659353477/1000000000000 : ℝ)*(major_s8_1) + (19422659353477/1000000000000 : ℝ)*(major_s8_2) + (45639073/125000000000 : ℝ)*(sp_s8_0) + (17179203/500000000000 : ℝ)*(sp_s8_1) + (304385279/1000000000000 : ℝ)*(sp_s8_6) + (6509812858253/250000000000 : ℝ)*(sp_s8_7) + (26039043184697/1000000000000 : ℝ)*(sp_s8_8) + (13019660965527/500000000000 : ℝ)*(sp_s8_9) + (12805394328707/1000000000000 : ℝ)*(sp_s8_13) + (134750623/250000000000 : ℝ)*(sp_s8_15) + (147307271/500000000000 : ℝ)*(sp_s8_23) + (6402849356993/500000000000 : ℝ)*(f.failure) + (6509904136399/250000000000 : ℝ)*(f.sum) + (875116900011138329/1514602287500000000000000000000 : ℝ)*base63 + (53711188417217/139796000000000000000000000 : ℝ)*base64 + (2060903890841573/3813700000000000000000000000 : ℝ)*base66 + (368642260407107/873725000000000000000000000 : ℝ)*base69 + (56117145611156036053/114671163900000000000000000000000 : ℝ)*base70 + (314403064655603/656220000000000000000000000 : ℝ)*base73 + (18377711781583/43337500000000000000000000 : ℝ)*base75 + (159287537075911/1640550000000000000000000000 : ℝ)*base76 + (23896600395886234129/62565655350000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (963/6250000000000000 : ℝ)*base86 + (963/6250000000000000 : ℝ)*base88 + (963/6250000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s8_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3961/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(3961/20000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (203417834714376839539257141/20855218450000000000000000000000 : ℝ) := by norm_num
    linear_combination (72781/31250000000 : ℝ)*(base39) + (9365886557/62500000000 : ℝ)*(base40) + (1542863429271/500000000000 : ℝ)*(base59) + (1294206664469/62500000000 : ℝ)*(major_s8_0) + (1294206664469/62500000000 : ℝ)*(major_s8_1) + (1294206664469/62500000000 : ℝ)*(major_s8_2) + (714044661/1000000000000 : ℝ)*(sp_s8_1) + (427933153/500000000000 : ℝ)*(sp_s8_2) + (67450213/250000000000 : ℝ)*(sp_s8_6) + (962889763/1000000000000 : ℝ)*(sp_s8_7) + (6940239502237/250000000000 : ℝ)*(sp_s8_14) + (555224137081/20000000000 : ℝ)*(sp_s8_15) + (13880532516203/500000000000 : ℝ)*(sp_s8_16) + (13652419312171/1000000000000 : ℝ)*(sp_s8_20) + (13652689113023/1000000000000 : ℝ)*(f.failure) + (27761920898711/1000000000000 : ℝ)*(f.sum) + (1903400082738464073/6058409150000000000000000000000 : ℝ)*base62 + (173329486776339/349490000000000000000000000 : ℝ)*base65 + (803833215530867/1906850000000000000000000000 : ℝ)*base67 + (509017076352463/1747450000000000000000000000 : ℝ)*base69 + (13175873216067529453/57335581950000000000000000000000 : ℝ)*base70 + (86905291315867/164055000000000000000000000 : ℝ)*base73 + (30137690052391/173350000000000000000000000 : ℝ)*base74 + (214914978719161/820275000000000000000000000 : ℝ)*base76 + (5875360196929458907/62565655350000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (3057/12500000000000000 : ℝ)*base87 + (3057/12500000000000000 : ℝ)*base89 + (3057/12500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s8_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3653/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(3653/20000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (175010634198498695831296735533/36443451480452500000000000000000000 : ℝ) := by norm_num
    linear_combination (627413129129/1000000000000 : ℝ)*(base40) + (3394119/1000000000000 : ℝ)*(base50) + (393321542163/125000000000 : ℝ)*(base59) + (4095773043279/200000000000 : ℝ)*(major_s8_0) + (4095773043279/200000000000 : ℝ)*(major_s8_1) + (4095773043279/200000000000 : ℝ)*(major_s8_2) + (116066259/200000000000 : ℝ)*(sp_s8_0) + (645721419/1000000000000 : ℝ)*(sp_s8_1) + (27940419/200000000000 : ℝ)*(sp_s8_2) + (82481271/1000000000000 : ℝ)*(sp_s8_9) + (214492771911/7812500000 : ℝ)*(sp_s8_21) + (6863752353621/250000000000 : ℝ)*(sp_s8_22) + (27455432952537/1000000000000 : ℝ)*(sp_s8_23) + (13502073696131/1000000000000 : ℝ)*(sp_s8_27) + (13502073696131/1000000000000 : ℝ)*(f.failure) + (27455655135903/1000000000000 : ℝ)*(f.sum) + (391817619044671183/1211681830000000000000000000000 : ℝ)*base63 + (487312982909603/698980000000000000000000000 : ℝ)*base64 + (151774202062059/152548000000000000000000000 : ℝ)*base66 + (200376965756071/349490000000000000000000000 : ℝ)*base68 + (2163806990051984537/7644744260000000000000000000000 : ℝ)*base70 + (113537508146979/218740000000000000000000000 : ℝ)*base72 + (146556023289/1733500000000000000000000 : ℝ)*base74 + (13033772051831/27342500000000000000000000 : ℝ)*base76 + (503394961673414549/834208738000000000000000000000 : ℝ)*base78 + (10129/12500000000000000 : ℝ)*base87 + (10129/12500000000000000 : ℝ)*base89 + (10129/12500000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s8_0,ratio_s8_1,ratio_s8_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev7 : (0 : ℝ) ≤ ((32811/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(32811/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(38137/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(38137/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(34949/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(34949/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((3979/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3979/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3961/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(3961/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3653/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(3653/20000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c304061_s8 p hpa hpb X hX hprev7

#print axioms solution
