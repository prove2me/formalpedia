-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c309080_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:06:08.321011+00:00
-- url     : https://prove2.me/submissions/83645974-e697-48d4-ae0f-7f658261d7e8

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
theorem collision_support_c309080_s2_s2_0 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-174736117/500000000 : ℝ)*x 0 + (1090231811/2000000000 : ℝ)*x 1 + (3834525409/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (174736117/500000000 : ℝ)^35 ≤ (6398343501659/25000000000000 : ℝ)^27 := by
    have hnat : (174736117 : ℕ)^35*25000000000000^27 ≤ 6398343501659^27*500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174736117 500000000 6398343501659 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1090231811/2000000000 : ℝ)^35 ≤ (45541934840793/100000000000000 : ℝ)^27 := by
    have hnat : (1090231811 : ℕ)^35*100000000000000^27 ≤ 45541934840793^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090231811 2000000000 45541934840793 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3834525409/10000000000 : ℝ)^35 ≤ (28864691134071/100000000000000 : ℝ)^27 := by
    have hnat : (3834525409 : ℕ)^35*100000000000000^27 ≤ 28864691134071^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3834525409 10000000000 28864691134071 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-174736117/500000000 : ℝ), (1090231811/2000000000 : ℝ), (3834525409/10000000000 : ℝ)] ![(6398343501659/25000000000000 : ℝ), (45541934840793/100000000000000 : ℝ), (28864691134071/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-174736117/500000000 : ℝ)|^35 ≤ (6398343501659/25000000000000 : ℝ)^27
        have hw : |(-174736117/500000000 : ℝ)|=(174736117/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1090231811/2000000000 : ℝ)|^35 ≤ (45541934840793/100000000000000 : ℝ)^27
        have hw : |(1090231811/2000000000 : ℝ)|=(1090231811/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3834525409/10000000000 : ℝ)|^35 ≤ (28864691134071/100000000000000 : ℝ)^27
        have hw : |(3834525409/10000000000 : ℝ)|=(3834525409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309080_s2_s2_2 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (409318127/1250000000 : ℝ)*x 0 + (5853615819/10000000000 : ℝ)*x 1 + (-3592939537/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (409318127/1250000000 : ℝ)^35 ≤ (23522961180953/100000000000000 : ℝ)^27 := by
    have hnat : (409318127 : ℕ)^35*100000000000000^27 ≤ 23522961180953^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      409318127 1250000000 23522961180953 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5853615819/10000000000 : ℝ)^35 ≤ (12486849600949/25000000000000 : ℝ)^27 := by
    have hnat : (5853615819 : ℕ)^35*25000000000000^27 ≤ 12486849600949^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5853615819 10000000000 12486849600949 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3592939537/10000000000 : ℝ)^35 ≤ (5305928079923/20000000000000 : ℝ)^27 := by
    have hnat : (3592939537 : ℕ)^35*20000000000000^27 ≤ 5305928079923^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3592939537 10000000000 5305928079923 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(409318127/1250000000 : ℝ), (5853615819/10000000000 : ℝ), (-3592939537/10000000000 : ℝ)] ![(23522961180953/100000000000000 : ℝ), (12486849600949/25000000000000 : ℝ), (5305928079923/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(409318127/1250000000 : ℝ)|^35 ≤ (23522961180953/100000000000000 : ℝ)^27
        have hw : |(409318127/1250000000 : ℝ)|=(409318127/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5853615819/10000000000 : ℝ)|^35 ≤ (12486849600949/25000000000000 : ℝ)^27
        have hw : |(5853615819/10000000000 : ℝ)|=(5853615819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3592939537/10000000000 : ℝ)|^35 ≤ (5305928079923/20000000000000 : ℝ)^27
        have hw : |(-3592939537/10000000000 : ℝ)|=(3592939537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309080_s2_s2_6 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4127744629/10000000000 : ℝ)*x 0 + (4925201303/10000000000 : ℝ)*x 1 + (3777869323/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4127744629/10000000000 : ℝ)^35 ≤ (1270310665527/4000000000000 : ℝ)^27 := by
    have hnat : (4127744629 : ℕ)^35*4000000000000^27 ≤ 1270310665527^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4127744629 10000000000 1270310665527 4000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4925201303/10000000000 : ℝ)^35 ≤ (19964588178177/50000000000000 : ℝ)^27 := by
    have hnat : (4925201303 : ℕ)^35*50000000000000^27 ≤ 19964588178177^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4925201303 10000000000 19964588178177 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3777869323/10000000000 : ℝ)^35 ≤ (14156528494661/50000000000000 : ℝ)^27 := by
    have hnat : (3777869323 : ℕ)^35*50000000000000^27 ≤ 14156528494661^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3777869323 10000000000 14156528494661 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4127744629/10000000000 : ℝ), (4925201303/10000000000 : ℝ), (3777869323/10000000000 : ℝ)] ![(1270310665527/4000000000000 : ℝ), (19964588178177/50000000000000 : ℝ), (14156528494661/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4127744629/10000000000 : ℝ)|^35 ≤ (1270310665527/4000000000000 : ℝ)^27
        have hw : |(4127744629/10000000000 : ℝ)|=(4127744629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4925201303/10000000000 : ℝ)|^35 ≤ (19964588178177/50000000000000 : ℝ)^27
        have hw : |(4925201303/10000000000 : ℝ)|=(4925201303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3777869323/10000000000 : ℝ)|^35 ≤ (14156528494661/50000000000000 : ℝ)^27
        have hw : |(3777869323/10000000000 : ℝ)|=(3777869323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309080_s2_s2_7 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-223651167/625000000 : ℝ)*x 0 + (1077668671/2000000000 : ℝ)*x 1 + (3822403037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (223651167/625000000 : ℝ)^35 ≤ (659768385079/2500000000000 : ℝ)^27 := by
    have hnat : (223651167 : ℕ)^35*2500000000000^27 ≤ 659768385079^27*625000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223651167 625000000 659768385079 2500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1077668671/2000000000 : ℝ)^35 ≤ (8972561553471/20000000000000 : ℝ)^27 := by
    have hnat : (1077668671 : ℕ)^35*20000000000000^27 ≤ 8972561553471^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077668671 2000000000 8972561553471 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3822403037/10000000000 : ℝ)^35 ≤ (28746456807877/100000000000000 : ℝ)^27 := by
    have hnat : (3822403037 : ℕ)^35*100000000000000^27 ≤ 28746456807877^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3822403037 10000000000 28746456807877 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-223651167/625000000 : ℝ), (1077668671/2000000000 : ℝ), (3822403037/10000000000 : ℝ)] ![(659768385079/2500000000000 : ℝ), (8972561553471/20000000000000 : ℝ), (28746456807877/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-223651167/625000000 : ℝ)|^35 ≤ (659768385079/2500000000000 : ℝ)^27
        have hw : |(-223651167/625000000 : ℝ)|=(223651167/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1077668671/2000000000 : ℝ)|^35 ≤ (8972561553471/20000000000000 : ℝ)^27
        have hw : |(1077668671/2000000000 : ℝ)|=(1077668671/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3822403037/10000000000 : ℝ)|^35 ≤ (28746456807877/100000000000000 : ℝ)^27
        have hw : |(3822403037/10000000000 : ℝ)|=(3822403037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309080_s2_s2_8 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (576384747/1000000000 : ℝ)*x 0 + (-71341983/2000000000 : ℝ)*x 1 + (2916284817/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (576384747/1000000000 : ℝ)^35 ≤ (24478369024029/50000000000000 : ℝ)^27 := by
    have hnat : (576384747 : ℕ)^35*50000000000000^27 ≤ 24478369024029^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      576384747 1000000000 24478369024029 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (71341983/2000000000 : ℝ)^35 ≤ (1328530505183/100000000000000 : ℝ)^27 := by
    have hnat : (71341983 : ℕ)^35*100000000000000^27 ≤ 1328530505183^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71341983 2000000000 1328530505183 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2916284817/5000000000 : ℝ)^35 ≤ (24857365716827/50000000000000 : ℝ)^27 := by
    have hnat : (2916284817 : ℕ)^35*50000000000000^27 ≤ 24857365716827^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2916284817 5000000000 24857365716827 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(576384747/1000000000 : ℝ), (-71341983/2000000000 : ℝ), (2916284817/5000000000 : ℝ)] ![(24478369024029/50000000000000 : ℝ), (1328530505183/100000000000000 : ℝ), (24857365716827/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(576384747/1000000000 : ℝ)|^35 ≤ (24478369024029/50000000000000 : ℝ)^27
        have hw : |(576384747/1000000000 : ℝ)|=(576384747/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-71341983/2000000000 : ℝ)|^35 ≤ (1328530505183/100000000000000 : ℝ)^27
        have hw : |(-71341983/2000000000 : ℝ)|=(71341983/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2916284817/5000000000 : ℝ)|^35 ≤ (24857365716827/50000000000000 : ℝ)^27
        have hw : |(2916284817/5000000000 : ℝ)|=(2916284817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309080_s2_s2_9 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2943364941/10000000000 : ℝ)*x 0 + (1299781327/2000000000 : ℝ)*x 1 + (-1572024981/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2943364941/10000000000 : ℝ)^35 ≤ (10243175052947/50000000000000 : ℝ)^27 := by
    have hnat : (2943364941 : ℕ)^35*50000000000000^27 ≤ 10243175052947^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2943364941 10000000000 10243175052947 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1299781327/2000000000 : ℝ)^35 ≤ (3574913917263/6250000000000 : ℝ)^27 := by
    have hnat : (1299781327 : ℕ)^35*6250000000000^27 ≤ 3574913917263^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299781327 2000000000 3574913917263 6250000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1572024981/5000000000 : ℝ)^35 ≤ (22315027205197/100000000000000 : ℝ)^27 := by
    have hnat : (1572024981 : ℕ)^35*100000000000000^27 ≤ 22315027205197^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1572024981 5000000000 22315027205197 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2943364941/10000000000 : ℝ), (1299781327/2000000000 : ℝ), (-1572024981/5000000000 : ℝ)] ![(10243175052947/50000000000000 : ℝ), (3574913917263/6250000000000 : ℝ), (22315027205197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2943364941/10000000000 : ℝ)|^35 ≤ (10243175052947/50000000000000 : ℝ)^27
        have hw : |(2943364941/10000000000 : ℝ)|=(2943364941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1299781327/2000000000 : ℝ)|^35 ≤ (3574913917263/6250000000000 : ℝ)^27
        have hw : |(1299781327/2000000000 : ℝ)|=(1299781327/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1572024981/5000000000 : ℝ)|^35 ≤ (22315027205197/100000000000000 : ℝ)^27
        have hw : |(-1572024981/5000000000 : ℝ)|=(1572024981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309080_s2_s2_12 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3838538159/10000000000 : ℝ)*x 0 + (5097082393/10000000000 : ℝ)*x 1 + (3884304923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3838538159/10000000000 : ℝ)^35 ≤ (14451926752973/50000000000000 : ℝ)^27 := by
    have hnat : (3838538159 : ℕ)^35*50000000000000^27 ≤ 14451926752973^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3838538159 10000000000 14451926752973 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5097082393/10000000000 : ℝ)^35 ≤ (20872388430111/50000000000000 : ℝ)^27 := by
    have hnat : (5097082393 : ℕ)^35*50000000000000^27 ≤ 20872388430111^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5097082393 10000000000 20872388430111 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3884304923/10000000000 : ℝ)^35 ≤ (29351369629029/100000000000000 : ℝ)^27 := by
    have hnat : (3884304923 : ℕ)^35*100000000000000^27 ≤ 29351369629029^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3884304923 10000000000 29351369629029 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3838538159/10000000000 : ℝ), (5097082393/10000000000 : ℝ), (3884304923/10000000000 : ℝ)] ![(14451926752973/50000000000000 : ℝ), (20872388430111/50000000000000 : ℝ), (29351369629029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3838538159/10000000000 : ℝ)|^35 ≤ (14451926752973/50000000000000 : ℝ)^27
        have hw : |(3838538159/10000000000 : ℝ)|=(3838538159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5097082393/10000000000 : ℝ)|^35 ≤ (20872388430111/50000000000000 : ℝ)^27
        have hw : |(5097082393/10000000000 : ℝ)|=(5097082393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3884304923/10000000000 : ℝ)|^35 ≤ (29351369629029/100000000000000 : ℝ)^27
        have hw : |(3884304923/10000000000 : ℝ)|=(3884304923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309080_s2_s2_13 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-740781499/2000000000 : ℝ)*x 0 + (136217739/250000000 : ℝ)*x 1 + (3630319957/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (740781499/2000000000 : ℝ)^35 ≤ (27596609372017/100000000000000 : ℝ)^27 := by
    have hnat : (740781499 : ℕ)^35*100000000000000^27 ≤ 27596609372017^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      740781499 2000000000 27596609372017 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (136217739/250000000 : ℝ)^35 ≤ (45515408670977/100000000000000 : ℝ)^27 := by
    have hnat : (136217739 : ℕ)^35*100000000000000^27 ≤ 45515408670977^27*250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136217739 250000000 45515408670977 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3630319957/10000000000 : ℝ)^35 ≤ (6721995484823/25000000000000 : ℝ)^27 := by
    have hnat : (3630319957 : ℕ)^35*25000000000000^27 ≤ 6721995484823^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3630319957 10000000000 6721995484823 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-740781499/2000000000 : ℝ), (136217739/250000000 : ℝ), (3630319957/10000000000 : ℝ)] ![(27596609372017/100000000000000 : ℝ), (45515408670977/100000000000000 : ℝ), (6721995484823/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-740781499/2000000000 : ℝ)|^35 ≤ (27596609372017/100000000000000 : ℝ)^27
        have hw : |(-740781499/2000000000 : ℝ)|=(740781499/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(136217739/250000000 : ℝ)|^35 ≤ (45515408670977/100000000000000 : ℝ)^27
        have hw : |(136217739/250000000 : ℝ)|=(136217739/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3630319957/10000000000 : ℝ)|^35 ≤ (6721995484823/25000000000000 : ℝ)^27
        have hw : |(3630319957/10000000000 : ℝ)|=(3630319957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309080_s2_s2_14 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1441136791/2500000000 : ℝ)*x 0 + (-481671399/5000000000 : ℝ)*x 1 + (2756815171/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1441136791/2500000000 : ℝ)^35 ≤ (1530138816197/3125000000000 : ℝ)^27 := by
    have hnat : (1441136791 : ℕ)^35*3125000000000^27 ≤ 1530138816197^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1441136791 2500000000 1530138816197 3125000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (481671399/5000000000 : ℝ)^35 ≤ (601989476061/12500000000000 : ℝ)^27 := by
    have hnat : (481671399 : ℕ)^35*12500000000000^27 ≤ 601989476061^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      481671399 5000000000 601989476061 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2756815171/5000000000 : ℝ)^35 ≤ (46219642056579/100000000000000 : ℝ)^27 := by
    have hnat : (2756815171 : ℕ)^35*100000000000000^27 ≤ 46219642056579^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2756815171 5000000000 46219642056579 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1441136791/2500000000 : ℝ), (-481671399/5000000000 : ℝ), (2756815171/5000000000 : ℝ)] ![(1530138816197/3125000000000 : ℝ), (601989476061/12500000000000 : ℝ), (46219642056579/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1441136791/2500000000 : ℝ)|^35 ≤ (1530138816197/3125000000000 : ℝ)^27
        have hw : |(1441136791/2500000000 : ℝ)|=(1441136791/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-481671399/5000000000 : ℝ)|^35 ≤ (601989476061/12500000000000 : ℝ)^27
        have hw : |(-481671399/5000000000 : ℝ)|=(481671399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2756815171/5000000000 : ℝ)|^35 ≤ (46219642056579/100000000000000 : ℝ)^27
        have hw : |(2756815171/5000000000 : ℝ)|=(2756815171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309080_s2_s2_15 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3085043107/10000000000 : ℝ)*x 0 + (5832250391/10000000000 : ℝ)*x 1 + (-759730821/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3085043107/10000000000 : ℝ)^35 ≤ (21773649762327/100000000000000 : ℝ)^27 := by
    have hnat : (3085043107 : ℕ)^35*100000000000000^27 ≤ 21773649762327^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3085043107 10000000000 21773649762327 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5832250391/10000000000 : ℝ)^35 ≤ (49711204093787/100000000000000 : ℝ)^27 := by
    have hnat : (5832250391 : ℕ)^35*100000000000000^27 ≤ 49711204093787^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5832250391 10000000000 49711204093787 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (759730821/2000000000 : ℝ)^35 ≤ (712878653123/2500000000000 : ℝ)^27 := by
    have hnat : (759730821 : ℕ)^35*2500000000000^27 ≤ 712878653123^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      759730821 2000000000 712878653123 2500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3085043107/10000000000 : ℝ), (5832250391/10000000000 : ℝ), (-759730821/2000000000 : ℝ)] ![(21773649762327/100000000000000 : ℝ), (49711204093787/100000000000000 : ℝ), (712878653123/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3085043107/10000000000 : ℝ)|^35 ≤ (21773649762327/100000000000000 : ℝ)^27
        have hw : |(3085043107/10000000000 : ℝ)|=(3085043107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5832250391/10000000000 : ℝ)|^35 ≤ (49711204093787/100000000000000 : ℝ)^27
        have hw : |(5832250391/10000000000 : ℝ)|=(5832250391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-759730821/2000000000 : ℝ)|^35 ≤ (712878653123/2500000000000 : ℝ)^27
        have hw : |(-759730821/2000000000 : ℝ)|=(759730821/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309080_s2_s2_19 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (88415289/200000000 : ℝ)*x 0 + (1208509719/2500000000 : ℝ)*x 1 + (892645397/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (88415289/200000000 : ℝ)^35 ≤ (6942079071663/20000000000000 : ℝ)^27 := by
    have hnat : (88415289 : ℕ)^35*20000000000000^27 ≤ 6942079071663^27*200000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88415289 200000000 6942079071663 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1208509719/2500000000 : ℝ)^35 ≤ (2435860536341/6250000000000 : ℝ)^27 := by
    have hnat : (1208509719 : ℕ)^35*6250000000000^27 ≤ 2435860536341^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1208509719 2500000000 2435860536341 6250000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (892645397/2500000000 : ℝ)^35 ≤ (26315836041397/100000000000000 : ℝ)^27 := by
    have hnat : (892645397 : ℕ)^35*100000000000000^27 ≤ 26315836041397^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      892645397 2500000000 26315836041397 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(88415289/200000000 : ℝ), (1208509719/2500000000 : ℝ), (892645397/2500000000 : ℝ)] ![(6942079071663/20000000000000 : ℝ), (2435860536341/6250000000000 : ℝ), (26315836041397/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(88415289/200000000 : ℝ)|^35 ≤ (6942079071663/20000000000000 : ℝ)^27
        have hw : |(88415289/200000000 : ℝ)|=(88415289/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1208509719/2500000000 : ℝ)|^35 ≤ (2435860536341/6250000000000 : ℝ)^27
        have hw : |(1208509719/2500000000 : ℝ)|=(1208509719/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(892645397/2500000000 : ℝ)|^35 ≤ (26315836041397/100000000000000 : ℝ)^27
        have hw : |(892645397/2500000000 : ℝ)|=(892645397/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309080_s2_s2_20 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-192555577/625000000 : ℝ)*x 0 + (2829236683/5000000000 : ℝ)*x 1 + (249842223/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (192555577/625000000 : ℝ)^35 ≤ (21735653486403/100000000000000 : ℝ)^27 := by
    have hnat : (192555577 : ℕ)^35*100000000000000^27 ≤ 21735653486403^27*625000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      192555577 625000000 21735653486403 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2829236683/5000000000 : ℝ)^35 ≤ (47799679808993/100000000000000 : ℝ)^27 := by
    have hnat : (2829236683 : ℕ)^35*100000000000000^27 ≤ 47799679808993^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2829236683 5000000000 47799679808993 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (249842223/625000000 : ℝ)^35 ≤ (30464666684297/100000000000000 : ℝ)^27 := by
    have hnat : (249842223 : ℕ)^35*100000000000000^27 ≤ 30464666684297^27*625000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249842223 625000000 30464666684297 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-192555577/625000000 : ℝ), (2829236683/5000000000 : ℝ), (249842223/625000000 : ℝ)] ![(21735653486403/100000000000000 : ℝ), (47799679808993/100000000000000 : ℝ), (30464666684297/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-192555577/625000000 : ℝ)|^35 ≤ (21735653486403/100000000000000 : ℝ)^27
        have hw : |(-192555577/625000000 : ℝ)|=(192555577/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2829236683/5000000000 : ℝ)|^35 ≤ (47799679808993/100000000000000 : ℝ)^27
        have hw : |(2829236683/5000000000 : ℝ)|=(2829236683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(249842223/625000000 : ℝ)|^35 ≤ (30464666684297/100000000000000 : ℝ)^27
        have hw : |(249842223/625000000 : ℝ)|=(249842223/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309080_s2_s2_21 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1652154157/2500000000 : ℝ)*x 0 + (-464073283/10000000000 : ℝ)*x 1 + (4901287117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1652154157/2500000000 : ℝ)^35 ≤ (58453427752491/100000000000000 : ℝ)^27 := by
    have hnat : (1652154157 : ℕ)^35*100000000000000^27 ≤ 58453427752491^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1652154157 2500000000 58453427752491 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (464073283/10000000000 : ℝ)^35 ≤ (373706886081/20000000000000 : ℝ)^27 := by
    have hnat : (464073283 : ℕ)^35*20000000000000^27 ≤ 373706886081^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      464073283 10000000000 373706886081 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4901287117/10000000000 : ℝ)^35 ≤ (7935607561659/20000000000000 : ℝ)^27 := by
    have hnat : (4901287117 : ℕ)^35*20000000000000^27 ≤ 7935607561659^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4901287117 10000000000 7935607561659 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1652154157/2500000000 : ℝ), (-464073283/10000000000 : ℝ), (4901287117/10000000000 : ℝ)] ![(58453427752491/100000000000000 : ℝ), (373706886081/20000000000000 : ℝ), (7935607561659/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1652154157/2500000000 : ℝ)|^35 ≤ (58453427752491/100000000000000 : ℝ)^27
        have hw : |(1652154157/2500000000 : ℝ)|=(1652154157/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-464073283/10000000000 : ℝ)|^35 ≤ (373706886081/20000000000000 : ℝ)^27
        have hw : |(-464073283/10000000000 : ℝ)|=(464073283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4901287117/10000000000 : ℝ)|^35 ≤ (7935607561659/20000000000000 : ℝ)^27
        have hw : |(4901287117/10000000000 : ℝ)|=(4901287117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309080_s2_s2_22 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (540290737/2000000000 : ℝ)*x 0 + (399471439/625000000 : ℝ)*x 1 + (-1752577631/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540290737/2000000000 : ℝ)^35 ≤ (4582705902469/25000000000000 : ℝ)^27 := by
    have hnat : (540290737 : ℕ)^35*25000000000000^27 ≤ 4582705902469^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540290737 2000000000 4582705902469 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (399471439/625000000 : ℝ)^35 ≤ (27988357644799/50000000000000 : ℝ)^27 := by
    have hnat : (399471439 : ℕ)^35*50000000000000^27 ≤ 27988357644799^27*625000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      399471439 625000000 27988357644799 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1752577631/5000000000 : ℝ)^35 ≤ (12846230540683/50000000000000 : ℝ)^27 := by
    have hnat : (1752577631 : ℕ)^35*50000000000000^27 ≤ 12846230540683^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1752577631 5000000000 12846230540683 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(540290737/2000000000 : ℝ), (399471439/625000000 : ℝ), (-1752577631/5000000000 : ℝ)] ![(4582705902469/25000000000000 : ℝ), (27988357644799/50000000000000 : ℝ), (12846230540683/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(540290737/2000000000 : ℝ)|^35 ≤ (4582705902469/25000000000000 : ℝ)^27
        have hw : |(540290737/2000000000 : ℝ)|=(540290737/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(399471439/625000000 : ℝ)|^35 ≤ (27988357644799/50000000000000 : ℝ)^27
        have hw : |(399471439/625000000 : ℝ)|=(399471439/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1752577631/5000000000 : ℝ)|^35 ≤ (12846230540683/50000000000000 : ℝ)^27
        have hw : |(-1752577631/5000000000 : ℝ)|=(1752577631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309080_s2_s2_25 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2387948627/5000000000 : ℝ)*x 0 + (563357923/1250000000 : ℝ)*x 1 + (885512241/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2387948627/5000000000 : ℝ)^35 ≤ (38367204140511/100000000000000 : ℝ)^27 := by
    have hnat : (2387948627 : ℕ)^35*100000000000000^27 ≤ 38367204140511^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2387948627 5000000000 38367204140511 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (563357923/1250000000 : ℝ)^35 ≤ (142356941797/400000000000 : ℝ)^27 := by
    have hnat : (563357923 : ℕ)^35*400000000000^27 ≤ 142356941797^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563357923 1250000000 142356941797 400000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (885512241/2500000000 : ℝ)^35 ≤ (6510890100081/25000000000000 : ℝ)^27 := by
    have hnat : (885512241 : ℕ)^35*25000000000000^27 ≤ 6510890100081^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      885512241 2500000000 6510890100081 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2387948627/5000000000 : ℝ), (563357923/1250000000 : ℝ), (885512241/2500000000 : ℝ)] ![(38367204140511/100000000000000 : ℝ), (142356941797/400000000000 : ℝ), (6510890100081/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2387948627/5000000000 : ℝ)|^35 ≤ (38367204140511/100000000000000 : ℝ)^27
        have hw : |(2387948627/5000000000 : ℝ)|=(2387948627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(563357923/1250000000 : ℝ)|^35 ≤ (142356941797/400000000000 : ℝ)^27
        have hw : |(563357923/1250000000 : ℝ)|=(563357923/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(885512241/2500000000 : ℝ)|^35 ≤ (6510890100081/25000000000000 : ℝ)^27
        have hw : |(885512241/2500000000 : ℝ)|=(885512241/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c309080_s2 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((31667/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(31667/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((4629/20000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(4629/20000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(17727/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(17727/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((1123/5000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1123/5000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1493/50000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(1493/50000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(27407/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(27407/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (77509/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (77509/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (77509/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (77509/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (77509/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (77509/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
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
  have s2_pow0 : (31667/50000 : ℝ) ^ (69/16 : ℝ) ≤ (6974759097814924487/50000000000000000000 : ℝ) := by
    have hpowers : (31667/50000 : ℝ)^69 ≤ (6974759097814924487/50000000000000000000 : ℝ)^16 := by
      have hnat : (31667 : ℕ)^69*50000000000000000000^16 ≤ 6974759097814924487^16*50000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31667 50000 6974759097814924487 50000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (31667/50000 : ℝ)) (X := (6974759097814924487/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s2_corner0a : (56974759097814924487/50000000000000000000 : ℝ) ≤ (6442148629829/6250000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (56974759097814924487/50000000000000000000 : ℝ)^16 ≤ (6442148629829/6250000000000 : ℝ)^69 := by
      have hnat : (56974759097814924487 : ℕ)^16*6250000000000^69 ≤ 6442148629829^69*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        56974759097814924487 50000000000000000000 6442148629829 6250000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6442148629829/6250000000000 : ℝ)) (X := (56974759097814924487/50000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s2_corner0b : (31974759097814924487/25000000000000000000 : ℝ) ≤ (10587192674487687/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (31974759097814924487/25000000000000000000 : ℝ)^16 ≤ (10587192674487687/10000000000000000 : ℝ)^69 := by
      have hnat : (31974759097814924487 : ℕ)^16*10000000000000000^69 ≤ 10587192674487687^69*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31974759097814924487 25000000000000000000 10587192674487687 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10587192674487687/10000000000000000 : ℝ)) (X := (31974759097814924487/25000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(192148629829/3958375000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(279754866761287/6333400000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (31667/50000 : ℝ)) (alpha := (192148629829/3958375000000 : ℝ)) (beta := (279754866761287/6333400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (31667/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(192148629829/3958375000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(279754866761287/6333400000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (4629/20000 : ℝ) ^ (69/16 : ℝ) ≤ (36328846329679611/20000000000000000000 : ℝ) := by
    have hpowers : (4629/20000 : ℝ)^69 ≤ (36328846329679611/20000000000000000000 : ℝ)^16 := by
      have hnat : (4629 : ℕ)^69*20000000000000000000^16 ≤ 36328846329679611^16*20000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4629 20000 36328846329679611 20000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4629/20000 : ℝ)) (X := (36328846329679611/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s2_corner1a : (20036328846329679611/20000000000000000000 : ℝ) ≤ (10004209104896077/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (20036328846329679611/20000000000000000000 : ℝ)^16 ≤ (10004209104896077/10000000000000000 : ℝ)^69 := by
      have hnat : (20036328846329679611 : ℕ)^16*10000000000000000^69 ≤ 10004209104896077^69*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20036328846329679611 20000000000000000000 10004209104896077 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004209104896077/10000000000000000 : ℝ)) (X := (20036328846329679611/20000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s2_corner1b : (10036328846329679611/10000000000000000000 : ℝ) ≤ (10008412351811611/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (10036328846329679611/10000000000000000000 : ℝ)^16 ≤ (10008412351811611/10000000000000000 : ℝ)^69 := by
      have hnat : (10036328846329679611 : ℕ)^16*10000000000000000^69 ≤ 10008412351811611^69*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10036328846329679611 10000000000000000000 10008412351811611 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10008412351811611/10000000000000000 : ℝ)) (X := (10036328846329679611/10000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1403034965359/771500000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(700541152589/385750000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (4629/20000 : ℝ)) (alpha := (1403034965359/771500000000000 : ℝ)) (beta := (700541152589/385750000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (4629/20000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1403034965359/771500000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(700541152589/385750000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (17727/25000 : ℝ) ^ (69/16 : ℝ) ≤ (1135254441552887071/5000000000000000000 : ℝ) := by
    have hpowers : (17727/25000 : ℝ)^69 ≤ (1135254441552887071/5000000000000000000 : ℝ)^16 := by
      have hnat : (17727 : ℕ)^69*5000000000000000000^16 ≤ 1135254441552887071^16*25000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17727 25000 1135254441552887071 5000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17727/25000 : ℝ)) (X := (1135254441552887071/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s2_corner2a : (6135254441552887071/5000000000000000000 : ℝ) ≤ (5242951238683017/5000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (6135254441552887071/5000000000000000000 : ℝ)^16 ≤ (5242951238683017/5000000000000000 : ℝ)^69 := by
      have hnat : (6135254441552887071 : ℕ)^16*5000000000000000^69 ≤ 5242951238683017^69*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6135254441552887071 5000000000000000000 5242951238683017 5000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5242951238683017/5000000000000000 : ℝ)) (X := (6135254441552887071/5000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s2_corner2b : (3635254441552887071/2500000000000000000 : ℝ) ≤ (2726736375953241/2500000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (3635254441552887071/2500000000000000000 : ℝ)^16 ≤ (2726736375953241/2500000000000000 : ℝ)^69 := by
      have hnat : (3635254441552887071 : ℕ)^16*2500000000000000^69 ≤ 2726736375953241^69*2500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3635254441552887071 2500000000000000000 2726736375953241 2500000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2726736375953241/2500000000000000 : ℝ)) (X := (3635254441552887071/2500000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(242951238683017/3545400000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(14034767548231/236360000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (17727/25000 : ℝ)) (alpha := (242951238683017/3545400000000000 : ℝ)) (beta := (14034767548231/236360000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (17727/25000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(242951238683017/3545400000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(14034767548231/236360000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-174736117/500000000 : ℝ)*X 0 0+(1090231811/2000000000 : ℝ)*X 0 1+(3834525409/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309080_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((409318127/1250000000 : ℝ)*X 2 0+(5853615819/10000000000 : ℝ)*X 2 1+(-3592939537/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309080_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((4127744629/10000000000 : ℝ)*X 0 0+(4925201303/10000000000 : ℝ)*X 0 1+(3777869323/10000000000 : ℝ)*X 0 2+(4127744629/10000000000 : ℝ)*X 1 0+(4925201303/10000000000 : ℝ)*X 1 1+(3777869323/10000000000 : ℝ)*X 1 2+(4127744629/10000000000 : ℝ)*X 2 0+(4925201303/10000000000 : ℝ)*X 2 1+(3777869323/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309080_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-223651167/625000000 : ℝ)*X 0 0+(1077668671/2000000000 : ℝ)*X 0 1+(3822403037/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309080_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((576384747/1000000000 : ℝ)*X 1 0+(-71341983/2000000000 : ℝ)*X 1 1+(2916284817/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309080_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((2943364941/10000000000 : ℝ)*X 2 0+(1299781327/2000000000 : ℝ)*X 2 1+(-1572024981/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309080_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_12 : ((3838538159/10000000000 : ℝ)*X 0 0+(5097082393/10000000000 : ℝ)*X 0 1+(3884304923/10000000000 : ℝ)*X 0 2+(3838538159/10000000000 : ℝ)*X 1 0+(5097082393/10000000000 : ℝ)*X 1 1+(3884304923/10000000000 : ℝ)*X 1 2+(3838538159/10000000000 : ℝ)*X 2 0+(5097082393/10000000000 : ℝ)*X 2 1+(3884304923/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309080_s2_s2_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((-740781499/2000000000 : ℝ)*X 0 0+(136217739/250000000 : ℝ)*X 0 1+(3630319957/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309080_s2_s2_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((1441136791/2500000000 : ℝ)*X 1 0+(-481671399/5000000000 : ℝ)*X 1 1+(2756815171/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309080_s2_s2_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((3085043107/10000000000 : ℝ)*X 2 0+(5832250391/10000000000 : ℝ)*X 2 1+(-759730821/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309080_s2_s2_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_19 : ((88415289/200000000 : ℝ)*X 0 0+(1208509719/2500000000 : ℝ)*X 0 1+(892645397/2500000000 : ℝ)*X 0 2+(88415289/200000000 : ℝ)*X 1 0+(1208509719/2500000000 : ℝ)*X 1 1+(892645397/2500000000 : ℝ)*X 1 2+(88415289/200000000 : ℝ)*X 2 0+(1208509719/2500000000 : ℝ)*X 2 1+(892645397/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309080_s2_s2_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((-192555577/625000000 : ℝ)*X 0 0+(2829236683/5000000000 : ℝ)*X 0 1+(249842223/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309080_s2_s2_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((1652154157/2500000000 : ℝ)*X 1 0+(-464073283/10000000000 : ℝ)*X 1 1+(4901287117/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309080_s2_s2_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((540290737/2000000000 : ℝ)*X 2 0+(399471439/625000000 : ℝ)*X 2 1+(-1752577631/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309080_s2_s2_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_25 : ((2387948627/5000000000 : ℝ)*X 0 0+(563357923/1250000000 : ℝ)*X 0 1+(885512241/2500000000 : ℝ)*X 0 2+(2387948627/5000000000 : ℝ)*X 1 0+(563357923/1250000000 : ℝ)*X 1 1+(885512241/2500000000 : ℝ)*X 1 2+(2387948627/5000000000 : ℝ)*X 2 0+(563357923/1250000000 : ℝ)*X 2 1+(885512241/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309080_s2_s2_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((1123/5000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1123/5000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (14297627906885590563302027413/3609082844112500000000000000000000 : ℝ) := by norm_num
    linear_combination (104891/250000000000 : ℝ)*(base40) + (3348164151593/1000000000000 : ℝ)*(base49) + (44002610973/31250000000 : ℝ)*(base50) + (1225412761801/200000000000 : ℝ)*(major_s2_0) + (1225412761801/200000000000 : ℝ)*(major_s2_1) + (1225412761801/200000000000 : ℝ)*(major_s2_2) + (208629517/1000000000000 : ℝ)*(sp_s2_0) + (37653891/1000000000000 : ℝ)*(sp_s2_6) + (8406395385591/1000000000000 : ℝ)*(sp_s2_7) + (1050822378133/125000000000 : ℝ)*(sp_s2_8) + (8406546330437/1000000000000 : ℝ)*(sp_s2_9) + (1923742314239/500000000000 : ℝ)*(sp_s2_12) + (24990043/1000000000000 : ℝ)*(sp_s2_14) + (57684671/1000000000000 : ℝ)*(sp_s2_22) + (3847522282369/1000000000000 : ℝ)*(f.failure) + (8406604015107/1000000000000 : ℝ)*(f.sum) + (6731674592066725763/5470552200000000000000000000000 : ℝ)*base63 + (62434074884543/236360000000000000000000000 : ℝ)*base65 + (22379452788569/154300000000000000000000000 : ℝ)*base66 + (575396068951333/709080000000000000000000000 : ℝ)*base69 + (907679105178613051/7484812120000000000000000000000 : ℝ)*base70 + (265852939458439/253336000000000000000000000 : ℝ)*base73 + (24265606702929/19287500000000000000000000 : ℝ)*base75 + (10206485996271/158335000000000000000000000 : ℝ)*base76 + (1191838995886957079/9772436200000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base85 + (83857/100000000000000000 : ℝ)*base86 + (83857/100000000000000000 : ℝ)*base88 + (83857/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((1493/50000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(1493/50000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (303432237159407270926086593221/28872662752900000000000000000000000 : ℝ) := by norm_num
    linear_combination (230035248909/1000000000000 : ℝ)*(base40) + (538839774801/500000000000 : ℝ)*(base49) + (2544931/1000000000000 : ℝ)*(base60) + (724984768499/200000000000 : ℝ)*(major_s2_0) + (724984768499/200000000000 : ℝ)*(major_s2_1) + (724984768499/200000000000 : ℝ)*(major_s2_2) + (51857519/250000000000 : ℝ)*(sp_s2_6) + (757347/15625000000 : ℝ)*(sp_s2_7) + (8719979/250000000000 : ℝ)*(sp_s2_8) + (4973505519391/1000000000000 : ℝ)*(sp_s2_13) + (4973519109683/1000000000000 : ℝ)*(sp_s2_14) + (6216942487/1250000000 : ℝ)*(sp_s2_15) + (2275795319091/1000000000000 : ℝ)*(sp_s2_19) + (28744311/100000000000 : ℝ)*(sp_s2_25) + (2276290192277/1000000000000 : ℝ)*(f.failure) + (6216942487/1250000000 : ℝ)*(f.sum) + (2083146741342663097/5470552200000000000000000000000 : ℝ)*base63 + (5258910654279/236360000000000000000000000 : ℝ)*base64 + (27299938467889/154300000000000000000000000 : ℝ)*base67 + (16094137538891/28363200000000000000000000 : ℝ)*base69 + (136591887191150041/1496962424000000000000000000000 : ℝ)*base70 + (10761631336471/253336000000000000000000000 : ℝ)*base72 + (19317438263879/77150000000000000000000000 : ℝ)*base75 + (1113969372359/39583750000000000000000000 : ℝ)*base77 + (2767982767917588319/9772436200000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (35419/100000000000000000 : ℝ)*base87 + (35419/100000000000000000 : ℝ)*base89 + (35419/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(27407/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(27407/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (323492892311768838644832005939/36090828441125000000000000000000000 : ℝ) := by norm_num
    linear_combination (3307369/500000000000 : ℝ)*(base39) + (201681424171/250000000000 : ℝ)*(base40) + (1871909770131/500000000000 : ℝ)*(base49) + (1371607897451/1000000000000 : ℝ)*(base50) + (1810146343019/250000000000 : ℝ)*(major_s2_0) + (1810146343019/250000000000 : ℝ)*(major_s2_1) + (1810146343019/250000000000 : ℝ)*(major_s2_2) + (4035141/1000000000000 : ℝ)*(sp_s2_2) + (46506361/200000000000 : ℝ)*(sp_s2_9) + (16453101/250000000000 : ℝ)*(sp_s2_19) + (9934403690447/1000000000000 : ℝ)*(sp_s2_20) + (9934403690447/1000000000000 : ℝ)*(sp_s2_21) + (4967083561751/500000000000 : ℝ)*(sp_s2_22) + (4546698253529/1000000000000 : ℝ)*(sp_s2_25) + (4546764065933/1000000000000 : ℝ)*(f.failure) + (9934403690447/1000000000000 : ℝ)*(f.sum) + (4721488843311029033/6838190250000000000000000000000 : ℝ)*base62 + (14115896050189/59090000000000000000000000 : ℝ)*base64 + (23514585895971/192875000000000000000000000 : ℝ)*base66 + (190388841232747/886350000000000000000000000 : ℝ)*base68 + (166931614717183487/935601515000000000000000000000 : ℝ)*base70 + (105834290335223/395837500000000000000000000 : ℝ)*base72 + (462556906474039/385750000000000000000000000 : ℝ)*base74 + (156331589876797/158335000000000000000000000 : ℝ)*base76 + (1190837978131598189/3053886312500000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (32451/100000000000000000 : ℝ)*base87 + (32451/100000000000000000 : ℝ)*base89 + (32451/100000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((31667/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(31667/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((4629/20000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(4629/20000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(17727/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(17727/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((1123/5000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1123/5000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1493/50000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(1493/50000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(27407/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(27407/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c309080_s2 p hpa hpb X hX hprev1

#print axioms solution
