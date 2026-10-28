-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c302083_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:25:11.339215+00:00
-- url     : https://prove2.me/submissions/aa7a62f8-1f52-4f46-ae51-5b829aef0251

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
theorem collision_support_c302083_s1_s1_0 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-907395919/5000000000 : ℝ)*x 0 + (5078791749/10000000000 : ℝ)*x 1 + (5810007877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (907395919/5000000000 : ℝ)^131 ≤ (1045335471523/10000000000000 : ℝ)^99 := by
    have hnat : (907395919 : ℕ)^131*10000000000000^99 ≤ 1045335471523^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      907395919 5000000000 1045335471523 10000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5078791749/10000000000 : ℝ)^131 ≤ (20399647449767/50000000000000 : ℝ)^99 := by
    have hnat : (5078791749 : ℕ)^131*50000000000000^99 ≤ 20399647449767^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5078791749 10000000000 20399647449767 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5810007877/10000000000 : ℝ)^131 ≤ (6093418796579/12500000000000 : ℝ)^99 := by
    have hnat : (5810007877 : ℕ)^131*12500000000000^99 ≤ 6093418796579^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5810007877 10000000000 6093418796579 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-907395919/5000000000 : ℝ), (5078791749/10000000000 : ℝ), (5810007877/10000000000 : ℝ)] ![(1045335471523/10000000000000 : ℝ), (20399647449767/50000000000000 : ℝ), (6093418796579/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-907395919/5000000000 : ℝ)|^131 ≤ (1045335471523/10000000000000 : ℝ)^99
        have hw : |(-907395919/5000000000 : ℝ)|=(907395919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5078791749/10000000000 : ℝ)|^131 ≤ (20399647449767/50000000000000 : ℝ)^99
        have hw : |(5078791749/10000000000 : ℝ)|=(5078791749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5810007877/10000000000 : ℝ)|^131 ≤ (6093418796579/12500000000000 : ℝ)^99
        have hw : |(5810007877/10000000000 : ℝ)|=(5810007877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302083_s1_s1_2 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3586652459/10000000000 : ℝ)*x 0 + (1756474761/2500000000 : ℝ)*x 1 + (-244907609/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3586652459/10000000000 : ℝ)^131 ≤ (12874206986477/50000000000000 : ℝ)^99 := by
    have hnat : (3586652459 : ℕ)^131*50000000000000^99 ≤ 12874206986477^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3586652459 10000000000 12874206986477 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1756474761/2500000000 : ℝ)^131 ≤ (6268317783713/10000000000000 : ℝ)^99 := by
    have hnat : (1756474761 : ℕ)^131*10000000000000^99 ≤ 6268317783713^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1756474761 2500000000 6268317783713 10000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (244907609/1250000000 : ℝ)^131 ≤ (2892102043539/25000000000000 : ℝ)^99 := by
    have hnat : (244907609 : ℕ)^131*25000000000000^99 ≤ 2892102043539^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      244907609 1250000000 2892102043539 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3586652459/10000000000 : ℝ), (1756474761/2500000000 : ℝ), (-244907609/1250000000 : ℝ)] ![(12874206986477/50000000000000 : ℝ), (6268317783713/10000000000000 : ℝ), (2892102043539/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3586652459/10000000000 : ℝ)|^131 ≤ (12874206986477/50000000000000 : ℝ)^99
        have hw : |(3586652459/10000000000 : ℝ)|=(3586652459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1756474761/2500000000 : ℝ)|^131 ≤ (6268317783713/10000000000000 : ℝ)^99
        have hw : |(1756474761/2500000000 : ℝ)|=(1756474761/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-244907609/1250000000 : ℝ)|^131 ≤ (2892102043539/25000000000000 : ℝ)^99
        have hw : |(-244907609/1250000000 : ℝ)|=(244907609/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302083_s1_s1_6 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (649271267/2000000000 : ℝ)*x 0 + (4669605383/10000000000 : ℝ)*x 1 + (5090719561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (649271267/2000000000 : ℝ)^131 ≤ (2256647072493/10000000000000 : ℝ)^99 := by
    have hnat : (649271267 : ℕ)^131*10000000000000^99 ≤ 2256647072493^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      649271267 2000000000 2256647072493 10000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4669605383/10000000000 : ℝ)^131 ≤ (1825369752933/5000000000000 : ℝ)^99 := by
    have hnat : (4669605383 : ℕ)^131*5000000000000^99 ≤ 1825369752933^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4669605383 10000000000 1825369752933 5000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5090719561/10000000000 : ℝ)^131 ≤ (10231533551797/25000000000000 : ℝ)^99 := by
    have hnat : (5090719561 : ℕ)^131*25000000000000^99 ≤ 10231533551797^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5090719561 10000000000 10231533551797 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(649271267/2000000000 : ℝ), (4669605383/10000000000 : ℝ), (5090719561/10000000000 : ℝ)] ![(2256647072493/10000000000000 : ℝ), (1825369752933/5000000000000 : ℝ), (10231533551797/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(649271267/2000000000 : ℝ)|^131 ≤ (2256647072493/10000000000000 : ℝ)^99
        have hw : |(649271267/2000000000 : ℝ)|=(649271267/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4669605383/10000000000 : ℝ)|^131 ≤ (1825369752933/5000000000000 : ℝ)^99
        have hw : |(4669605383/10000000000 : ℝ)|=(4669605383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5090719561/10000000000 : ℝ)|^131 ≤ (10231533551797/25000000000000 : ℝ)^99
        have hw : |(5090719561/10000000000 : ℝ)|=(5090719561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302083_s1_s1_7 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2615980621/10000000000 : ℝ)*x 0 + (1711192819/5000000000 : ℝ)*x 1 + (3348994941/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2615980621/10000000000 : ℝ)^131 ≤ (16958802253493/100000000000000 : ℝ)^99 := by
    have hnat : (2615980621 : ℕ)^131*100000000000000^99 ≤ 16958802253493^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615980621 10000000000 16958802253493 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1711192819/5000000000 : ℝ)^131 ≤ (6049911425169/25000000000000 : ℝ)^99 := by
    have hnat : (1711192819 : ℕ)^131*25000000000000^99 ≤ 6049911425169^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1711192819 5000000000 6049911425169 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3348994941/5000000000 : ℝ)^131 ≤ (58841552033623/100000000000000 : ℝ)^99 := by
    have hnat : (3348994941 : ℕ)^131*100000000000000^99 ≤ 58841552033623^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3348994941 5000000000 58841552033623 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2615980621/10000000000 : ℝ), (1711192819/5000000000 : ℝ), (3348994941/5000000000 : ℝ)] ![(16958802253493/100000000000000 : ℝ), (6049911425169/25000000000000 : ℝ), (58841552033623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2615980621/10000000000 : ℝ)|^131 ≤ (16958802253493/100000000000000 : ℝ)^99
        have hw : |(-2615980621/10000000000 : ℝ)|=(2615980621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1711192819/5000000000 : ℝ)|^131 ≤ (6049911425169/25000000000000 : ℝ)^99
        have hw : |(1711192819/5000000000 : ℝ)|=(1711192819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3348994941/5000000000 : ℝ)|^131 ≤ (58841552033623/100000000000000 : ℝ)^99
        have hw : |(3348994941/5000000000 : ℝ)|=(3348994941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302083_s1_s1_8 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5620584001/10000000000 : ℝ)*x 0 + (46986839/10000000000 : ℝ)*x 1 + (6212169801/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5620584001/10000000000 : ℝ)^131 ≤ (46655485951483/100000000000000 : ℝ)^99 := by
    have hnat : (5620584001 : ℕ)^131*100000000000000^99 ≤ 46655485951483^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5620584001 10000000000 46655485951483 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (46986839/10000000000 : ℝ)^131 ≤ (41538776603/50000000000000 : ℝ)^99 := by
    have hnat : (46986839 : ℕ)^131*50000000000000^99 ≤ 41538776603^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46986839 10000000000 41538776603 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6212169801/10000000000 : ℝ)^131 ≤ (13315359121989/25000000000000 : ℝ)^99 := by
    have hnat : (6212169801 : ℕ)^131*25000000000000^99 ≤ 13315359121989^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6212169801 10000000000 13315359121989 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5620584001/10000000000 : ℝ), (46986839/10000000000 : ℝ), (6212169801/10000000000 : ℝ)] ![(46655485951483/100000000000000 : ℝ), (41538776603/50000000000000 : ℝ), (13315359121989/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5620584001/10000000000 : ℝ)|^131 ≤ (46655485951483/100000000000000 : ℝ)^99
        have hw : |(5620584001/10000000000 : ℝ)|=(5620584001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(46986839/10000000000 : ℝ)|^131 ≤ (41538776603/50000000000000 : ℝ)^99
        have hw : |(46986839/10000000000 : ℝ)|=(46986839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6212169801/10000000000 : ℝ)|^131 ≤ (13315359121989/25000000000000 : ℝ)^99
        have hw : |(6212169801/10000000000 : ℝ)|=(6212169801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302083_s1_s1_9 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1268050397/10000000000 : ℝ)*x 0 + (8832100153/10000000000 : ℝ)*x 1 + (-393179687/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1268050397/10000000000 : ℝ)^131 ≤ (162622732811/2500000000000 : ℝ)^99 := by
    have hnat : (1268050397 : ℕ)^131*2500000000000^99 ≤ 162622732811^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1268050397 10000000000 162622732811 2500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8832100153/10000000000 : ℝ)^131 ≤ (84845755623757/100000000000000 : ℝ)^99 := by
    have hnat : (8832100153 : ℕ)^131*100000000000000^99 ≤ 84845755623757^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8832100153 10000000000 84845755623757 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (393179687/2500000000 : ℝ)^131 ≤ (2162333763661/25000000000000 : ℝ)^99 := by
    have hnat : (393179687 : ℕ)^131*25000000000000^99 ≤ 2162333763661^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      393179687 2500000000 2162333763661 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1268050397/10000000000 : ℝ), (8832100153/10000000000 : ℝ), (-393179687/2500000000 : ℝ)] ![(162622732811/2500000000000 : ℝ), (84845755623757/100000000000000 : ℝ), (2162333763661/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1268050397/10000000000 : ℝ)|^131 ≤ (162622732811/2500000000000 : ℝ)^99
        have hw : |(1268050397/10000000000 : ℝ)|=(1268050397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8832100153/10000000000 : ℝ)|^131 ≤ (84845755623757/100000000000000 : ℝ)^99
        have hw : |(8832100153/10000000000 : ℝ)|=(8832100153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-393179687/2500000000 : ℝ)|^131 ≤ (2162333763661/25000000000000 : ℝ)^99
        have hw : |(-393179687/2500000000 : ℝ)|=(393179687/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302083_s1_s1_13 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2613124201/10000000000 : ℝ)*x 0 + (25168733/40000000 : ℝ)*x 1 + (3913143941/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2613124201/10000000000 : ℝ)^131 ≤ (8467151801719/50000000000000 : ℝ)^99 := by
    have hnat : (2613124201 : ℕ)^131*50000000000000^99 ≤ 8467151801719^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613124201 10000000000 8467151801719 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (25168733/40000000 : ℝ)^131 ≤ (54171075640689/100000000000000 : ℝ)^99 := by
    have hnat : (25168733 : ℕ)^131*100000000000000^99 ≤ 54171075640689^99*40000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25168733 40000000 54171075640689 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3913143941/10000000000 : ℝ)^131 ≤ (722365518533/2500000000000 : ℝ)^99 := by
    have hnat : (3913143941 : ℕ)^131*2500000000000^99 ≤ 722365518533^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3913143941 10000000000 722365518533 2500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2613124201/10000000000 : ℝ), (25168733/40000000 : ℝ), (3913143941/10000000000 : ℝ)] ![(8467151801719/50000000000000 : ℝ), (54171075640689/100000000000000 : ℝ), (722365518533/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2613124201/10000000000 : ℝ)|^131 ≤ (8467151801719/50000000000000 : ℝ)^99
        have hw : |(2613124201/10000000000 : ℝ)|=(2613124201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(25168733/40000000 : ℝ)|^131 ≤ (54171075640689/100000000000000 : ℝ)^99
        have hw : |(25168733/40000000 : ℝ)|=(25168733/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3913143941/10000000000 : ℝ)|^131 ≤ (722365518533/2500000000000 : ℝ)^99
        have hw : |(3913143941/10000000000 : ℝ)|=(3913143941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302083_s1_s1_14 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-441450257/10000000000 : ℝ)*x 0 + (636997917/2500000000 : ℝ)*x 1 + (1076029711/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (441450257/10000000000 : ℝ)^131 ≤ (1610140453849/100000000000000 : ℝ)^99 := by
    have hnat : (441450257 : ℕ)^131*100000000000000^99 ≤ 1610140453849^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441450257 10000000000 1610140453849 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (636997917/2500000000 : ℝ)^131 ≤ (16378042911061/100000000000000 : ℝ)^99 := by
    have hnat : (636997917 : ℕ)^131*100000000000000^99 ≤ 16378042911061^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      636997917 2500000000 16378042911061 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1076029711/1250000000 : ℝ)^131 ≤ (82011816621341/100000000000000 : ℝ)^99 := by
    have hnat : (1076029711 : ℕ)^131*100000000000000^99 ≤ 82011816621341^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076029711 1250000000 82011816621341 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-441450257/10000000000 : ℝ), (636997917/2500000000 : ℝ), (1076029711/1250000000 : ℝ)] ![(1610140453849/100000000000000 : ℝ), (16378042911061/100000000000000 : ℝ), (82011816621341/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-441450257/10000000000 : ℝ)|^131 ≤ (1610140453849/100000000000000 : ℝ)^99
        have hw : |(-441450257/10000000000 : ℝ)|=(441450257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(636997917/2500000000 : ℝ)|^131 ≤ (16378042911061/100000000000000 : ℝ)^99
        have hw : |(636997917/2500000000 : ℝ)|=(636997917/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1076029711/1250000000 : ℝ)|^131 ≤ (82011816621341/100000000000000 : ℝ)^99
        have hw : |(1076029711/1250000000 : ℝ)|=(1076029711/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302083_s1_s1_15 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1822707023/2000000000 : ℝ)*x 0 + (49357/10000000000 : ℝ)*x 1 + (1957984439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1822707023/2000000000 : ℝ)^131 ≤ (88441554019681/100000000000000 : ℝ)^99 := by
    have hnat : (1822707023 : ℕ)^131*100000000000000^99 ≤ 88441554019681^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1822707023 2000000000 88441554019681 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (49357/10000000000 : ℝ)^131 ≤ (9507527/100000000000000 : ℝ)^99 := by
    have hnat : (49357 : ℕ)^131*100000000000000^99 ≤ 9507527^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49357 10000000000 9507527 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1957984439/10000000000 : ℝ)^131 ≤ (5779218231081/50000000000000 : ℝ)^99 := by
    have hnat : (1957984439 : ℕ)^131*50000000000000^99 ≤ 5779218231081^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1957984439 10000000000 5779218231081 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1822707023/2000000000 : ℝ), (49357/10000000000 : ℝ), (1957984439/10000000000 : ℝ)] ![(88441554019681/100000000000000 : ℝ), (9507527/100000000000000 : ℝ), (5779218231081/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1822707023/2000000000 : ℝ)|^131 ≤ (88441554019681/100000000000000 : ℝ)^99
        have hw : |(1822707023/2000000000 : ℝ)|=(1822707023/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(49357/10000000000 : ℝ)|^131 ≤ (9507527/100000000000000 : ℝ)^99
        have hw : |(49357/10000000000 : ℝ)|=(49357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1957984439/10000000000 : ℝ)|^131 ≤ (5779218231081/50000000000000 : ℝ)^99
        have hw : |(1957984439/10000000000 : ℝ)|=(1957984439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302083_s1_s1_16 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (163546369/312500000 : ℝ)*x 0 + (3051759399/5000000000 : ℝ)*x 1 + (-1119476677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (163546369/312500000 : ℝ)^131 ≤ (42451692448867/100000000000000 : ℝ)^99 := by
    have hnat : (163546369 : ℕ)^131*100000000000000^99 ≤ 42451692448867^99*312500000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163546369 312500000 42451692448867 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3051759399/5000000000 : ℝ)^131 ≤ (6504035714177/12500000000000 : ℝ)^99 := by
    have hnat : (3051759399 : ℕ)^131*12500000000000^99 ≤ 6504035714177^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3051759399 5000000000 6504035714177 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1119476677/10000000000 : ℝ)^131 ≤ (110320436341/2000000000000 : ℝ)^99 := by
    have hnat : (1119476677 : ℕ)^131*2000000000000^99 ≤ 110320436341^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119476677 10000000000 110320436341 2000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(163546369/312500000 : ℝ), (3051759399/5000000000 : ℝ), (-1119476677/10000000000 : ℝ)] ![(42451692448867/100000000000000 : ℝ), (6504035714177/12500000000000 : ℝ), (110320436341/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(163546369/312500000 : ℝ)|^131 ≤ (42451692448867/100000000000000 : ℝ)^99
        have hw : |(163546369/312500000 : ℝ)|=(163546369/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3051759399/5000000000 : ℝ)|^131 ≤ (6504035714177/12500000000000 : ℝ)^99
        have hw : |(3051759399/5000000000 : ℝ)|=(3051759399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1119476677/10000000000 : ℝ)|^131 ≤ (110320436341/2000000000000 : ℝ)^99
        have hw : |(-1119476677/10000000000 : ℝ)|=(1119476677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302083_s1_s1_20 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2881653397/10000000000 : ℝ)*x 0 + (1522973903/5000000000 : ℝ)*x 1 + (679602843/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2881653397/10000000000 : ℝ)^131 ≤ (602324473839/3125000000000 : ℝ)^99 := by
    have hnat : (2881653397 : ℕ)^131*3125000000000^99 ≤ 602324473839^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2881653397 10000000000 602324473839 3125000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1522973903/5000000000 : ℝ)^131 ≤ (10370862395737/50000000000000 : ℝ)^99 := by
    have hnat : (1522973903 : ℕ)^131*50000000000000^99 ≤ 10370862395737^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1522973903 5000000000 10370862395737 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (679602843/1000000000 : ℝ)^131 ≤ (7497986504151/12500000000000 : ℝ)^99 := by
    have hnat : (679602843 : ℕ)^131*12500000000000^99 ≤ 7497986504151^99*1000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679602843 1000000000 7497986504151 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2881653397/10000000000 : ℝ), (1522973903/5000000000 : ℝ), (679602843/1000000000 : ℝ)] ![(602324473839/3125000000000 : ℝ), (10370862395737/50000000000000 : ℝ), (7497986504151/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2881653397/10000000000 : ℝ)|^131 ≤ (602324473839/3125000000000 : ℝ)^99
        have hw : |(2881653397/10000000000 : ℝ)|=(2881653397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1522973903/5000000000 : ℝ)|^131 ≤ (10370862395737/50000000000000 : ℝ)^99
        have hw : |(1522973903/5000000000 : ℝ)|=(1522973903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(679602843/1000000000 : ℝ)|^131 ≤ (7497986504151/12500000000000 : ℝ)^99
        have hw : |(679602843/1000000000 : ℝ)|=(679602843/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302083_s1_s1_21 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-350918509/2500000000 : ℝ)*x 0 + (135099389/200000000 : ℝ)*x 1 + (2165891001/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (350918509/2500000000 : ℝ)^131 ≤ (1860266519103/25000000000000 : ℝ)^99 := by
    have hnat : (350918509 : ℕ)^131*25000000000000^99 ≤ 1860266519103^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      350918509 2500000000 1860266519103 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (135099389/200000000 : ℝ)^131 ≤ (11900964430009/20000000000000 : ℝ)^99 := by
    have hnat : (135099389 : ℕ)^131*20000000000000^99 ≤ 11900964430009^99*200000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135099389 200000000 11900964430009 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2165891001/5000000000 : ℝ)^131 ≤ (33054111756809/100000000000000 : ℝ)^99 := by
    have hnat : (2165891001 : ℕ)^131*100000000000000^99 ≤ 33054111756809^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2165891001 5000000000 33054111756809 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-350918509/2500000000 : ℝ), (135099389/200000000 : ℝ), (2165891001/5000000000 : ℝ)] ![(1860266519103/25000000000000 : ℝ), (11900964430009/20000000000000 : ℝ), (33054111756809/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-350918509/2500000000 : ℝ)|^131 ≤ (1860266519103/25000000000000 : ℝ)^99
        have hw : |(-350918509/2500000000 : ℝ)|=(350918509/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(135099389/200000000 : ℝ)|^131 ≤ (11900964430009/20000000000000 : ℝ)^99
        have hw : |(135099389/200000000 : ℝ)|=(135099389/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2165891001/5000000000 : ℝ)|^131 ≤ (33054111756809/100000000000000 : ℝ)^99
        have hw : |(2165891001/5000000000 : ℝ)|=(2165891001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302083_s1_s1_22 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (8784495167/10000000000 : ℝ)*x 0 + (478157/2500000000 : ℝ)*x 1 + (494941807/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8784495167/10000000000 : ℝ)^131 ≤ (84241145054791/100000000000000 : ℝ)^99 := by
    have hnat : (8784495167 : ℕ)^131*100000000000000^99 ≤ 84241145054791^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8784495167 10000000000 84241145054791 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (478157/2500000000 : ℝ)^131 ≤ (1201526353/100000000000000 : ℝ)^99 := by
    have hnat : (478157 : ℕ)^131*100000000000000^99 ≤ 1201526353^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      478157 2500000000 1201526353 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (494941807/2000000000 : ℝ)^131 ≤ (15757653411017/100000000000000 : ℝ)^99 := by
    have hnat : (494941807 : ℕ)^131*100000000000000^99 ≤ 15757653411017^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      494941807 2000000000 15757653411017 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8784495167/10000000000 : ℝ), (478157/2500000000 : ℝ), (494941807/2000000000 : ℝ)] ![(84241145054791/100000000000000 : ℝ), (1201526353/100000000000000 : ℝ), (15757653411017/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8784495167/10000000000 : ℝ)|^131 ≤ (84241145054791/100000000000000 : ℝ)^99
        have hw : |(8784495167/10000000000 : ℝ)|=(8784495167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(478157/2500000000 : ℝ)|^131 ≤ (1201526353/100000000000000 : ℝ)^99
        have hw : |(478157/2500000000 : ℝ)|=(478157/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(494941807/2000000000 : ℝ)|^131 ≤ (15757653411017/100000000000000 : ℝ)^99
        have hw : |(494941807/2000000000 : ℝ)|=(494941807/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302083_s1_s1_23 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1940606977/10000000000 : ℝ)*x 0 + (1634706681/2000000000 : ℝ)*x 1 + (-503569459/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1940606977/10000000000 : ℝ)^131 ≤ (11422890163857/100000000000000 : ℝ)^99 := by
    have hnat : (1940606977 : ℕ)^131*100000000000000^99 ≤ 11422890163857^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1940606977 10000000000 11422890163857 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1634706681/2000000000 : ℝ)^131 ≤ (76576915947271/100000000000000 : ℝ)^99 := by
    have hnat : (1634706681 : ℕ)^131*100000000000000^99 ≤ 76576915947271^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1634706681 2000000000 76576915947271 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (503569459/2500000000 : ℝ)^131 ≤ (12000193875957/100000000000000 : ℝ)^99 := by
    have hnat : (503569459 : ℕ)^131*100000000000000^99 ≤ 12000193875957^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      503569459 2500000000 12000193875957 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1940606977/10000000000 : ℝ), (1634706681/2000000000 : ℝ), (-503569459/2500000000 : ℝ)] ![(11422890163857/100000000000000 : ℝ), (76576915947271/100000000000000 : ℝ), (12000193875957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1940606977/10000000000 : ℝ)|^131 ≤ (11422890163857/100000000000000 : ℝ)^99
        have hw : |(1940606977/10000000000 : ℝ)|=(1940606977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1634706681/2000000000 : ℝ)|^131 ≤ (76576915947271/100000000000000 : ℝ)^99
        have hw : |(1634706681/2000000000 : ℝ)|=(1634706681/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-503569459/2500000000 : ℝ)|^131 ≤ (12000193875957/100000000000000 : ℝ)^99
        have hw : |(-503569459/2500000000 : ℝ)|=(503569459/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302083_s1_s1_27 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (6391820571/10000000000 : ℝ)*x 0 + (3542725209/10000000000 : ℝ)*x 1 + (578241693/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6391820571/10000000000 : ℝ)^131 ≤ (11061808877909/20000000000000 : ℝ)^99 := by
    have hnat : (6391820571 : ℕ)^131*20000000000000^99 ≤ 11061808877909^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6391820571 10000000000 11061808877909 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3542725209/10000000000 : ℝ)^131 ≤ (25331958642699/100000000000000 : ℝ)^99 := by
    have hnat : (3542725209 : ℕ)^131*100000000000000^99 ≤ 25331958642699^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3542725209 10000000000 25331958642699 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (578241693/2000000000 : ℝ)^131 ≤ (19358996948699/100000000000000 : ℝ)^99 := by
    have hnat : (578241693 : ℕ)^131*100000000000000^99 ≤ 19358996948699^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      578241693 2000000000 19358996948699 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6391820571/10000000000 : ℝ), (3542725209/10000000000 : ℝ), (578241693/2000000000 : ℝ)] ![(11061808877909/20000000000000 : ℝ), (25331958642699/100000000000000 : ℝ), (19358996948699/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6391820571/10000000000 : ℝ)|^131 ≤ (11061808877909/20000000000000 : ℝ)^99
        have hw : |(6391820571/10000000000 : ℝ)|=(6391820571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3542725209/10000000000 : ℝ)|^131 ≤ (25331958642699/100000000000000 : ℝ)^99
        have hw : |(3542725209/10000000000 : ℝ)|=(3542725209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(578241693/2000000000 : ℝ)|^131 ≤ (19358996948699/100000000000000 : ℝ)^99
        have hw : |(578241693/2000000000 : ℝ)|=(578241693/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c302083_s1 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((20617/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(20617/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((89901/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(89901/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18521/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(18521/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((66689/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(66689/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((8907/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(8907/12500 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(76309/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(76309/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4769/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4769/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4769/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4769/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4769/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4769/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (36753/20000 : ℝ) := by
    linarith only [f.Tcap]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base54 : ((-1 : ℝ)*N 2+(1 : ℝ)*P 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 2]
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (20617/25000 : ℝ) ^ (65/16 : ℝ) ≤ (45699315005611239867/100000000000000000000 : ℝ) := by
    have hpowers : (20617/25000 : ℝ)^65 ≤ (45699315005611239867/100000000000000000000 : ℝ)^16 := by
      have hnat : (20617 : ℕ)^65*100000000000000000000^16 ≤ 45699315005611239867^16*25000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20617 25000 45699315005611239867 100000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20617/25000 : ℝ)) (X := (45699315005611239867/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (145699315005611239867/100000000000000000000 : ℝ) ≤ (2194146848616479/2000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (145699315005611239867/100000000000000000000 : ℝ)^16 ≤ (2194146848616479/2000000000000000 : ℝ)^65 := by
      have hnat : (145699315005611239867 : ℕ)^16*2000000000000000^65 ≤ 2194146848616479^65*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        145699315005611239867 100000000000000000000 2194146848616479 2000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2194146848616479/2000000000000000 : ℝ)) (X := (145699315005611239867/100000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (95699315005611239867/50000000000000000000 : ℝ) ≤ (2933190939397401/2500000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (95699315005611239867/50000000000000000000 : ℝ)^16 ≤ (2933190939397401/2500000000000000 : ℝ)^65 := by
      have hnat : (95699315005611239867 : ℕ)^16*2500000000000000^65 ≤ 2933190939397401^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        95699315005611239867 50000000000000000000 2933190939397401 2500000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2933190939397401/2500000000000000 : ℝ)) (X := (95699315005611239867/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(194146848616479/1649360000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(762029514507209/8246800000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (20617/25000 : ℝ)) (alpha := (194146848616479/1649360000000000 : ℝ)) (beta := (762029514507209/8246800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (20617/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(194146848616479/1649360000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(762029514507209/8246800000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (89901/100000 : ℝ) ^ (65/16 : ℝ) ≤ (12977719066700618453/20000000000000000000 : ℝ) := by
    have hpowers : (89901/100000 : ℝ)^65 ≤ (12977719066700618453/20000000000000000000 : ℝ)^16 := by
      have hnat : (89901 : ℕ)^65*20000000000000000000^16 ≤ 12977719066700618453^16*100000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        89901 100000 12977719066700618453 20000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (89901/100000 : ℝ)) (X := (12977719066700618453/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (32977719066700618453/20000000000000000000 : ℝ) ≤ (11309992216557289/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (32977719066700618453/20000000000000000000 : ℝ)^16 ≤ (11309992216557289/10000000000000000 : ℝ)^65 := by
      have hnat : (32977719066700618453 : ℕ)^16*10000000000000000^65 ≤ 11309992216557289^65*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        32977719066700618453 20000000000000000000 11309992216557289 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11309992216557289/10000000000000000 : ℝ)) (X := (32977719066700618453/20000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (22977719066700618453/10000000000000000000 : ℝ) ≤ (12272614336369241/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (22977719066700618453/10000000000000000000 : ℝ)^16 ≤ (12272614336369241/10000000000000000 : ℝ)^65 := by
      have hnat : (22977719066700618453 : ℕ)^16*10000000000000000^65 ≤ 12272614336369241^65*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22977719066700618453 10000000000000000000 12272614336369241 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12272614336369241/10000000000000000 : ℝ)) (X := (22977719066700618453/10000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(436664072185763/2996700000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(60163882488247/561881250000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (89901/100000 : ℝ)) (alpha := (436664072185763/2996700000000000 : ℝ)) (beta := (60163882488247/561881250000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (89901/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(436664072185763/2996700000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(60163882488247/561881250000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (18521/20000 : ℝ) ^ (65/16 : ℝ) ≤ (14638021888065049697/20000000000000000000 : ℝ) := by
    have hpowers : (18521/20000 : ℝ)^65 ≤ (14638021888065049697/20000000000000000000 : ℝ)^16 := by
      have hnat : (18521 : ℕ)^65*20000000000000000000^16 ≤ 14638021888065049697^16*20000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18521 20000 14638021888065049697 20000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18521/20000 : ℝ)) (X := (14638021888065049697/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (34638021888065049697/20000000000000000000 : ℝ) ≤ (11447571774730497/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (34638021888065049697/20000000000000000000 : ℝ)^16 ≤ (11447571774730497/10000000000000000 : ℝ)^65 := by
      have hnat : (34638021888065049697 : ℕ)^16*10000000000000000^65 ≤ 11447571774730497^65*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        34638021888065049697 20000000000000000000 11447571774730497 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11447571774730497/10000000000000000 : ℝ)) (X := (34638021888065049697/20000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (24638021888065049697/10000000000000000000 : ℝ) ≤ (6242596826051591/5000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (24638021888065049697/10000000000000000000 : ℝ)^16 ≤ (6242596826051591/5000000000000000 : ℝ)^65 := by
      have hnat : (24638021888065049697 : ℕ)^16*5000000000000000^65 ≤ 6242596826051591^65*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24638021888065049697 10000000000000000000 6242596826051591 5000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6242596826051591/5000000000000000 : ℝ)) (X := (24638021888065049697/10000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1447571774730497/9260500000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(207524375474537/1852100000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (18521/20000 : ℝ)) (alpha := (1447571774730497/9260500000000000 : ℝ)) (beta := (207524375474537/1852100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (18521/20000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1447571774730497/9260500000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(207524375474537/1852100000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-907395919/5000000000 : ℝ)*X 0 0+(5078791749/10000000000 : ℝ)*X 0 1+(5810007877/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302083_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((3586652459/10000000000 : ℝ)*X 2 0+(1756474761/2500000000 : ℝ)*X 2 1+(-244907609/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302083_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((649271267/2000000000 : ℝ)*X 0 0+(4669605383/10000000000 : ℝ)*X 0 1+(5090719561/10000000000 : ℝ)*X 0 2+(649271267/2000000000 : ℝ)*X 1 0+(4669605383/10000000000 : ℝ)*X 1 1+(5090719561/10000000000 : ℝ)*X 1 2+(649271267/2000000000 : ℝ)*X 2 0+(4669605383/10000000000 : ℝ)*X 2 1+(5090719561/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302083_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-2615980621/10000000000 : ℝ)*X 0 0+(1711192819/5000000000 : ℝ)*X 0 1+(3348994941/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302083_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((5620584001/10000000000 : ℝ)*X 1 0+(46986839/10000000000 : ℝ)*X 1 1+(6212169801/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302083_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((1268050397/10000000000 : ℝ)*X 2 0+(8832100153/10000000000 : ℝ)*X 2 1+(-393179687/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302083_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((2613124201/10000000000 : ℝ)*X 0 0+(25168733/40000000 : ℝ)*X 0 1+(3913143941/10000000000 : ℝ)*X 0 2+(2613124201/10000000000 : ℝ)*X 1 0+(25168733/40000000 : ℝ)*X 1 1+(3913143941/10000000000 : ℝ)*X 1 2+(2613124201/10000000000 : ℝ)*X 2 0+(25168733/40000000 : ℝ)*X 2 1+(3913143941/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302083_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-441450257/10000000000 : ℝ)*X 0 0+(636997917/2500000000 : ℝ)*X 0 1+(1076029711/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302083_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((1822707023/2000000000 : ℝ)*X 1 0+(49357/10000000000 : ℝ)*X 1 1+(1957984439/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302083_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((163546369/312500000 : ℝ)*X 2 0+(3051759399/5000000000 : ℝ)*X 2 1+(-1119476677/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302083_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((2881653397/10000000000 : ℝ)*X 0 0+(1522973903/5000000000 : ℝ)*X 0 1+(679602843/1000000000 : ℝ)*X 0 2+(2881653397/10000000000 : ℝ)*X 1 0+(1522973903/5000000000 : ℝ)*X 1 1+(679602843/1000000000 : ℝ)*X 1 2+(2881653397/10000000000 : ℝ)*X 2 0+(1522973903/5000000000 : ℝ)*X 2 1+(679602843/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302083_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-350918509/2500000000 : ℝ)*X 0 0+(135099389/200000000 : ℝ)*X 0 1+(2165891001/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302083_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((8784495167/10000000000 : ℝ)*X 1 0+(478157/2500000000 : ℝ)*X 1 1+(494941807/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302083_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((1940606977/10000000000 : ℝ)*X 2 0+(1634706681/2000000000 : ℝ)*X 2 1+(-503569459/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302083_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((6391820571/10000000000 : ℝ)*X 0 0+(3542725209/10000000000 : ℝ)*X 0 1+(578241693/2000000000 : ℝ)*X 0 2+(6391820571/10000000000 : ℝ)*X 1 0+(3542725209/10000000000 : ℝ)*X 1 1+(578241693/2000000000 : ℝ)*X 1 2+(6391820571/10000000000 : ℝ)*X 2 0+(3542725209/10000000000 : ℝ)*X 2 1+(578241693/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302083_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((66689/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(66689/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (22473933073030983835554273/3818474570000000000000000000000 : ℝ) := by norm_num
    linear_combination (148145776129/200000000000 : ℝ)*(base7) + (714863/100000000000 : ℝ)*(base23) + (53974702317/200000000000 : ℝ)*(base49) + (74328569749/500000000000 : ℝ)*(base60) + (1953567044677/1000000000000 : ℝ)*(major_s1_0) + (1953567044677/1000000000000 : ℝ)*(major_s1_1) + (1953567044677/1000000000000 : ℝ)*(major_s1_2) + (972507/50000000000 : ℝ)*(sp_s1_0) + (124723/15625000000 : ℝ)*(sp_s1_6) + (1071873904313/500000000000 : ℝ)*(sp_s1_7) + (1071887016153/500000000000 : ℝ)*(sp_s1_8) + (535941720919/250000000000 : ℝ)*(sp_s1_9) + (1025172758859/500000000000 : ℝ)*(sp_s1_13) + (6773541/1000000000000 : ℝ)*(sp_s1_14) + (261924923869/200000000000 : ℝ)*(f.failure) + (1071887016153/500000000000 : ℝ)*(f.sum) + (329474944114214942101/832528210500000000000000000000000 : ℝ)*base62 + (902225792924029/1852100000000000000000000000 : ℝ)*base65 + (195838414740949/2996700000000000000000000000 : ℝ)*base66 + (1661632386333269/9260500000000000000000000000 : ℝ)*base69 + (70259315836631679347/152738982800000000000000000000000 : ℝ)*base71 + (4640777143684013/8246800000000000000000000000 : ℝ)*base73 + (328131539543099/2247525000000000000000000000 : ℝ)*base75 + (1102820339622939/1649360000000000000000000000 : ℝ)*base77 + (3552759553850893679/247131855600000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (127/2000000000000000 : ℝ)*base86 + (127/2000000000000000 : ℝ)*base88 + (127/2000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((8907/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(8907/12500 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (43008423078845520419077711805851/3814274247973000000000000000000000000 : ℝ) := by norm_num
    linear_combination (261454832951/500000000000 : ℝ)*(base7) + (5014803/250000000000 : ℝ)*(base33) + (469789758819/1000000000000 : ℝ)*(base40) + (24817388937/1000000000000 : ℝ)*(base49) + (173059/100000000000 : ℝ)*(base54) + (362276599447/1000000000000 : ℝ)*(base60) + (2025215094231/1000000000000 : ℝ)*(major_s1_0) + (2025235153443/1000000000000 : ℝ)*(major_s1_1) + (506308355713/250000000000 : ℝ)*(major_s1_2) + (2372489027251/1000000000000 : ℝ)*(sp_s1_14) + (9266820191/3906250000 : ℝ)*(sp_s1_15) + (2372467237449/1000000000000 : ℝ)*(sp_s1_16) + (940288570271/500000000000 : ℝ)*(sp_s1_20) + (162999143/1000000000000 : ℝ)*(sp_s1_22) + (1357669205231/1000000000000 : ℝ)*(f.failure) + (2372489027251/1000000000000 : ℝ)*(f.sum) + (70731007674219572569/138754701750000000000000000000000 : ℝ)*base63 + (110752748665081/463025000000000000000000000 : ℝ)*base65 + (308225873533717/998900000000000000000000000 : ℝ)*base66 + (2050975349921347/4630250000000000000000000000 : ℝ)*base69 + (82701339437937365963/152738982800000000000000000000000 : ℝ)*base70 + (1156554703517159/8246800000000000000000000000 : ℝ)*base73 + (456863318145467/749175000000000000000000000 : ℝ)*base75 + (29445149904101/329872000000000000000000000 : ℝ)*base77 + (10236965224527416819/16475457040000000000000000000000 : ℝ)*base79 + (827/10000000000000000 : ℝ)*base87 + (827/10000000000000000 : ℝ)*base89 + (10827/10000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(76309/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(76309/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (142160585356952640485109751/41188642600000000000000000000000 : ℝ) := by norm_num
    linear_combination (412978209193/500000000000 : ℝ)*(base7) + (369281/200000000000 : ℝ)*(base11) + (309156173471/1000000000000 : ℝ)*(base40) + (13781/62500000000 : ℝ)*(base49) + (91609/1000000000000 : ℝ)*(base50) + (2082104016593/1000000000000 : ℝ)*(major_s1_0) + (2082104016593/1000000000000 : ℝ)*(major_s1_1) + (2082104016593/1000000000000 : ℝ)*(major_s1_2) + (11277753/500000000000 : ℝ)*(sp_s1_2) + (34974453/1000000000000 : ℝ)*(sp_s1_9) + (226247270137/100000000000 : ℝ)*(sp_s1_21) + (90498981911/40000000000 : ℝ)*(sp_s1_22) + (282802127227/125000000000 : ℝ)*(sp_s1_23) + (88869965969/40000000000 : ℝ)*(sp_s1_27) + (34894818271/25000000000 : ℝ)*(f.failure) + (90498981911/40000000000 : ℝ)*(f.sum) + (157491173133035560591/832528210500000000000000000000000 : ℝ)*base63 + (650918941632809/1852100000000000000000000000 : ℝ)*base64 + (1458515451454091/2996700000000000000000000000 : ℝ)*base66 + (3300998192808279/9260500000000000000000000000 : ℝ)*base68 + (47790937024538303823/152738982800000000000000000000000 : ℝ)*base71 + (5233339416871063/8246800000000000000000000000 : ℝ)*base72 + (411166133196389/2247525000000000000000000000 : ℝ)*base74 + (52632387852961/1649360000000000000000000000 : ℝ)*base76 + (95204170740730275989/247131855600000000000000000000000 : ℝ)*base78 + (257/250000000000000 : ℝ)*base87 + (257/250000000000000 : ℝ)*base89 + (257/250000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((20617/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(20617/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((89901/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(89901/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18521/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(18521/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((66689/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(66689/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((8907/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(8907/12500 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(76309/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(76309/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c302083_s1 p hpa hpb X hX hprev0

#print axioms solution
