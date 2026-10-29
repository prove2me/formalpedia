-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c315057_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:55:57.357743+00:00
-- url     : https://prove2.me/submissions/963f106a-8c03-4a51-ac42-26d7c59f5c91

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
theorem collision_support_c315057_s1_s1_1 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3191382493/10000000000 : ℝ)*x 0 + (-3183702839/10000000000 : ℝ)*x 1 + (757267827/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3191382493/10000000000 : ℝ)^19 ≤ (23534585504943/100000000000000 : ℝ)^15 := by
    have hnat : (3191382493 : ℕ)^19*100000000000000^15 ≤ 23534585504943^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3191382493 10000000000 23534585504943 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3183702839/10000000000 : ℝ)^19 ≤ (4692574687493/20000000000000 : ℝ)^15 := by
    have hnat : (3183702839 : ℕ)^19*20000000000000^15 ≤ 4692574687493^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3183702839 10000000000 4692574687493 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (757267827/1250000000 : ℝ)^19 ≤ (26501270524161/50000000000000 : ℝ)^15 := by
    have hnat : (757267827 : ℕ)^19*50000000000000^15 ≤ 26501270524161^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      757267827 1250000000 26501270524161 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3191382493/10000000000 : ℝ), (-3183702839/10000000000 : ℝ), (757267827/1250000000 : ℝ)] ![(23534585504943/100000000000000 : ℝ), (4692574687493/20000000000000 : ℝ), (26501270524161/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3191382493/10000000000 : ℝ)|^19 ≤ (23534585504943/100000000000000 : ℝ)^15
        have hw : |(3191382493/10000000000 : ℝ)|=(3191382493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3183702839/10000000000 : ℝ)|^19 ≤ (4692574687493/20000000000000 : ℝ)^15
        have hw : |(-3183702839/10000000000 : ℝ)|=(3183702839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(757267827/1250000000 : ℝ)|^19 ≤ (26501270524161/50000000000000 : ℝ)^15
        have hw : |(757267827/1250000000 : ℝ)|=(757267827/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315057_s1_s1_2 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2846939117/5000000000 : ℝ)*x 0 + (5705528763/10000000000 : ℝ)*x 1 + (-108307929/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2846939117/5000000000 : ℝ)^19 ≤ (24499300977321/50000000000000 : ℝ)^15 := by
    have hnat : (2846939117 : ℕ)^19*50000000000000^15 ≤ 24499300977321^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2846939117 5000000000 24499300977321 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5705528763/10000000000 : ℝ)^19 ≤ (49125630670977/100000000000000 : ℝ)^15 := by
    have hnat : (5705528763 : ℕ)^19*100000000000000^15 ≤ 49125630670977^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5705528763 10000000000 49125630670977 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (108307929/2500000000 : ℝ)^19 ≤ (1875767359489/100000000000000 : ℝ)^15 := by
    have hnat : (108307929 : ℕ)^19*100000000000000^15 ≤ 1875767359489^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108307929 2500000000 1875767359489 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2846939117/5000000000 : ℝ), (5705528763/10000000000 : ℝ), (-108307929/2500000000 : ℝ)] ![(24499300977321/50000000000000 : ℝ), (49125630670977/100000000000000 : ℝ), (1875767359489/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2846939117/5000000000 : ℝ)|^19 ≤ (24499300977321/50000000000000 : ℝ)^15
        have hw : |(2846939117/5000000000 : ℝ)|=(2846939117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5705528763/10000000000 : ℝ)|^19 ≤ (49125630670977/100000000000000 : ℝ)^15
        have hw : |(5705528763/10000000000 : ℝ)|=(5705528763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-108307929/2500000000 : ℝ)|^19 ≤ (1875767359489/100000000000000 : ℝ)^15
        have hw : |(-108307929/2500000000 : ℝ)|=(108307929/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315057_s1_s1_6 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2285597293/5000000000 : ℝ)*x 0 + (4580547937/10000000000 : ℝ)*x 1 + (10692159/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2285597293/5000000000 : ℝ)^19 ≤ (37099748396199/100000000000000 : ℝ)^15 := by
    have hnat : (2285597293 : ℕ)^19*100000000000000^15 ≤ 37099748396199^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2285597293 5000000000 37099748396199 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4580547937/10000000000 : ℝ)^19 ≤ (37195929385247/100000000000000 : ℝ)^15 := by
    have hnat : (4580547937 : ℕ)^19*100000000000000^15 ≤ 37195929385247^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4580547937 10000000000 37195929385247 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (10692159/31250000 : ℝ)^19 ≤ (25704322206813/100000000000000 : ℝ)^15 := by
    have hnat : (10692159 : ℕ)^19*100000000000000^15 ≤ 25704322206813^15*31250000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10692159 31250000 25704322206813 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2285597293/5000000000 : ℝ), (4580547937/10000000000 : ℝ), (10692159/31250000 : ℝ)] ![(37099748396199/100000000000000 : ℝ), (37195929385247/100000000000000 : ℝ), (25704322206813/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2285597293/5000000000 : ℝ)|^19 ≤ (37099748396199/100000000000000 : ℝ)^15
        have hw : |(2285597293/5000000000 : ℝ)|=(2285597293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4580547937/10000000000 : ℝ)|^19 ≤ (37195929385247/100000000000000 : ℝ)^15
        have hw : |(4580547937/10000000000 : ℝ)|=(4580547937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(10692159/31250000 : ℝ)|^19 ≤ (25704322206813/100000000000000 : ℝ)^15
        have hw : |(10692159/31250000 : ℝ)|=(10692159/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315057_s1_s1_7 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1507748279/5000000000 : ℝ)*x 0 + (2784268711/10000000000 : ℝ)*x 1 + (261244377/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1507748279/5000000000 : ℝ)^19 ≤ (10951943583997/50000000000000 : ℝ)^15 := by
    have hnat : (1507748279 : ℕ)^19*50000000000000^15 ≤ 10951943583997^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1507748279 5000000000 10951943583997 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2784268711/10000000000 : ℝ)^19 ≤ (309352867099/1562500000000 : ℝ)^15 := by
    have hnat : (2784268711 : ℕ)^19*1562500000000^15 ≤ 309352867099^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2784268711 10000000000 309352867099 1562500000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (261244377/400000000 : ℝ)^19 ≤ (58297529325051/100000000000000 : ℝ)^15 := by
    have hnat : (261244377 : ℕ)^19*100000000000000^15 ≤ 58297529325051^15*400000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261244377 400000000 58297529325051 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1507748279/5000000000 : ℝ), (2784268711/10000000000 : ℝ), (261244377/400000000 : ℝ)] ![(10951943583997/50000000000000 : ℝ), (309352867099/1562500000000 : ℝ), (58297529325051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1507748279/5000000000 : ℝ)|^19 ≤ (10951943583997/50000000000000 : ℝ)^15
        have hw : |(-1507748279/5000000000 : ℝ)|=(1507748279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2784268711/10000000000 : ℝ)|^19 ≤ (309352867099/1562500000000 : ℝ)^15
        have hw : |(2784268711/10000000000 : ℝ)|=(2784268711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(261244377/400000000 : ℝ)|^19 ≤ (58297529325051/100000000000000 : ℝ)^15
        have hw : |(261244377/400000000 : ℝ)|=(261244377/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315057_s1_s1_8 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (18807721/62500000 : ℝ)*x 0 + (-2778487621/10000000000 : ℝ)*x 1 + (1635201347/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (18807721/62500000 : ℝ)^19 ≤ (2730786901543/12500000000000 : ℝ)^15 := by
    have hnat : (18807721 : ℕ)^19*12500000000000^15 ≤ 2730786901543^15*62500000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18807721 62500000 2730786901543 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2778487621/10000000000 : ℝ)^19 ≤ (19746527021949/100000000000000 : ℝ)^15 := by
    have hnat : (2778487621 : ℕ)^19*100000000000000^15 ≤ 19746527021949^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2778487621 10000000000 19746527021949 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1635201347/2500000000 : ℝ)^19 ≤ (7300897219053/12500000000000 : ℝ)^15 := by
    have hnat : (1635201347 : ℕ)^19*12500000000000^15 ≤ 7300897219053^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1635201347 2500000000 7300897219053 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(18807721/62500000 : ℝ), (-2778487621/10000000000 : ℝ), (1635201347/2500000000 : ℝ)] ![(2730786901543/12500000000000 : ℝ), (19746527021949/100000000000000 : ℝ), (7300897219053/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(18807721/62500000 : ℝ)|^19 ≤ (2730786901543/12500000000000 : ℝ)^15
        have hw : |(18807721/62500000 : ℝ)|=(18807721/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2778487621/10000000000 : ℝ)|^19 ≤ (19746527021949/100000000000000 : ℝ)^15
        have hw : |(-2778487621/10000000000 : ℝ)|=(2778487621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1635201347/2500000000 : ℝ)|^19 ≤ (7300897219053/12500000000000 : ℝ)^15
        have hw : |(1635201347/2500000000 : ℝ)|=(1635201347/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315057_s1_s1_9 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2651203307/5000000000 : ℝ)*x 0 + (6258007829/10000000000 : ℝ)*x 1 + (-1664347/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651203307/5000000000 : ℝ)^19 ≤ (44771244789589/100000000000000 : ℝ)^15 := by
    have hnat : (2651203307 : ℕ)^19*100000000000000^15 ≤ 44771244789589^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651203307 5000000000 44771244789589 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6258007829/10000000000 : ℝ)^19 ≤ (27613559995647/50000000000000 : ℝ)^15 := by
    have hnat : (6258007829 : ℕ)^19*50000000000000^15 ≤ 27613559995647^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6258007829 10000000000 27613559995647 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1664347/10000000000 : ℝ)^19 ≤ (51100553/3125000000000 : ℝ)^15 := by
    have hnat : (1664347 : ℕ)^19*3125000000000^15 ≤ 51100553^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1664347 10000000000 51100553 3125000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651203307/5000000000 : ℝ), (6258007829/10000000000 : ℝ), (-1664347/10000000000 : ℝ)] ![(44771244789589/100000000000000 : ℝ), (27613559995647/50000000000000 : ℝ), (51100553/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651203307/5000000000 : ℝ)|^19 ≤ (44771244789589/100000000000000 : ℝ)^15
        have hw : |(2651203307/5000000000 : ℝ)|=(2651203307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6258007829/10000000000 : ℝ)|^19 ≤ (27613559995647/50000000000000 : ℝ)^15
        have hw : |(6258007829/10000000000 : ℝ)|=(6258007829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1664347/10000000000 : ℝ)|^19 ≤ (51100553/3125000000000 : ℝ)^15
        have hw : |(-1664347/10000000000 : ℝ)|=(1664347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315057_s1_s1_12 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4626684801/10000000000 : ℝ)*x 0 + (5460507241/10000000000 : ℝ)*x 1 + (73031691/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4626684801/10000000000 : ℝ)^19 ≤ (1506844886231/4000000000000 : ℝ)^15 := by
    have hnat : (4626684801 : ℕ)^19*4000000000000^15 ≤ 1506844886231^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4626684801 10000000000 1506844886231 4000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5460507241/10000000000 : ℝ)^19 ≤ (46468834931881/100000000000000 : ℝ)^15 := by
    have hnat : (5460507241 : ℕ)^19*100000000000000^15 ≤ 46468834931881^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5460507241 10000000000 46468834931881 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (73031691/312500000 : ℝ)^19 ≤ (15860042892659/100000000000000 : ℝ)^15 := by
    have hnat : (73031691 : ℕ)^19*100000000000000^15 ≤ 15860042892659^15*312500000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      73031691 312500000 15860042892659 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4626684801/10000000000 : ℝ), (5460507241/10000000000 : ℝ), (73031691/312500000 : ℝ)] ![(1506844886231/4000000000000 : ℝ), (46468834931881/100000000000000 : ℝ), (15860042892659/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4626684801/10000000000 : ℝ)|^19 ≤ (1506844886231/4000000000000 : ℝ)^15
        have hw : |(4626684801/10000000000 : ℝ)|=(4626684801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5460507241/10000000000 : ℝ)|^19 ≤ (46468834931881/100000000000000 : ℝ)^15
        have hw : |(5460507241/10000000000 : ℝ)|=(5460507241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(73031691/312500000 : ℝ)|^19 ≤ (15860042892659/100000000000000 : ℝ)^15
        have hw : |(73031691/312500000 : ℝ)|=(73031691/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315057_s1_s1_13 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-2791931179/10000000000 : ℝ)*x 0 + (300799011/1000000000 : ℝ)*x 1 + (6531109449/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2791931179/10000000000 : ℝ)^19 ≤ (19867625470323/100000000000000 : ℝ)^15 := by
    have hnat : (2791931179 : ℕ)^19*100000000000000^15 ≤ 19867625470323^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2791931179 10000000000 19867625470323 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (300799011/1000000000 : ℝ)^19 ≤ (10917422460081/50000000000000 : ℝ)^15 := by
    have hnat : (300799011 : ℕ)^19*50000000000000^15 ≤ 10917422460081^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      300799011 1000000000 10917422460081 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6531109449/10000000000 : ℝ)^19 ≤ (11659505919281/20000000000000 : ℝ)^15 := by
    have hnat : (6531109449 : ℕ)^19*20000000000000^15 ≤ 11659505919281^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6531109449 10000000000 11659505919281 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2791931179/10000000000 : ℝ), (300799011/1000000000 : ℝ), (6531109449/10000000000 : ℝ)] ![(19867625470323/100000000000000 : ℝ), (10917422460081/50000000000000 : ℝ), (11659505919281/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2791931179/10000000000 : ℝ)|^19 ≤ (19867625470323/100000000000000 : ℝ)^15
        have hw : |(-2791931179/10000000000 : ℝ)|=(2791931179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(300799011/1000000000 : ℝ)|^19 ≤ (10917422460081/50000000000000 : ℝ)^15
        have hw : |(300799011/1000000000 : ℝ)|=(300799011/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6531109449/10000000000 : ℝ)|^19 ≤ (11659505919281/20000000000000 : ℝ)^15
        have hw : |(6531109449/10000000000 : ℝ)|=(6531109449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315057_s1_s1_14 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (278613417/1000000000 : ℝ)*x 0 + (-375218061/1250000000 : ℝ)*x 1 + (6540805427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (278613417/1000000000 : ℝ)^19 ≤ (19815387383627/100000000000000 : ℝ)^15 := by
    have hnat : (278613417 : ℕ)^19*100000000000000^15 ≤ 19815387383627^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      278613417 1000000000 19815387383627 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (375218061/1250000000 : ℝ)^19 ≤ (1361089650383/6250000000000 : ℝ)^15 := by
    have hnat : (375218061 : ℕ)^19*6250000000000^15 ≤ 1361089650383^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      375218061 1250000000 1361089650383 6250000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6540805427/10000000000 : ℝ)^19 ≤ (58407178193549/100000000000000 : ℝ)^15 := by
    have hnat : (6540805427 : ℕ)^19*100000000000000^15 ≤ 58407178193549^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6540805427 10000000000 58407178193549 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(278613417/1000000000 : ℝ), (-375218061/1250000000 : ℝ), (6540805427/10000000000 : ℝ)] ![(19815387383627/100000000000000 : ℝ), (1361089650383/6250000000000 : ℝ), (58407178193549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(278613417/1000000000 : ℝ)|^19 ≤ (19815387383627/100000000000000 : ℝ)^15
        have hw : |(278613417/1000000000 : ℝ)|=(278613417/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-375218061/1250000000 : ℝ)|^19 ≤ (1361089650383/6250000000000 : ℝ)^15
        have hw : |(-375218061/1250000000 : ℝ)|=(375218061/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6540805427/10000000000 : ℝ)|^19 ≤ (58407178193549/100000000000000 : ℝ)^15
        have hw : |(6540805427/10000000000 : ℝ)|=(6540805427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315057_s1_s1_15 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (195208363/312500000 : ℝ)*x 0 + (5314252763/10000000000 : ℝ)*x 1 + (-832157/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (195208363/312500000 : ℝ)^19 ≤ (55100385491109/100000000000000 : ℝ)^15 := by
    have hnat : (195208363 : ℕ)^19*100000000000000^15 ≤ 55100385491109^15*312500000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      195208363 312500000 55100385491109 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5314252763/10000000000 : ℝ)^19 ≤ (2244898965883/5000000000000 : ℝ)^15 := by
    have hnat : (5314252763 : ℕ)^19*5000000000000^15 ≤ 2244898965883^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5314252763 10000000000 2244898965883 5000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (832157/5000000000 : ℝ)^19 ≤ (408794157/25000000000000 : ℝ)^15 := by
    have hnat : (832157 : ℕ)^19*25000000000000^15 ≤ 408794157^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      832157 5000000000 408794157 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(195208363/312500000 : ℝ), (5314252763/10000000000 : ℝ), (-832157/5000000000 : ℝ)] ![(55100385491109/100000000000000 : ℝ), (2244898965883/5000000000000 : ℝ), (408794157/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(195208363/312500000 : ℝ)|^19 ≤ (55100385491109/100000000000000 : ℝ)^15
        have hw : |(195208363/312500000 : ℝ)|=(195208363/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5314252763/10000000000 : ℝ)|^19 ≤ (2244898965883/5000000000000 : ℝ)^15
        have hw : |(5314252763/10000000000 : ℝ)|=(5314252763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-832157/5000000000 : ℝ)|^19 ≤ (408794157/25000000000000 : ℝ)^15
        have hw : |(-832157/5000000000 : ℝ)|=(832157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315057_s1_s1_18 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5450612193/10000000000 : ℝ)*x 0 + (4637021319/10000000000 : ℝ)*x 1 + (2337014099/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5450612193/10000000000 : ℝ)^19 ≤ (46362198881153/100000000000000 : ℝ)^15 := by
    have hnat : (5450612193 : ℕ)^19*100000000000000^15 ≤ 46362198881153^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5450612193 10000000000 46362198881153 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4637021319/10000000000 : ℝ)^19 ≤ (3777775832351/10000000000000 : ℝ)^15 := by
    have hnat : (4637021319 : ℕ)^19*10000000000000^15 ≤ 3777775832351^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4637021319 10000000000 3777775832351 10000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2337014099/10000000000 : ℝ)^19 ≤ (15860042780909/100000000000000 : ℝ)^15 := by
    have hnat : (2337014099 : ℕ)^19*100000000000000^15 ≤ 15860042780909^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2337014099 10000000000 15860042780909 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5450612193/10000000000 : ℝ), (4637021319/10000000000 : ℝ), (2337014099/10000000000 : ℝ)] ![(46362198881153/100000000000000 : ℝ), (3777775832351/10000000000000 : ℝ), (15860042780909/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5450612193/10000000000 : ℝ)|^19 ≤ (46362198881153/100000000000000 : ℝ)^15
        have hw : |(5450612193/10000000000 : ℝ)|=(5450612193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4637021319/10000000000 : ℝ)|^19 ≤ (3777775832351/10000000000000 : ℝ)^15
        have hw : |(4637021319/10000000000 : ℝ)|=(4637021319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2337014099/10000000000 : ℝ)|^19 ≤ (15860042780909/100000000000000 : ℝ)^15
        have hw : |(2337014099/10000000000 : ℝ)|=(2337014099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315057_s1_s1_19 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1855186347/5000000000 : ℝ)*x 0 + (545213209/2000000000 : ℝ)*x 1 + (5989278081/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1855186347/5000000000 : ℝ)^19 ≤ (5696728739749/20000000000000 : ℝ)^15 := by
    have hnat : (1855186347 : ℕ)^19*20000000000000^15 ≤ 5696728739749^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1855186347 5000000000 5696728739749 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (545213209/2000000000 : ℝ)^19 ≤ (9637907280457/50000000000000 : ℝ)^15 := by
    have hnat : (545213209 : ℕ)^19*50000000000000^15 ≤ 9637907280457^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545213209 2000000000 9637907280457 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5989278081/10000000000 : ℝ)^19 ≤ (52240541722933/100000000000000 : ℝ)^15 := by
    have hnat : (5989278081 : ℕ)^19*100000000000000^15 ≤ 52240541722933^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5989278081 10000000000 52240541722933 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1855186347/5000000000 : ℝ), (545213209/2000000000 : ℝ), (5989278081/10000000000 : ℝ)] ![(5696728739749/20000000000000 : ℝ), (9637907280457/50000000000000 : ℝ), (52240541722933/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1855186347/5000000000 : ℝ)|^19 ≤ (5696728739749/20000000000000 : ℝ)^15
        have hw : |(-1855186347/5000000000 : ℝ)|=(1855186347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(545213209/2000000000 : ℝ)|^19 ≤ (9637907280457/50000000000000 : ℝ)^15
        have hw : |(545213209/2000000000 : ℝ)|=(545213209/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5989278081/10000000000 : ℝ)|^19 ≤ (52240541722933/100000000000000 : ℝ)^15
        have hw : |(5989278081/10000000000 : ℝ)|=(5989278081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315057_s1_s1_20 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2728392427/10000000000 : ℝ)*x 0 + (-147888191/400000000 : ℝ)*x 1 + (1499743447/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2728392427/10000000000 : ℝ)^19 ≤ (9648326594889/50000000000000 : ℝ)^15 := by
    have hnat : (2728392427 : ℕ)^19*50000000000000^15 ≤ 9648326594889^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2728392427 10000000000 9648326594889 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (147888191/400000000 : ℝ)^19 ≤ (27691075051/97656250000 : ℝ)^15 := by
    have hnat : (147888191 : ℕ)^19*97656250000^15 ≤ 27691075051^15*400000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      147888191 400000000 27691075051 97656250000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1499743447/2500000000 : ℝ)^19 ≤ (5234768593423/10000000000000 : ℝ)^15 := by
    have hnat : (1499743447 : ℕ)^19*10000000000000^15 ≤ 5234768593423^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1499743447 2500000000 5234768593423 10000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2728392427/10000000000 : ℝ), (-147888191/400000000 : ℝ), (1499743447/2500000000 : ℝ)] ![(9648326594889/50000000000000 : ℝ), (27691075051/97656250000 : ℝ), (5234768593423/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2728392427/10000000000 : ℝ)|^19 ≤ (9648326594889/50000000000000 : ℝ)^15
        have hw : |(2728392427/10000000000 : ℝ)|=(2728392427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-147888191/400000000 : ℝ)|^19 ≤ (27691075051/97656250000 : ℝ)^15
        have hw : |(-147888191/400000000 : ℝ)|=(147888191/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1499743447/2500000000 : ℝ)|^19 ≤ (5234768593423/10000000000000 : ℝ)^15
        have hw : |(1499743447/2500000000 : ℝ)|=(1499743447/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315057_s1_s1_21 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2981168027/5000000000 : ℝ)*x 0 + (273434693/500000000 : ℝ)*x 1 + (-363108569/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2981168027/5000000000 : ℝ)^19 ≤ (25971528401639/50000000000000 : ℝ)^15 := by
    have hnat : (2981168027 : ℕ)^19*50000000000000^15 ≤ 25971528401639^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2981168027 5000000000 25971528401639 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (273434693/500000000 : ℝ)^19 ≤ (46557098705667/100000000000000 : ℝ)^15 := by
    have hnat : (273434693 : ℕ)^19*100000000000000^15 ≤ 46557098705667^15*500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273434693 500000000 46557098705667 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (363108569/10000000000 : ℝ)^19 ≤ (2343507009/156250000000 : ℝ)^15 := by
    have hnat : (363108569 : ℕ)^19*156250000000^15 ≤ 2343507009^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      363108569 10000000000 2343507009 156250000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2981168027/5000000000 : ℝ), (273434693/500000000 : ℝ), (-363108569/10000000000 : ℝ)] ![(25971528401639/50000000000000 : ℝ), (46557098705667/100000000000000 : ℝ), (2343507009/156250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2981168027/5000000000 : ℝ)|^19 ≤ (25971528401639/50000000000000 : ℝ)^15
        have hw : |(2981168027/5000000000 : ℝ)|=(2981168027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(273434693/500000000 : ℝ)|^19 ≤ (46557098705667/100000000000000 : ℝ)^15
        have hw : |(273434693/500000000 : ℝ)|=(273434693/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-363108569/10000000000 : ℝ)|^19 ≤ (2343507009/156250000000 : ℝ)^15
        have hw : |(-363108569/10000000000 : ℝ)|=(363108569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315057_s1_s1_25 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1003405377/2500000000 : ℝ)*x 0 + (2641496019/5000000000 : ℝ)*x 1 + (3238159701/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1003405377/2500000000 : ℝ)^19 ≤ (31463917359099/100000000000000 : ℝ)^15 := by
    have hnat : (1003405377 : ℕ)^19*100000000000000^15 ≤ 31463917359099^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1003405377 2500000000 31463917359099 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2641496019/5000000000 : ℝ)^19 ≤ (22281851840867/50000000000000 : ℝ)^15 := by
    have hnat : (2641496019 : ℕ)^19*50000000000000^15 ≤ 22281851840867^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2641496019 5000000000 22281851840867 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3238159701/10000000000 : ℝ)^19 ≤ (23972378932243/100000000000000 : ℝ)^15 := by
    have hnat : (3238159701 : ℕ)^19*100000000000000^15 ≤ 23972378932243^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3238159701 10000000000 23972378932243 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1003405377/2500000000 : ℝ), (2641496019/5000000000 : ℝ), (3238159701/10000000000 : ℝ)] ![(31463917359099/100000000000000 : ℝ), (22281851840867/50000000000000 : ℝ), (23972378932243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1003405377/2500000000 : ℝ)|^19 ≤ (31463917359099/100000000000000 : ℝ)^15
        have hw : |(1003405377/2500000000 : ℝ)|=(1003405377/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2641496019/5000000000 : ℝ)|^19 ≤ (22281851840867/50000000000000 : ℝ)^15
        have hw : |(2641496019/5000000000 : ℝ)|=(2641496019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3238159701/10000000000 : ℝ)|^19 ≤ (23972378932243/100000000000000 : ℝ)^15
        have hw : |(3238159701/10000000000 : ℝ)|=(3238159701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c315057_s1 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (174659/100000 : ℝ) (34911/20000 : ℝ) (15821/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((40027/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(40027/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(79379/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(79379/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(40117/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(40117/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((9623/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9623/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(48047/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(48047/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(431/6250 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(431/6250 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (15821/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (15821/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (15821/20000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (15821/20000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (15821/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (15821/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s1_pow0 : (40027/50000 : ℝ) ^ (75/16 : ℝ) ≤ (7049169946996539227/20000000000000000000 : ℝ) := by
    have hpowers : (40027/50000 : ℝ)^75 ≤ (7049169946996539227/20000000000000000000 : ℝ)^16 := by
      have hnat : (40027 : ℕ)^75*20000000000000000000^16 ≤ 7049169946996539227^16*50000^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        40027 50000 7049169946996539227 20000000000000000000 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (40027/50000 : ℝ)) (X := (7049169946996539227/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (27049169946996539227/20000000000000000000 : ℝ) ≤ (5332650400415769/5000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (27049169946996539227/20000000000000000000 : ℝ)^16 ≤ (5332650400415769/5000000000000000 : ℝ)^75 := by
      have hnat : (27049169946996539227 : ℕ)^16*5000000000000000^75 ≤ 5332650400415769^75*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27049169946996539227 20000000000000000000 5332650400415769 5000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5332650400415769/5000000000000000 : ℝ)) (X := (27049169946996539227/20000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (17049169946996539227/10000000000000000000 : ℝ) ≤ (2241093727990929/2000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (17049169946996539227/10000000000000000000 : ℝ)^16 ≤ (2241093727990929/2000000000000000 : ℝ)^75 := by
      have hnat : (17049169946996539227 : ℕ)^16*2000000000000000^75 ≤ 2241093727990929^75*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17049169946996539227 10000000000000000000 2241093727990929 2000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2241093727990929/2000000000000000 : ℝ)) (X := (17049169946996539227/10000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(332650400415769/4002700000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(41551372240239/615800000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (40027/50000 : ℝ)) (alpha := (332650400415769/4002700000000000 : ℝ)) (beta := (41551372240239/615800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (40027/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(332650400415769/4002700000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(41551372240239/615800000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (79379/100000 : ℝ) ^ (75/16 : ℝ) ≤ (33874282879766716269/100000000000000000000 : ℝ) := by
    have hpowers : (79379/100000 : ℝ)^75 ≤ (33874282879766716269/100000000000000000000 : ℝ)^16 := by
      have hnat : (79379 : ℕ)^75*100000000000000000000^16 ≤ 33874282879766716269^16*100000^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        79379 100000 33874282879766716269 100000000000000000000 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (79379/100000 : ℝ)) (X := (33874282879766716269/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (133874282879766716269/100000000000000000000 : ℝ) ≤ (5321067047824197/5000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (133874282879766716269/100000000000000000000 : ℝ)^16 ≤ (5321067047824197/5000000000000000 : ℝ)^75 := by
      have hnat : (133874282879766716269 : ℕ)^16*5000000000000000^75 ≤ 5321067047824197^75*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        133874282879766716269 100000000000000000000 5321067047824197 5000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5321067047824197/5000000000000000 : ℝ)) (X := (133874282879766716269/100000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (83874282879766716269/50000000000000000000 : ℝ) ≤ (11166760817201263/10000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (83874282879766716269/50000000000000000000 : ℝ)^16 ≤ (11166760817201263/10000000000000000 : ℝ)^75 := by
      have hnat : (83874282879766716269 : ℕ)^16*10000000000000000^75 ≤ 11166760817201263^75*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        83874282879766716269 50000000000000000000 11166760817201263 10000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11166760817201263/10000000000000000 : ℝ)) (X := (83874282879766716269/50000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(321067047824197/3968950000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(524626721552869/7937900000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (79379/100000 : ℝ)) (alpha := (321067047824197/3968950000000000 : ℝ)) (beta := (524626721552869/7937900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (79379/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(321067047824197/3968950000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(524626721552869/7937900000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (40117/100000 : ℝ) ^ (75/16 : ℝ) ≤ (345574836235509513/25000000000000000000 : ℝ) := by
    have hpowers : (40117/100000 : ℝ)^75 ≤ (345574836235509513/25000000000000000000 : ℝ)^16 := by
      have hnat : (40117 : ℕ)^75*25000000000000000000^16 ≤ 345574836235509513^16*100000^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        40117 100000 345574836235509513 25000000000000000000 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (40117/100000 : ℝ)) (X := (345574836235509513/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (25345574836235509513/25000000000000000000 : ℝ) ≤ (10029330026754547/10000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (25345574836235509513/25000000000000000000 : ℝ)^16 ≤ (10029330026754547/10000000000000000 : ℝ)^75 := by
      have hnat : (25345574836235509513 : ℕ)^16*10000000000000000^75 ≤ 10029330026754547^75*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25345574836235509513 25000000000000000000 10029330026754547 10000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10029330026754547/10000000000000000 : ℝ)) (X := (25345574836235509513/25000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (12845574836235509513/12500000000000000000 : ℝ) ≤ (2011669426485771/2000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (12845574836235509513/12500000000000000000 : ℝ)^16 ≤ (2011669426485771/2000000000000000 : ℝ)^75 := by
      have hnat : (12845574836235509513 : ℕ)^16*2000000000000000^75 ≤ 2011669426485771^75*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12845574836235509513 12500000000000000000 2011669426485771 2000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2011669426485771/2000000000000000 : ℝ)) (X := (12845574836235509513/12500000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(29330026754547/4011700000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(7254276418577/1002925000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (40117/100000 : ℝ)) (alpha := (29330026754547/4011700000000000 : ℝ)) (beta := (7254276418577/1002925000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (40117/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(29330026754547/4011700000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(7254276418577/1002925000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_1 : ((3191382493/10000000000 : ℝ)*X 1 0+(-3183702839/10000000000 : ℝ)*X 1 1+(757267827/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315057_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2846939117/5000000000 : ℝ)*X 2 0+(5705528763/10000000000 : ℝ)*X 2 1+(-108307929/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315057_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((2285597293/5000000000 : ℝ)*X 0 0+(4580547937/10000000000 : ℝ)*X 0 1+(10692159/31250000 : ℝ)*X 0 2+(2285597293/5000000000 : ℝ)*X 1 0+(4580547937/10000000000 : ℝ)*X 1 1+(10692159/31250000 : ℝ)*X 1 2+(2285597293/5000000000 : ℝ)*X 2 0+(4580547937/10000000000 : ℝ)*X 2 1+(10692159/31250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315057_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-1507748279/5000000000 : ℝ)*X 0 0+(2784268711/10000000000 : ℝ)*X 0 1+(261244377/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315057_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((18807721/62500000 : ℝ)*X 1 0+(-2778487621/10000000000 : ℝ)*X 1 1+(1635201347/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315057_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((2651203307/5000000000 : ℝ)*X 2 0+(6258007829/10000000000 : ℝ)*X 2 1+(-1664347/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315057_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_12 : ((4626684801/10000000000 : ℝ)*X 0 0+(5460507241/10000000000 : ℝ)*X 0 1+(73031691/312500000 : ℝ)*X 0 2+(4626684801/10000000000 : ℝ)*X 1 0+(5460507241/10000000000 : ℝ)*X 1 1+(73031691/312500000 : ℝ)*X 1 2+(4626684801/10000000000 : ℝ)*X 2 0+(5460507241/10000000000 : ℝ)*X 2 1+(73031691/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315057_s1_s1_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((-2791931179/10000000000 : ℝ)*X 0 0+(300799011/1000000000 : ℝ)*X 0 1+(6531109449/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315057_s1_s1_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((278613417/1000000000 : ℝ)*X 1 0+(-375218061/1250000000 : ℝ)*X 1 1+(6540805427/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315057_s1_s1_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((195208363/312500000 : ℝ)*X 2 0+(5314252763/10000000000 : ℝ)*X 2 1+(-832157/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315057_s1_s1_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_18 : ((5450612193/10000000000 : ℝ)*X 0 0+(4637021319/10000000000 : ℝ)*X 0 1+(2337014099/10000000000 : ℝ)*X 0 2+(5450612193/10000000000 : ℝ)*X 1 0+(4637021319/10000000000 : ℝ)*X 1 1+(2337014099/10000000000 : ℝ)*X 1 2+(5450612193/10000000000 : ℝ)*X 2 0+(4637021319/10000000000 : ℝ)*X 2 1+(2337014099/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315057_s1_s1_18 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_19 : ((-1855186347/5000000000 : ℝ)*X 0 0+(545213209/2000000000 : ℝ)*X 0 1+(5989278081/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315057_s1_s1_19 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((2728392427/10000000000 : ℝ)*X 1 0+(-147888191/400000000 : ℝ)*X 1 1+(1499743447/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315057_s1_s1_20 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((2981168027/5000000000 : ℝ)*X 2 0+(273434693/500000000 : ℝ)*X 2 1+(-363108569/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315057_s1_s1_21 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_25 : ((1003405377/2500000000 : ℝ)*X 0 0+(2641496019/5000000000 : ℝ)*X 0 1+(3238159701/10000000000 : ℝ)*X 0 2+(1003405377/2500000000 : ℝ)*X 1 0+(2641496019/5000000000 : ℝ)*X 1 1+(3238159701/10000000000 : ℝ)*X 1 2+(1003405377/2500000000 : ℝ)*X 2 0+(2641496019/5000000000 : ℝ)*X 2 1+(3238159701/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315057_s1_s1_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((9623/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9623/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (83094524740060217134811133/15922236715000000000000000000000 : ℝ) := by norm_num
    linear_combination (2245929/500000000000 : ℝ)*(base23) + (3911/125000000000 : ℝ)*(base49) + (132754969987/31250000000 : ℝ)*(base59) + (121674898003/62500000000 : ℝ)*(base60) + (8141035138807/1000000000000 : ℝ)*(major_s1_0) + (8141035138807/1000000000000 : ℝ)*(major_s1_1) + (8141035138807/1000000000000 : ℝ)*(major_s1_2) + (12661521/500000000000 : ℝ)*(sp_s1_2) + (5810438867207/500000000000 : ℝ)*(sp_s1_7) + (11620965967407/1000000000000 : ℝ)*(sp_s1_8) + (11620936152507/1000000000000 : ℝ)*(sp_s1_9) + (4661090497709/1000000000000 : ℝ)*(sp_s1_12) + (88232993/1000000000000 : ℝ)*(sp_s1_13) + (1509113/125000000000 : ℝ)*(sp_s1_25) + (4661102570613/1000000000000 : ℝ)*(f.failure) + (11620965967407/1000000000000 : ℝ)*(f.sum) + (24806252453554087647/63688946860000000000000000000000 : ℝ)*base63 + (100334677413797/2005850000000000000000000000 : ℝ)*base65 + (834933491324273/7937900000000000000000000000 : ℝ)*base67 + (3171980308751201/4011700000000000000000000000 : ℝ)*base69 + (54120995925385831461/160576315900000000000000000000000 : ℝ)*base70 + (225145144130633/615800000000000000000000000 : ℝ)*base73 + (873535559093507/1984475000000000000000000000 : ℝ)*base75 + (1306879851083683/4002700000000000000000000000 : ℝ)*base77 + (14350934111059436439/48881588200000000000000000000000 : ℝ)*base78 + (4033/100000000000000000 : ℝ)*base86 + (4033/100000000000000000 : ℝ)*base88 + (4033/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(48047/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(48047/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1380167645536413062463067581423/182091248283230000000000000000000000 : ℝ) := by norm_num
    linear_combination (1766127/250000000000 : ℝ)*(base21) + (14617/1000000000000 : ℝ)*(base40) + (265430927107/62500000000 : ℝ)*(base59) + (92106986177/40000000000 : ℝ)*(base60) + (813928311357/100000000000 : ℝ)*(major_s1_0) + (813928311357/100000000000 : ℝ)*(major_s1_1) + (813928311357/100000000000 : ℝ)*(major_s1_2) + (3570381/250000000000 : ℝ)*(sp_s1_6) + (130446889/1000000000000 : ℝ)*(sp_s1_8) + (11618464241919/1000000000000 : ℝ)*(sp_s1_13) + (11618333795031/1000000000000 : ℝ)*(sp_s1_14) + (11618412012667/1000000000000 : ℝ)*(sp_s1_15) + (186403407087/40000000000 : ℝ)*(sp_s1_18) + (5645593/125000000000 : ℝ)*(sp_s1_21) + (4660099458699/1000000000000 : ℝ)*(f.failure) + (11618464241919/1000000000000 : ℝ)*(f.sum) + (1256513456211303527/4549210490000000000000000000000 : ℝ)*base62 + (31254863821199/57310000000000000000000000 : ℝ)*base65 + (490889807964429/793790000000000000000000000 : ℝ)*base67 + (234619891713/1790937500000000000000000 : ℝ)*base68 + (47536212465983697/458789474000000000000000000000 : ℝ)*base70 + (28135658317311/61580000000000000000000000 : ℝ)*base73 + (127109585199297/158758000000000000000000000 : ℝ)*base75 + (474909679393/80054000000000000000000000 : ℝ)*base76 + (3062333410912269409/4888158820000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (91359/100000000000000000 : ℝ)*base86 + (91359/100000000000000000 : ℝ)*base88 + (91359/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(431/6250 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(431/6250 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1488456052985877245446837644117/231752497815020000000000000000000000 : ℝ) := by norm_num
    linear_combination (1468367/1000000000000 : ℝ)*(base40) + (8583/6250000000 : ℝ)*(base50) + (403238703107/500000000000 : ℝ)*(base59) + (535583905681/200000000000 : ℝ)*(major_s1_0) + (535583905681/200000000000 : ℝ)*(major_s1_1) + (535583905681/200000000000 : ℝ)*(major_s1_2) + (2464877/1000000000000 : ℝ)*(sp_s1_1) + (1332523/50000000000 : ℝ)*(sp_s1_9) + (28504191/500000000000 : ℝ)*(sp_s1_12) + (17018549/500000000000 : ℝ)*(sp_s1_15) + (1911304791221/500000000000 : ℝ)*(sp_s1_19) + (764521423513/200000000000 : ℝ)*(sp_s1_20) + (3822548894883/1000000000000 : ℝ)*(sp_s1_21) + (1533170325111/1000000000000 : ℝ)*(sp_s1_25) + (1533227333493/1000000000000 : ℝ)*(f.failure) + (1911304791221/500000000000 : ℝ)*(f.sum) + (1826559237503727263/5789904260000000000000000000000 : ℝ)*base63 + (1795699824869/9117500000000000000000000 : ℝ)*base65 + (1002667490214137/1587580000000000000000000000 : ℝ)*base66 + (19589655570021/72940000000000000000000000 : ℝ)*base68 + (1306902658914726271/2919569380000000000000000000000 : ℝ)*base71 + (41435542549093/123160000000000000000000000 : ℝ)*base72 + (397250142578217/793790000000000000000000000 : ℝ)*base75 + (134272400047893/800540000000000000000000000 : ℝ)*base77 + (3819083908686454541/9776317640000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (53887/100000000000000000 : ℝ)*base87 + (53887/100000000000000000 : ℝ)*base89 + (53887/100000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (174659/100000 : ℝ) (34911/20000 : ℝ) (15821/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((40027/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(40027/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(79379/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(79379/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(40117/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(40117/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((9623/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9623/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(48047/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(48047/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(431/6250 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(431/6250 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c315057_s1 p hpa hpb X hX hprev0

#print axioms solution
