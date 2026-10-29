-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c320062_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:37:15.140245+00:00
-- url     : https://prove2.me/submissions/8c7f3c09-0753-49b9-8927-715bc7975cb4

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
theorem collision_support_c320062_s1_s1_0 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1443165037/10000000000 : ℝ)*x 0 + (2487813913/5000000000 : ℝ)*x 1 + (-9046651/16000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1443165037/10000000000 : ℝ)^81 ≤ (4480726161197/50000000000000 : ℝ)^65 := by
    have hnat : (1443165037 : ℕ)^81*50000000000000^65 ≤ 4480726161197^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1443165037 10000000000 4480726161197 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2487813913/5000000000 : ℝ)^81 ≤ (41901139096999/100000000000000 : ℝ)^65 := by
    have hnat : (2487813913 : ℕ)^81*100000000000000^65 ≤ 41901139096999^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2487813913 5000000000 41901139096999 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9046651/16000000 : ℝ)^81 ≤ (12284352139977/25000000000000 : ℝ)^65 := by
    have hnat : (9046651 : ℕ)^81*25000000000000^65 ≤ 12284352139977^65*16000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9046651 16000000 12284352139977 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1443165037/10000000000 : ℝ), (2487813913/5000000000 : ℝ), (-9046651/16000000 : ℝ)] ![(4480726161197/50000000000000 : ℝ), (41901139096999/100000000000000 : ℝ), (12284352139977/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1443165037/10000000000 : ℝ)|^81 ≤ (4480726161197/50000000000000 : ℝ)^65
        have hw : |(-1443165037/10000000000 : ℝ)|=(1443165037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2487813913/5000000000 : ℝ)|^81 ≤ (41901139096999/100000000000000 : ℝ)^65
        have hw : |(2487813913/5000000000 : ℝ)|=(2487813913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-9046651/16000000 : ℝ)|^81 ≤ (12284352139977/25000000000000 : ℝ)^65
        have hw : |(-9046651/16000000 : ℝ)|=(9046651/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320062_s1_s1_2 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5139594629/10000000000 : ℝ)*x 0 + (5151064919/10000000000 : ℝ)*x 1 + (379916713/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5139594629/10000000000 : ℝ)^81 ≤ (43628762560397/100000000000000 : ℝ)^65 := by
    have hnat : (5139594629 : ℕ)^81*100000000000000^65 ≤ 43628762560397^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5139594629 10000000000 43628762560397 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5151064919/10000000000 : ℝ)^81 ≤ (43750131986001/100000000000000 : ℝ)^65 := by
    have hnat : (5151064919 : ℕ)^81*100000000000000^65 ≤ 43750131986001^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5151064919 10000000000 43750131986001 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (379916713/2000000000 : ℝ)^81 ≤ (12621105443321/100000000000000 : ℝ)^65 := by
    have hnat : (379916713 : ℕ)^81*100000000000000^65 ≤ 12621105443321^65*2000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      379916713 2000000000 12621105443321 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5139594629/10000000000 : ℝ), (5151064919/10000000000 : ℝ), (379916713/2000000000 : ℝ)] ![(43628762560397/100000000000000 : ℝ), (43750131986001/100000000000000 : ℝ), (12621105443321/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5139594629/10000000000 : ℝ)|^81 ≤ (43628762560397/100000000000000 : ℝ)^65
        have hw : |(5139594629/10000000000 : ℝ)|=(5139594629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5151064919/10000000000 : ℝ)|^81 ≤ (43750131986001/100000000000000 : ℝ)^65
        have hw : |(5151064919/10000000000 : ℝ)|=(5151064919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(379916713/2000000000 : ℝ)|^81 ≤ (12621105443321/100000000000000 : ℝ)^65
        have hw : |(379916713/2000000000 : ℝ)|=(379916713/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320062_s1_s1_7 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-212724317/2000000000 : ℝ)*x 0 + (4400784/9765625 : ℝ)*x 1 + (-6354824447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212724317/2000000000 : ℝ)^81 ≤ (3063353096679/50000000000000 : ℝ)^65 := by
    have hnat : (212724317 : ℕ)^81*50000000000000^65 ≤ 3063353096679^65*2000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212724317 2000000000 3063353096679 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4400784/9765625 : ℝ)^81 ≤ (1481422465577/4000000000000 : ℝ)^65 := by
    have hnat : (4400784 : ℕ)^81*4000000000000^65 ≤ 1481422465577^65*9765625^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4400784 9765625 1481422465577 4000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6354824447/10000000000 : ℝ)^81 ≤ (5683773214347/10000000000000 : ℝ)^65 := by
    have hnat : (6354824447 : ℕ)^81*10000000000000^65 ≤ 5683773214347^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6354824447 10000000000 5683773214347 10000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-212724317/2000000000 : ℝ), (4400784/9765625 : ℝ), (-6354824447/10000000000 : ℝ)] ![(3063353096679/50000000000000 : ℝ), (1481422465577/4000000000000 : ℝ), (5683773214347/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-212724317/2000000000 : ℝ)|^81 ≤ (3063353096679/50000000000000 : ℝ)^65
        have hw : |(-212724317/2000000000 : ℝ)|=(212724317/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4400784/9765625 : ℝ)|^81 ≤ (1481422465577/4000000000000 : ℝ)^65
        have hw : |(4400784/9765625 : ℝ)|=(4400784/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6354824447/10000000000 : ℝ)|^81 ≤ (5683773214347/10000000000000 : ℝ)^65
        have hw : |(-6354824447/10000000000 : ℝ)|=(6354824447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320062_s1_s1_8 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2455430521/5000000000 : ℝ)*x 0 + (-740572497/10000000000 : ℝ)*x 1 + (-6178140587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2455430521/5000000000 : ℝ)^81 ≤ (824451111279/2000000000000 : ℝ)^65 := by
    have hnat : (2455430521 : ℕ)^81*2000000000000^65 ≤ 824451111279^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2455430521 5000000000 824451111279 2000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (740572497/10000000000 : ℝ)^81 ≤ (3902179933323/100000000000000 : ℝ)^65 := by
    have hnat : (740572497 : ℕ)^81*100000000000000^65 ≤ 3902179933323^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      740572497 10000000000 3902179933323 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6178140587/10000000000 : ℝ)^81 ≤ (10975052898093/20000000000000 : ℝ)^65 := by
    have hnat : (6178140587 : ℕ)^81*20000000000000^65 ≤ 10975052898093^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6178140587 10000000000 10975052898093 20000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2455430521/5000000000 : ℝ), (-740572497/10000000000 : ℝ), (-6178140587/10000000000 : ℝ)] ![(824451111279/2000000000000 : ℝ), (3902179933323/100000000000000 : ℝ), (10975052898093/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2455430521/5000000000 : ℝ)|^81 ≤ (824451111279/2000000000000 : ℝ)^65
        have hw : |(2455430521/5000000000 : ℝ)|=(2455430521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-740572497/10000000000 : ℝ)|^81 ≤ (3902179933323/100000000000000 : ℝ)^65
        have hw : |(-740572497/10000000000 : ℝ)|=(740572497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6178140587/10000000000 : ℝ)|^81 ≤ (10975052898093/20000000000000 : ℝ)^65
        have hw : |(-6178140587/10000000000 : ℝ)|=(6178140587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320062_s1_s1_9 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2413515753/5000000000 : ℝ)*x 0 + (6134356543/10000000000 : ℝ)*x 1 + (470646517/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2413515753/5000000000 : ℝ)^81 ≤ (4034751406917/10000000000000 : ℝ)^65 := by
    have hnat : (2413515753 : ℕ)^81*10000000000000^65 ≤ 4034751406917^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2413515753 5000000000 4034751406917 10000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6134356543/10000000000 : ℝ)^81 ≤ (54391062329741/100000000000000 : ℝ)^65 := by
    have hnat : (6134356543 : ℕ)^81*100000000000000^65 ≤ 54391062329741^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6134356543 10000000000 54391062329741 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (470646517/5000000000 : ℝ)^81 ≤ (5261423594601/100000000000000 : ℝ)^65 := by
    have hnat : (470646517 : ℕ)^81*100000000000000^65 ≤ 5261423594601^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      470646517 5000000000 5261423594601 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2413515753/5000000000 : ℝ), (6134356543/10000000000 : ℝ), (470646517/5000000000 : ℝ)] ![(4034751406917/10000000000000 : ℝ), (54391062329741/100000000000000 : ℝ), (5261423594601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2413515753/5000000000 : ℝ)|^81 ≤ (4034751406917/10000000000000 : ℝ)^65
        have hw : |(2413515753/5000000000 : ℝ)|=(2413515753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6134356543/10000000000 : ℝ)|^81 ≤ (54391062329741/100000000000000 : ℝ)^65
        have hw : |(6134356543/10000000000 : ℝ)|=(6134356543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(470646517/5000000000 : ℝ)|^81 ≤ (5261423594601/100000000000000 : ℝ)^65
        have hw : |(470646517/5000000000 : ℝ)|=(470646517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320062_s1_s1_13 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (317210233/625000000 : ℝ)*x 0 + (3097629693/5000000000 : ℝ)*x 1 + (-430502889/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (317210233/625000000 : ℝ)^81 ≤ (2684397343747/6250000000000 : ℝ)^65 := by
    have hnat : (317210233 : ℕ)^81*6250000000000^65 ≤ 2684397343747^65*625000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      317210233 625000000 2684397343747 6250000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3097629693/5000000000 : ℝ)^81 ≤ (13766202311639/25000000000000 : ℝ)^65 := by
    have hnat : (3097629693 : ℕ)^81*25000000000000^65 ≤ 13766202311639^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3097629693 5000000000 13766202311639 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (430502889/10000000000 : ℝ)^81 ≤ (248104155881/12500000000000 : ℝ)^65 := by
    have hnat : (430502889 : ℕ)^81*12500000000000^65 ≤ 248104155881^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430502889 10000000000 248104155881 12500000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(317210233/625000000 : ℝ), (3097629693/5000000000 : ℝ), (-430502889/10000000000 : ℝ)] ![(2684397343747/6250000000000 : ℝ), (13766202311639/25000000000000 : ℝ), (248104155881/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(317210233/625000000 : ℝ)|^81 ≤ (2684397343747/6250000000000 : ℝ)^65
        have hw : |(317210233/625000000 : ℝ)|=(317210233/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3097629693/5000000000 : ℝ)|^81 ≤ (13766202311639/25000000000000 : ℝ)^65
        have hw : |(3097629693/5000000000 : ℝ)|=(3097629693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-430502889/10000000000 : ℝ)|^81 ≤ (248104155881/12500000000000 : ℝ)^65
        have hw : |(-430502889/10000000000 : ℝ)|=(430502889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320062_s1_s1_14 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-323536791/5000000000 : ℝ)*x 0 + (2404810723/5000000000 : ℝ)*x 1 + (-6327706117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (323536791/5000000000 : ℝ)^81 ≤ (3298111559883/100000000000000 : ℝ)^65 := by
    have hnat : (323536791 : ℕ)^81*100000000000000^65 ≤ 3298111559883^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323536791 5000000000 3298111559883 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2404810723/5000000000 : ℝ)^81 ≤ (40166248394451/100000000000000 : ℝ)^65 := by
    have hnat : (2404810723 : ℕ)^81*100000000000000^65 ≤ 40166248394451^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2404810723 5000000000 40166248394451 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6327706117/10000000000 : ℝ)^81 ≤ (56535640032159/100000000000000 : ℝ)^65 := by
    have hnat : (6327706117 : ℕ)^81*100000000000000^65 ≤ 56535640032159^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6327706117 10000000000 56535640032159 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-323536791/5000000000 : ℝ), (2404810723/5000000000 : ℝ), (-6327706117/10000000000 : ℝ)] ![(3298111559883/100000000000000 : ℝ), (40166248394451/100000000000000 : ℝ), (56535640032159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-323536791/5000000000 : ℝ)|^81 ≤ (3298111559883/100000000000000 : ℝ)^65
        have hw : |(-323536791/5000000000 : ℝ)|=(323536791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2404810723/5000000000 : ℝ)|^81 ≤ (40166248394451/100000000000000 : ℝ)^65
        have hw : |(2404810723/5000000000 : ℝ)|=(2404810723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6327706117/10000000000 : ℝ)|^81 ≤ (56535640032159/100000000000000 : ℝ)^65
        have hw : |(-6327706117/10000000000 : ℝ)|=(6327706117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320062_s1_s1_15 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4622672799/10000000000 : ℝ)*x 0 + (-72342393/625000000 : ℝ)*x 1 + (-154650129/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4622672799/10000000000 : ℝ)^81 ≤ (7646017912839/20000000000000 : ℝ)^65 := by
    have hnat : (4622672799 : ℕ)^81*20000000000000^65 ≤ 7646017912839^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4622672799 10000000000 7646017912839 20000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (72342393/625000000 : ℝ)^81 ≤ (425473932731/6250000000000 : ℝ)^65 := by
    have hnat : (72342393 : ℕ)^81*6250000000000^65 ≤ 425473932731^65*625000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      72342393 625000000 425473932731 6250000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (154650129/250000000 : ℝ)^81 ≤ (27481163748961/50000000000000 : ℝ)^65 := by
    have hnat : (154650129 : ℕ)^81*50000000000000^65 ≤ 27481163748961^65*250000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      154650129 250000000 27481163748961 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4622672799/10000000000 : ℝ), (-72342393/625000000 : ℝ), (-154650129/250000000 : ℝ)] ![(7646017912839/20000000000000 : ℝ), (425473932731/6250000000000 : ℝ), (27481163748961/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4622672799/10000000000 : ℝ)|^81 ≤ (7646017912839/20000000000000 : ℝ)^65
        have hw : |(4622672799/10000000000 : ℝ)|=(4622672799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-72342393/625000000 : ℝ)|^81 ≤ (425473932731/6250000000000 : ℝ)^65
        have hw : |(-72342393/625000000 : ℝ)|=(72342393/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-154650129/250000000 : ℝ)|^81 ≤ (27481163748961/50000000000000 : ℝ)^65
        have hw : |(-154650129/250000000 : ℝ)|=(154650129/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320062_s1_s1_16 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5976161133/10000000000 : ℝ)*x 0 + (4986137023/10000000000 : ℝ)*x 1 + (119066629/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5976161133/10000000000 : ℝ)^81 ≤ (52648716429273/100000000000000 : ℝ)^65 := by
    have hnat : (5976161133 : ℕ)^81*100000000000000^65 ≤ 52648716429273^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5976161133 10000000000 52648716429273 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4986137023/10000000000 : ℝ)^81 ≤ (21005726717051/50000000000000 : ℝ)^65 := by
    have hnat : (4986137023 : ℕ)^81*50000000000000^65 ≤ 21005726717051^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4986137023 10000000000 21005726717051 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (119066629/1250000000 : ℝ)^81 ≤ (5339830121267/100000000000000 : ℝ)^65 := by
    have hnat : (119066629 : ℕ)^81*100000000000000^65 ≤ 5339830121267^65*1250000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      119066629 1250000000 5339830121267 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5976161133/10000000000 : ℝ), (4986137023/10000000000 : ℝ), (119066629/1250000000 : ℝ)] ![(52648716429273/100000000000000 : ℝ), (21005726717051/50000000000000 : ℝ), (5339830121267/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5976161133/10000000000 : ℝ)|^81 ≤ (52648716429273/100000000000000 : ℝ)^65
        have hw : |(5976161133/10000000000 : ℝ)|=(5976161133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4986137023/10000000000 : ℝ)|^81 ≤ (21005726717051/50000000000000 : ℝ)^65
        have hw : |(4986137023/10000000000 : ℝ)|=(4986137023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(119066629/1250000000 : ℝ)|^81 ≤ (5339830121267/100000000000000 : ℝ)^65
        have hw : |(119066629/1250000000 : ℝ)|=(119066629/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320062_s1_s1_20 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6568272013/10000000000 : ℝ)*x 0 + (4664444737/10000000000 : ℝ)*x 1 + (-452576247/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6568272013/10000000000 : ℝ)^81 ≤ (14806623460387/25000000000000 : ℝ)^65 := by
    have hnat : (6568272013 : ℕ)^81*25000000000000^65 ≤ 14806623460387^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6568272013 10000000000 14806623460387 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4664444737/10000000000 : ℝ)^81 ≤ (38661062595351/100000000000000 : ℝ)^65 := by
    have hnat : (4664444737 : ℕ)^81*100000000000000^65 ≤ 38661062595351^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4664444737 10000000000 38661062595351 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (452576247/10000000000 : ℝ)^81 ≤ (528110887403/25000000000000 : ℝ)^65 := by
    have hnat : (452576247 : ℕ)^81*25000000000000^65 ≤ 528110887403^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      452576247 10000000000 528110887403 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6568272013/10000000000 : ℝ), (4664444737/10000000000 : ℝ), (-452576247/10000000000 : ℝ)] ![(14806623460387/25000000000000 : ℝ), (38661062595351/100000000000000 : ℝ), (528110887403/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6568272013/10000000000 : ℝ)|^81 ≤ (14806623460387/25000000000000 : ℝ)^65
        have hw : |(6568272013/10000000000 : ℝ)|=(6568272013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4664444737/10000000000 : ℝ)|^81 ≤ (38661062595351/100000000000000 : ℝ)^65
        have hw : |(4664444737/10000000000 : ℝ)|=(4664444737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-452576247/10000000000 : ℝ)|^81 ≤ (528110887403/25000000000000 : ℝ)^65
        have hw : |(-452576247/10000000000 : ℝ)|=(452576247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320062_s1_s1_21 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-40384511/1000000000 : ℝ)*x 0 + (5424480649/10000000000 : ℝ)*x 1 + (-5871709709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (40384511/1000000000 : ℝ)^81 ≤ (229107476011/12500000000000 : ℝ)^65 := by
    have hnat : (40384511 : ℕ)^81*12500000000000^65 ≤ 229107476011^65*1000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40384511 1000000000 229107476011 12500000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5424480649/10000000000 : ℝ)^81 ≤ (46662650611181/100000000000000 : ℝ)^65 := by
    have hnat : (5424480649 : ℕ)^81*100000000000000^65 ≤ 46662650611181^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424480649 10000000000 46662650611181 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5871709709/10000000000 : ℝ)^81 ≤ (51504489570121/100000000000000 : ℝ)^65 := by
    have hnat : (5871709709 : ℕ)^81*100000000000000^65 ≤ 51504489570121^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5871709709 10000000000 51504489570121 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-40384511/1000000000 : ℝ), (5424480649/10000000000 : ℝ), (-5871709709/10000000000 : ℝ)] ![(229107476011/12500000000000 : ℝ), (46662650611181/100000000000000 : ℝ), (51504489570121/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-40384511/1000000000 : ℝ)|^81 ≤ (229107476011/12500000000000 : ℝ)^65
        have hw : |(-40384511/1000000000 : ℝ)|=(40384511/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5424480649/10000000000 : ℝ)|^81 ≤ (46662650611181/100000000000000 : ℝ)^65
        have hw : |(5424480649/10000000000 : ℝ)|=(5424480649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5871709709/10000000000 : ℝ)|^81 ≤ (51504489570121/100000000000000 : ℝ)^65
        have hw : |(-5871709709/10000000000 : ℝ)|=(5871709709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320062_s1_s1_22 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (606383711/1000000000 : ℝ)*x 0 + (-517276021/5000000000 : ℝ)*x 1 + (-2419310421/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (606383711/1000000000 : ℝ)^81 ≤ (13403246452831/25000000000000 : ℝ)^65 := by
    have hnat : (606383711 : ℕ)^81*25000000000000^65 ≤ 13403246452831^65*1000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      606383711 1000000000 13403246452831 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (517276021/5000000000 : ℝ)^81 ≤ (2959373947487/50000000000000 : ℝ)^65 := by
    have hnat : (517276021 : ℕ)^81*50000000000000^65 ≤ 2959373947487^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517276021 5000000000 2959373947487 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2419310421/5000000000 : ℝ)^81 ≤ (20234133141497/50000000000000 : ℝ)^65 := by
    have hnat : (2419310421 : ℕ)^81*50000000000000^65 ≤ 20234133141497^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2419310421 5000000000 20234133141497 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(606383711/1000000000 : ℝ), (-517276021/5000000000 : ℝ), (-2419310421/5000000000 : ℝ)] ![(13403246452831/25000000000000 : ℝ), (2959373947487/50000000000000 : ℝ), (20234133141497/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(606383711/1000000000 : ℝ)|^81 ≤ (13403246452831/25000000000000 : ℝ)^65
        have hw : |(606383711/1000000000 : ℝ)|=(606383711/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-517276021/5000000000 : ℝ)|^81 ≤ (2959373947487/50000000000000 : ℝ)^65
        have hw : |(-517276021/5000000000 : ℝ)|=(517276021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2419310421/5000000000 : ℝ)|^81 ≤ (20234133141497/50000000000000 : ℝ)^65
        have hw : |(-2419310421/5000000000 : ℝ)|=(2419310421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320062_s1_s1_23 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (470154071/1000000000 : ℝ)*x 0 + (175031159/312500000 : ℝ)*x 1 + (467997099/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (470154071/1000000000 : ℝ)^81 ≤ (19522294957997/50000000000000 : ℝ)^65 := by
    have hnat : (470154071 : ℕ)^81*50000000000000^65 ≤ 19522294957997^65*1000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      470154071 1000000000 19522294957997 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (175031159/312500000 : ℝ)^81 ≤ (48562372263871/100000000000000 : ℝ)^65 := by
    have hnat : (175031159 : ℕ)^81*100000000000000^65 ≤ 48562372263871^65*312500000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      175031159 312500000 48562372263871 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (467997099/2500000000 : ℝ)^81 ≤ (12393037802733/100000000000000 : ℝ)^65 := by
    have hnat : (467997099 : ℕ)^81*100000000000000^65 ≤ 12393037802733^65*2500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      467997099 2500000000 12393037802733 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(470154071/1000000000 : ℝ), (175031159/312500000 : ℝ), (467997099/2500000000 : ℝ)] ![(19522294957997/50000000000000 : ℝ), (48562372263871/100000000000000 : ℝ), (12393037802733/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(470154071/1000000000 : ℝ)|^81 ≤ (19522294957997/50000000000000 : ℝ)^65
        have hw : |(470154071/1000000000 : ℝ)|=(470154071/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(175031159/312500000 : ℝ)|^81 ≤ (48562372263871/100000000000000 : ℝ)^65
        have hw : |(175031159/312500000 : ℝ)|=(175031159/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(467997099/2500000000 : ℝ)|^81 ≤ (12393037802733/100000000000000 : ℝ)^65
        have hw : |(467997099/2500000000 : ℝ)|=(467997099/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320062_s1_s1_27 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6779490957/10000000000 : ℝ)*x 0 + (1081463863/2500000000 : ℝ)*x 1 + (-315401253/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6779490957/10000000000 : ℝ)^81 ≤ (61609204214973/100000000000000 : ℝ)^65 := by
    have hnat : (6779490957 : ℕ)^81*100000000000000^65 ≤ 61609204214973^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6779490957 10000000000 61609204214973 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081463863/2500000000 : ℝ)^81 ≤ (56313135579/160000000000 : ℝ)^65 := by
    have hnat : (1081463863 : ℕ)^81*160000000000^65 ≤ 56313135579^65*2500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081463863 2500000000 56313135579 160000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (315401253/5000000000 : ℝ)^81 ≤ (798771508823/25000000000000 : ℝ)^65 := by
    have hnat : (315401253 : ℕ)^81*25000000000000^65 ≤ 798771508823^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      315401253 5000000000 798771508823 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6779490957/10000000000 : ℝ), (1081463863/2500000000 : ℝ), (-315401253/5000000000 : ℝ)] ![(61609204214973/100000000000000 : ℝ), (56313135579/160000000000 : ℝ), (798771508823/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6779490957/10000000000 : ℝ)|^81 ≤ (61609204214973/100000000000000 : ℝ)^65
        have hw : |(6779490957/10000000000 : ℝ)|=(6779490957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1081463863/2500000000 : ℝ)|^81 ≤ (56313135579/160000000000 : ℝ)^65
        have hw : |(1081463863/2500000000 : ℝ)|=(1081463863/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-315401253/5000000000 : ℝ)|^81 ≤ (798771508823/25000000000000 : ℝ)^65
        have hw : |(-315401253/5000000000 : ℝ)|=(315401253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c320062_s1 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4693/2500 : ℝ) (1059/625 : ℝ) (80273/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((583/800 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(583/800 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(36193/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(36193/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-30901/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-30901/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((10173/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(10173/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(20533/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(20533/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-26987/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-26987/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (80273/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (80273/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (80273/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (80273/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (80273/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (80273/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (583/800 : ℝ) ^ (5 : ℝ) ≤ (10276916861441497803/50000000000000000000 : ℝ) := by
    have hpowers : (583/800 : ℝ)^5 ≤ (10276916861441497803/50000000000000000000 : ℝ)^1 := by
      have hnat : (583 : ℕ)^5*50000000000000000000^1 ≤ 10276916861441497803^1*800^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        583 800 10276916861441497803 50000000000000000000 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (583/800 : ℝ)) (X := (10276916861441497803/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner0a : (60276916861441497803/50000000000000000000 : ℝ) ≤ (5190464314376251/5000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (60276916861441497803/50000000000000000000 : ℝ)^1 ≤ (5190464314376251/5000000000000000 : ℝ)^5 := by
      have hnat : (60276916861441497803 : ℕ)^1*5000000000000000^5 ≤ 5190464314376251^5*50000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        60276916861441497803 50000000000000000000 5190464314376251 5000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5190464314376251/5000000000000000 : ℝ)) (X := (60276916861441497803/50000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner0b : (35276916861441497803/25000000000000000000 : ℝ) ≤ (5356487884115313/5000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (35276916861441497803/25000000000000000000 : ℝ)^1 ≤ (5356487884115313/5000000000000000 : ℝ)^5 := by
      have hnat : (35276916861441497803 : ℕ)^1*5000000000000000^5 ≤ 5356487884115313^5*25000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        35276916861441497803 25000000000000000000 5356487884115313 5000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5356487884115313/5000000000000000 : ℝ)) (X := (35276916861441497803/25000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(190464314376251/3643750000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(83011784869531/1821875000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (583/800 : ℝ)) (alpha := (190464314376251/3643750000000000 : ℝ)) (beta := (83011784869531/1821875000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (583/800 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(190464314376251/3643750000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(83011784869531/1821875000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (36193/50000 : ℝ) ^ (5 : ℝ) ≤ (19873432881162990517/100000000000000000000 : ℝ) := by
    have hpowers : (36193/50000 : ℝ)^5 ≤ (19873432881162990517/100000000000000000000 : ℝ)^1 := by
      have hnat : (36193 : ℕ)^5*100000000000000000000^1 ≤ 19873432881162990517^1*50000^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        36193 50000 19873432881162990517 100000000000000000000 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (36193/50000 : ℝ)) (X := (19873432881162990517/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner1a : (119873432881162990517/100000000000000000000 : ℝ) ≤ (10369184178464633/10000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (119873432881162990517/100000000000000000000 : ℝ)^1 ≤ (10369184178464633/10000000000000000 : ℝ)^5 := by
      have hnat : (119873432881162990517 : ℕ)^1*10000000000000000^5 ≤ 10369184178464633^5*100000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        119873432881162990517 100000000000000000000 10369184178464633 10000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10369184178464633/10000000000000000 : ℝ)) (X := (119873432881162990517/100000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner1b : (69873432881162990517/50000000000000000000 : ℝ) ≤ (2138446605619251/2000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (69873432881162990517/50000000000000000000 : ℝ)^1 ≤ (2138446605619251/2000000000000000 : ℝ)^5 := by
      have hnat : (69873432881162990517 : ℕ)^1*2000000000000000^5 ≤ 2138446605619251^5*50000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        69873432881162990517 50000000000000000000 2138446605619251 2000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2138446605619251/2000000000000000 : ℝ)) (X := (69873432881162990517/50000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(369184178464633/7238600000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(161524424815811/3619300000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (36193/50000 : ℝ)) (alpha := (369184178464633/7238600000000000 : ℝ)) (beta := (161524424815811/3619300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (36193/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(369184178464633/7238600000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(161524424815811/3619300000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (30901/50000 : ℝ) ^ (5 : ℝ) ≤ (4507986977794614121/50000000000000000000 : ℝ) := by
    have hpowers : (30901/50000 : ℝ)^5 ≤ (4507986977794614121/50000000000000000000 : ℝ)^1 := by
      have hnat : (30901 : ℕ)^5*50000000000000000000^1 ≤ 4507986977794614121^1*50000^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        30901 50000 4507986977794614121 50000000000000000000 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (30901/50000 : ℝ)) (X := (4507986977794614121/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner2a : (54507986977794614121/50000000000000000000 : ℝ) ≤ (5087073730008879/5000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (54507986977794614121/50000000000000000000 : ℝ)^1 ≤ (5087073730008879/5000000000000000 : ℝ)^5 := by
      have hnat : (54507986977794614121 : ℕ)^1*5000000000000000^5 ≤ 5087073730008879^5*50000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        54507986977794614121 50000000000000000000 5087073730008879 5000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5087073730008879/5000000000000000 : ℝ)) (X := (54507986977794614121/50000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner2b : (29507986977794614121/25000000000000000000 : ℝ) ≤ (413485139909309/400000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (29507986977794614121/25000000000000000000 : ℝ)^1 ≤ (413485139909309/400000000000000 : ℝ)^5 := by
      have hnat : (29507986977794614121 : ℕ)^1*400000000000000^5 ≤ 413485139909309^5*25000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        29507986977794614121 25000000000000000000 413485139909309 400000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (413485139909309/400000000000000 : ℝ)) (X := (29507986977794614121/25000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(87073730008879/3090100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(162981037714967/6180200000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (30901/50000 : ℝ)) (alpha := (87073730008879/3090100000000000 : ℝ)) (beta := (162981037714967/6180200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (30901/50000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(87073730008879/3090100000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(162981037714967/6180200000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1443165037/10000000000 : ℝ)*X 0 0+(2487813913/5000000000 : ℝ)*X 0 1+(-9046651/16000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320062_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((5139594629/10000000000 : ℝ)*X 2 0+(5151064919/10000000000 : ℝ)*X 2 1+(379916713/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320062_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-212724317/2000000000 : ℝ)*X 0 0+(4400784/9765625 : ℝ)*X 0 1+(-6354824447/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320062_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((2455430521/5000000000 : ℝ)*X 1 0+(-740572497/10000000000 : ℝ)*X 1 1+(-6178140587/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320062_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((2413515753/5000000000 : ℝ)*X 2 0+(6134356543/10000000000 : ℝ)*X 2 1+(470646517/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320062_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((317210233/625000000 : ℝ)*X 0 0+(3097629693/5000000000 : ℝ)*X 0 1+(-430502889/10000000000 : ℝ)*X 0 2+(317210233/625000000 : ℝ)*X 1 0+(3097629693/5000000000 : ℝ)*X 1 1+(-430502889/10000000000 : ℝ)*X 1 2+(317210233/625000000 : ℝ)*X 2 0+(3097629693/5000000000 : ℝ)*X 2 1+(-430502889/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c320062_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-323536791/5000000000 : ℝ)*X 0 0+(2404810723/5000000000 : ℝ)*X 0 1+(-6327706117/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320062_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((4622672799/10000000000 : ℝ)*X 1 0+(-72342393/625000000 : ℝ)*X 1 1+(-154650129/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320062_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((5976161133/10000000000 : ℝ)*X 2 0+(4986137023/10000000000 : ℝ)*X 2 1+(119066629/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320062_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((6568272013/10000000000 : ℝ)*X 0 0+(4664444737/10000000000 : ℝ)*X 0 1+(-452576247/10000000000 : ℝ)*X 0 2+(6568272013/10000000000 : ℝ)*X 1 0+(4664444737/10000000000 : ℝ)*X 1 1+(-452576247/10000000000 : ℝ)*X 1 2+(6568272013/10000000000 : ℝ)*X 2 0+(4664444737/10000000000 : ℝ)*X 2 1+(-452576247/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c320062_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-40384511/1000000000 : ℝ)*X 0 0+(5424480649/10000000000 : ℝ)*X 0 1+(-5871709709/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320062_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((606383711/1000000000 : ℝ)*X 1 0+(-517276021/5000000000 : ℝ)*X 1 1+(-2419310421/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320062_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((470154071/1000000000 : ℝ)*X 2 0+(175031159/312500000 : ℝ)*X 2 1+(467997099/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320062_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((6779490957/10000000000 : ℝ)*X 0 0+(1081463863/2500000000 : ℝ)*X 0 1+(-315401253/5000000000 : ℝ)*X 0 2+(6779490957/10000000000 : ℝ)*X 1 0+(1081463863/2500000000 : ℝ)*X 1 1+(-315401253/5000000000 : ℝ)*X 1 2+(6779490957/10000000000 : ℝ)*X 2 0+(1081463863/2500000000 : ℝ)*X 2 1+(-315401253/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c320062_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((10173/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(10173/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1979196487214384501585920531953/163006784404750000000000000000000000 : ℝ) := by norm_num
    linear_combination (28103305133/200000000000 : ℝ)*(base39) + (9598979/1000000000000 : ℝ)*(base49) + (19749820399/100000000000 : ℝ)*(base60) + (112459109283/20000000000 : ℝ)*(major_s1_0) + (112459109283/20000000000 : ℝ)*(major_s1_1) + (112459109283/20000000000 : ℝ)*(major_s1_2) + (20071077/200000000000 : ℝ)*(sp_s1_0) + (2062600158769/250000000000 : ℝ)*(sp_s1_7) + (4125174062421/500000000000 : ℝ)*(sp_s1_8) + (8250376600407/1000000000000 : ℝ)*(sp_s1_9) + (2995394984099/1000000000000 : ℝ)*(sp_s1_13) + (10906469/1000000000000 : ℝ)*(sp_s1_14) + (20471511/125000000000 : ℝ)*(sp_s1_15) + (135296523/1000000000000 : ℝ)*(sp_s1_23) + (2995394984099/1000000000000 : ℝ)*(f.failure) + (825051189693/100000000000 : ℝ)*(f.sum) + (3966844194842659269/22367997860000000000000000000000 : ℝ)*base62 + (189563179600723/618020000000000000000000000 : ℝ)*base64 + (3402740151603/22620625000000000000000000 : ℝ)*base67 + (127036021095163/309010000000000000000000000 : ℝ)*base68 + (889205196170502093/9007641500000000000000000000000 : ℝ)*base70 + (30503907203467/145750000000000000000000000 : ℝ)*base73 + (260991189170089/723860000000000000000000000 : ℝ)*base74 + (61319790882359/145750000000000000000000000 : ℝ)*base76 + (261131886515795997/2637564875000000000000000000000 : ℝ)*base78 + (1607/2500000000000000 : ℝ)*base87 + (1607/2500000000000000 : ℝ)*base89 + (1607/2500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(20533/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(20533/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (13859590031727158970356553/822352862500000000000000000000 : ℝ) := by norm_num
    linear_combination (25782916563/200000000000 : ℝ)*(base39) + (3986904589/250000000000 : ℝ)*(base49) + (3186499/1000000000000 : ℝ)*(base60) + (355574605163/62500000000 : ℝ)*(major_s1_0) + (355574605163/62500000000 : ℝ)*(major_s1_1) + (355574605163/62500000000 : ℝ)*(major_s1_2) + (42108927/1000000000000 : ℝ)*(sp_s1_2) + (23375913/250000000000 : ℝ)*(sp_s1_7) + (13129069/200000000000 : ℝ)*(sp_s1_8) + (130431368931/15625000000 : ℝ)*(sp_s1_14) + (8347635469891/1000000000000 : ℝ)*(sp_s1_15) + (2086914751577/250000000000 : ℝ)*(sp_s1_16) + (3030483967121/1000000000000 : ℝ)*(sp_s1_20) + (39332999/200000000000 : ℝ)*(sp_s1_27) + (757670158029/250000000000 : ℝ)*(f.failure) + (2086925278809/250000000000 : ℝ)*(f.sum) + (539721530923663401/13979998662500000000000000000000 : ℝ)*base63 + (87642218557081/1545050000000000000000000000 : ℝ)*base64 + (509642342182029/1809650000000000000000000000 : ℝ)*base67 + (337464910650781/1545050000000000000000000000 : ℝ)*base69 + (99963392566667407/439826245117187500000000000000 : ℝ)*base70 + (16807673041413/455468750000000000000000000 : ℝ)*base72 + (1072296739184941/1809650000000000000000000000 : ℝ)*base75 + (1124837814139429/1821875000000000000000000000 : ℝ)*base77 + (43762681310154368539/65939121875000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (97/625000000000000 : ℝ)*base87 + (97/625000000000000 : ℝ)*base89 + (97/625000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-26987/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-26987/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (154514779229061962781198429/13979998662500000000000000000000 : ℝ) := by norm_num
    linear_combination (1675779/200000000000 : ℝ)*(base11) + (169235243597/250000000000 : ℝ)*(base39) + (258901369/500000000000 : ℝ)*(base49) + (76779/500000000000 : ℝ)*(base59) + (4490101606529/1000000000000 : ℝ)*(major_s1_0) + (4490101606529/1000000000000 : ℝ)*(major_s1_1) + (4490101606529/1000000000000 : ℝ)*(major_s1_2) + (4335289/125000000000 : ℝ)*(sp_s1_0) + (13937477/1000000000000 : ℝ)*(sp_s1_2) + (45753579/1000000000000 : ℝ)*(sp_s1_9) + (3294121061837/500000000000 : ℝ)*(sp_s1_21) + (6588285184881/1000000000000 : ℝ)*(sp_s1_22) + (102941023341/15625000000 : ℝ)*(sp_s1_23) + (478382868797/200000000000 : ℝ)*(sp_s1_27) + (478382868797/200000000000 : ℝ)*(f.failure) + (6588285184881/1000000000000 : ℝ)*(f.sum) + (23746473416780301223/223679978600000000000000000000000 : ℝ)*base63 + (2503587518111617/6180200000000000000000000000 : ℝ)*base64 + (1059540115117301/3619300000000000000000000000 : ℝ)*base66 + (360104734100441/3090100000000000000000000000 : ℝ)*base69 + (9264220092115316669/40943825000000000000000000000000 : ℝ)*base70 + (9296079331059/165625000000000000000000000 : ℝ)*base73 + (4253397067937737/7238600000000000000000000000 : ℝ)*base75 + (206276422431389/331250000000000000000000000 : ℝ)*base77 + (139221080165066827/23977862500000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (179/500000000000000 : ℝ)*base86 + (179/500000000000000 : ℝ)*base88 + (179/500000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4693/2500 : ℝ) (1059/625 : ℝ) (80273/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((583/800 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(583/800 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(36193/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(36193/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-30901/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-30901/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((10173/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(10173/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(20533/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(20533/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-26987/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-26987/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c320062_s1 p hpa hpb X hX hprev0

#print axioms solution
