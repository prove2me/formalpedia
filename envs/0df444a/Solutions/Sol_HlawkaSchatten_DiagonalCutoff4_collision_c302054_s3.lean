-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c302054_s3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:22:37.446566+00:00
-- url     : https://prove2.me/submissions/dee88ab7-7240-4380-a958-74a3d78df9ae

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
theorem collision_support_c302054_s3_s3_0 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-403068411/5000000000 : ℝ)*x 0 + (1117914011/2500000000 : ℝ)*x 1 + (-1736940891/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (403068411/5000000000 : ℝ)^33 ≤ (3601302162277/100000000000000 : ℝ)^25 := by
    have hnat : (403068411 : ℕ)^33*100000000000000^25 ≤ 3601302162277^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      403068411 5000000000 3601302162277 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1117914011/2500000000 : ℝ)^33 ≤ (1382541787939/4000000000000 : ℝ)^25 := by
    have hnat : (1117914011 : ℕ)^33*4000000000000^25 ≤ 1382541787939^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1117914011 2500000000 1382541787939 4000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1736940891/2500000000 : ℝ)^33 ≤ (2473406125089/4000000000000 : ℝ)^25 := by
    have hnat : (1736940891 : ℕ)^33*4000000000000^25 ≤ 2473406125089^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1736940891 2500000000 2473406125089 4000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-403068411/5000000000 : ℝ), (1117914011/2500000000 : ℝ), (-1736940891/2500000000 : ℝ)] ![(3601302162277/100000000000000 : ℝ), (1382541787939/4000000000000 : ℝ), (2473406125089/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-403068411/5000000000 : ℝ)|^33 ≤ (3601302162277/100000000000000 : ℝ)^25
        have hw : |(-403068411/5000000000 : ℝ)|=(403068411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1117914011/2500000000 : ℝ)|^33 ≤ (1382541787939/4000000000000 : ℝ)^25
        have hw : |(1117914011/2500000000 : ℝ)|=(1117914011/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1736940891/2500000000 : ℝ)|^33 ≤ (2473406125089/4000000000000 : ℝ)^25
        have hw : |(-1736940891/2500000000 : ℝ)|=(1736940891/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s3_s3_1 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1146306569/2000000000 : ℝ)*x 0 + (-1081870971/5000000000 : ℝ)*x 1 + (-609862793/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1146306569/2000000000 : ℝ)^33 ≤ (11991056395971/25000000000000 : ℝ)^25 := by
    have hnat : (1146306569 : ℕ)^33*25000000000000^25 ≤ 11991056395971^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1146306569 2000000000 11991056395971 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081870971/5000000000 : ℝ)^33 ≤ (13257792327249/100000000000000 : ℝ)^25 := by
    have hnat : (1081870971 : ℕ)^33*100000000000000^25 ≤ 13257792327249^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081870971 5000000000 13257792327249 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (609862793/1250000000 : ℝ)^33 ≤ (60590596983/156250000000 : ℝ)^25 := by
    have hnat : (609862793 : ℕ)^33*156250000000^25 ≤ 60590596983^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      609862793 1250000000 60590596983 156250000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1146306569/2000000000 : ℝ), (-1081870971/5000000000 : ℝ), (-609862793/1250000000 : ℝ)] ![(11991056395971/25000000000000 : ℝ), (13257792327249/100000000000000 : ℝ), (60590596983/156250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1146306569/2000000000 : ℝ)|^33 ≤ (11991056395971/25000000000000 : ℝ)^25
        have hw : |(1146306569/2000000000 : ℝ)|=(1146306569/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1081870971/5000000000 : ℝ)|^33 ≤ (13257792327249/100000000000000 : ℝ)^25
        have hw : |(-1081870971/5000000000 : ℝ)|=(1081870971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-609862793/1250000000 : ℝ)|^33 ≤ (60590596983/156250000000 : ℝ)^25
        have hw : |(-609862793/1250000000 : ℝ)|=(609862793/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s3_s3_2 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5473524661/10000000000 : ℝ)*x 0 + (1350678261/2500000000 : ℝ)*x 1 + (11332783/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5473524661/10000000000 : ℝ)^33 ≤ (22567453111781/50000000000000 : ℝ)^25 := by
    have hnat : (5473524661 : ℕ)^33*50000000000000^25 ≤ 22567453111781^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5473524661 10000000000 22567453111781 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1350678261/2500000000 : ℝ)^33 ≤ (11091434489531/25000000000000 : ℝ)^25 := by
    have hnat : (1350678261 : ℕ)^33*25000000000000^25 ≤ 11091434489531^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350678261 2500000000 11091434489531 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (11332783/62500000 : ℝ)^33 ≤ (10499355804577/100000000000000 : ℝ)^25 := by
    have hnat : (11332783 : ℕ)^33*100000000000000^25 ≤ 10499355804577^25*62500000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11332783 62500000 10499355804577 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5473524661/10000000000 : ℝ), (1350678261/2500000000 : ℝ), (11332783/62500000 : ℝ)] ![(22567453111781/50000000000000 : ℝ), (11091434489531/25000000000000 : ℝ), (10499355804577/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5473524661/10000000000 : ℝ)|^33 ≤ (22567453111781/50000000000000 : ℝ)^25
        have hw : |(5473524661/10000000000 : ℝ)|=(5473524661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1350678261/2500000000 : ℝ)|^33 ≤ (11091434489531/25000000000000 : ℝ)^25
        have hw : |(1350678261/2500000000 : ℝ)|=(1350678261/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(11332783/62500000 : ℝ)|^33 ≤ (10499355804577/100000000000000 : ℝ)^25
        have hw : |(11332783/62500000 : ℝ)|=(11332783/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s3_s3_6 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2688296343/5000000000 : ℝ)*x 0 + (5321782829/10000000000 : ℝ)*x 1 + (-1030083691/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2688296343/5000000000 : ℝ)^33 ≤ (44082825274799/100000000000000 : ℝ)^25 := by
    have hnat : (2688296343 : ℕ)^33*100000000000000^25 ≤ 44082825274799^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688296343 5000000000 44082825274799 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5321782829/10000000000 : ℝ)^33 ≤ (21745301801309/50000000000000 : ℝ)^25 := by
    have hnat : (5321782829 : ℕ)^33*50000000000000^25 ≤ 21745301801309^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5321782829 10000000000 21745301801309 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1030083691/5000000000 : ℝ)^33 ≤ (2485314219983/20000000000000 : ℝ)^25 := by
    have hnat : (1030083691 : ℕ)^33*20000000000000^25 ≤ 2485314219983^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030083691 5000000000 2485314219983 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2688296343/5000000000 : ℝ), (5321782829/10000000000 : ℝ), (-1030083691/5000000000 : ℝ)] ![(44082825274799/100000000000000 : ℝ), (21745301801309/50000000000000 : ℝ), (2485314219983/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2688296343/5000000000 : ℝ)|^33 ≤ (44082825274799/100000000000000 : ℝ)^25
        have hw : |(2688296343/5000000000 : ℝ)|=(2688296343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5321782829/10000000000 : ℝ)|^33 ≤ (21745301801309/50000000000000 : ℝ)^25
        have hw : |(5321782829/10000000000 : ℝ)|=(5321782829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1030083691/5000000000 : ℝ)|^33 ≤ (2485314219983/20000000000000 : ℝ)^25
        have hw : |(-1030083691/5000000000 : ℝ)|=(1030083691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s3_s3_7 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-178867757/5000000000 : ℝ)*x 0 + (343584383/1000000000 : ℝ)*x 1 + (-1997380297/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (178867757/5000000000 : ℝ)^33 ≤ (1232258761623/100000000000000 : ℝ)^25 := by
    have hnat : (178867757 : ℕ)^33*100000000000000^25 ≤ 1232258761623^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      178867757 5000000000 1232258761623 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (343584383/1000000000 : ℝ)^33 ≤ (12204896837049/50000000000000 : ℝ)^25 := by
    have hnat : (343584383 : ℕ)^33*50000000000000^25 ≤ 12204896837049^25*1000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343584383 1000000000 12204896837049 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1997380297/2500000000 : ℝ)^33 ≤ (74357947548147/100000000000000 : ℝ)^25 := by
    have hnat : (1997380297 : ℕ)^33*100000000000000^25 ≤ 74357947548147^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1997380297 2500000000 74357947548147 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-178867757/5000000000 : ℝ), (343584383/1000000000 : ℝ), (-1997380297/2500000000 : ℝ)] ![(1232258761623/100000000000000 : ℝ), (12204896837049/50000000000000 : ℝ), (74357947548147/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-178867757/5000000000 : ℝ)|^33 ≤ (1232258761623/100000000000000 : ℝ)^25
        have hw : |(-178867757/5000000000 : ℝ)|=(178867757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(343584383/1000000000 : ℝ)|^33 ≤ (12204896837049/50000000000000 : ℝ)^25
        have hw : |(343584383/1000000000 : ℝ)|=(343584383/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1997380297/2500000000 : ℝ)|^33 ≤ (74357947548147/100000000000000 : ℝ)^25
        have hw : |(-1997380297/2500000000 : ℝ)|=(1997380297/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s3_s3_8 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4881509/10000000 : ℝ)*x 0 + (-18998869/200000000 : ℝ)*x 1 + (-130160277/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4881509/10000000 : ℝ)^33 ≤ (38805332101911/100000000000000 : ℝ)^25 := by
    have hnat : (4881509 : ℕ)^33*100000000000000^25 ≤ 38805332101911^25*10000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4881509 10000000 38805332101911 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (18998869/200000000 : ℝ)^33 ≤ (2236305015039/50000000000000 : ℝ)^25 := by
    have hnat : (18998869 : ℕ)^33*50000000000000^25 ≤ 2236305015039^25*200000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18998869 200000000 2236305015039 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (130160277/200000000 : ℝ)^33 ≤ (56722057845623/100000000000000 : ℝ)^25 := by
    have hnat : (130160277 : ℕ)^33*100000000000000^25 ≤ 56722057845623^25*200000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130160277 200000000 56722057845623 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4881509/10000000 : ℝ), (-18998869/200000000 : ℝ), (-130160277/200000000 : ℝ)] ![(38805332101911/100000000000000 : ℝ), (2236305015039/50000000000000 : ℝ), (56722057845623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4881509/10000000 : ℝ)|^33 ≤ (38805332101911/100000000000000 : ℝ)^25
        have hw : |(4881509/10000000 : ℝ)|=(4881509/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-18998869/200000000 : ℝ)|^33 ≤ (2236305015039/50000000000000 : ℝ)^25
        have hw : |(-18998869/200000000 : ℝ)|=(18998869/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-130160277/200000000 : ℝ)|^33 ≤ (56722057845623/100000000000000 : ℝ)^25
        have hw : |(-130160277/200000000 : ℝ)|=(130160277/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s3_s3_9 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4394890077/10000000000 : ℝ)*x 0 + (895745743/1250000000 : ℝ)*x 1 + (477922819/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4394890077/10000000000 : ℝ)^33 ≤ (33782468669369/100000000000000 : ℝ)^25 := by
    have hnat : (4394890077 : ℕ)^33*100000000000000^25 ≤ 33782468669369^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4394890077 10000000000 33782468669369 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (895745743/1250000000 : ℝ)^33 ≤ (64411387816253/100000000000000 : ℝ)^25 := by
    have hnat : (895745743 : ℕ)^33*100000000000000^25 ≤ 64411387816253^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895745743 1250000000 64411387816253 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (477922819/10000000000 : ℝ)^33 ≤ (225767937419/12500000000000 : ℝ)^25 := by
    have hnat : (477922819 : ℕ)^33*12500000000000^25 ≤ 225767937419^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      477922819 10000000000 225767937419 12500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4394890077/10000000000 : ℝ), (895745743/1250000000 : ℝ), (477922819/10000000000 : ℝ)] ![(33782468669369/100000000000000 : ℝ), (64411387816253/100000000000000 : ℝ), (225767937419/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4394890077/10000000000 : ℝ)|^33 ≤ (33782468669369/100000000000000 : ℝ)^25
        have hw : |(4394890077/10000000000 : ℝ)|=(4394890077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(895745743/1250000000 : ℝ)|^33 ≤ (64411387816253/100000000000000 : ℝ)^25
        have hw : |(895745743/1250000000 : ℝ)|=(895745743/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(477922819/10000000000 : ℝ)|^33 ≤ (225767937419/12500000000000 : ℝ)^25
        have hw : |(477922819/10000000000 : ℝ)|=(477922819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s3_s3_13 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4609802343/10000000000 : ℝ)*x 0 + (3465035563/5000000000 : ℝ)*x 1 + (-59139681/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4609802343/10000000000 : ℝ)^33 ≤ (8994989285351/25000000000000 : ℝ)^25 := by
    have hnat : (4609802343 : ℕ)^33*25000000000000^25 ≤ 8994989285351^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4609802343 10000000000 8994989285351 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3465035563/5000000000 : ℝ)^33 ≤ (61627386908159/100000000000000 : ℝ)^25 := by
    have hnat : (3465035563 : ℕ)^33*100000000000000^25 ≤ 61627386908159^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3465035563 5000000000 61627386908159 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (59139681/1000000000 : ℝ)^33 ≤ (2392655929937/100000000000000 : ℝ)^25 := by
    have hnat : (59139681 : ℕ)^33*100000000000000^25 ≤ 2392655929937^25*1000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      59139681 1000000000 2392655929937 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4609802343/10000000000 : ℝ), (3465035563/5000000000 : ℝ), (-59139681/1000000000 : ℝ)] ![(8994989285351/25000000000000 : ℝ), (61627386908159/100000000000000 : ℝ), (2392655929937/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4609802343/10000000000 : ℝ)|^33 ≤ (8994989285351/25000000000000 : ℝ)^25
        have hw : |(4609802343/10000000000 : ℝ)|=(4609802343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3465035563/5000000000 : ℝ)|^33 ≤ (61627386908159/100000000000000 : ℝ)^25
        have hw : |(3465035563/5000000000 : ℝ)|=(3465035563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-59139681/1000000000 : ℝ)|^33 ≤ (2392655929937/100000000000000 : ℝ)^25
        have hw : |(-59139681/1000000000 : ℝ)|=(59139681/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s3_s3_14 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-314109/625000000 : ℝ)*x 0 + (228308163/625000000 : ℝ)*x 1 + (-30945349/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (314109/625000000 : ℝ)^33 ≤ (884330237/20000000000000 : ℝ)^25 := by
    have hnat : (314109 : ℕ)^33*20000000000000^25 ≤ 884330237^25*625000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      314109 625000000 884330237 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (228308163/625000000 : ℝ)^33 ≤ (13232950312567/50000000000000 : ℝ)^25 := by
    have hnat : (228308163 : ℕ)^33*50000000000000^25 ≤ 13232950312567^25*625000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      228308163 625000000 13232950312567 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (30945349/39062500 : ℝ)^33 ≤ (73529677712151/100000000000000 : ℝ)^25 := by
    have hnat : (30945349 : ℕ)^33*100000000000000^25 ≤ 73529677712151^25*39062500^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30945349 39062500 73529677712151 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-314109/625000000 : ℝ), (228308163/625000000 : ℝ), (-30945349/39062500 : ℝ)] ![(884330237/20000000000000 : ℝ), (13232950312567/50000000000000 : ℝ), (73529677712151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-314109/625000000 : ℝ)|^33 ≤ (884330237/20000000000000 : ℝ)^25
        have hw : |(-314109/625000000 : ℝ)|=(314109/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(228308163/625000000 : ℝ)|^33 ≤ (13232950312567/50000000000000 : ℝ)^25
        have hw : |(228308163/625000000 : ℝ)|=(228308163/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-30945349/39062500 : ℝ)|^33 ≤ (73529677712151/100000000000000 : ℝ)^25
        have hw : |(-30945349/39062500 : ℝ)|=(30945349/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s3_s3_15 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4265354671/10000000000 : ℝ)*x 0 + (-210985187/1250000000 : ℝ)*x 1 + (-6616518063/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4265354671/10000000000 : ℝ)^33 ≤ (1298974986931/4000000000000 : ℝ)^25 := by
    have hnat : (4265354671 : ℕ)^33*4000000000000^25 ≤ 1298974986931^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4265354671 10000000000 1298974986931 4000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210985187/1250000000 : ℝ)^33 ≤ (2387983850673/25000000000000 : ℝ)^25 := by
    have hnat : (210985187 : ℕ)^33*25000000000000^25 ≤ 2387983850673^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210985187 1250000000 2387983850673 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6616518063/10000000000 : ℝ)^33 ≤ (1811677809723/3125000000000 : ℝ)^25 := by
    have hnat : (6616518063 : ℕ)^33*3125000000000^25 ≤ 1811677809723^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6616518063 10000000000 1811677809723 3125000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4265354671/10000000000 : ℝ), (-210985187/1250000000 : ℝ), (-6616518063/10000000000 : ℝ)] ![(1298974986931/4000000000000 : ℝ), (2387983850673/25000000000000 : ℝ), (1811677809723/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4265354671/10000000000 : ℝ)|^33 ≤ (1298974986931/4000000000000 : ℝ)^25
        have hw : |(4265354671/10000000000 : ℝ)|=(4265354671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-210985187/1250000000 : ℝ)|^33 ≤ (2387983850673/25000000000000 : ℝ)^25
        have hw : |(-210985187/1250000000 : ℝ)|=(210985187/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6616518063/10000000000 : ℝ)|^33 ≤ (1811677809723/3125000000000 : ℝ)^25
        have hw : |(-6616518063/10000000000 : ℝ)|=(6616518063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s3_s3_16 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (918761191/1250000000 : ℝ)*x 0 + (2050025817/5000000000 : ℝ)*x 1 + (624607589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (918761191/1250000000 : ℝ)^33 ≤ (13320982753169/20000000000000 : ℝ)^25 := by
    have hnat : (918761191 : ℕ)^33*20000000000000^25 ≤ 13320982753169^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      918761191 1250000000 13320982753169 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2050025817/5000000000 : ℝ)^33 ≤ (30823497102351/100000000000000 : ℝ)^25 := by
    have hnat : (2050025817 : ℕ)^33*100000000000000^25 ≤ 30823497102351^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2050025817 5000000000 30823497102351 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (624607589/10000000000 : ℝ)^33 ≤ (2571589114517/100000000000000 : ℝ)^25 := by
    have hnat : (624607589 : ℕ)^33*100000000000000^25 ≤ 2571589114517^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      624607589 10000000000 2571589114517 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(918761191/1250000000 : ℝ), (2050025817/5000000000 : ℝ), (624607589/10000000000 : ℝ)] ![(13320982753169/20000000000000 : ℝ), (30823497102351/100000000000000 : ℝ), (2571589114517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(918761191/1250000000 : ℝ)|^33 ≤ (13320982753169/20000000000000 : ℝ)^25
        have hw : |(918761191/1250000000 : ℝ)|=(918761191/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2050025817/5000000000 : ℝ)|^33 ≤ (30823497102351/100000000000000 : ℝ)^25
        have hw : |(2050025817/5000000000 : ℝ)|=(2050025817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(624607589/10000000000 : ℝ)|^33 ≤ (2571589114517/100000000000000 : ℝ)^25
        have hw : |(624607589/10000000000 : ℝ)|=(624607589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s3_s3_20 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3416598867/5000000000 : ℝ)*x 0 + (551844913/1250000000 : ℝ)*x 1 + (-111455479/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3416598867/5000000000 : ℝ)^33 ≤ (60492796862359/100000000000000 : ℝ)^25 := by
    have hnat : (3416598867 : ℕ)^33*100000000000000^25 ≤ 60492796862359^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3416598867 5000000000 60492796862359 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (551844913/1250000000 : ℝ)^33 ≤ (33984217944801/100000000000000 : ℝ)^25 := by
    have hnat : (551844913 : ℕ)^33*100000000000000^25 ≤ 33984217944801^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551844913 1250000000 33984217944801 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (111455479/1000000000 : ℝ)^33 ≤ (5522985180669/100000000000000 : ℝ)^25 := by
    have hnat : (111455479 : ℕ)^33*100000000000000^25 ≤ 5522985180669^25*1000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111455479 1000000000 5522985180669 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3416598867/5000000000 : ℝ), (551844913/1250000000 : ℝ), (-111455479/1000000000 : ℝ)] ![(60492796862359/100000000000000 : ℝ), (33984217944801/100000000000000 : ℝ), (5522985180669/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3416598867/5000000000 : ℝ)|^33 ≤ (60492796862359/100000000000000 : ℝ)^25
        have hw : |(3416598867/5000000000 : ℝ)|=(3416598867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(551844913/1250000000 : ℝ)|^33 ≤ (33984217944801/100000000000000 : ℝ)^25
        have hw : |(551844913/1250000000 : ℝ)|=(551844913/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-111455479/1000000000 : ℝ)|^33 ≤ (5522985180669/100000000000000 : ℝ)^25
        have hw : |(-111455479/1000000000 : ℝ)|=(111455479/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s3_s3_21 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5397241/10000000000 : ℝ)*x 0 + (2817857489/5000000000 : ℝ)*x 1 + (-6189487891/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5397241/10000000000 : ℝ)^33 ≤ (971620761/20000000000000 : ℝ)^25 := by
    have hnat : (5397241 : ℕ)^33*20000000000000^25 ≤ 971620761^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397241 10000000000 971620761 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2817857489/5000000000 : ℝ)^33 ≤ (11727156374219/25000000000000 : ℝ)^25 := by
    have hnat : (2817857489 : ℕ)^33*25000000000000^25 ≤ 11727156374219^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2817857489 5000000000 11727156374219 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6189487891/10000000000 : ℝ)^33 ≤ (53086516389147/100000000000000 : ℝ)^25 := by
    have hnat : (6189487891 : ℕ)^33*100000000000000^25 ≤ 53086516389147^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6189487891 10000000000 53086516389147 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5397241/10000000000 : ℝ), (2817857489/5000000000 : ℝ), (-6189487891/10000000000 : ℝ)] ![(971620761/20000000000000 : ℝ), (11727156374219/25000000000000 : ℝ), (53086516389147/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5397241/10000000000 : ℝ)|^33 ≤ (971620761/20000000000000 : ℝ)^25
        have hw : |(5397241/10000000000 : ℝ)|=(5397241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2817857489/5000000000 : ℝ)|^33 ≤ (11727156374219/25000000000000 : ℝ)^25
        have hw : |(2817857489/5000000000 : ℝ)|=(2817857489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6189487891/10000000000 : ℝ)|^33 ≤ (53086516389147/100000000000000 : ℝ)^25
        have hw : |(-6189487891/10000000000 : ℝ)|=(6189487891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s3_s3_22 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (352862047/500000000 : ℝ)*x 0 + (-760770623/5000000000 : ℝ)*x 1 + (-3868432013/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (352862047/500000000 : ℝ)^33 ≤ (63124525589519/100000000000000 : ℝ)^25 := by
    have hnat : (352862047 : ℕ)^33*100000000000000^25 ≤ 63124525589519^25*500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      352862047 500000000 63124525589519 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (760770623/5000000000 : ℝ)^33 ≤ (8329415432963/100000000000000 : ℝ)^25 := by
    have hnat : (760770623 : ℕ)^33*100000000000000^25 ≤ 8329415432963^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      760770623 5000000000 8329415432963 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3868432013/10000000000 : ℝ)^33 ≤ (14273029483457/50000000000000 : ℝ)^25 := by
    have hnat : (3868432013 : ℕ)^33*50000000000000^25 ≤ 14273029483457^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3868432013 10000000000 14273029483457 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(352862047/500000000 : ℝ), (-760770623/5000000000 : ℝ), (-3868432013/10000000000 : ℝ)] ![(63124525589519/100000000000000 : ℝ), (8329415432963/100000000000000 : ℝ), (14273029483457/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(352862047/500000000 : ℝ)|^33 ≤ (63124525589519/100000000000000 : ℝ)^25
        have hw : |(352862047/500000000 : ℝ)|=(352862047/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-760770623/5000000000 : ℝ)|^33 ≤ (8329415432963/100000000000000 : ℝ)^25
        have hw : |(-760770623/5000000000 : ℝ)|=(760770623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3868432013/10000000000 : ℝ)|^33 ≤ (14273029483457/50000000000000 : ℝ)^25
        have hw : |(-3868432013/10000000000 : ℝ)|=(3868432013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s3_s3_23 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4759340379/10000000000 : ℝ)*x 0 + (2984186589/5000000000 : ℝ)*x 1 + (497591847/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4759340379/10000000000 : ℝ)^33 ≤ (293191760487/781250000000 : ℝ)^25 := by
    have hnat : (4759340379 : ℕ)^33*781250000000^25 ≤ 293191760487^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4759340379 10000000000 293191760487 781250000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2984186589/5000000000 : ℝ)^33 ≤ (50597595684879/100000000000000 : ℝ)^25 := by
    have hnat : (2984186589 : ℕ)^33*100000000000000^25 ≤ 50597595684879^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2984186589 5000000000 50597595684879 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (497591847/2500000000 : ℝ)^33 ≤ (371058092761/3125000000000 : ℝ)^25 := by
    have hnat : (497591847 : ℕ)^33*3125000000000^25 ≤ 371058092761^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      497591847 2500000000 371058092761 3125000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4759340379/10000000000 : ℝ), (2984186589/5000000000 : ℝ), (497591847/2500000000 : ℝ)] ![(293191760487/781250000000 : ℝ), (50597595684879/100000000000000 : ℝ), (371058092761/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4759340379/10000000000 : ℝ)|^33 ≤ (293191760487/781250000000 : ℝ)^25
        have hw : |(4759340379/10000000000 : ℝ)|=(4759340379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2984186589/5000000000 : ℝ)|^33 ≤ (50597595684879/100000000000000 : ℝ)^25
        have hw : |(2984186589/5000000000 : ℝ)|=(2984186589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(497591847/2500000000 : ℝ)|^33 ≤ (371058092761/3125000000000 : ℝ)^25
        have hw : |(497591847/2500000000 : ℝ)|=(497591847/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s3_s3_27 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6519425621/10000000000 : ℝ)*x 0 + (4373207499/10000000000 : ℝ)*x 1 + (-423042239/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6519425621/10000000000 : ℝ)^33 ≤ (5685338431511/10000000000000 : ℝ)^25 := by
    have hnat : (6519425621 : ℕ)^33*10000000000000^25 ≤ 5685338431511^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6519425621 10000000000 5685338431511 10000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4373207499/10000000000 : ℝ)^33 ≤ (524416245711/1562500000000 : ℝ)^25 := by
    have hnat : (4373207499 : ℕ)^33*1562500000000^25 ≤ 524416245711^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4373207499 10000000000 524416245711 1562500000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (423042239/2500000000 : ℝ)^33 ≤ (4791987970613/50000000000000 : ℝ)^25 := by
    have hnat : (423042239 : ℕ)^33*50000000000000^25 ≤ 4791987970613^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423042239 2500000000 4791987970613 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6519425621/10000000000 : ℝ), (4373207499/10000000000 : ℝ), (-423042239/2500000000 : ℝ)] ![(5685338431511/10000000000000 : ℝ), (524416245711/1562500000000 : ℝ), (4791987970613/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6519425621/10000000000 : ℝ)|^33 ≤ (5685338431511/10000000000000 : ℝ)^25
        have hw : |(6519425621/10000000000 : ℝ)|=(6519425621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4373207499/10000000000 : ℝ)|^33 ≤ (524416245711/1562500000000 : ℝ)^25
        have hw : |(4373207499/10000000000 : ℝ)|=(4373207499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-423042239/2500000000 : ℝ)|^33 ≤ (4791987970613/50000000000000 : ℝ)^25
        have hw : |(-423042239/2500000000 : ℝ)|=(423042239/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c302054_s3 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev2 : (0 : ℝ) ≤ ((75729/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(75729/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(39817/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(39817/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-63459/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-63459/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((62397/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(62397/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8199/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8199/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-50523/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-50523/100000 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4769/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4769/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (36753/20000 : ℝ) := by
    linarith only [f.Tcap]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
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
  rcases hprev2 with ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩
  have s3_pow0 : (75729/100000 : ℝ) ^ (65/16 : ℝ) ≤ (32322338705709828569/100000000000000000000 : ℝ) := by
    have hpowers : (75729/100000 : ℝ)^65 ≤ (32322338705709828569/100000000000000000000 : ℝ)^16 := by
      have hnat : (75729 : ℕ)^65*100000000000000000000^16 ≤ 32322338705709828569^16*100000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        75729 100000 32322338705709828569 100000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (75729/100000 : ℝ)) (X := (32322338705709828569/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s3_corner0a : (132322338705709828569/100000000000000000000 : ℝ) ≤ (2142744888743563/2000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (132322338705709828569/100000000000000000000 : ℝ)^16 ≤ (2142744888743563/2000000000000000 : ℝ)^65 := by
      have hnat : (132322338705709828569 : ℕ)^16*2000000000000000^65 ≤ 2142744888743563^65*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        132322338705709828569 100000000000000000000 2142744888743563 2000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2142744888743563/2000000000000000 : ℝ)) (X := (132322338705709828569/100000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s3_corner0b : (82322338705709828569/50000000000000000000 : ℝ) ≤ (11305871579910703/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (82322338705709828569/50000000000000000000 : ℝ)^16 ≤ (11305871579910703/10000000000000000 : ℝ)^65 := by
      have hnat : (82322338705709828569 : ℕ)^16*10000000000000000^65 ≤ 11305871579910703^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        82322338705709828569 50000000000000000000 11305871579910703 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11305871579910703/10000000000000000 : ℝ)) (X := (82322338705709828569/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s3_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(142744888743563/1514580000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(74018392024111/946612500000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (75729/100000 : ℝ)) (alpha := (142744888743563/1514580000000000 : ℝ)) (beta := (74018392024111/946612500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow0,s3_corner0a]) (by linarith only [s3_pow0,s3_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (75729/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(142744888743563/1514580000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(74018392024111/946612500000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow1 : (39817/50000 : ℝ) ^ (65/16 : ℝ) ≤ (39647223714707697843/100000000000000000000 : ℝ) := by
    have hpowers : (39817/50000 : ℝ)^65 ≤ (39647223714707697843/100000000000000000000 : ℝ)^16 := by
      have hnat : (39817 : ℕ)^65*100000000000000000000^16 ≤ 39647223714707697843^16*50000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        39817 50000 39647223714707697843 100000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (39817/50000 : ℝ)) (X := (39647223714707697843/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s3_corner1a : (139647223714707697843/100000000000000000000 : ℝ) ≤ (1085676056364991/1000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (139647223714707697843/100000000000000000000 : ℝ)^16 ≤ (1085676056364991/1000000000000000 : ℝ)^65 := by
      have hnat : (139647223714707697843 : ℕ)^16*1000000000000000^65 ≤ 1085676056364991^65*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        139647223714707697843 100000000000000000000 1085676056364991 1000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1085676056364991/1000000000000000 : ℝ)) (X := (139647223714707697843/100000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s3_corner1b : (89647223714707697843/50000000000000000000 : ℝ) ≤ (1443199819750647/1250000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (89647223714707697843/50000000000000000000 : ℝ)^16 ≤ (1443199819750647/1250000000000000 : ℝ)^65 := by
      have hnat : (89647223714707697843 : ℕ)^16*1250000000000000^65 ≤ 1443199819750647^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        89647223714707697843 50000000000000000000 1443199819750647 1250000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1443199819750647/1250000000000000 : ℝ)) (X := (89647223714707697843/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s3_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(85676056364991/796340000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(344418997177633/3981700000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (39817/50000 : ℝ)) (alpha := (85676056364991/796340000000000 : ℝ)) (beta := (344418997177633/3981700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow1,s3_corner1a]) (by linarith only [s3_pow1,s3_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (39817/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(85676056364991/796340000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(344418997177633/3981700000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow2 : (63459/100000 : ℝ) ^ (65/16 : ℝ) ≤ (15762631509726228513/100000000000000000000 : ℝ) := by
    have hpowers : (63459/100000 : ℝ)^65 ≤ (15762631509726228513/100000000000000000000 : ℝ)^16 := by
      have hnat : (63459 : ℕ)^65*100000000000000000000^16 ≤ 15762631509726228513^16*100000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        63459 100000 15762631509726228513 100000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (63459/100000 : ℝ)) (X := (15762631509726228513/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s3_corner2a : (115762631509726228513/100000000000000000000 : ℝ) ≤ (2591717209348929/2500000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (115762631509726228513/100000000000000000000 : ℝ)^16 ≤ (2591717209348929/2500000000000000 : ℝ)^65 := by
      have hnat : (115762631509726228513 : ℕ)^16*2500000000000000^65 ≤ 2591717209348929^65*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        115762631509726228513 100000000000000000000 2591717209348929 2500000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2591717209348929/2500000000000000 : ℝ)) (X := (115762631509726228513/100000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s3_corner2b : (65762631509726228513/50000000000000000000 : ℝ) ≤ (1069780228630167/1000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (65762631509726228513/50000000000000000000 : ℝ)^16 ≤ (1069780228630167/1000000000000000 : ℝ)^65 := by
      have hnat : (65762631509726228513 : ℕ)^16*1000000000000000^65 ≤ 1069780228630167^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        65762631509726228513 50000000000000000000 1069780228630167 1000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1069780228630167/1000000000000000 : ℝ)) (X := (65762631509726228513/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s3_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(91717209348929/1586475000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(55155574817659/1057650000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (63459/100000 : ℝ)) (alpha := (91717209348929/1586475000000000 : ℝ)) (beta := (55155574817659/1057650000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow2,s3_corner2a]) (by linarith only [s3_pow2,s3_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (63459/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(91717209348929/1586475000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(55155574817659/1057650000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s3_0 : ((-403068411/5000000000 : ℝ)*X 0 0+(1117914011/2500000000 : ℝ)*X 0 1+(-1736940891/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s3_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_1 : ((1146306569/2000000000 : ℝ)*X 1 0+(-1081870971/5000000000 : ℝ)*X 1 1+(-609862793/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s3_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_2 : ((5473524661/10000000000 : ℝ)*X 2 0+(1350678261/2500000000 : ℝ)*X 2 1+(11332783/62500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s3_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_6 : ((2688296343/5000000000 : ℝ)*X 0 0+(5321782829/10000000000 : ℝ)*X 0 1+(-1030083691/5000000000 : ℝ)*X 0 2+(2688296343/5000000000 : ℝ)*X 1 0+(5321782829/10000000000 : ℝ)*X 1 1+(-1030083691/5000000000 : ℝ)*X 1 2+(2688296343/5000000000 : ℝ)*X 2 0+(5321782829/10000000000 : ℝ)*X 2 1+(-1030083691/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s3_s3_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_7 : ((-178867757/5000000000 : ℝ)*X 0 0+(343584383/1000000000 : ℝ)*X 0 1+(-1997380297/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s3_s3_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_8 : ((4881509/10000000 : ℝ)*X 1 0+(-18998869/200000000 : ℝ)*X 1 1+(-130160277/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s3_s3_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_9 : ((4394890077/10000000000 : ℝ)*X 2 0+(895745743/1250000000 : ℝ)*X 2 1+(477922819/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s3_s3_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_13 : ((4609802343/10000000000 : ℝ)*X 0 0+(3465035563/5000000000 : ℝ)*X 0 1+(-59139681/1000000000 : ℝ)*X 0 2+(4609802343/10000000000 : ℝ)*X 1 0+(3465035563/5000000000 : ℝ)*X 1 1+(-59139681/1000000000 : ℝ)*X 1 2+(4609802343/10000000000 : ℝ)*X 2 0+(3465035563/5000000000 : ℝ)*X 2 1+(-59139681/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s3_s3_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_14 : ((-314109/625000000 : ℝ)*X 0 0+(228308163/625000000 : ℝ)*X 0 1+(-30945349/39062500 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s3_s3_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_15 : ((4265354671/10000000000 : ℝ)*X 1 0+(-210985187/1250000000 : ℝ)*X 1 1+(-6616518063/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s3_s3_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_16 : ((918761191/1250000000 : ℝ)*X 2 0+(2050025817/5000000000 : ℝ)*X 2 1+(624607589/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s3_s3_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_20 : ((3416598867/5000000000 : ℝ)*X 0 0+(551844913/1250000000 : ℝ)*X 0 1+(-111455479/1000000000 : ℝ)*X 0 2+(3416598867/5000000000 : ℝ)*X 1 0+(551844913/1250000000 : ℝ)*X 1 1+(-111455479/1000000000 : ℝ)*X 1 2+(3416598867/5000000000 : ℝ)*X 2 0+(551844913/1250000000 : ℝ)*X 2 1+(-111455479/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s3_s3_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_21 : ((5397241/10000000000 : ℝ)*X 0 0+(2817857489/5000000000 : ℝ)*X 0 1+(-6189487891/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s3_s3_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_22 : ((352862047/500000000 : ℝ)*X 1 0+(-760770623/5000000000 : ℝ)*X 1 1+(-3868432013/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s3_s3_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_23 : ((4759340379/10000000000 : ℝ)*X 2 0+(2984186589/5000000000 : ℝ)*X 2 1+(497591847/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s3_s3_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_27 : ((6519425621/10000000000 : ℝ)*X 0 0+(4373207499/10000000000 : ℝ)*X 0 1+(-423042239/2500000000 : ℝ)*X 0 2+(6519425621/10000000000 : ℝ)*X 1 0+(4373207499/10000000000 : ℝ)*X 1 1+(-423042239/2500000000 : ℝ)*X 1 2+(6519425621/10000000000 : ℝ)*X 2 0+(4373207499/10000000000 : ℝ)*X 2 1+(-423042239/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s3_s3_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s3_0 : (0 : ℝ) ≤ ((62397/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(62397/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (11701323579274124095448193533359/1063044576612150000000000000000000000 : ℝ) := by norm_num
    linear_combination (108074316899/1000000000000 : ℝ)*(base7) + (87381596827/1000000000000 : ℝ)*(base39) + (8533201691/25000000000 : ℝ)*(base60) + (3009747391961/1000000000000 : ℝ)*(major_s3_0) + (3009747391961/1000000000000 : ℝ)*(major_s3_1) + (3009747391961/1000000000000 : ℝ)*(major_s3_2) + (7313/10000000000 : ℝ)*(sp_s3_0) + (787087684619/200000000000 : ℝ)*(sp_s3_7) + (3935618493357/1000000000000 : ℝ)*(sp_s3_8) + (787124596351/200000000000 : ℝ)*(sp_s3_9) + (1062868489133/500000000000 : ℝ)*(sp_s3_13) + (23547027/125000000000 : ℝ)*(sp_s3_14) + (4518627/500000000000 : ℝ)*(sp_s3_22) + (4548857/1000000000000 : ℝ)*(sp_s3_23) + (2017662661367/1000000000000 : ℝ)*(f.failure) + (3935627530611/1000000000000 : ℝ)*(f.sum) + (174293235331654748483/252674700300000000000000000000000 : ℝ)*base62 + (95981220180389/1057650000000000000000000000 : ℝ)*base65 + (302657629006233/3981700000000000000000000000 : ℝ)*base66 + (260390337887609/396618750000000000000000000 : ℝ)*base68 + (2000376263954728833/17798839300000000000000000000000 : ℝ)*base71 + (26989068589411/236653125000000000000000000 : ℝ)*base72 + (554548443024233/796340000000000000000000000 : ℝ)*base74 + (1349575933791113/1514580000000000000000000000 : ℝ)*base76 + (43115903023942159451/301530159300000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + (1539/10000000000000000 : ℝ)*base87 + (1539/10000000000000000 : ℝ)*base89 + (1539/10000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s3_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8199/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8199/12500 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (114520810621566435471607251/7018741675000000000000000000000 : ℝ) := by norm_num
    linear_combination (314231318981/1000000000000 : ℝ)*(base7) + (86807/250000000000 : ℝ)*(base39) + (2528345361/62500000000 : ℝ)*(base60) + (2827390402377/1000000000000 : ℝ)*(major_s3_0) + (2827390402377/1000000000000 : ℝ)*(major_s3_1) + (2827390402377/1000000000000 : ℝ)*(major_s3_2) + (2240243/1000000000000 : ℝ)*(sp_s3_1) + (100721429/1000000000000 : ℝ)*(sp_s3_8) + (3566869971327/1000000000000 : ℝ)*(sp_s3_14) + (1783387556237/500000000000 : ℝ)*(sp_s3_15) + (1783439037073/500000000000 : ℝ)*(sp_s3_16) + (1104813257251/500000000000 : ℝ)*(sp_s3_20) + (8102819/1000000000000 : ℝ)*(sp_s3_21) + (4925457/250000000000 : ℝ)*(sp_s3_27) + (37908297947/20000000000 : ℝ)*(f.failure) + (1783439037073/500000000000 : ℝ)*(f.sum) + (22919429096417118011/28074966700000000000000000000000 : ℝ)*base63 + (72525426011091/352550000000000000000000000 : ℝ)*base65 + (2286455641901591/3981700000000000000000000000 : ℝ)*base66 + (460865297337799/352550000000000000000000000 : ℝ)*base69 + (4661001028301806499/17798839300000000000000000000000 : ℝ)*base70 + (5352487839891/19721093750000000000000000 : ℝ)*base72 + (622185978991911/796340000000000000000000000 : ℝ)*base75 + (350155247195233/504860000000000000000000000 : ℝ)*base77 + (9104231883632536641/100510053100000000000000000000000 : ℝ)*base79 + (1/200000000000000 : ℝ)*base86 + (1/200000000000000 : ℝ)*base88 + (1/200000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s3_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-50523/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-50523/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (7780392169449041725054100239/966404160556500000000000000000000 : ℝ) := by norm_num
    linear_combination (12294234247/40000000000 : ℝ)*(base7) + (15155203491/40000000000 : ℝ)*(base39) + (1468108600969/500000000000 : ℝ)*(major_s3_0) + (1468108600969/500000000000 : ℝ)*(major_s3_1) + (1468108600969/500000000000 : ℝ)*(major_s3_2) + (225753/125000000000 : ℝ)*(sp_s3_1) + (51918437/1000000000000 : ℝ)*(sp_s3_2) + (2820509/125000000000 : ℝ)*(sp_s3_6) + (4969003/200000000000 : ℝ)*(sp_s3_9) + (21813967/250000000000 : ℝ)*(sp_s3_20) + (3715791109801/1000000000000 : ℝ)*(sp_s3_21) + (3715789303777/1000000000000 : ℝ)*(sp_s3_22) + (74314286927/20000000000 : ℝ)*(sp_s3_23) + (113780790849/50000000000 : ℝ)*(sp_s3_27) + (393673956149/200000000000 : ℝ)*(f.failure) + (3715791109801/1000000000000 : ℝ)*(f.sum) + (26286368396800518649/63168675075000000000000000000000 : ℝ)*base63 + (84195580580659/132206250000000000000000000 : ℝ)*base65 + (443296088119401/995425000000000000000000000 : ℝ)*base66 + (608131690911581/793237500000000000000000000 : ℝ)*base69 + (2436805076428180047/8899419650000000000000000000000 : ℝ)*base71 + (256421108851183/3786450000000000000000000000 : ℝ)*base72 + (86937794278797/398170000000000000000000000 : ℝ)*base75 + (484075205087/30291600000000000000000000 : ℝ)*base77 + (10145482333453319863/75382539825000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (1367/2000000000000000 : ℝ)*base86 + (1367/2000000000000000 : ℝ)*base88 + (1367/2000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev2 : (0 : ℝ) ≤ ((75729/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(75729/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(39817/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(39817/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-63459/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-63459/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((62397/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(62397/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8199/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8199/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-50523/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-50523/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c302054_s3 p hpa hpb X hX hprev2

#print axioms solution
