-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c329053_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:28:05.793442+00:00
-- url     : https://prove2.me/submissions/06e1c1fd-d27c-4412-b3d0-9dce60e80ef5

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
theorem collision_support_c329053_s1_s1_0 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1925872147/10000000000 : ℝ)*x 0 + (619919151/1250000000 : ℝ)*x 1 + (4973800583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1925872147/10000000000 : ℝ)^95 ≤ (13795640637493/100000000000000 : ℝ)^79 := by
    have hnat : (1925872147 : ℕ)^95*100000000000000^79 ≤ 13795640637493^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1925872147 10000000000 13795640637493 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (619919151/1250000000 : ℝ)^95 ≤ (1344587266073/3125000000000 : ℝ)^79 := by
    have hnat : (619919151 : ℕ)^95*3125000000000^79 ≤ 1344587266073^79*1250000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      619919151 1250000000 1344587266073 3125000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4973800583/10000000000 : ℝ)^95 ≤ (1727102673563/4000000000000 : ℝ)^79 := by
    have hnat : (4973800583 : ℕ)^95*4000000000000^79 ≤ 1727102673563^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4973800583 10000000000 1727102673563 4000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1925872147/10000000000 : ℝ), (619919151/1250000000 : ℝ), (4973800583/10000000000 : ℝ)] ![(13795640637493/100000000000000 : ℝ), (1344587266073/3125000000000 : ℝ), (1727102673563/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1925872147/10000000000 : ℝ)|^95 ≤ (13795640637493/100000000000000 : ℝ)^79
        have hw : |(-1925872147/10000000000 : ℝ)|=(1925872147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(619919151/1250000000 : ℝ)|^95 ≤ (1344587266073/3125000000000 : ℝ)^79
        have hw : |(619919151/1250000000 : ℝ)|=(619919151/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4973800583/10000000000 : ℝ)|^95 ≤ (1727102673563/4000000000000 : ℝ)^79
        have hw : |(4973800583/10000000000 : ℝ)|=(4973800583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329053_s1_s1_1 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (221633267/500000000 : ℝ)*x 0 + (-1400650359/10000000000 : ℝ)*x 1 + (2949091083/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (221633267/500000000 : ℝ)^95 ≤ (9398172719957/25000000000000 : ℝ)^79 := by
    have hnat : (221633267 : ℕ)^95*25000000000000^79 ≤ 9398172719957^79*500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221633267 500000000 9398172719957 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1400650359/10000000000 : ℝ)^95 ≤ (58791495971/625000000000 : ℝ)^79 := by
    have hnat : (1400650359 : ℕ)^95*625000000000^79 ≤ 58791495971^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1400650359 10000000000 58791495971 625000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2949091083/5000000000 : ℝ)^95 ≤ (6625083719231/12500000000000 : ℝ)^79 := by
    have hnat : (2949091083 : ℕ)^95*12500000000000^79 ≤ 6625083719231^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2949091083 5000000000 6625083719231 12500000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(221633267/500000000 : ℝ), (-1400650359/10000000000 : ℝ), (2949091083/5000000000 : ℝ)] ![(9398172719957/25000000000000 : ℝ), (58791495971/625000000000 : ℝ), (6625083719231/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(221633267/500000000 : ℝ)|^95 ≤ (9398172719957/25000000000000 : ℝ)^79
        have hw : |(221633267/500000000 : ℝ)|=(221633267/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1400650359/10000000000 : ℝ)|^95 ≤ (58791495971/625000000000 : ℝ)^79
        have hw : |(-1400650359/10000000000 : ℝ)|=(1400650359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2949091083/5000000000 : ℝ)|^95 ≤ (6625083719231/12500000000000 : ℝ)^79
        have hw : |(2949091083/5000000000 : ℝ)|=(2949091083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329053_s1_s1_2 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4444957171/10000000000 : ℝ)*x 0 + (2947446803/5000000000 : ℝ)*x 1 + (-694757397/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4444957171/10000000000 : ℝ)^95 ≤ (18859041957119/50000000000000 : ℝ)^79 := by
    have hnat : (4444957171 : ℕ)^95*50000000000000^79 ≤ 18859041957119^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4444957171 10000000000 18859041957119 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2947446803/5000000000 : ℝ)^95 ≤ (52965136012653/100000000000000 : ℝ)^79 := by
    have hnat : (2947446803 : ℕ)^95*100000000000000^79 ≤ 52965136012653^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2947446803 5000000000 52965136012653 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (694757397/5000000000 : ℝ)^95 ≤ (4658390031087/50000000000000 : ℝ)^79 := by
    have hnat : (694757397 : ℕ)^95*50000000000000^79 ≤ 4658390031087^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      694757397 5000000000 4658390031087 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4444957171/10000000000 : ℝ), (2947446803/5000000000 : ℝ), (-694757397/5000000000 : ℝ)] ![(18859041957119/50000000000000 : ℝ), (52965136012653/100000000000000 : ℝ), (4658390031087/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4444957171/10000000000 : ℝ)|^95 ≤ (18859041957119/50000000000000 : ℝ)^79
        have hw : |(4444957171/10000000000 : ℝ)|=(4444957171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2947446803/5000000000 : ℝ)|^95 ≤ (52965136012653/100000000000000 : ℝ)^79
        have hw : |(2947446803/5000000000 : ℝ)|=(2947446803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-694757397/5000000000 : ℝ)|^95 ≤ (4658390031087/50000000000000 : ℝ)^79
        have hw : |(-694757397/5000000000 : ℝ)|=(694757397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329053_s1_s1_6 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7218637737/10000000000 : ℝ)*x 0 + (442783527/2000000000 : ℝ)*x 1 + (2191158427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7218637737/10000000000 : ℝ)^95 ≤ (527931999031/781250000000 : ℝ)^79 := by
    have hnat : (7218637737 : ℕ)^95*781250000000^79 ≤ 527931999031^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7218637737 10000000000 527931999031 781250000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (442783527/2000000000 : ℝ)^95 ≤ (16313078742319/100000000000000 : ℝ)^79 := by
    have hnat : (442783527 : ℕ)^95*100000000000000^79 ≤ 16313078742319^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442783527 2000000000 16313078742319 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2191158427/10000000000 : ℝ)^95 ≤ (16111625368517/100000000000000 : ℝ)^79 := by
    have hnat : (2191158427 : ℕ)^95*100000000000000^79 ≤ 16111625368517^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2191158427 10000000000 16111625368517 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7218637737/10000000000 : ℝ), (442783527/2000000000 : ℝ), (2191158427/10000000000 : ℝ)] ![(527931999031/781250000000 : ℝ), (16313078742319/100000000000000 : ℝ), (16111625368517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7218637737/10000000000 : ℝ)|^95 ≤ (527931999031/781250000000 : ℝ)^79
        have hw : |(7218637737/10000000000 : ℝ)|=(7218637737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(442783527/2000000000 : ℝ)|^95 ≤ (16313078742319/100000000000000 : ℝ)^79
        have hw : |(442783527/2000000000 : ℝ)|=(442783527/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2191158427/10000000000 : ℝ)|^95 ≤ (16111625368517/100000000000000 : ℝ)^79
        have hw : |(2191158427/10000000000 : ℝ)|=(2191158427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329053_s1_s1_7 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-240947701/1250000000 : ℝ)*x 0 + (235260941/500000000 : ℝ)*x 1 + (1305945631/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (240947701/1250000000 : ℝ)^95 ≤ (13810367463579/100000000000000 : ℝ)^79 := by
    have hnat : (240947701 : ℕ)^95*100000000000000^79 ≤ 13810367463579^79*1250000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      240947701 1250000000 13810367463579 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (235260941/500000000 : ℝ)^95 ≤ (5048668921251/12500000000000 : ℝ)^79 := by
    have hnat : (235260941 : ℕ)^95*12500000000000^79 ≤ 5048668921251^79*500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      235260941 500000000 5048668921251 12500000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1305945631/2500000000 : ℝ)^95 ≤ (22900140574357/50000000000000 : ℝ)^79 := by
    have hnat : (1305945631 : ℕ)^95*50000000000000^79 ≤ 22900140574357^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1305945631 2500000000 22900140574357 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-240947701/1250000000 : ℝ), (235260941/500000000 : ℝ), (1305945631/2500000000 : ℝ)] ![(13810367463579/100000000000000 : ℝ), (5048668921251/12500000000000 : ℝ), (22900140574357/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-240947701/1250000000 : ℝ)|^95 ≤ (13810367463579/100000000000000 : ℝ)^79
        have hw : |(-240947701/1250000000 : ℝ)|=(240947701/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(235260941/500000000 : ℝ)|^95 ≤ (5048668921251/12500000000000 : ℝ)^79
        have hw : |(235260941/500000000 : ℝ)|=(235260941/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1305945631/2500000000 : ℝ)|^95 ≤ (22900140574357/50000000000000 : ℝ)^79
        have hw : |(1305945631/2500000000 : ℝ)|=(1305945631/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329053_s1_s1_8 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4380611671/10000000000 : ℝ)*x 0 + (-1342758033/10000000000 : ℝ)*x 1 + (5990190987/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4380611671/10000000000 : ℝ)^95 ≤ (37062456426781/100000000000000 : ℝ)^79 := by
    have hnat : (4380611671 : ℕ)^95*100000000000000^79 ≤ 37062456426781^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4380611671 10000000000 37062456426781 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1342758033/10000000000 : ℝ)^95 ≤ (111763430441/1250000000000 : ℝ)^79 := by
    have hnat : (1342758033 : ℕ)^95*1250000000000^79 ≤ 111763430441^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342758033 10000000000 111763430441 1250000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5990190987/10000000000 : ℝ)^95 ≤ (26998234562937/50000000000000 : ℝ)^79 := by
    have hnat : (5990190987 : ℕ)^95*50000000000000^79 ≤ 26998234562937^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5990190987 10000000000 26998234562937 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4380611671/10000000000 : ℝ), (-1342758033/10000000000 : ℝ), (5990190987/10000000000 : ℝ)] ![(37062456426781/100000000000000 : ℝ), (111763430441/1250000000000 : ℝ), (26998234562937/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4380611671/10000000000 : ℝ)|^95 ≤ (37062456426781/100000000000000 : ℝ)^79
        have hw : |(4380611671/10000000000 : ℝ)|=(4380611671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1342758033/10000000000 : ℝ)|^95 ≤ (111763430441/1250000000000 : ℝ)^79
        have hw : |(-1342758033/10000000000 : ℝ)|=(1342758033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5990190987/10000000000 : ℝ)|^95 ≤ (26998234562937/50000000000000 : ℝ)^79
        have hw : |(5990190987/10000000000 : ℝ)|=(5990190987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329053_s1_s1_9 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (878581453/2000000000 : ℝ)*x 0 + (3062322913/5000000000 : ℝ)*x 1 + (-570759487/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (878581453/2000000000 : ℝ)^95 ≤ (18593794273723/50000000000000 : ℝ)^79 := by
    have hnat : (878581453 : ℕ)^95*50000000000000^79 ≤ 18593794273723^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      878581453 2000000000 18593794273723 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3062322913/5000000000 : ℝ)^95 ≤ (55457225717907/100000000000000 : ℝ)^79 := by
    have hnat : (3062322913 : ℕ)^95*100000000000000^79 ≤ 55457225717907^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3062322913 5000000000 55457225717907 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (570759487/5000000000 : ℝ)^95 ≤ (147103714281/2000000000000 : ℝ)^79 := by
    have hnat : (570759487 : ℕ)^95*2000000000000^79 ≤ 147103714281^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      570759487 5000000000 147103714281 2000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(878581453/2000000000 : ℝ), (3062322913/5000000000 : ℝ), (-570759487/5000000000 : ℝ)] ![(18593794273723/50000000000000 : ℝ), (55457225717907/100000000000000 : ℝ), (147103714281/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(878581453/2000000000 : ℝ)|^95 ≤ (18593794273723/50000000000000 : ℝ)^79
        have hw : |(878581453/2000000000 : ℝ)|=(878581453/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3062322913/5000000000 : ℝ)|^95 ≤ (55457225717907/100000000000000 : ℝ)^79
        have hw : |(3062322913/5000000000 : ℝ)|=(3062322913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-570759487/5000000000 : ℝ)|^95 ≤ (147103714281/2000000000000 : ℝ)^79
        have hw : |(-570759487/5000000000 : ℝ)|=(570759487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329053_s1_s1_13 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7222458149/10000000000 : ℝ)*x 0 + (2510706453/10000000000 : ℝ)*x 1 + (940168607/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7222458149/10000000000 : ℝ)^95 ≤ (67618305207701/100000000000000 : ℝ)^79 := by
    have hnat : (7222458149 : ℕ)^95*100000000000000^79 ≤ 67618305207701^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7222458149 10000000000 67618305207701 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2510706453/10000000000 : ℝ)^95 ≤ (18977352413357/100000000000000 : ℝ)^79 := by
    have hnat : (2510706453 : ℕ)^95*100000000000000^79 ≤ 18977352413357^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2510706453 10000000000 18977352413357 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (940168607/5000000000 : ℝ)^95 ≤ (13404342362821/100000000000000 : ℝ)^79 := by
    have hnat : (940168607 : ℕ)^95*100000000000000^79 ≤ 13404342362821^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      940168607 5000000000 13404342362821 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7222458149/10000000000 : ℝ), (2510706453/10000000000 : ℝ), (940168607/5000000000 : ℝ)] ![(67618305207701/100000000000000 : ℝ), (18977352413357/100000000000000 : ℝ), (13404342362821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7222458149/10000000000 : ℝ)|^95 ≤ (67618305207701/100000000000000 : ℝ)^79
        have hw : |(7222458149/10000000000 : ℝ)|=(7222458149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2510706453/10000000000 : ℝ)|^95 ≤ (18977352413357/100000000000000 : ℝ)^79
        have hw : |(2510706453/10000000000 : ℝ)|=(2510706453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(940168607/5000000000 : ℝ)|^95 ≤ (13404342362821/100000000000000 : ℝ)^79
        have hw : |(940168607/5000000000 : ℝ)|=(940168607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329053_s1_s1_14 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1693825303/10000000000 : ℝ)*x 0 + (492595627/1000000000 : ℝ)*x 1 + (1298807871/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1693825303/10000000000 : ℝ)^95 ≤ (11821976946857/100000000000000 : ℝ)^79 := by
    have hnat : (1693825303 : ℕ)^95*100000000000000^79 ≤ 11821976946857^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1693825303 10000000000 11821976946857 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (492595627/1000000000 : ℝ)^95 ≤ (21339299650621/50000000000000 : ℝ)^79 := by
    have hnat : (492595627 : ℕ)^95*50000000000000^79 ≤ 21339299650621^79*1000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      492595627 1000000000 21339299650621 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1298807871/2500000000 : ℝ)^95 ≤ (22749711869041/50000000000000 : ℝ)^79 := by
    have hnat : (1298807871 : ℕ)^95*50000000000000^79 ≤ 22749711869041^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1298807871 2500000000 22749711869041 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1693825303/10000000000 : ℝ), (492595627/1000000000 : ℝ), (1298807871/2500000000 : ℝ)] ![(11821976946857/100000000000000 : ℝ), (21339299650621/50000000000000 : ℝ), (22749711869041/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1693825303/10000000000 : ℝ)|^95 ≤ (11821976946857/100000000000000 : ℝ)^79
        have hw : |(-1693825303/10000000000 : ℝ)|=(1693825303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(492595627/1000000000 : ℝ)|^95 ≤ (21339299650621/50000000000000 : ℝ)^79
        have hw : |(492595627/1000000000 : ℝ)|=(492595627/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1298807871/2500000000 : ℝ)|^95 ≤ (22749711869041/50000000000000 : ℝ)^79
        have hw : |(1298807871/2500000000 : ℝ)|=(1298807871/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329053_s1_s1_15 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (34777881/80000000 : ℝ)*x 0 + (-1365091117/10000000000 : ℝ)*x 1 + (3002482403/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (34777881/80000000 : ℝ)^95 ≤ (36723142680147/100000000000000 : ℝ)^79 := by
    have hnat : (34777881 : ℕ)^95*100000000000000^79 ≤ 36723142680147^79*80000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34777881 80000000 36723142680147 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1365091117/10000000000 : ℝ)^95 ≤ (4560101494081/50000000000000 : ℝ)^79 := by
    have hnat : (1365091117 : ℕ)^95*50000000000000^79 ≤ 4560101494081^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1365091117 10000000000 4560101494081 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3002482403/5000000000 : ℝ)^95 ≤ (54156654316867/100000000000000 : ℝ)^79 := by
    have hnat : (3002482403 : ℕ)^95*100000000000000^79 ≤ 54156654316867^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3002482403 5000000000 54156654316867 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(34777881/80000000 : ℝ), (-1365091117/10000000000 : ℝ), (3002482403/5000000000 : ℝ)] ![(36723142680147/100000000000000 : ℝ), (4560101494081/50000000000000 : ℝ), (54156654316867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(34777881/80000000 : ℝ)|^95 ≤ (36723142680147/100000000000000 : ℝ)^79
        have hw : |(34777881/80000000 : ℝ)|=(34777881/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1365091117/10000000000 : ℝ)|^95 ≤ (4560101494081/50000000000000 : ℝ)^79
        have hw : |(-1365091117/10000000000 : ℝ)|=(1365091117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3002482403/5000000000 : ℝ)|^95 ≤ (54156654316867/100000000000000 : ℝ)^79
        have hw : |(3002482403/5000000000 : ℝ)|=(3002482403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329053_s1_s1_16 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (233949589/500000000 : ℝ)*x 0 + (1166732669/2000000000 : ℝ)*x 1 + (-1170069541/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (233949589/500000000 : ℝ)^95 ≤ (5014847077107/12500000000000 : ℝ)^79 := by
    have hnat : (233949589 : ℕ)^95*12500000000000^79 ≤ 5014847077107^79*500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      233949589 500000000 5014847077107 12500000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1166732669/2000000000 : ℝ)^95 ≤ (26152131190209/50000000000000 : ℝ)^79 := by
    have hnat : (1166732669 : ℕ)^95*50000000000000^79 ≤ 26152131190209^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1166732669 2000000000 26152131190209 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1170069541/10000000000 : ℝ)^95 ≤ (378848049293/5000000000000 : ℝ)^79 := by
    have hnat : (1170069541 : ℕ)^95*5000000000000^79 ≤ 378848049293^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1170069541 10000000000 378848049293 5000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(233949589/500000000 : ℝ), (1166732669/2000000000 : ℝ), (-1170069541/10000000000 : ℝ)] ![(5014847077107/12500000000000 : ℝ), (26152131190209/50000000000000 : ℝ), (378848049293/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(233949589/500000000 : ℝ)|^95 ≤ (5014847077107/12500000000000 : ℝ)^79
        have hw : |(233949589/500000000 : ℝ)|=(233949589/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1166732669/2000000000 : ℝ)|^95 ≤ (26152131190209/50000000000000 : ℝ)^79
        have hw : |(1166732669/2000000000 : ℝ)|=(1166732669/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1170069541/10000000000 : ℝ)|^95 ≤ (378848049293/5000000000000 : ℝ)^79
        have hw : |(-1170069541/10000000000 : ℝ)|=(1170069541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329053_s1_s1_20 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3758946603/5000000000 : ℝ)*x 0 + (1093392907/5000000000 : ℝ)*x 1 + (1829409937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3758946603/5000000000 : ℝ)^95 ≤ (35479027434757/50000000000000 : ℝ)^79 := by
    have hnat : (3758946603 : ℕ)^95*50000000000000^79 ≤ 35479027434757^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3758946603 5000000000 35479027434757 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1093392907/5000000000 : ℝ)^95 ≤ (8036484755487/50000000000000 : ℝ)^79 := by
    have hnat : (1093392907 : ℕ)^95*50000000000000^79 ≤ 8036484755487^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093392907 5000000000 8036484755487 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1829409937/10000000000 : ℝ)^95 ≤ (6484487805087/50000000000000 : ℝ)^79 := by
    have hnat : (1829409937 : ℕ)^95*50000000000000^79 ≤ 6484487805087^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1829409937 10000000000 6484487805087 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3758946603/5000000000 : ℝ), (1093392907/5000000000 : ℝ), (1829409937/10000000000 : ℝ)] ![(35479027434757/50000000000000 : ℝ), (8036484755487/50000000000000 : ℝ), (6484487805087/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3758946603/5000000000 : ℝ)|^95 ≤ (35479027434757/50000000000000 : ℝ)^79
        have hw : |(3758946603/5000000000 : ℝ)|=(3758946603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1093392907/5000000000 : ℝ)|^95 ≤ (8036484755487/50000000000000 : ℝ)^79
        have hw : |(1093392907/5000000000 : ℝ)|=(1093392907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1829409937/10000000000 : ℝ)|^95 ≤ (6484487805087/50000000000000 : ℝ)^79
        have hw : |(1829409937/10000000000 : ℝ)|=(1829409937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329053_s1_s1_21 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-832449011/5000000000 : ℝ)*x 0 + (202108497/400000000 : ℝ)*x 1 + (2546157607/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (832449011/5000000000 : ℝ)^95 ≤ (2894902910749/25000000000000 : ℝ)^79 := by
    have hnat : (832449011 : ℕ)^95*25000000000000^79 ≤ 2894902910749^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      832449011 5000000000 2894902910749 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (202108497/400000000 : ℝ)^95 ≤ (4400265957949/10000000000000 : ℝ)^79 := by
    have hnat : (202108497 : ℕ)^95*10000000000000^79 ≤ 4400265957949^79*400000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      202108497 400000000 4400265957949 10000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2546157607/5000000000 : ℝ)^95 ≤ (11104432189443/25000000000000 : ℝ)^79 := by
    have hnat : (2546157607 : ℕ)^95*25000000000000^79 ≤ 11104432189443^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2546157607 5000000000 11104432189443 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-832449011/5000000000 : ℝ), (202108497/400000000 : ℝ), (2546157607/5000000000 : ℝ)] ![(2894902910749/25000000000000 : ℝ), (4400265957949/10000000000000 : ℝ), (11104432189443/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-832449011/5000000000 : ℝ)|^95 ≤ (2894902910749/25000000000000 : ℝ)^79
        have hw : |(-832449011/5000000000 : ℝ)|=(832449011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(202108497/400000000 : ℝ)|^95 ≤ (4400265957949/10000000000000 : ℝ)^79
        have hw : |(202108497/400000000 : ℝ)|=(202108497/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2546157607/5000000000 : ℝ)|^95 ≤ (11104432189443/25000000000000 : ℝ)^79
        have hw : |(2546157607/5000000000 : ℝ)|=(2546157607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329053_s1_s1_22 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (939124517/2000000000 : ℝ)*x 0 + (-607272161/5000000000 : ℝ)*x 1 + (1446367161/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (939124517/2000000000 : ℝ)^95 ≤ (20145157502811/50000000000000 : ℝ)^79 := by
    have hnat : (939124517 : ℕ)^95*50000000000000^79 ≤ 20145157502811^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      939124517 2000000000 20145157502811 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (607272161/5000000000 : ℝ)^95 ≤ (1981153424333/25000000000000 : ℝ)^79 := by
    have hnat : (607272161 : ℕ)^95*25000000000000^79 ≤ 1981153424333^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      607272161 5000000000 1981153424333 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1446367161/2500000000 : ℝ)^95 ≤ (25892535641841/50000000000000 : ℝ)^79 := by
    have hnat : (1446367161 : ℕ)^95*50000000000000^79 ≤ 25892535641841^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1446367161 2500000000 25892535641841 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(939124517/2000000000 : ℝ), (-607272161/5000000000 : ℝ), (1446367161/2500000000 : ℝ)] ![(20145157502811/50000000000000 : ℝ), (1981153424333/25000000000000 : ℝ), (25892535641841/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(939124517/2000000000 : ℝ)|^95 ≤ (20145157502811/50000000000000 : ℝ)^79
        have hw : |(939124517/2000000000 : ℝ)|=(939124517/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-607272161/5000000000 : ℝ)|^95 ≤ (1981153424333/25000000000000 : ℝ)^79
        have hw : |(-607272161/5000000000 : ℝ)|=(607272161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1446367161/2500000000 : ℝ)|^95 ≤ (25892535641841/50000000000000 : ℝ)^79
        have hw : |(1446367161/2500000000 : ℝ)|=(1446367161/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329053_s1_s1_23 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (434812717/1000000000 : ℝ)*x 0 + (6059805861/10000000000 : ℝ)*x 1 + (-1289434451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (434812717/1000000000 : ℝ)^95 ≤ (36732204574841/100000000000000 : ℝ)^79 := by
    have hnat : (434812717 : ℕ)^95*100000000000000^79 ≤ 36732204574841^79*1000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434812717 1000000000 36732204574841 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6059805861/10000000000 : ℝ)^95 ≤ (54751965669363/100000000000000 : ℝ)^79 := by
    have hnat : (6059805861 : ℕ)^95*100000000000000^79 ≤ 54751965669363^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6059805861 10000000000 54751965669363 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1289434451/10000000000 : ℝ)^95 ≤ (133059839617/1562500000000 : ℝ)^79 := by
    have hnat : (1289434451 : ℕ)^95*1562500000000^79 ≤ 133059839617^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1289434451 10000000000 133059839617 1562500000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(434812717/1000000000 : ℝ), (6059805861/10000000000 : ℝ), (-1289434451/10000000000 : ℝ)] ![(36732204574841/100000000000000 : ℝ), (54751965669363/100000000000000 : ℝ), (133059839617/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(434812717/1000000000 : ℝ)|^95 ≤ (36732204574841/100000000000000 : ℝ)^79
        have hw : |(434812717/1000000000 : ℝ)|=(434812717/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6059805861/10000000000 : ℝ)|^95 ≤ (54751965669363/100000000000000 : ℝ)^79
        have hw : |(6059805861/10000000000 : ℝ)|=(6059805861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1289434451/10000000000 : ℝ)|^95 ≤ (133059839617/1562500000000 : ℝ)^79
        have hw : |(-1289434451/10000000000 : ℝ)|=(1289434451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329053_s1_s1_27 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (755720441/1000000000 : ℝ)*x 0 + (1978331309/10000000000 : ℝ)*x 1 + (79585519/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (755720441/1000000000 : ℝ)^95 ≤ (35702239672753/50000000000000 : ℝ)^79 := by
    have hnat : (755720441 : ℕ)^95*50000000000000^79 ≤ 35702239672753^79*1000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      755720441 1000000000 35702239672753 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1978331309/10000000000 : ℝ)^95 ≤ (7124383873017/50000000000000 : ℝ)^79 := by
    have hnat : (1978331309 : ℕ)^95*50000000000000^79 ≤ 7124383873017^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1978331309 10000000000 7124383873017 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (79585519/400000000 : ℝ)^95 ≤ (7173376447757/50000000000000 : ℝ)^79 := by
    have hnat : (79585519 : ℕ)^95*50000000000000^79 ≤ 7173376447757^79*400000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79585519 400000000 7173376447757 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(755720441/1000000000 : ℝ), (1978331309/10000000000 : ℝ), (79585519/400000000 : ℝ)] ![(35702239672753/50000000000000 : ℝ), (7124383873017/50000000000000 : ℝ), (7173376447757/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(755720441/1000000000 : ℝ)|^95 ≤ (35702239672753/50000000000000 : ℝ)^79
        have hw : |(755720441/1000000000 : ℝ)|=(755720441/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1978331309/10000000000 : ℝ)|^95 ≤ (7124383873017/50000000000000 : ℝ)^79
        have hw : |(1978331309/10000000000 : ℝ)|=(1978331309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(79585519/400000000 : ℝ)|^95 ≤ (7173376447757/50000000000000 : ℝ)^79
        have hw : |(79585519/400000000 : ℝ)|=(79585519/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c329053_s1 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (55589/25000 : ℝ) (160257/100000 : ℝ) (10347/12500 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((7421/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7421/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7447/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(7447/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(11549/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(11549/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((3333/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3333/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22207/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(22207/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(21759/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(21759/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (10347/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (10347/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (10347/12500 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (10347/12500 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (10347/12500 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (10347/12500 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (7421/12500 : ℝ) ^ (93/16 : ℝ) ≤ (1207017152290484753/25000000000000000000 : ℝ) := by
    have hpowers : (7421/12500 : ℝ)^93 ≤ (1207017152290484753/25000000000000000000 : ℝ)^16 := by
      have hnat : (7421 : ℕ)^93*25000000000000000000^16 ≤ 1207017152290484753^16*12500^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7421 12500 1207017152290484753 25000000000000000000 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7421/12500 : ℝ)) (X := (1207017152290484753/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (26207017152290484753/25000000000000000000 : ℝ) ≤ (5040725286888303/5000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (26207017152290484753/25000000000000000000 : ℝ)^16 ≤ (5040725286888303/5000000000000000 : ℝ)^93 := by
      have hnat : (26207017152290484753 : ℕ)^16*5000000000000000^93 ≤ 5040725286888303^93*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26207017152290484753 25000000000000000000 5040725286888303 5000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5040725286888303/5000000000000000 : ℝ)) (X := (26207017152290484753/25000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (13707017152290484753/12500000000000000000 : ℝ) ≤ (1015985215244443/1000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (13707017152290484753/12500000000000000000 : ℝ)^16 ≤ (1015985215244443/1000000000000000 : ℝ)^93 := by
      have hnat : (13707017152290484753 : ℕ)^16*1000000000000000^93 ≤ 1015985215244443^93*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13707017152290484753 12500000000000000000 1015985215244443 1000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1015985215244443/1000000000000000 : ℝ)) (X := (13707017152290484753/12500000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(40725286888303/2968400000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(4900098666739/371050000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (7421/12500 : ℝ)) (alpha := (40725286888303/2968400000000000 : ℝ)) (beta := (4900098666739/371050000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (7421/12500 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(40725286888303/2968400000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(4900098666739/371050000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (7447/12500 : ℝ) ^ (93/16 : ℝ) ≤ (2463611217819018811/50000000000000000000 : ℝ) := by
    have hpowers : (7447/12500 : ℝ)^93 ≤ (2463611217819018811/50000000000000000000 : ℝ)^16 := by
      have hnat : (7447 : ℕ)^93*50000000000000000000^16 ≤ 2463611217819018811^16*12500^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7447 12500 2463611217819018811 50000000000000000000 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7447/12500 : ℝ)) (X := (2463611217819018811/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (52463611217819018811/50000000000000000000 : ℝ) ≤ (10083090491131077/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (52463611217819018811/50000000000000000000 : ℝ)^16 ≤ (10083090491131077/10000000000000000 : ℝ)^93 := by
      have hnat : (52463611217819018811 : ℕ)^16*10000000000000000^93 ≤ 10083090491131077^93*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52463611217819018811 50000000000000000000 10083090491131077 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10083090491131077/10000000000000000 : ℝ)) (X := (52463611217819018811/50000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (27463611217819018811/25000000000000000000 : ℝ) ≤ (1270376354437907/1250000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (27463611217819018811/25000000000000000000 : ℝ)^16 ≤ (1270376354437907/1250000000000000 : ℝ)^93 := by
      have hnat : (27463611217819018811 : ℕ)^16*1250000000000000^93 ≤ 1270376354437907^93*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27463611217819018811 25000000000000000000 1270376354437907 1250000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1270376354437907/1250000000000000 : ℝ)) (X := (27463611217819018811/25000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(83090491131077/5957600000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(79920344372179/5957600000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (7447/12500 : ℝ)) (alpha := (83090491131077/5957600000000000 : ℝ)) (beta := (79920344372179/5957600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (7447/12500 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(83090491131077/5957600000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(79920344372179/5957600000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (11549/20000 : ℝ) ^ (93/16 : ℝ) ≤ (164385065149283907/4000000000000000000 : ℝ) := by
    have hpowers : (11549/20000 : ℝ)^93 ≤ (164385065149283907/4000000000000000000 : ℝ)^16 := by
      have hnat : (11549 : ℕ)^93*4000000000000000000^16 ≤ 164385065149283907^16*20000^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11549 20000 164385065149283907 4000000000000000000 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11549/20000 : ℝ)) (X := (164385065149283907/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (4164385065149283907/4000000000000000000 : ℝ) ≤ (10069529653774199/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (4164385065149283907/4000000000000000000 : ℝ)^16 ≤ (10069529653774199/10000000000000000 : ℝ)^93 := by
      have hnat : (4164385065149283907 : ℕ)^16*10000000000000000^93 ≤ 10069529653774199^93*4000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4164385065149283907 4000000000000000000 10069529653774199 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10069529653774199/10000000000000000 : ℝ)) (X := (4164385065149283907/4000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (2164385065149283907/2000000000000000000 : ℝ) ≤ (2534205702210477/2500000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (2164385065149283907/2000000000000000000 : ℝ)^16 ≤ (2534205702210477/2500000000000000 : ℝ)^93 := by
      have hnat : (2164385065149283907 : ℕ)^16*2500000000000000^93 ≤ 2534205702210477^93*2000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2164385065149283907 2000000000000000000 2534205702210477 2500000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2534205702210477/2500000000000000 : ℝ)) (X := (2164385065149283907/2000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(69529653774199/5774500000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(67293155067709/5774500000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (11549/20000 : ℝ)) (alpha := (69529653774199/5774500000000000 : ℝ)) (beta := (67293155067709/5774500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (11549/20000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(69529653774199/5774500000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(67293155067709/5774500000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1925872147/10000000000 : ℝ)*X 0 0+(619919151/1250000000 : ℝ)*X 0 1+(4973800583/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329053_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((221633267/500000000 : ℝ)*X 1 0+(-1400650359/10000000000 : ℝ)*X 1 1+(2949091083/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329053_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((4444957171/10000000000 : ℝ)*X 2 0+(2947446803/5000000000 : ℝ)*X 2 1+(-694757397/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329053_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((7218637737/10000000000 : ℝ)*X 0 0+(442783527/2000000000 : ℝ)*X 0 1+(2191158427/10000000000 : ℝ)*X 0 2+(7218637737/10000000000 : ℝ)*X 1 0+(442783527/2000000000 : ℝ)*X 1 1+(2191158427/10000000000 : ℝ)*X 1 2+(7218637737/10000000000 : ℝ)*X 2 0+(442783527/2000000000 : ℝ)*X 2 1+(2191158427/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329053_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-240947701/1250000000 : ℝ)*X 0 0+(235260941/500000000 : ℝ)*X 0 1+(1305945631/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329053_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((4380611671/10000000000 : ℝ)*X 1 0+(-1342758033/10000000000 : ℝ)*X 1 1+(5990190987/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329053_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((878581453/2000000000 : ℝ)*X 2 0+(3062322913/5000000000 : ℝ)*X 2 1+(-570759487/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329053_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((7222458149/10000000000 : ℝ)*X 0 0+(2510706453/10000000000 : ℝ)*X 0 1+(940168607/5000000000 : ℝ)*X 0 2+(7222458149/10000000000 : ℝ)*X 1 0+(2510706453/10000000000 : ℝ)*X 1 1+(940168607/5000000000 : ℝ)*X 1 2+(7222458149/10000000000 : ℝ)*X 2 0+(2510706453/10000000000 : ℝ)*X 2 1+(940168607/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329053_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-1693825303/10000000000 : ℝ)*X 0 0+(492595627/1000000000 : ℝ)*X 0 1+(1298807871/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329053_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((34777881/80000000 : ℝ)*X 1 0+(-1365091117/10000000000 : ℝ)*X 1 1+(3002482403/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329053_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((233949589/500000000 : ℝ)*X 2 0+(1166732669/2000000000 : ℝ)*X 2 1+(-1170069541/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329053_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((3758946603/5000000000 : ℝ)*X 0 0+(1093392907/5000000000 : ℝ)*X 0 1+(1829409937/10000000000 : ℝ)*X 0 2+(3758946603/5000000000 : ℝ)*X 1 0+(1093392907/5000000000 : ℝ)*X 1 1+(1829409937/10000000000 : ℝ)*X 1 2+(3758946603/5000000000 : ℝ)*X 2 0+(1093392907/5000000000 : ℝ)*X 2 1+(1829409937/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329053_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-832449011/5000000000 : ℝ)*X 0 0+(202108497/400000000 : ℝ)*X 0 1+(2546157607/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329053_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((939124517/2000000000 : ℝ)*X 1 0+(-607272161/5000000000 : ℝ)*X 1 1+(1446367161/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329053_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((434812717/1000000000 : ℝ)*X 2 0+(6059805861/10000000000 : ℝ)*X 2 1+(-1289434451/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329053_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((755720441/1000000000 : ℝ)*X 0 0+(1978331309/10000000000 : ℝ)*X 0 1+(79585519/400000000 : ℝ)*X 0 2+(755720441/1000000000 : ℝ)*X 1 0+(1978331309/10000000000 : ℝ)*X 1 1+(79585519/400000000 : ℝ)*X 1 2+(755720441/1000000000 : ℝ)*X 2 0+(1978331309/10000000000 : ℝ)*X 2 1+(79585519/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329053_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((3333/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3333/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (366499865287305723546229131/43002701500000000000000000000000 : ℝ) := by norm_num
    linear_combination (946937114067/500000000000 : ℝ)*(base49) + (2999105612607/1000000000000 : ℝ)*(base59) + (10271184609131/500000000000 : ℝ)*(major_s1_0) + (10271184609131/500000000000 : ℝ)*(major_s1_1) + (10271184609131/500000000000 : ℝ)*(major_s1_2) + (286473681/1000000000000 : ℝ)*(sp_s1_0) + (1157461/100000000000 : ℝ)*(sp_s1_6) + (31845933709039/1000000000000 : ℝ)*(sp_s1_7) + (7961376693277/250000000000 : ℝ)*(sp_s1_8) + (31845758343641/1000000000000 : ℝ)*(sp_s1_9) + (4619246496929/500000000000 : ℝ)*(sp_s1_13) + (5422213/500000000000 : ℝ)*(sp_s1_14) + (724254037/1000000000000 : ℝ)*(sp_s1_15) + (94536701/200000000000 : ℝ)*(sp_s1_23) + (2309626142117/250000000000 : ℝ)*(f.failure) + (15923115513573/500000000000 : ℝ)*(f.sum) + (20751792181744958441/172010806000000000000000000000000 : ℝ)*base62 + (401505211274079/2887250000000000000000000000 : ℝ)*base64 + (2165099745569449/2978800000000000000000000000 : ℝ)*base66 + (16197312746257/360906250000000000000000000 : ℝ)*base68 + (6748460040783865149/85705129000000000000000000000000 : ℝ)*base71 + (35668392245059/185525000000000000000000000 : ℝ)*base73 + (1428405881086673/2978800000000000000000000000 : ℝ)*base74 + (590275058649207/1484200000000000000000000000 : ℝ)*base76 + (8152470603490315701/22105674800000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (4413/6250000000000000 : ℝ)*base87 + (4413/6250000000000000 : ℝ)*base89 + (4413/6250000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22207/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(22207/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (975678461770811118463261779/85705129000000000000000000000000 : ℝ) := by norm_num
    linear_combination (199716651269/100000000000 : ℝ)*(base49) + (582263311169/250000000000 : ℝ)*(base59) + (20191841427867/1000000000000 : ℝ)*(major_s1_0) + (20191841427867/1000000000000 : ℝ)*(major_s1_1) + (20191841427867/1000000000000 : ℝ)*(major_s1_2) + (152341727/1000000000000 : ℝ)*(sp_s1_1) + (16215893/250000000000 : ℝ)*(sp_s1_2) + (341993/40000000000 : ℝ)*(sp_s1_6) + (87222901/500000000000 : ℝ)*(sp_s1_7) + (1565132132579/50000000000 : ℝ)*(sp_s1_14) + (6260532951131/200000000000 : ℝ)*(sp_s1_15) + (3130275223381/100000000000 : ℝ)*(sp_s1_16) + (4540318577541/500000000000 : ℝ)*(sp_s1_20) + (216258731/1000000000000 : ℝ)*(sp_s1_27) + (4540430981819/500000000000 : ℝ)*(f.failure) + (15651408548691/500000000000 : ℝ)*(f.sum) + (66492548523794915263/344021612000000000000000000000000 : ℝ)*base63 + (3272053526464603/5774500000000000000000000000 : ℝ)*base64 + (757159817591713/5957600000000000000000000000 : ℝ)*base66 + (2057985087317367/5774500000000000000000000000 : ℝ)*base68 + (4765698185313046807/171410258000000000000000000000000 : ℝ)*base70 + (186127404248117/371050000000000000000000000 : ℝ)*base72 + (2133726981903881/5957600000000000000000000000 : ℝ)*base74 + (1448782851774859/2968400000000000000000000000 : ℝ)*base76 + (18818244902371069363/44211349600000000000000000000000 : ℝ)*base79 + (1109/12500000000000000 : ℝ)*base86 + (1109/12500000000000000 : ℝ)*base88 + (1109/12500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(21759/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(21759/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3883801348841807846925492014463/255298438265200000000000000000000000 : ℝ) := by norm_num
    linear_combination (131650805337/500000000000 : ℝ)*(base40) + (856291844341/500000000000 : ℝ)*(base49) + (208091261873/100000000000 : ℝ)*(base59) + (17928498444083/1000000000000 : ℝ)*(major_s1_0) + (17928498444083/1000000000000 : ℝ)*(major_s1_1) + (17928498444083/1000000000000 : ℝ)*(major_s1_2) + (212399461/1000000000000 : ℝ)*(sp_s1_0) + (76667021/1000000000000 : ℝ)*(sp_s1_2) + (103501027/1000000000000 : ℝ)*(sp_s1_16) + (74716533/100000000000 : ℝ)*(sp_s1_20) + (6948452256527/250000000000 : ℝ)*(sp_s1_21) + (27794021425569/1000000000000 : ℝ)*(sp_s1_22) + (27793841257521/1000000000000 : ℝ)*(sp_s1_23) + (2015555806583/250000000000 : ℝ)*(sp_s1_27) + (4031485195831/500000000000 : ℝ)*(f.failure) + (27794021425569/1000000000000 : ℝ)*(f.sum) + (88835119399322310313/344021612000000000000000000000000 : ℝ)*base62 + (4074980224606047/5774500000000000000000000000 : ℝ)*base64 + (582848103878457/5957600000000000000000000000 : ℝ)*base66 + (2696868982774733/5774500000000000000000000000 : ℝ)*base68 + (154566991632584095343/171410258000000000000000000000000 : ℝ)*base70 + (48760988617007/371050000000000000000000000 : ℝ)*base73 + (2786385607251569/5957600000000000000000000000 : ℝ)*base74 + (2089519154516051/2968400000000000000000000000 : ℝ)*base76 + (24073454371897384747/44211349600000000000000000000000 : ℝ)*base79 + (11959/12500000000000000 : ℝ)*base87 + (11959/12500000000000000 : ℝ)*base89 + (11959/12500000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (55589/25000 : ℝ) (160257/100000 : ℝ) (10347/12500 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((7421/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7421/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7447/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(7447/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(11549/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(11549/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((3333/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3333/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22207/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(22207/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(21759/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(21759/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c329053_s1 p hpa hpb X hX hprev0

#print axioms solution
