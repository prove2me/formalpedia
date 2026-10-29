-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c317060_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:15:36.268166+00:00
-- url     : https://prove2.me/submissions/2d8d0397-3f91-4ead-91f4-56ac2a687689

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
theorem collision_support_c317060_s1_s1_0 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1911711307/10000000000 : ℝ)*x 0 + (411211319/1000000000 : ℝ)*x 1 + (-6202535579/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1911711307/10000000000 : ℝ)^39 ≤ (31183360347/250000000000 : ℝ)^31 := by
    have hnat : (1911711307 : ℕ)^39*250000000000^31 ≤ 31183360347^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1911711307 10000000000 31183360347 250000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (411211319/1000000000 : ℝ)^39 ≤ (510844795511/1562500000000 : ℝ)^31 := by
    have hnat : (411211319 : ℕ)^39*1562500000000^31 ≤ 510844795511^31*1000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      411211319 1000000000 510844795511 1562500000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6202535579/10000000000 : ℝ)^39 ≤ (2193303557303/4000000000000 : ℝ)^31 := by
    have hnat : (6202535579 : ℕ)^39*4000000000000^31 ≤ 2193303557303^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6202535579 10000000000 2193303557303 4000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1911711307/10000000000 : ℝ), (411211319/1000000000 : ℝ), (-6202535579/10000000000 : ℝ)] ![(31183360347/250000000000 : ℝ), (510844795511/1562500000000 : ℝ), (2193303557303/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1911711307/10000000000 : ℝ)|^39 ≤ (31183360347/250000000000 : ℝ)^31
        have hw : |(-1911711307/10000000000 : ℝ)|=(1911711307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(411211319/1000000000 : ℝ)|^39 ≤ (510844795511/1562500000000 : ℝ)^31
        have hw : |(411211319/1000000000 : ℝ)|=(411211319/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6202535579/10000000000 : ℝ)|^39 ≤ (2193303557303/4000000000000 : ℝ)^31
        have hw : |(-6202535579/10000000000 : ℝ)|=(6202535579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317060_s1_s1_2 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1165108547/2500000000 : ℝ)*x 0 + (730082863/1250000000 : ℝ)*x 1 + (1716330127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1165108547/2500000000 : ℝ)^39 ≤ (9567511705263/25000000000000 : ℝ)^31 := by
    have hnat : (1165108547 : ℕ)^39*25000000000000^31 ≤ 9567511705263^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1165108547 2500000000 9567511705263 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (730082863/1250000000 : ℝ)^39 ≤ (50838684828579/100000000000000 : ℝ)^31 := by
    have hnat : (730082863 : ℕ)^39*100000000000000^31 ≤ 50838684828579^31*1250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      730082863 1250000000 50838684828579 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1716330127/10000000000 : ℝ)^39 ≤ (5445634168633/50000000000000 : ℝ)^31 := by
    have hnat : (1716330127 : ℕ)^39*50000000000000^31 ≤ 5445634168633^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1716330127 10000000000 5445634168633 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1165108547/2500000000 : ℝ), (730082863/1250000000 : ℝ), (1716330127/10000000000 : ℝ)] ![(9567511705263/25000000000000 : ℝ), (50838684828579/100000000000000 : ℝ), (5445634168633/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1165108547/2500000000 : ℝ)|^39 ≤ (9567511705263/25000000000000 : ℝ)^31
        have hw : |(1165108547/2500000000 : ℝ)|=(1165108547/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(730082863/1250000000 : ℝ)|^39 ≤ (50838684828579/100000000000000 : ℝ)^31
        have hw : |(730082863/1250000000 : ℝ)|=(730082863/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1716330127/10000000000 : ℝ)|^39 ≤ (5445634168633/50000000000000 : ℝ)^31
        have hw : |(1716330127/10000000000 : ℝ)|=(1716330127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317060_s1_s1_6 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1414036901/2000000000 : ℝ)*x 0 + (801479387/2000000000 : ℝ)*x 1 + (-90933801/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1414036901/2000000000 : ℝ)^39 ≤ (32325419559223/50000000000000 : ℝ)^31 := by
    have hnat : (1414036901 : ℕ)^39*50000000000000^31 ≤ 32325419559223^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1414036901 2000000000 32325419559223 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (801479387/2000000000 : ℝ)^39 ≤ (3165011039857/10000000000000 : ℝ)^31 := by
    have hnat : (801479387 : ℕ)^39*10000000000000^31 ≤ 3165011039857^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      801479387 2000000000 3165011039857 10000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (90933801/1250000000 : ℝ)^39 ≤ (3699050463709/100000000000000 : ℝ)^31 := by
    have hnat : (90933801 : ℕ)^39*100000000000000^31 ≤ 3699050463709^31*1250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90933801 1250000000 3699050463709 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1414036901/2000000000 : ℝ), (801479387/2000000000 : ℝ), (-90933801/1250000000 : ℝ)] ![(32325419559223/50000000000000 : ℝ), (3165011039857/10000000000000 : ℝ), (3699050463709/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1414036901/2000000000 : ℝ)|^39 ≤ (32325419559223/50000000000000 : ℝ)^31
        have hw : |(1414036901/2000000000 : ℝ)|=(1414036901/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(801479387/2000000000 : ℝ)|^39 ≤ (3165011039857/10000000000000 : ℝ)^31
        have hw : |(801479387/2000000000 : ℝ)|=(801479387/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-90933801/1250000000 : ℝ)|^39 ≤ (3699050463709/100000000000000 : ℝ)^31
        have hw : |(-90933801/1250000000 : ℝ)|=(90933801/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317060_s1_s1_7 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-357294209/2000000000 : ℝ)*x 0 + (3939484591/10000000000 : ℝ)*x 1 + (-6447346731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (357294209/2000000000 : ℝ)^39 ≤ (5727072630333/50000000000000 : ℝ)^31 := by
    have hnat : (357294209 : ℕ)^39*50000000000000^31 ≤ 5727072630333^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      357294209 2000000000 5727072630333 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3939484591/10000000000 : ℝ)^39 ≤ (6195361718033/20000000000000 : ℝ)^31 := by
    have hnat : (3939484591 : ℕ)^39*20000000000000^31 ≤ 6195361718033^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3939484591 10000000000 6195361718033 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6447346731/10000000000 : ℝ)^39 ≤ (14392261531507/25000000000000 : ℝ)^31 := by
    have hnat : (6447346731 : ℕ)^39*25000000000000^31 ≤ 14392261531507^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6447346731 10000000000 14392261531507 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-357294209/2000000000 : ℝ), (3939484591/10000000000 : ℝ), (-6447346731/10000000000 : ℝ)] ![(5727072630333/50000000000000 : ℝ), (6195361718033/20000000000000 : ℝ), (14392261531507/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-357294209/2000000000 : ℝ)|^39 ≤ (5727072630333/50000000000000 : ℝ)^31
        have hw : |(-357294209/2000000000 : ℝ)|=(357294209/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3939484591/10000000000 : ℝ)|^39 ≤ (6195361718033/20000000000000 : ℝ)^31
        have hw : |(3939484591/10000000000 : ℝ)|=(3939484591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6447346731/10000000000 : ℝ)|^39 ≤ (14392261531507/25000000000000 : ℝ)^31
        have hw : |(-6447346731/10000000000 : ℝ)|=(6447346731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317060_s1_s1_8 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2104864653/5000000000 : ℝ)*x 0 + (-36275507/250000000 : ℝ)*x 1 + (-805253989/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2104864653/5000000000 : ℝ)^39 ≤ (8418360386687/25000000000000 : ℝ)^31 := by
    have hnat : (2104864653 : ℕ)^39*25000000000000^31 ≤ 8418360386687^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2104864653 5000000000 8418360386687 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (36275507/250000000 : ℝ)^39 ≤ (1102151175571/12500000000000 : ℝ)^31 := by
    have hnat : (36275507 : ℕ)^39*12500000000000^31 ≤ 1102151175571^31*250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36275507 250000000 1102151175571 12500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (805253989/1250000000 : ℝ)^39 ≤ (14377337257937/25000000000000 : ℝ)^31 := by
    have hnat : (805253989 : ℕ)^39*25000000000000^31 ≤ 14377337257937^31*1250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      805253989 1250000000 14377337257937 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2104864653/5000000000 : ℝ), (-36275507/250000000 : ℝ), (-805253989/1250000000 : ℝ)] ![(8418360386687/25000000000000 : ℝ), (1102151175571/12500000000000 : ℝ), (14377337257937/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2104864653/5000000000 : ℝ)|^39 ≤ (8418360386687/25000000000000 : ℝ)^31
        have hw : |(2104864653/5000000000 : ℝ)|=(2104864653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-36275507/250000000 : ℝ)|^39 ≤ (1102151175571/12500000000000 : ℝ)^31
        have hw : |(-36275507/250000000 : ℝ)|=(36275507/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-805253989/1250000000 : ℝ)|^39 ≤ (14377337257937/25000000000000 : ℝ)^31
        have hw : |(-805253989/1250000000 : ℝ)|=(805253989/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317060_s1_s1_9 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4381257083/10000000000 : ℝ)*x 0 + (664815269/1000000000 : ℝ)*x 1 + (888584539/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4381257083/10000000000 : ℝ)^39 ≤ (8852136409311/25000000000000 : ℝ)^31 := by
    have hnat : (4381257083 : ℕ)^39*25000000000000^31 ≤ 8852136409311^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4381257083 10000000000 8852136409311 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (664815269/1000000000 : ℝ)^39 ≤ (7479221824679/12500000000000 : ℝ)^31 := by
    have hnat : (664815269 : ℕ)^39*12500000000000^31 ≤ 7479221824679^31*1000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664815269 1000000000 7479221824679 12500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (888584539/10000000000 : ℝ)^39 ≤ (2378839871217/50000000000000 : ℝ)^31 := by
    have hnat : (888584539 : ℕ)^39*50000000000000^31 ≤ 2378839871217^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      888584539 10000000000 2378839871217 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4381257083/10000000000 : ℝ), (664815269/1000000000 : ℝ), (888584539/10000000000 : ℝ)] ![(8852136409311/25000000000000 : ℝ), (7479221824679/12500000000000 : ℝ), (2378839871217/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4381257083/10000000000 : ℝ)|^39 ≤ (8852136409311/25000000000000 : ℝ)^31
        have hw : |(4381257083/10000000000 : ℝ)|=(4381257083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(664815269/1000000000 : ℝ)|^39 ≤ (7479221824679/12500000000000 : ℝ)^31
        have hw : |(664815269/1000000000 : ℝ)|=(664815269/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(888584539/10000000000 : ℝ)|^39 ≤ (2378839871217/50000000000000 : ℝ)^31
        have hw : |(888584539/10000000000 : ℝ)|=(888584539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317060_s1_s1_13 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6715293387/10000000000 : ℝ)*x 0 + (73517201/156250000 : ℝ)*x 1 + (-93864837/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6715293387/10000000000 : ℝ)^39 ≤ (60594973820771/100000000000000 : ℝ)^31 := by
    have hnat : (6715293387 : ℕ)^39*100000000000000^31 ≤ 60594973820771^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6715293387 10000000000 60594973820771 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (73517201/156250000 : ℝ)^39 ≤ (38732060298641/100000000000000 : ℝ)^31 := by
    have hnat : (73517201 : ℕ)^39*100000000000000^31 ≤ 38732060298641^31*156250000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      73517201 156250000 38732060298641 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (93864837/5000000000 : ℝ)^39 ≤ (16824146623/2500000000000 : ℝ)^31 := by
    have hnat : (93864837 : ℕ)^39*2500000000000^31 ≤ 16824146623^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      93864837 5000000000 16824146623 2500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6715293387/10000000000 : ℝ), (73517201/156250000 : ℝ), (-93864837/5000000000 : ℝ)] ![(60594973820771/100000000000000 : ℝ), (38732060298641/100000000000000 : ℝ), (16824146623/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6715293387/10000000000 : ℝ)|^39 ≤ (60594973820771/100000000000000 : ℝ)^31
        have hw : |(6715293387/10000000000 : ℝ)|=(6715293387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(73517201/156250000 : ℝ)|^39 ≤ (38732060298641/100000000000000 : ℝ)^31
        have hw : |(73517201/156250000 : ℝ)|=(73517201/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-93864837/5000000000 : ℝ)|^39 ≤ (16824146623/2500000000000 : ℝ)^31
        have hw : |(-93864837/5000000000 : ℝ)|=(93864837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317060_s1_s1_14 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-4595053/39062500 : ℝ)*x 0 + (4408237569/10000000000 : ℝ)*x 1 + (-201414599/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4595053/39062500 : ℝ)^39 ≤ (423201704627/6250000000000 : ℝ)^31 := by
    have hnat : (4595053 : ℕ)^39*6250000000000^31 ≤ 423201704627^31*39062500^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4595053 39062500 423201704627 6250000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4408237569/10000000000 : ℝ)^39 ≤ (35683086164473/100000000000000 : ℝ)^31 := by
    have hnat : (4408237569 : ℕ)^39*100000000000000^31 ≤ 35683086164473^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4408237569 10000000000 35683086164473 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (201414599/312500000 : ℝ)^39 ≤ (57545686551663/100000000000000 : ℝ)^31 := by
    have hnat : (201414599 : ℕ)^39*100000000000000^31 ≤ 57545686551663^31*312500000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201414599 312500000 57545686551663 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4595053/39062500 : ℝ), (4408237569/10000000000 : ℝ), (-201414599/312500000 : ℝ)] ![(423201704627/6250000000000 : ℝ), (35683086164473/100000000000000 : ℝ), (57545686551663/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4595053/39062500 : ℝ)|^39 ≤ (423201704627/6250000000000 : ℝ)^31
        have hw : |(-4595053/39062500 : ℝ)|=(4595053/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4408237569/10000000000 : ℝ)|^39 ≤ (35683086164473/100000000000000 : ℝ)^31
        have hw : |(4408237569/10000000000 : ℝ)|=(4408237569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-201414599/312500000 : ℝ)|^39 ≤ (57545686551663/100000000000000 : ℝ)^31
        have hw : |(-201414599/312500000 : ℝ)|=(201414599/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317060_s1_s1_15 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (525820669/1250000000 : ℝ)*x 0 + (-380170553/2500000000 : ℝ)*x 1 + (-6397118423/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (525820669/1250000000 : ℝ)^39 ≤ (33641605122651/100000000000000 : ℝ)^31 := by
    have hnat : (525820669 : ℕ)^39*100000000000000^31 ≤ 33641605122651^31*1250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525820669 1250000000 33641605122651 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (380170553/2500000000 : ℝ)^39 ≤ (1169126841337/12500000000000 : ℝ)^31 := by
    have hnat : (380170553 : ℕ)^39*12500000000000^31 ≤ 1169126841337^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      380170553 2500000000 1169126841337 12500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6397118423/10000000000 : ℝ)^39 ≤ (14251345031863/25000000000000 : ℝ)^31 := by
    have hnat : (6397118423 : ℕ)^39*25000000000000^31 ≤ 14251345031863^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6397118423 10000000000 14251345031863 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(525820669/1250000000 : ℝ), (-380170553/2500000000 : ℝ), (-6397118423/10000000000 : ℝ)] ![(33641605122651/100000000000000 : ℝ), (1169126841337/12500000000000 : ℝ), (14251345031863/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(525820669/1250000000 : ℝ)|^39 ≤ (33641605122651/100000000000000 : ℝ)^31
        have hw : |(525820669/1250000000 : ℝ)|=(525820669/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-380170553/2500000000 : ℝ)|^39 ≤ (1169126841337/12500000000000 : ℝ)^31
        have hw : |(-380170553/2500000000 : ℝ)|=(380170553/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6397118423/10000000000 : ℝ)|^39 ≤ (14251345031863/25000000000000 : ℝ)^31
        have hw : |(-6397118423/10000000000 : ℝ)|=(6397118423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317060_s1_s1_16 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5435013003/10000000000 : ℝ)*x 0 + (5626135083/10000000000 : ℝ)*x 1 + (933496559/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5435013003/10000000000 : ℝ)^39 ≤ (46437117641317/100000000000000 : ℝ)^31 := by
    have hnat : (5435013003 : ℕ)^39*100000000000000^31 ≤ 46437117641317^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435013003 10000000000 46437117641317 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5626135083/10000000000 : ℝ)^39 ≤ (48500728276787/100000000000000 : ℝ)^31 := by
    have hnat : (5626135083 : ℕ)^39*100000000000000^31 ≤ 48500728276787^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5626135083 10000000000 48500728276787 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (933496559/10000000000 : ℝ)^39 ≤ (5062154071631/100000000000000 : ℝ)^31 := by
    have hnat : (933496559 : ℕ)^39*100000000000000^31 ≤ 5062154071631^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      933496559 10000000000 5062154071631 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5435013003/10000000000 : ℝ), (5626135083/10000000000 : ℝ), (933496559/10000000000 : ℝ)] ![(46437117641317/100000000000000 : ℝ), (48500728276787/100000000000000 : ℝ), (5062154071631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5435013003/10000000000 : ℝ)|^39 ≤ (46437117641317/100000000000000 : ℝ)^31
        have hw : |(5435013003/10000000000 : ℝ)|=(5435013003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5626135083/10000000000 : ℝ)|^39 ≤ (48500728276787/100000000000000 : ℝ)^31
        have hw : |(5626135083/10000000000 : ℝ)|=(5626135083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(933496559/10000000000 : ℝ)|^39 ≤ (5062154071631/100000000000000 : ℝ)^31
        have hw : |(933496559/10000000000 : ℝ)|=(933496559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317060_s1_s1_20 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (787568637/1000000000 : ℝ)*x 0 + (133959073/400000000 : ℝ)*x 1 + (-96563883/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (787568637/1000000000 : ℝ)^39 ≤ (14809968277053/20000000000000 : ℝ)^31 := by
    have hnat : (787568637 : ℕ)^39*20000000000000^31 ≤ 14809968277053^31*1000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      787568637 1000000000 14809968277053 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (133959073/400000000 : ℝ)^39 ≤ (3156594802509/12500000000000 : ℝ)^31 := by
    have hnat : (133959073 : ℕ)^39*12500000000000^31 ≤ 3156594802509^31*400000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133959073 400000000 3156594802509 12500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (96563883/5000000000 : ℝ)^39 ≤ (43587512051/6250000000000 : ℝ)^31 := by
    have hnat : (96563883 : ℕ)^39*6250000000000^31 ≤ 43587512051^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      96563883 5000000000 43587512051 6250000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(787568637/1000000000 : ℝ), (133959073/400000000 : ℝ), (-96563883/5000000000 : ℝ)] ![(14809968277053/20000000000000 : ℝ), (3156594802509/12500000000000 : ℝ), (43587512051/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(787568637/1000000000 : ℝ)|^39 ≤ (14809968277053/20000000000000 : ℝ)^31
        have hw : |(787568637/1000000000 : ℝ)|=(787568637/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(133959073/400000000 : ℝ)|^39 ≤ (3156594802509/12500000000000 : ℝ)^31
        have hw : |(133959073/400000000 : ℝ)|=(133959073/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-96563883/5000000000 : ℝ)|^39 ≤ (43587512051/6250000000000 : ℝ)^31
        have hw : |(-96563883/5000000000 : ℝ)|=(96563883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317060_s1_s1_21 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-944754727/10000000000 : ℝ)*x 0 + (1975953/3906250 : ℝ)*x 1 + (-5985952477/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (944754727/10000000000 : ℝ)^39 ≤ (513907890761/10000000000000 : ℝ)^31 := by
    have hnat : (944754727 : ℕ)^39*10000000000000^31 ≤ 513907890761^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      944754727 10000000000 513907890761 10000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1975953/3906250 : ℝ)^39 ≤ (10606540754277/25000000000000 : ℝ)^31 := by
    have hnat : (1975953 : ℕ)^39*25000000000000^31 ≤ 10606540754277^31*3906250^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1975953 3906250 10606540754277 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5985952477/10000000000 : ℝ)^39 ≤ (13108689512813/25000000000000 : ℝ)^31 := by
    have hnat : (5985952477 : ℕ)^39*25000000000000^31 ≤ 13108689512813^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5985952477 10000000000 13108689512813 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-944754727/10000000000 : ℝ), (1975953/3906250 : ℝ), (-5985952477/10000000000 : ℝ)] ![(513907890761/10000000000000 : ℝ), (10606540754277/25000000000000 : ℝ), (13108689512813/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-944754727/10000000000 : ℝ)|^39 ≤ (513907890761/10000000000000 : ℝ)^31
        have hw : |(-944754727/10000000000 : ℝ)|=(944754727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1975953/3906250 : ℝ)|^39 ≤ (10606540754277/25000000000000 : ℝ)^31
        have hw : |(1975953/3906250 : ℝ)|=(1975953/3906250 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5985952477/10000000000 : ℝ)|^39 ≤ (13108689512813/25000000000000 : ℝ)^31
        have hw : |(-5985952477/10000000000 : ℝ)|=(5985952477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317060_s1_s1_22 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5495062397/10000000000 : ℝ)*x 0 + (-1373354857/10000000000 : ℝ)*x 1 + (-5271731163/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5495062397/10000000000 : ℝ)^39 ≤ (235417527797/500000000000 : ℝ)^31 := by
    have hnat : (5495062397 : ℕ)^39*500000000000^31 ≤ 235417527797^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5495062397 10000000000 235417527797 500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1373354857/10000000000 : ℝ)^39 ≤ (8227636476927/100000000000000 : ℝ)^31 := by
    have hnat : (1373354857 : ℕ)^39*100000000000000^31 ≤ 8227636476927^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1373354857 10000000000 8227636476927 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5271731163/10000000000 : ℝ)^39 ≤ (44688857949493/100000000000000 : ℝ)^31 := by
    have hnat : (5271731163 : ℕ)^39*100000000000000^31 ≤ 44688857949493^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271731163 10000000000 44688857949493 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5495062397/10000000000 : ℝ), (-1373354857/10000000000 : ℝ), (-5271731163/10000000000 : ℝ)] ![(235417527797/500000000000 : ℝ), (8227636476927/100000000000000 : ℝ), (44688857949493/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5495062397/10000000000 : ℝ)|^39 ≤ (235417527797/500000000000 : ℝ)^31
        have hw : |(5495062397/10000000000 : ℝ)|=(5495062397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1373354857/10000000000 : ℝ)|^39 ≤ (8227636476927/100000000000000 : ℝ)^31
        have hw : |(-1373354857/10000000000 : ℝ)|=(1373354857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5271731163/10000000000 : ℝ)|^39 ≤ (44688857949493/100000000000000 : ℝ)^31
        have hw : |(-5271731163/10000000000 : ℝ)|=(5271731163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317060_s1_s1_23 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (213759707/500000000 : ℝ)*x 0 + (783535691/1250000000 : ℝ)*x 1 + (404164697/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213759707/500000000 : ℝ)^39 ≤ (34333544325779/100000000000000 : ℝ)^31 := by
    have hnat : (213759707 : ℕ)^39*100000000000000^31 ≤ 34333544325779^31*500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213759707 500000000 34333544325779 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (783535691/1250000000 : ℝ)^39 ≤ (27782419902331/50000000000000 : ℝ)^31 := by
    have hnat : (783535691 : ℕ)^39*50000000000000^31 ≤ 27782419902331^31*1250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      783535691 1250000000 27782419902331 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (404164697/2500000000 : ℝ)^39 ≤ (10101615859289/100000000000000 : ℝ)^31 := by
    have hnat : (404164697 : ℕ)^39*100000000000000^31 ≤ 10101615859289^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      404164697 2500000000 10101615859289 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213759707/500000000 : ℝ), (783535691/1250000000 : ℝ), (404164697/2500000000 : ℝ)] ![(34333544325779/100000000000000 : ℝ), (27782419902331/50000000000000 : ℝ), (10101615859289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213759707/500000000 : ℝ)|^39 ≤ (34333544325779/100000000000000 : ℝ)^31
        have hw : |(213759707/500000000 : ℝ)|=(213759707/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(783535691/1250000000 : ℝ)|^39 ≤ (27782419902331/50000000000000 : ℝ)^31
        have hw : |(783535691/1250000000 : ℝ)|=(783535691/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(404164697/2500000000 : ℝ)|^39 ≤ (10101615859289/100000000000000 : ℝ)^31
        have hw : |(404164697/2500000000 : ℝ)|=(404164697/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317060_s1_s1_27 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2035736029/2500000000 : ℝ)*x 0 + (597448813/2000000000 : ℝ)*x 1 + (-118756259/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2035736029/2500000000 : ℝ)^39 ≤ (77224892686381/100000000000000 : ℝ)^31 := by
    have hnat : (2035736029 : ℕ)^39*100000000000000^31 ≤ 77224892686381^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2035736029 2500000000 77224892686381 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (597448813/2000000000 : ℝ)^39 ≤ (21870398473119/100000000000000 : ℝ)^31 := by
    have hnat : (597448813 : ℕ)^39*100000000000000^31 ≤ 21870398473119^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      597448813 2000000000 21870398473119 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (118756259/5000000000 : ℝ)^39 ≤ (904708826639/100000000000000 : ℝ)^31 := by
    have hnat : (118756259 : ℕ)^39*100000000000000^31 ≤ 904708826639^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      118756259 5000000000 904708826639 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2035736029/2500000000 : ℝ), (597448813/2000000000 : ℝ), (-118756259/5000000000 : ℝ)] ![(77224892686381/100000000000000 : ℝ), (21870398473119/100000000000000 : ℝ), (904708826639/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2035736029/2500000000 : ℝ)|^39 ≤ (77224892686381/100000000000000 : ℝ)^31
        have hw : |(2035736029/2500000000 : ℝ)|=(2035736029/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(597448813/2000000000 : ℝ)|^39 ≤ (21870398473119/100000000000000 : ℝ)^31
        have hw : |(597448813/2000000000 : ℝ)|=(597448813/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-118756259/5000000000 : ℝ)|^39 ≤ (904708826639/100000000000000 : ℝ)^31
        have hw : |(-118756259/5000000000 : ℝ)|=(118756259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c317060_s1 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (89931/50000 : ℝ) (34473/20000 : ℝ) (19897/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev0 : (0 : ℝ) ≤ ((77633/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(77633/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15451/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(15451/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-68109/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-68109/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((10651/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(10651/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2379/5000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2379/5000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-3973/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-3973/12500 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (19897/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (19897/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (19897/25000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (19897/25000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (19897/25000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (19897/25000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base18 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  have s1_pow0 : (77633/100000 : ℝ) ^ (77/16 : ℝ) ≤ (14784891969446630149/50000000000000000000 : ℝ) := by
    have hpowers : (77633/100000 : ℝ)^77 ≤ (14784891969446630149/50000000000000000000 : ℝ)^16 := by
      have hnat : (77633 : ℕ)^77*50000000000000000000^16 ≤ 14784891969446630149^16*100000^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        77633 100000 14784891969446630149 50000000000000000000 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (77633/100000 : ℝ)) (X := (14784891969446630149/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (64784891969446630149/50000000000000000000 : ℝ) ≤ (10553035507276313/10000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (64784891969446630149/50000000000000000000 : ℝ)^16 ≤ (10553035507276313/10000000000000000 : ℝ)^77 := by
      have hnat : (64784891969446630149 : ℕ)^16*10000000000000000^77 ≤ 10553035507276313^77*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        64784891969446630149 50000000000000000000 10553035507276313 10000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10553035507276313/10000000000000000 : ℝ)) (X := (64784891969446630149/50000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (39784891969446630149/25000000000000000000 : ℝ) ≤ (1101356533197273/1000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (39784891969446630149/25000000000000000000 : ℝ)^16 ≤ (1101356533197273/1000000000000000 : ℝ)^77 := by
      have hnat : (39784891969446630149 : ℕ)^16*1000000000000000^77 ≤ 1101356533197273^77*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        39784891969446630149 25000000000000000000 1101356533197273 1000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1101356533197273/1000000000000000 : ℝ)) (X := (39784891969446630149/25000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(553035507276313/7763300000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(460529824696417/7763300000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (77633/100000 : ℝ)) (alpha := (553035507276313/7763300000000000 : ℝ)) (beta := (460529824696417/7763300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (77633/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(553035507276313/7763300000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(460529824696417/7763300000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (15451/20000 : ℝ) ^ (77/16 : ℝ) ≤ (5776659152388505861/20000000000000000000 : ℝ) := by
    have hpowers : (15451/20000 : ℝ)^77 ≤ (5776659152388505861/20000000000000000000 : ℝ)^16 := by
      have hnat : (15451 : ℕ)^77*20000000000000000000^16 ≤ 5776659152388505861^16*20000^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15451 20000 5776659152388505861 20000000000000000000 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15451/20000 : ℝ)) (X := (5776659152388505861/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (25776659152388505861/20000000000000000000 : ℝ) ≤ (2108278584829387/2000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (25776659152388505861/20000000000000000000 : ℝ)^16 ≤ (2108278584829387/2000000000000000 : ℝ)^77 := by
      have hnat : (25776659152388505861 : ℕ)^16*2000000000000000^77 ≤ 2108278584829387^77*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25776659152388505861 20000000000000000000 2108278584829387 2000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2108278584829387/2000000000000000 : ℝ)) (X := (25776659152388505861/20000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (15776659152388505861/10000000000000000000 : ℝ) ≤ (2198750638614143/2000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (15776659152388505861/10000000000000000000 : ℝ)^16 ≤ (2198750638614143/2000000000000000 : ℝ)^77 := by
      have hnat : (15776659152388505861 : ℕ)^16*2000000000000000^77 ≤ 2198750638614143^77*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15776659152388505861 10000000000000000000 2198750638614143 2000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2198750638614143/2000000000000000 : ℝ)) (X := (15776659152388505861/10000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(108278584829387/1545100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(22618013446189/386275000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (15451/20000 : ℝ)) (alpha := (108278584829387/1545100000000000 : ℝ)) (beta := (22618013446189/386275000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (15451/20000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(108278584829387/1545100000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(22618013446189/386275000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (68109/100000 : ℝ) ^ (77/16 : ℝ) ≤ (15750584495734562683/100000000000000000000 : ℝ) := by
    have hpowers : (68109/100000 : ℝ)^77 ≤ (15750584495734562683/100000000000000000000 : ℝ)^16 := by
      have hnat : (68109 : ℕ)^77*100000000000000000000^16 ≤ 15750584495734562683^16*100000^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        68109 100000 15750584495734562683 100000000000000000000 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (68109/100000 : ℝ)) (X := (15750584495734562683/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (115750584495734562683/100000000000000000000 : ℝ) ≤ (5154299243325437/5000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (115750584495734562683/100000000000000000000 : ℝ)^16 ≤ (5154299243325437/5000000000000000 : ℝ)^77 := by
      have hnat : (115750584495734562683 : ℕ)^16*5000000000000000^77 ≤ 5154299243325437^77*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        115750584495734562683 100000000000000000000 5154299243325437 5000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5154299243325437/5000000000000000 : ℝ)) (X := (115750584495734562683/100000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (65750584495734562683/50000000000000000000 : ℝ) ≤ (1323191370843259/1250000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (65750584495734562683/50000000000000000000 : ℝ)^16 ≤ (1323191370843259/1250000000000000 : ℝ)^77 := by
      have hnat : (65750584495734562683 : ℕ)^16*1250000000000000^77 ≤ 1323191370843259^77*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        65750584495734562683 50000000000000000000 1323191370843259 1250000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1323191370843259/1250000000000000 : ℝ)) (X := (65750584495734562683/50000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(51433081108479/1135150000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(138466240047599/3405450000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (68109/100000 : ℝ)) (alpha := (51433081108479/1135150000000000 : ℝ)) (beta := (138466240047599/3405450000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (68109/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(51433081108479/1135150000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(138466240047599/3405450000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1911711307/10000000000 : ℝ)*X 0 0+(411211319/1000000000 : ℝ)*X 0 1+(-6202535579/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317060_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((1165108547/2500000000 : ℝ)*X 2 0+(730082863/1250000000 : ℝ)*X 2 1+(1716330127/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317060_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((1414036901/2000000000 : ℝ)*X 0 0+(801479387/2000000000 : ℝ)*X 0 1+(-90933801/1250000000 : ℝ)*X 0 2+(1414036901/2000000000 : ℝ)*X 1 0+(801479387/2000000000 : ℝ)*X 1 1+(-90933801/1250000000 : ℝ)*X 1 2+(1414036901/2000000000 : ℝ)*X 2 0+(801479387/2000000000 : ℝ)*X 2 1+(-90933801/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c317060_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-357294209/2000000000 : ℝ)*X 0 0+(3939484591/10000000000 : ℝ)*X 0 1+(-6447346731/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317060_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((2104864653/5000000000 : ℝ)*X 1 0+(-36275507/250000000 : ℝ)*X 1 1+(-805253989/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c317060_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((4381257083/10000000000 : ℝ)*X 2 0+(664815269/1000000000 : ℝ)*X 2 1+(888584539/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317060_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((6715293387/10000000000 : ℝ)*X 0 0+(73517201/156250000 : ℝ)*X 0 1+(-93864837/5000000000 : ℝ)*X 0 2+(6715293387/10000000000 : ℝ)*X 1 0+(73517201/156250000 : ℝ)*X 1 1+(-93864837/5000000000 : ℝ)*X 1 2+(6715293387/10000000000 : ℝ)*X 2 0+(73517201/156250000 : ℝ)*X 2 1+(-93864837/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c317060_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-4595053/39062500 : ℝ)*X 0 0+(4408237569/10000000000 : ℝ)*X 0 1+(-201414599/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317060_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((525820669/1250000000 : ℝ)*X 1 0+(-380170553/2500000000 : ℝ)*X 1 1+(-6397118423/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c317060_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((5435013003/10000000000 : ℝ)*X 2 0+(5626135083/10000000000 : ℝ)*X 2 1+(933496559/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317060_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((787568637/1000000000 : ℝ)*X 0 0+(133959073/400000000 : ℝ)*X 0 1+(-96563883/5000000000 : ℝ)*X 0 2+(787568637/1000000000 : ℝ)*X 1 0+(133959073/400000000 : ℝ)*X 1 1+(-96563883/5000000000 : ℝ)*X 1 2+(787568637/1000000000 : ℝ)*X 2 0+(133959073/400000000 : ℝ)*X 2 1+(-96563883/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c317060_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-944754727/10000000000 : ℝ)*X 0 0+(1975953/3906250 : ℝ)*X 0 1+(-5985952477/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317060_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((5495062397/10000000000 : ℝ)*X 1 0+(-1373354857/10000000000 : ℝ)*X 1 1+(-5271731163/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c317060_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((213759707/500000000 : ℝ)*X 2 0+(783535691/1250000000 : ℝ)*X 2 1+(404164697/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317060_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((2035736029/2500000000 : ℝ)*X 0 0+(597448813/2000000000 : ℝ)*X 0 1+(-118756259/5000000000 : ℝ)*X 0 2+(2035736029/2500000000 : ℝ)*X 1 0+(597448813/2000000000 : ℝ)*X 1 1+(-118756259/5000000000 : ℝ)*X 1 2+(2035736029/2500000000 : ℝ)*X 2 0+(597448813/2000000000 : ℝ)*X 2 1+(-118756259/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c317060_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((10651/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(10651/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (58433393999432259072787583/3507840530000000000000000000000 : ℝ) := by norm_num
    linear_combination (3801881/1000000000000 : ℝ)*(base5) + (2065089/500000000000 : ℝ)*(base18) + (1637213/100000000000 : ℝ)*(base39) + (2328851/1000000000000 : ℝ)*(base49) + (428556134471/500000000000 : ℝ)*(base59) + (1330128422867/200000000000 : ℝ)*(major_s1_0) + (1330128422867/200000000000 : ℝ)*(major_s1_1) + (1330128422867/200000000000 : ℝ)*(major_s1_2) + (1200455330887/125000000000 : ℝ)*(sp_s1_7) + (4800272045651/500000000000 : ℝ)*(sp_s1_8) + (4801704350979/500000000000 : ℝ)*(sp_s1_9) + (1848816113519/500000000000 : ℝ)*(sp_s1_13) + (3094425617/1000000000000 : ℝ)*(sp_s1_15) + (11887351/50000000000 : ℝ)*(sp_s1_23) + (3697636028919/1000000000000 : ℝ)*(f.failure) + (1200455330887/125000000000 : ℝ)*(f.sum) + (684761362692342743/7015681060000000000000000000000 : ℝ)*base62 + (93105544749151/136218000000000000000000000 : ℝ)*base65 + (65473939524443/77255000000000000000000000 : ℝ)*base66 + (9637451584987/227030000000000000000000000 : ℝ)*base69 + (44526338601172442669/105750119940000000000000000000000 : ℝ)*base71 + (799139149361721/1552660000000000000000000000 : ℝ)*base73 + (2029389816489/309020000000000000000000000 : ℝ)*base75 + (44265961684221/1552660000000000000000000000 : ℝ)*base76 + (2125152034208912091/4798029932000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (35411/50000000000000000 : ℝ)*base86 + (35411/50000000000000000 : ℝ)*base88 + (35411/50000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2379/5000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2379/5000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (7461468471054584001090944391207/680810459663725000000000000000000000 : ℝ) := by norm_num
    linear_combination (2014997/500000000000 : ℝ)*(base18) + (10131457753/250000000000 : ℝ)*(base39) + (209569682949/500000000000 : ℝ)*(base59) + (3276087815481/500000000000 : ℝ)*(major_s1_0) + (3276087815481/500000000000 : ℝ)*(major_s1_1) + (3276087815481/500000000000 : ℝ)*(major_s1_2) + (989043/40000000000 : ℝ)*(sp_s1_6) + (21191333/500000000000 : ℝ)*(sp_s1_7) + (323532231/1000000000000 : ℝ)*(sp_s1_8) + (9461414770587/1000000000000 : ℝ)*(sp_s1_14) + (2365282397757/250000000000 : ℝ)*(sp_s1_15) + (9461457153253/1000000000000 : ℝ)*(sp_s1_16) + (910669893709/250000000000 : ℝ)*(sp_s1_20) + (5817329/31250000000 : ℝ)*(sp_s1_27) + (3642890455439/1000000000000 : ℝ)*(f.failure) + (9461457153253/1000000000000 : ℝ)*(f.sum) + (307056074943979067/8769601325000000000000000000000 : ℝ)*base63 + (500534355441/70946875000000000000000000 : ℝ)*base64 + (64931404764077/386275000000000000000000000 : ℝ)*base66 + (478244233819523/1135150000000000000000000000 : ℝ)*base69 + (11605612086636408407/44062549975000000000000000000000 : ℝ)*base70 + (1257926212393917/3881650000000000000000000000 : ℝ)*base73 + (150039635189637/772550000000000000000000000 : ℝ)*base75 + (934323800450793/3881650000000000000000000000 : ℝ)*base77 + (2054154574401893481/5997537415000000000000000000000 : ℝ)*base79 + (15291/50000000000000000 : ℝ)*base86 + (15291/50000000000000000 : ℝ)*base88 + (15291/50000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-3973/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-3973/12500 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4999197403015108985773159577667/340405229831862500000000000000000000 : ℝ) := by norm_num
    linear_combination (1921307/125000000000 : ℝ)*(base11) + (44921/200000000000 : ℝ)*(base15) + (254743201277/500000000000 : ℝ)*(base39) + (156297244083/500000000000 : ℝ)*(base59) + (155534646429/31250000000 : ℝ)*(major_s1_0) + (155534646429/31250000000 : ℝ)*(major_s1_1) + (155534646429/31250000000 : ℝ)*(major_s1_2) + (46654233/1000000000000 : ℝ)*(sp_s1_0) + (24522551/1000000000000 : ℝ)*(sp_s1_2) + (108264771/1000000000000 : ℝ)*(sp_s1_9) + (3593484282173/500000000000 : ℝ)*(sp_s1_21) + (7187030364431/1000000000000 : ℝ)*(sp_s1_22) + (3593448900857/500000000000 : ℝ)*(sp_s1_23) + (1383590943537/500000000000 : ℝ)*(sp_s1_27) + (1383590943537/500000000000 : ℝ)*(f.failure) + (1796757647259/250000000000 : ℝ)*(f.sum) + (8055654630402230599/17539202650000000000000000000000 : ℝ)*base62 + (63285190353053/141893750000000000000000000 : ℝ)*base64 + (107872581295161/772550000000000000000000000 : ℝ)*base66 + (862408298206153/1135150000000000000000000000 : ℝ)*base68 + (53025010594558560281/88125099950000000000000000000000 : ℝ)*base70 + (2504305028469813/3881650000000000000000000000 : ℝ)*base73 + (574987464007507/772550000000000000000000000 : ℝ)*base74 + (65001768138919/121301562500000000000000000 : ℝ)*base76 + (1368460291566158727/5997537415000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (25947/25000000000000000 : ℝ)*base87 + (25947/25000000000000000 : ℝ)*base89 + (25947/25000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (89931/50000 : ℝ) (34473/20000 : ℝ) (19897/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev0 : (0 : ℝ) ≤ ((77633/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(77633/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15451/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(15451/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-68109/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-68109/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((10651/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(10651/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2379/5000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2379/5000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-3973/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-3973/12500 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c317060_s1 p hpa hpb X hX hprev0

#print axioms solution
