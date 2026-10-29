-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c326055_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:10:51.289055+00:00
-- url     : https://prove2.me/submissions/05ed509f-728c-4175-8c82-4cb462fdb212

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
theorem collision_support_c326055_s1_s1_0 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-104670343/625000000 : ℝ)*x 0 + (5528734849/10000000000 : ℝ)*x 1 + (4728565921/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (104670343/625000000 : ℝ)^89 ≤ (2830017309249/25000000000000 : ℝ)^73 := by
    have hnat : (104670343 : ℕ)^89*25000000000000^73 ≤ 2830017309249^73*625000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104670343 625000000 2830017309249 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5528734849/10000000000 : ℝ)^89 ≤ (48552877142633/100000000000000 : ℝ)^73 := by
    have hnat : (5528734849 : ℕ)^89*100000000000000^73 ≤ 48552877142633^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5528734849 10000000000 48552877142633 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4728565921/10000000000 : ℝ)^89 ≤ (8025410721079/20000000000000 : ℝ)^73 := by
    have hnat : (4728565921 : ℕ)^89*20000000000000^73 ≤ 8025410721079^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4728565921 10000000000 8025410721079 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-104670343/625000000 : ℝ), (5528734849/10000000000 : ℝ), (4728565921/10000000000 : ℝ)] ![(2830017309249/25000000000000 : ℝ), (48552877142633/100000000000000 : ℝ), (8025410721079/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-104670343/625000000 : ℝ)|^89 ≤ (2830017309249/25000000000000 : ℝ)^73
        have hw : |(-104670343/625000000 : ℝ)|=(104670343/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5528734849/10000000000 : ℝ)|^89 ≤ (48552877142633/100000000000000 : ℝ)^73
        have hw : |(5528734849/10000000000 : ℝ)|=(5528734849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4728565921/10000000000 : ℝ)|^89 ≤ (8025410721079/20000000000000 : ℝ)^73
        have hw : |(4728565921/10000000000 : ℝ)|=(4728565921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326055_s1_s1_2 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (471217639/1000000000 : ℝ)*x 0 + (5563468377/10000000000 : ℝ)*x 1 + (-66003863/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (471217639/1000000000 : ℝ)^89 ≤ (1997877550497/5000000000000 : ℝ)^73 := by
    have hnat : (471217639 : ℕ)^89*5000000000000^73 ≤ 1997877550497^73*1000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      471217639 1000000000 1997877550497 5000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5563468377/10000000000 : ℝ)^89 ≤ (1528906713727/3125000000000 : ℝ)^73 := by
    have hnat : (5563468377 : ℕ)^89*3125000000000^73 ≤ 1528906713727^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5563468377 10000000000 1528906713727 3125000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (66003863/400000000 : ℝ)^89 ≤ (11117434148197/100000000000000 : ℝ)^73 := by
    have hnat : (66003863 : ℕ)^89*100000000000000^73 ≤ 11117434148197^73*400000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66003863 400000000 11117434148197 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(471217639/1000000000 : ℝ), (5563468377/10000000000 : ℝ), (-66003863/400000000 : ℝ)] ![(1997877550497/5000000000000 : ℝ), (1528906713727/3125000000000 : ℝ), (11117434148197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(471217639/1000000000 : ℝ)|^89 ≤ (1997877550497/5000000000000 : ℝ)^73
        have hw : |(471217639/1000000000 : ℝ)|=(471217639/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5563468377/10000000000 : ℝ)|^89 ≤ (1528906713727/3125000000000 : ℝ)^73
        have hw : |(5563468377/10000000000 : ℝ)|=(5563468377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-66003863/400000000 : ℝ)|^89 ≤ (11117434148197/100000000000000 : ℝ)^73
        have hw : |(-66003863/400000000 : ℝ)|=(66003863/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326055_s1_s1_6 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6292148613/10000000000 : ℝ)*x 0 + (1862707087/5000000000 : ℝ)*x 1 + (946844513/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6292148613/10000000000 : ℝ)^89 ≤ (14211506718567/25000000000000 : ℝ)^73 := by
    have hnat : (6292148613 : ℕ)^89*25000000000000^73 ≤ 14211506718567^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6292148613 10000000000 14211506718567 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1862707087/5000000000 : ℝ)^89 ≤ (30004433095933/100000000000000 : ℝ)^73 := by
    have hnat : (1862707087 : ℕ)^89*100000000000000^73 ≤ 30004433095933^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1862707087 5000000000 30004433095933 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (946844513/5000000000 : ℝ)^89 ≤ (13149540016137/100000000000000 : ℝ)^73 := by
    have hnat : (946844513 : ℕ)^89*100000000000000^73 ≤ 13149540016137^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      946844513 5000000000 13149540016137 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6292148613/10000000000 : ℝ), (1862707087/5000000000 : ℝ), (946844513/5000000000 : ℝ)] ![(14211506718567/25000000000000 : ℝ), (30004433095933/100000000000000 : ℝ), (13149540016137/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6292148613/10000000000 : ℝ)|^89 ≤ (14211506718567/25000000000000 : ℝ)^73
        have hw : |(6292148613/10000000000 : ℝ)|=(6292148613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1862707087/5000000000 : ℝ)|^89 ≤ (30004433095933/100000000000000 : ℝ)^73
        have hw : |(1862707087/5000000000 : ℝ)|=(1862707087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(946844513/5000000000 : ℝ)|^89 ≤ (13149540016137/100000000000000 : ℝ)^73
        have hw : |(946844513/5000000000 : ℝ)|=(946844513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326055_s1_s1_7 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-671517519/5000000000 : ℝ)*x 0 + (4942371269/10000000000 : ℝ)*x 1 + (2785264459/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671517519/5000000000 : ℝ)^89 ≤ (1729868914927/20000000000000 : ℝ)^73 := by
    have hnat : (671517519 : ℕ)^89*20000000000000^73 ≤ 1729868914927^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671517519 5000000000 1729868914927 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4942371269/10000000000 : ℝ)^89 ≤ (21174965490663/50000000000000 : ℝ)^73 := by
    have hnat : (4942371269 : ℕ)^89*50000000000000^73 ≤ 21174965490663^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4942371269 10000000000 21174965490663 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2785264459/5000000000 : ℝ)^89 ≤ (49000724420641/100000000000000 : ℝ)^73 := by
    have hnat : (2785264459 : ℕ)^89*100000000000000^73 ≤ 49000724420641^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2785264459 5000000000 49000724420641 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-671517519/5000000000 : ℝ), (4942371269/10000000000 : ℝ), (2785264459/5000000000 : ℝ)] ![(1729868914927/20000000000000 : ℝ), (21174965490663/50000000000000 : ℝ), (49000724420641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-671517519/5000000000 : ℝ)|^89 ≤ (1729868914927/20000000000000 : ℝ)^73
        have hw : |(-671517519/5000000000 : ℝ)|=(671517519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4942371269/10000000000 : ℝ)|^89 ≤ (21174965490663/50000000000000 : ℝ)^73
        have hw : |(4942371269/10000000000 : ℝ)|=(4942371269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2785264459/5000000000 : ℝ)|^89 ≤ (49000724420641/100000000000000 : ℝ)^73
        have hw : |(2785264459/5000000000 : ℝ)|=(2785264459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326055_s1_s1_8 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1166446371/2500000000 : ℝ)*x 0 + (-12738857/500000000 : ℝ)*x 1 + (6521455027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1166446371/2500000000 : ℝ)^89 ≤ (4934808977457/12500000000000 : ℝ)^73 := by
    have hnat : (1166446371 : ℕ)^89*12500000000000^73 ≤ 4934808977457^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1166446371 2500000000 4934808977457 12500000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (12738857/500000000 : ℝ)^89 ≤ (1139792418899/100000000000000 : ℝ)^73 := by
    have hnat : (12738857 : ℕ)^89*100000000000000^73 ≤ 1139792418899^73*500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12738857 500000000 1139792418899 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6521455027/10000000000 : ℝ)^89 ≤ (29690867874449/50000000000000 : ℝ)^73 := by
    have hnat : (6521455027 : ℕ)^89*50000000000000^73 ≤ 29690867874449^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6521455027 10000000000 29690867874449 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1166446371/2500000000 : ℝ), (-12738857/500000000 : ℝ), (6521455027/10000000000 : ℝ)] ![(4934808977457/12500000000000 : ℝ), (1139792418899/100000000000000 : ℝ), (29690867874449/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1166446371/2500000000 : ℝ)|^89 ≤ (4934808977457/12500000000000 : ℝ)^73
        have hw : |(1166446371/2500000000 : ℝ)|=(1166446371/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-12738857/500000000 : ℝ)|^89 ≤ (1139792418899/100000000000000 : ℝ)^73
        have hw : |(-12738857/500000000 : ℝ)|=(12738857/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6521455027/10000000000 : ℝ)|^89 ≤ (29690867874449/50000000000000 : ℝ)^73
        have hw : |(6521455027/10000000000 : ℝ)|=(6521455027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326055_s1_s1_9 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2326736939/5000000000 : ℝ)*x 0 + (247471979/400000000 : ℝ)*x 1 + (-425620599/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2326736939/5000000000 : ℝ)^89 ≤ (39351504564741/100000000000000 : ℝ)^73 := by
    have hnat : (2326736939 : ℕ)^89*100000000000000^73 ≤ 39351504564741^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2326736939 5000000000 39351504564741 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (247471979/400000000 : ℝ)^89 ≤ (27843893945927/50000000000000 : ℝ)^73 := by
    have hnat : (247471979 : ℕ)^89*50000000000000^73 ≤ 27843893945927^73*400000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      247471979 400000000 27843893945927 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (425620599/5000000000 : ℝ)^89 ≤ (198428301031/4000000000000 : ℝ)^73 := by
    have hnat : (425620599 : ℕ)^89*4000000000000^73 ≤ 198428301031^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425620599 5000000000 198428301031 4000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2326736939/5000000000 : ℝ), (247471979/400000000 : ℝ), (-425620599/5000000000 : ℝ)] ![(39351504564741/100000000000000 : ℝ), (27843893945927/50000000000000 : ℝ), (198428301031/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2326736939/5000000000 : ℝ)|^89 ≤ (39351504564741/100000000000000 : ℝ)^73
        have hw : |(2326736939/5000000000 : ℝ)|=(2326736939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(247471979/400000000 : ℝ)|^89 ≤ (27843893945927/50000000000000 : ℝ)^73
        have hw : |(247471979/400000000 : ℝ)|=(247471979/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-425620599/5000000000 : ℝ)|^89 ≤ (198428301031/4000000000000 : ℝ)^73
        have hw : |(-425620599/5000000000 : ℝ)|=(425620599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326055_s1_s1_13 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2610072159/5000000000 : ℝ)*x 0 + (5674747863/10000000000 : ℝ)*x 1 + (801544617/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2610072159/5000000000 : ℝ)^89 ≤ (45269396389857/100000000000000 : ℝ)^73 := by
    have hnat : (2610072159 : ℕ)^89*100000000000000^73 ≤ 45269396389857^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2610072159 5000000000 45269396389857 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5674747863/10000000000 : ℝ)^89 ≤ (391567899531/781250000000 : ℝ)^73 := by
    have hnat : (5674747863 : ℕ)^89*781250000000^73 ≤ 391567899531^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5674747863 10000000000 391567899531 781250000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (801544617/10000000000 : ℝ)^89 ≤ (921982490199/20000000000000 : ℝ)^73 := by
    have hnat : (801544617 : ℕ)^89*20000000000000^73 ≤ 921982490199^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      801544617 10000000000 921982490199 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2610072159/5000000000 : ℝ), (5674747863/10000000000 : ℝ), (801544617/10000000000 : ℝ)] ![(45269396389857/100000000000000 : ℝ), (391567899531/781250000000 : ℝ), (921982490199/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2610072159/5000000000 : ℝ)|^89 ≤ (45269396389857/100000000000000 : ℝ)^73
        have hw : |(2610072159/5000000000 : ℝ)|=(2610072159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5674747863/10000000000 : ℝ)|^89 ≤ (391567899531/781250000000 : ℝ)^73
        have hw : |(5674747863/10000000000 : ℝ)|=(5674747863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(801544617/10000000000 : ℝ)|^89 ≤ (921982490199/20000000000000 : ℝ)^73
        have hw : |(801544617/10000000000 : ℝ)|=(801544617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326055_s1_s1_14 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-764609927/10000000000 : ℝ)*x 0 + (5235949977/10000000000 : ℝ)*x 1 + (5683150163/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (764609927/10000000000 : ℝ)^89 ≤ (4352256052311/100000000000000 : ℝ)^73 := by
    have hnat : (764609927 : ℕ)^89*100000000000000^73 ≤ 4352256052311^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      764609927 10000000000 4352256052311 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5235949977/10000000000 : ℝ)^89 ≤ (45436561607079/100000000000000 : ℝ)^73 := by
    have hnat : (5235949977 : ℕ)^89*100000000000000^73 ≤ 45436561607079^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5235949977 10000000000 45436561607079 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5683150163/10000000000 : ℝ)^89 ≤ (1255279557983/2500000000000 : ℝ)^73 := by
    have hnat : (5683150163 : ℕ)^89*2500000000000^73 ≤ 1255279557983^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5683150163 10000000000 1255279557983 2500000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-764609927/10000000000 : ℝ), (5235949977/10000000000 : ℝ), (5683150163/10000000000 : ℝ)] ![(4352256052311/100000000000000 : ℝ), (45436561607079/100000000000000 : ℝ), (1255279557983/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-764609927/10000000000 : ℝ)|^89 ≤ (4352256052311/100000000000000 : ℝ)^73
        have hw : |(-764609927/10000000000 : ℝ)|=(764609927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5235949977/10000000000 : ℝ)|^89 ≤ (45436561607079/100000000000000 : ℝ)^73
        have hw : |(5235949977/10000000000 : ℝ)|=(5235949977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5683150163/10000000000 : ℝ)|^89 ≤ (1255279557983/2500000000000 : ℝ)^73
        have hw : |(5683150163/10000000000 : ℝ)|=(5683150163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326055_s1_s1_15 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (548472967/1250000000 : ℝ)*x 0 + (-350257097/5000000000 : ℝ)*x 1 + (6528385681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (548472967/1250000000 : ℝ)^89 ≤ (36629686873947/100000000000000 : ℝ)^73 := by
    have hnat : (548472967 : ℕ)^89*100000000000000^73 ≤ 36629686873947^73*1250000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548472967 1250000000 36629686873947 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (350257097/5000000000 : ℝ)^89 ≤ (3911628831837/100000000000000 : ℝ)^73 := by
    have hnat : (350257097 : ℕ)^89*100000000000000^73 ≤ 3911628831837^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      350257097 5000000000 3911628831837 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6528385681/10000000000 : ℝ)^89 ≤ (59458684276179/100000000000000 : ℝ)^73 := by
    have hnat : (6528385681 : ℕ)^89*100000000000000^73 ≤ 59458684276179^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6528385681 10000000000 59458684276179 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(548472967/1250000000 : ℝ), (-350257097/5000000000 : ℝ), (6528385681/10000000000 : ℝ)] ![(36629686873947/100000000000000 : ℝ), (3911628831837/100000000000000 : ℝ), (59458684276179/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(548472967/1250000000 : ℝ)|^89 ≤ (36629686873947/100000000000000 : ℝ)^73
        have hw : |(548472967/1250000000 : ℝ)|=(548472967/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-350257097/5000000000 : ℝ)|^89 ≤ (3911628831837/100000000000000 : ℝ)^73
        have hw : |(-350257097/5000000000 : ℝ)|=(350257097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6528385681/10000000000 : ℝ)|^89 ≤ (59458684276179/100000000000000 : ℝ)^73
        have hw : |(6528385681/10000000000 : ℝ)|=(6528385681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326055_s1_s1_16 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5665455313/10000000000 : ℝ)*x 0 + (5270918039/10000000000 : ℝ)*x 1 + (-1181791/16000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5665455313/10000000000 : ℝ)^89 ≤ (2501032316569/5000000000000 : ℝ)^73 := by
    have hnat : (5665455313 : ℕ)^89*5000000000000^73 ≤ 2501032316569^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5665455313 10000000000 2501032316569 5000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5270918039/10000000000 : ℝ)^89 ≤ (5725848339261/12500000000000 : ℝ)^73 := by
    have hnat : (5270918039 : ℕ)^89*12500000000000^73 ≤ 5725848339261^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5270918039 10000000000 5725848339261 12500000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1181791/16000000 : ℝ)^89 ≤ (4172566950349/100000000000000 : ℝ)^73 := by
    have hnat : (1181791 : ℕ)^89*100000000000000^73 ≤ 4172566950349^73*16000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1181791 16000000 4172566950349 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5665455313/10000000000 : ℝ), (5270918039/10000000000 : ℝ), (-1181791/16000000 : ℝ)] ![(2501032316569/5000000000000 : ℝ), (5725848339261/12500000000000 : ℝ), (4172566950349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5665455313/10000000000 : ℝ)|^89 ≤ (2501032316569/5000000000000 : ℝ)^73
        have hw : |(5665455313/10000000000 : ℝ)|=(5665455313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5270918039/10000000000 : ℝ)|^89 ≤ (5725848339261/12500000000000 : ℝ)^73
        have hw : |(5270918039/10000000000 : ℝ)|=(5270918039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1181791/16000000 : ℝ)|^89 ≤ (4172566950349/100000000000000 : ℝ)^73
        have hw : |(-1181791/16000000 : ℝ)|=(1181791/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326055_s1_s1_20 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3721989641/5000000000 : ℝ)*x 0 + (3287884189/10000000000 : ℝ)*x 1 + (779878371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3721989641/5000000000 : ℝ)^89 ≤ (1744406371571/2500000000000 : ℝ)^73 := by
    have hnat : (3721989641 : ℕ)^89*2500000000000^73 ≤ 1744406371571^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3721989641 5000000000 1744406371571 2500000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3287884189/10000000000 : ℝ)^89 ≤ (25765299743621/100000000000000 : ℝ)^73 := by
    have hnat : (3287884189 : ℕ)^89*100000000000000^73 ≤ 25765299743621^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3287884189 10000000000 25765299743621 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (779878371/10000000000 : ℝ)^89 ≤ (4458445389139/100000000000000 : ℝ)^73 := by
    have hnat : (779878371 : ℕ)^89*100000000000000^73 ≤ 4458445389139^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      779878371 10000000000 4458445389139 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3721989641/5000000000 : ℝ), (3287884189/10000000000 : ℝ), (779878371/10000000000 : ℝ)] ![(1744406371571/2500000000000 : ℝ), (25765299743621/100000000000000 : ℝ), (4458445389139/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3721989641/5000000000 : ℝ)|^89 ≤ (1744406371571/2500000000000 : ℝ)^73
        have hw : |(3721989641/5000000000 : ℝ)|=(3721989641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3287884189/10000000000 : ℝ)|^89 ≤ (25765299743621/100000000000000 : ℝ)^73
        have hw : |(3287884189/10000000000 : ℝ)|=(3287884189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(779878371/10000000000 : ℝ)|^89 ≤ (4458445389139/100000000000000 : ℝ)^73
        have hw : |(779878371/10000000000 : ℝ)|=(779878371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326055_s1_s1_21 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-835263277/10000000000 : ℝ)*x 0 + (6093583299/10000000000 : ℝ)*x 1 + (1190809023/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (835263277/10000000000 : ℝ)^89 ≤ (4847420616263/100000000000000 : ℝ)^73 := by
    have hnat : (835263277 : ℕ)^89*100000000000000^73 ≤ 4847420616263^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      835263277 10000000000 4847420616263 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6093583299/10000000000 : ℝ)^89 ≤ (10933307689827/20000000000000 : ℝ)^73 := by
    have hnat : (6093583299 : ℕ)^89*20000000000000^73 ≤ 10933307689827^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6093583299 10000000000 10933307689827 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1190809023/2500000000 : ℝ)^89 ≤ (4048604092873/10000000000000 : ℝ)^73 := by
    have hnat : (1190809023 : ℕ)^89*10000000000000^73 ≤ 4048604092873^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1190809023 2500000000 4048604092873 10000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-835263277/10000000000 : ℝ), (6093583299/10000000000 : ℝ), (1190809023/2500000000 : ℝ)] ![(4847420616263/100000000000000 : ℝ), (10933307689827/20000000000000 : ℝ), (4048604092873/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-835263277/10000000000 : ℝ)|^89 ≤ (4847420616263/100000000000000 : ℝ)^73
        have hw : |(-835263277/10000000000 : ℝ)|=(835263277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6093583299/10000000000 : ℝ)|^89 ≤ (10933307689827/20000000000000 : ℝ)^73
        have hw : |(6093583299/10000000000 : ℝ)|=(6093583299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1190809023/2500000000 : ℝ)|^89 ≤ (4048604092873/10000000000000 : ℝ)^73
        have hw : |(1190809023/2500000000 : ℝ)|=(1190809023/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326055_s1_s1_22 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5607112369/10000000000 : ℝ)*x 0 + (-2628101/125000000 : ℝ)*x 1 + (352256339/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5607112369/10000000000 : ℝ)^89 ≤ (49393342057629/100000000000000 : ℝ)^73 := by
    have hnat : (5607112369 : ℕ)^89*100000000000000^73 ≤ 49393342057629^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5607112369 10000000000 49393342057629 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2628101/125000000 : ℝ)^89 ≤ (901802974307/100000000000000 : ℝ)^73 := by
    have hnat : (2628101 : ℕ)^89*100000000000000^73 ≤ 901802974307^73*125000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628101 125000000 901802974307 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (352256339/625000000 : ℝ)^89 ≤ (49704854946737/100000000000000 : ℝ)^73 := by
    have hnat : (352256339 : ℕ)^89*100000000000000^73 ≤ 49704854946737^73*625000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      352256339 625000000 49704854946737 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5607112369/10000000000 : ℝ), (-2628101/125000000 : ℝ), (352256339/625000000 : ℝ)] ![(49393342057629/100000000000000 : ℝ), (901802974307/100000000000000 : ℝ), (49704854946737/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5607112369/10000000000 : ℝ)|^89 ≤ (49393342057629/100000000000000 : ℝ)^73
        have hw : |(5607112369/10000000000 : ℝ)|=(5607112369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2628101/125000000 : ℝ)|^89 ≤ (901802974307/100000000000000 : ℝ)^73
        have hw : |(-2628101/125000000 : ℝ)|=(2628101/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(352256339/625000000 : ℝ)|^89 ≤ (49704854946737/100000000000000 : ℝ)^73
        have hw : |(352256339/625000000 : ℝ)|=(352256339/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326055_s1_s1_23 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4283437823/10000000000 : ℝ)*x 0 + (155783171/250000000 : ℝ)*x 1 + (-258461973/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4283437823/10000000000 : ℝ)^89 ≤ (17785228557047/50000000000000 : ℝ)^73 := by
    have hnat : (4283437823 : ℕ)^89*50000000000000^73 ≤ 17785228557047^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4283437823 10000000000 17785228557047 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (155783171/250000000 : ℝ)^89 ≤ (28088405755509/50000000000000 : ℝ)^73 := by
    have hnat : (155783171 : ℕ)^89*50000000000000^73 ≤ 28088405755509^73*250000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      155783171 250000000 28088405755509 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (258461973/2000000000 : ℝ)^89 ≤ (103159141979/1250000000000 : ℝ)^73 := by
    have hnat : (258461973 : ℕ)^89*1250000000000^73 ≤ 103159141979^73*2000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258461973 2000000000 103159141979 1250000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4283437823/10000000000 : ℝ), (155783171/250000000 : ℝ), (-258461973/2000000000 : ℝ)] ![(17785228557047/50000000000000 : ℝ), (28088405755509/50000000000000 : ℝ), (103159141979/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4283437823/10000000000 : ℝ)|^89 ≤ (17785228557047/50000000000000 : ℝ)^73
        have hw : |(4283437823/10000000000 : ℝ)|=(4283437823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(155783171/250000000 : ℝ)|^89 ≤ (28088405755509/50000000000000 : ℝ)^73
        have hw : |(155783171/250000000 : ℝ)|=(155783171/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-258461973/2000000000 : ℝ)|^89 ≤ (103159141979/1250000000000 : ℝ)^73
        have hw : |(-258461973/2000000000 : ℝ)|=(258461973/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326055_s1_s1_27 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7731616629/10000000000 : ℝ)*x 0 + (1038431559/5000000000 : ℝ)*x 1 + (890780883/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7731616629/10000000000 : ℝ)^89 ≤ (73077151856193/100000000000000 : ℝ)^73 := by
    have hnat : (7731616629 : ℕ)^89*100000000000000^73 ≤ 73077151856193^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7731616629 10000000000 73077151856193 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1038431559/5000000000 : ℝ)^89 ≤ (2943260056177/20000000000000 : ℝ)^73 := by
    have hnat : (1038431559 : ℕ)^89*20000000000000^73 ≤ 2943260056177^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038431559 5000000000 2943260056177 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (890780883/5000000000 : ℝ)^89 ≤ (6103273930157/50000000000000 : ℝ)^73 := by
    have hnat : (890780883 : ℕ)^89*50000000000000^73 ≤ 6103273930157^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      890780883 5000000000 6103273930157 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7731616629/10000000000 : ℝ), (1038431559/5000000000 : ℝ), (890780883/5000000000 : ℝ)] ![(73077151856193/100000000000000 : ℝ), (2943260056177/20000000000000 : ℝ), (6103273930157/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7731616629/10000000000 : ℝ)|^89 ≤ (73077151856193/100000000000000 : ℝ)^73
        have hw : |(7731616629/10000000000 : ℝ)|=(7731616629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1038431559/5000000000 : ℝ)|^89 ≤ (2943260056177/20000000000000 : ℝ)^73
        have hw : |(1038431559/5000000000 : ℝ)|=(1038431559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(890780883/5000000000 : ℝ)|^89 ≤ (6103273930157/50000000000000 : ℝ)^73
        have hw : |(890780883/5000000000 : ℝ)|=(890780883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c326055_s1 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41253/20000 : ℝ) (163929/100000 : ℝ) (10213/12500 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((66743/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(66743/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(12719/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(12719/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(64731/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(64731/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((4481/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4481/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18223/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(18223/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7153/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(7153/20000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (10213/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (10213/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (10213/12500 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (10213/12500 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (10213/12500 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (10213/12500 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  have s1_pow0 : (66743/100000 : ℝ) ^ (87/16 : ℝ) ≤ (11097013704811834249/100000000000000000000 : ℝ) := by
    have hpowers : (66743/100000 : ℝ)^87 ≤ (11097013704811834249/100000000000000000000 : ℝ)^16 := by
      have hnat : (66743 : ℕ)^87*100000000000000000000^16 ≤ 11097013704811834249^16*100000^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        66743 100000 11097013704811834249 100000000000000000000 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (66743/100000 : ℝ)) (X := (11097013704811834249/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (111097013704811834249/100000000000000000000 : ℝ) ≤ (5097709003859293/5000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (111097013704811834249/100000000000000000000 : ℝ)^16 ≤ (5097709003859293/5000000000000000 : ℝ)^87 := by
      have hnat : (111097013704811834249 : ℕ)^16*5000000000000000^87 ≤ 5097709003859293^87*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        111097013704811834249 100000000000000000000 5097709003859293 5000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5097709003859293/5000000000000000 : ℝ)) (X := (111097013704811834249/100000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (61097013704811834249/50000000000000000000 : ℝ) ≤ (324234492069449/312500000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (61097013704811834249/50000000000000000000 : ℝ)^16 ≤ (324234492069449/312500000000000 : ℝ)^87 := by
      have hnat : (61097013704811834249 : ℕ)^16*312500000000000^87 ≤ 324234492069449^87*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        61097013704811834249 50000000000000000000 324234492069449 312500000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (324234492069449/312500000000000 : ℝ)) (X := (61097013704811834249/50000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(97709003859293/3337150000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(90042869251891/3337150000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (66743/100000 : ℝ)) (alpha := (97709003859293/3337150000000000 : ℝ)) (beta := (90042869251891/3337150000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (66743/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(97709003859293/3337150000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(90042869251891/3337150000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (12719/20000 : ℝ) ^ (87/16 : ℝ) ≤ (2133302376006878071/25000000000000000000 : ℝ) := by
    have hpowers : (12719/20000 : ℝ)^87 ≤ (2133302376006878071/25000000000000000000 : ℝ)^16 := by
      have hnat : (12719 : ℕ)^87*25000000000000000000^16 ≤ 2133302376006878071^16*20000^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12719 20000 2133302376006878071 25000000000000000000 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (12719/20000 : ℝ)) (X := (2133302376006878071/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (27133302376006878071/25000000000000000000 : ℝ) ≤ (2537933658166719/2500000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (27133302376006878071/25000000000000000000 : ℝ)^16 ≤ (2537933658166719/2500000000000000 : ℝ)^87 := by
      have hnat : (27133302376006878071 : ℕ)^16*2500000000000000^87 ≤ 2537933658166719^87*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27133302376006878071 25000000000000000000 2537933658166719 2500000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2537933658166719/2500000000000000 : ℝ)) (X := (27133302376006878071/25000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (14633302376006878071/12500000000000000000 : ℝ) ≤ (643376619003503/625000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (14633302376006878071/12500000000000000000 : ℝ)^16 ≤ (643376619003503/625000000000000 : ℝ)^87 := by
      have hnat : (14633302376006878071 : ℕ)^16*625000000000000^87 ≤ 643376619003503^87*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14633302376006878071 12500000000000000000 643376619003503 625000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (643376619003503/625000000000000 : ℝ)) (X := (14633302376006878071/12500000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(5419094023817/227125000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(35572817847293/1589875000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (12719/20000 : ℝ)) (alpha := (5419094023817/227125000000000 : ℝ)) (beta := (35572817847293/1589875000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (12719/20000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(5419094023817/227125000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(35572817847293/1589875000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (64731/100000 : ℝ) ^ (87/16 : ℝ) ≤ (4697785944237175437/50000000000000000000 : ℝ) := by
    have hpowers : (64731/100000 : ℝ)^87 ≤ (4697785944237175437/50000000000000000000 : ℝ)^16 := by
      have hnat : (64731 : ℕ)^87*50000000000000000000^16 ≤ 4697785944237175437^16*100000^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        64731 100000 4697785944237175437 50000000000000000000 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (64731/100000 : ℝ)) (X := (4697785944237175437/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (54697785944237175437/50000000000000000000 : ℝ) ≤ (10166521104379187/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (54697785944237175437/50000000000000000000 : ℝ)^16 ≤ (10166521104379187/10000000000000000 : ℝ)^87 := by
      have hnat : (54697785944237175437 : ℕ)^16*10000000000000000^87 ≤ 10166521104379187^87*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        54697785944237175437 50000000000000000000 10166521104379187 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10166521104379187/10000000000000000 : ℝ)) (X := (54697785944237175437/50000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (29697785944237175437/25000000000000000000 : ℝ) ≤ (10321751310131741/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (29697785944237175437/25000000000000000000 : ℝ)^16 ≤ (10321751310131741/10000000000000000 : ℝ)^87 := by
      have hnat : (29697785944237175437 : ℕ)^16*10000000000000000^87 ≤ 10321751310131741^87*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        29697785944237175437 25000000000000000000 10321751310131741 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10321751310131741/10000000000000000 : ℝ)) (X := (29697785944237175437/25000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(166521104379187/6473100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(25871700958759/1078850000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (64731/100000 : ℝ)) (alpha := (166521104379187/6473100000000000 : ℝ)) (beta := (25871700958759/1078850000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (64731/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(166521104379187/6473100000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(25871700958759/1078850000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-104670343/625000000 : ℝ)*X 0 0+(5528734849/10000000000 : ℝ)*X 0 1+(4728565921/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326055_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((471217639/1000000000 : ℝ)*X 2 0+(5563468377/10000000000 : ℝ)*X 2 1+(-66003863/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326055_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((6292148613/10000000000 : ℝ)*X 0 0+(1862707087/5000000000 : ℝ)*X 0 1+(946844513/5000000000 : ℝ)*X 0 2+(6292148613/10000000000 : ℝ)*X 1 0+(1862707087/5000000000 : ℝ)*X 1 1+(946844513/5000000000 : ℝ)*X 1 2+(6292148613/10000000000 : ℝ)*X 2 0+(1862707087/5000000000 : ℝ)*X 2 1+(946844513/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326055_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-671517519/5000000000 : ℝ)*X 0 0+(4942371269/10000000000 : ℝ)*X 0 1+(2785264459/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326055_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((1166446371/2500000000 : ℝ)*X 1 0+(-12738857/500000000 : ℝ)*X 1 1+(6521455027/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326055_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((2326736939/5000000000 : ℝ)*X 2 0+(247471979/400000000 : ℝ)*X 2 1+(-425620599/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326055_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((2610072159/5000000000 : ℝ)*X 0 0+(5674747863/10000000000 : ℝ)*X 0 1+(801544617/10000000000 : ℝ)*X 0 2+(2610072159/5000000000 : ℝ)*X 1 0+(5674747863/10000000000 : ℝ)*X 1 1+(801544617/10000000000 : ℝ)*X 1 2+(2610072159/5000000000 : ℝ)*X 2 0+(5674747863/10000000000 : ℝ)*X 2 1+(801544617/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326055_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-764609927/10000000000 : ℝ)*X 0 0+(5235949977/10000000000 : ℝ)*X 0 1+(5683150163/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326055_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((548472967/1250000000 : ℝ)*X 1 0+(-350257097/5000000000 : ℝ)*X 1 1+(6528385681/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326055_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((5665455313/10000000000 : ℝ)*X 2 0+(5270918039/10000000000 : ℝ)*X 2 1+(-1181791/16000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326055_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((3721989641/5000000000 : ℝ)*X 0 0+(3287884189/10000000000 : ℝ)*X 0 1+(779878371/10000000000 : ℝ)*X 0 2+(3721989641/5000000000 : ℝ)*X 1 0+(3287884189/10000000000 : ℝ)*X 1 1+(779878371/10000000000 : ℝ)*X 1 2+(3721989641/5000000000 : ℝ)*X 2 0+(3287884189/10000000000 : ℝ)*X 2 1+(779878371/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326055_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-835263277/10000000000 : ℝ)*X 0 0+(6093583299/10000000000 : ℝ)*X 0 1+(1190809023/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326055_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((5607112369/10000000000 : ℝ)*X 1 0+(-2628101/125000000 : ℝ)*X 1 1+(352256339/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326055_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((4283437823/10000000000 : ℝ)*X 2 0+(155783171/250000000 : ℝ)*X 2 1+(-258461973/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326055_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((7731616629/10000000000 : ℝ)*X 0 0+(1038431559/5000000000 : ℝ)*X 0 1+(890780883/5000000000 : ℝ)*X 0 2+(7731616629/10000000000 : ℝ)*X 1 0+(1038431559/5000000000 : ℝ)*X 1 1+(890780883/5000000000 : ℝ)*X 1 2+(7731616629/10000000000 : ℝ)*X 2 0+(1038431559/5000000000 : ℝ)*X 2 1+(890780883/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326055_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((4481/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4481/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (33993570129868899/2000000000000000000000 : ℝ) := by norm_num
    linear_combination (6544647/1000000000000 : ℝ)*(base19) + (516915775601/1000000000000 : ℝ)*(base49) + (272843546543/50000000000 : ℝ)*(major_s1_0) + (272843546543/50000000000 : ℝ)*(major_s1_1) + (272843546543/50000000000 : ℝ)*(major_s1_2) + (4681729/125000000000 : ℝ)*(sp_s1_0) + (1670187/1000000000000 : ℝ)*(sp_s1_6) + (258379021791/31250000000 : ℝ)*(sp_s1_7) + (4134047196519/500000000000 : ℝ)*(sp_s1_8) + (8268016522019/1000000000000 : ℝ)*(sp_s1_9) + (1322780764029/500000000000 : ℝ)*(sp_s1_13) + (72060193/1000000000000 : ℝ)*(sp_s1_15) + (3423367/500000000000 : ℝ)*(sp_s1_21) + (156475859/1000000000000 : ℝ)*(sp_s1_23) + (529112639649/200000000000 : ℝ)*(f.failure) + (4134086498939/500000000000 : ℝ)*(f.sum) + (589415865557705417/5880811350000000000000000000000 : ℝ)*base62 + (4342446902029/21577000000000000000000000 : ℝ)*base65 + (5383965224891/79493750000000000000000000 : ℝ)*base67 + (155742944528617/647310000000000000000000000 : ℝ)*base69 + (523171548081178737/7200568555000000000000000000000 : ℝ)*base70 + (266831092219751/667430000000000000000000000 : ℝ)*base73 + (11544589182679/45425000000000000000000000 : ℝ)*base75 + (35361542148977/133486000000000000000000000 : ℝ)*base77 + (13913372474170339851/42445210850000000000000000000000 : ℝ)*base78 + (197/4000000000000000 : ℝ)*base87 + (197/4000000000000000 : ℝ)*base89 + (197/4000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18223/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(18223/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (102226572629357231851183081263/24886965068218750000000000000000000 : ℝ) := by norm_num
    linear_combination (45519/1000000000000 : ℝ)*(base39) + (402710730869/1000000000000 : ℝ)*(base49) + (150387/250000000000 : ℝ)*(base60) + (5116229520273/1000000000000 : ℝ)*(major_s1_0) + (5116229520273/1000000000000 : ℝ)*(major_s1_1) + (5116229520273/1000000000000 : ℝ)*(major_s1_2) + (2332349/200000000000 : ℝ)*(sp_s1_2) + (2179091/125000000000 : ℝ)*(sp_s1_7) + (245241/12500000000 : ℝ)*(sp_s1_8) + (969003062679/125000000000 : ℝ)*(sp_s1_14) + (12112534867/1562500000 : ℝ)*(sp_s1_15) + (3876015136207/500000000000 : ℝ)*(sp_s1_16) + (1240201389867/500000000000 : ℝ)*(sp_s1_20) + (3239359/250000000000 : ℝ)*(sp_s1_27) + (248041573717/100000000000 : ℝ)*(f.failure) + (7752041934159/1000000000000 : ℝ)*(f.sum) + (104531236238215751/852291500000000000000000000000 : ℝ)*base63 + (800971564680743/1078850000000000000000000000 : ℝ)*base64 + (2654497936667/17281250000000000000000000 : ℝ)*base66 + (587632499316623/2157700000000000000000000000 : ℝ)*base68 + (6305470671608846879/18001421387500000000000000000000 : ℝ)*base70 + (2400378388781707/3337150000000000000000000000 : ℝ)*base72 + (988861860883/9875000000000000000000000 : ℝ)*base74 + (134693418717357/1668575000000000000000000000 : ℝ)*base77 + (182362385378165689/4613609875000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (1401/2000000000000000 : ℝ)*base87 + (1401/2000000000000000 : ℝ)*base89 + (1401/2000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7153/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(7153/20000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (8922157280300040478916199/980135225000000000000000000000 : ℝ) := by norm_num
    linear_combination (2234627/500000000000 : ℝ)*(base15) + (78377004693/1000000000000 : ℝ)*(base40) + (247794444221/500000000000 : ℝ)*(base49) + (3581353/1000000000000 : ℝ)*(base59) + (1006563298071/200000000000 : ℝ)*(major_s1_0) + (1006563298071/200000000000 : ℝ)*(major_s1_1) + (1006563298071/200000000000 : ℝ)*(major_s1_2) + (14301059/1000000000000 : ℝ)*(sp_s1_0) + (34805267/1000000000000 : ℝ)*(sp_s1_9) + (3377287/62500000000 : ℝ)*(sp_s1_20) + (7625639648247/1000000000000 : ℝ)*(sp_s1_21) + (1906412370013/250000000000 : ℝ)*(sp_s1_22) + (7625619144039/1000000000000 : ℝ)*(sp_s1_23) + (1219960980239/500000000000 : ℝ)*(sp_s1_27) + (2439975997069/1000000000000 : ℝ)*(f.failure) + (3812826974653/500000000000 : ℝ)*(f.sum) + (2592179764288759879/3920540900000000000000000000000 : ℝ)*base62 + (122366667559717/215770000000000000000000000 : ℝ)*base65 + (5304492725809/635950000000000000000000000 : ℝ)*base67 + (59409519833517/431540000000000000000000000 : ℝ)*base68 + (94543230352733503/7200568555000000000000000000000 : ℝ)*base71 + (204731958592057/667430000000000000000000000 : ℝ)*base73 + (25389516987951/90850000000000000000000000 : ℝ)*base74 + (179626626851/83428750000000000000000000 : ℝ)*base76 + (4353004354299833089/21222605425000000000000000000000 : ℝ)*base78 + (12543/20000000000000000 : ℝ)*base86 + (12543/20000000000000000 : ℝ)*base88 + (12543/20000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41253/20000 : ℝ) (163929/100000 : ℝ) (10213/12500 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((66743/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(66743/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(12719/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(12719/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(64731/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(64731/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((4481/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4481/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18223/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(18223/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7153/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(7153/20000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c326055_s1 p hpa hpb X hX hprev0

#print axioms solution
