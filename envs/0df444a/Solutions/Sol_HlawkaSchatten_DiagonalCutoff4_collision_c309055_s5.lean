-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c309055_s5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:03:11.661984+00:00
-- url     : https://prove2.me/submissions/9a536da8-f121-40bb-8094-af29f917fada

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
theorem collision_support_c309055_s5_s5_0 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2516597773/10000000000 : ℝ)*x 0 + (340750523/625000000 : ℝ)*x 1 + (4714330949/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2516597773/10000000000 : ℝ)^35 ≤ (8360787064153/50000000000000 : ℝ)^27 := by
    have hnat : (2516597773 : ℕ)^35*50000000000000^27 ≤ 8360787064153^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2516597773 10000000000 8360787064153 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (340750523/625000000 : ℝ)^35 ≤ (22775566539997/50000000000000 : ℝ)^27 := by
    have hnat : (340750523 : ℕ)^35*50000000000000^27 ≤ 22775566539997^27*625000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340750523 625000000 22775566539997 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4714330949/10000000000 : ℝ)^35 ≤ (37727292782089/100000000000000 : ℝ)^27 := by
    have hnat : (4714330949 : ℕ)^35*100000000000000^27 ≤ 37727292782089^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4714330949 10000000000 37727292782089 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2516597773/10000000000 : ℝ), (340750523/625000000 : ℝ), (4714330949/10000000000 : ℝ)] ![(8360787064153/50000000000000 : ℝ), (22775566539997/50000000000000 : ℝ), (37727292782089/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2516597773/10000000000 : ℝ)|^35 ≤ (8360787064153/50000000000000 : ℝ)^27
        have hw : |(-2516597773/10000000000 : ℝ)|=(2516597773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(340750523/625000000 : ℝ)|^35 ≤ (22775566539997/50000000000000 : ℝ)^27
        have hw : |(340750523/625000000 : ℝ)|=(340750523/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4714330949/10000000000 : ℝ)|^35 ≤ (37727292782089/100000000000000 : ℝ)^27
        have hw : |(4714330949/10000000000 : ℝ)|=(4714330949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309055_s5_s5_1 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2356046457/5000000000 : ℝ)*x 0 + (-1780948911/10000000000 : ℝ)*x 1 + (3001891541/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2356046457/5000000000 : ℝ)^35 ≤ (18852038690773/50000000000000 : ℝ)^27 := by
    have hnat : (2356046457 : ℕ)^35*50000000000000^27 ≤ 18852038690773^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2356046457 5000000000 18852038690773 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1780948911/10000000000 : ℝ)^35 ≤ (10681254539729/100000000000000 : ℝ)^27 := by
    have hnat : (1780948911 : ℕ)^35*100000000000000^27 ≤ 10681254539729^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1780948911 10000000000 10681254539729 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3001891541/5000000000 : ℝ)^35 ≤ (6451833507473/12500000000000 : ℝ)^27 := by
    have hnat : (3001891541 : ℕ)^35*12500000000000^27 ≤ 6451833507473^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3001891541 5000000000 6451833507473 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2356046457/5000000000 : ℝ), (-1780948911/10000000000 : ℝ), (3001891541/5000000000 : ℝ)] ![(18852038690773/50000000000000 : ℝ), (10681254539729/100000000000000 : ℝ), (6451833507473/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2356046457/5000000000 : ℝ)|^35 ≤ (18852038690773/50000000000000 : ℝ)^27
        have hw : |(2356046457/5000000000 : ℝ)|=(2356046457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1780948911/10000000000 : ℝ)|^35 ≤ (10681254539729/100000000000000 : ℝ)^27
        have hw : |(-1780948911/10000000000 : ℝ)|=(1780948911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3001891541/5000000000 : ℝ)|^35 ≤ (6451833507473/12500000000000 : ℝ)^27
        have hw : |(3001891541/5000000000 : ℝ)|=(3001891541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309055_s5_s5_2 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4714229887/10000000000 : ℝ)*x 0 + (1362558307/2500000000 : ℝ)*x 1 + (-2518951149/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4714229887/10000000000 : ℝ)^35 ≤ (37726244383651/100000000000000 : ℝ)^27 := by
    have hnat : (4714229887 : ℕ)^35*100000000000000^27 ≤ 37726244383651^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4714229887 10000000000 37726244383651 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1362558307/2500000000 : ℝ)^35 ≤ (22765954211267/50000000000000 : ℝ)^27 := by
    have hnat : (1362558307 : ℕ)^35*50000000000000^27 ≤ 22765954211267^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1362558307 2500000000 22765954211267 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2518951149/10000000000 : ℝ)^35 ≤ (4185461794681/25000000000000 : ℝ)^27 := by
    have hnat : (2518951149 : ℕ)^35*25000000000000^27 ≤ 4185461794681^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2518951149 10000000000 4185461794681 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4714229887/10000000000 : ℝ), (1362558307/2500000000 : ℝ), (-2518951149/10000000000 : ℝ)] ![(37726244383651/100000000000000 : ℝ), (22765954211267/50000000000000 : ℝ), (4185461794681/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4714229887/10000000000 : ℝ)|^35 ≤ (37726244383651/100000000000000 : ℝ)^27
        have hw : |(4714229887/10000000000 : ℝ)|=(4714229887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1362558307/2500000000 : ℝ)|^35 ≤ (22765954211267/50000000000000 : ℝ)^27
        have hw : |(1362558307/2500000000 : ℝ)|=(1362558307/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2518951149/10000000000 : ℝ)|^35 ≤ (4185461794681/25000000000000 : ℝ)^27
        have hw : |(-2518951149/10000000000 : ℝ)|=(2518951149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309055_s5_s5_6 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5721486307/10000000000 : ℝ)*x 0 + (4101961963/10000000000 : ℝ)*x 1 + (2890238089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5721486307/10000000000 : ℝ)^35 ≤ (48490832149229/100000000000000 : ℝ)^27 := by
    have hnat : (5721486307 : ℕ)^35*100000000000000^27 ≤ 48490832149229^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5721486307 10000000000 48490832149229 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4101961963/10000000000 : ℝ)^35 ≤ (31500865174437/100000000000000 : ℝ)^27 := by
    have hnat : (4101961963 : ℕ)^35*100000000000000^27 ≤ 31500865174437^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4101961963 10000000000 31500865174437 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2890238089/10000000000 : ℝ)^35 ≤ (10004151330813/50000000000000 : ℝ)^27 := by
    have hnat : (2890238089 : ℕ)^35*50000000000000^27 ≤ 10004151330813^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2890238089 10000000000 10004151330813 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5721486307/10000000000 : ℝ), (4101961963/10000000000 : ℝ), (2890238089/10000000000 : ℝ)] ![(48490832149229/100000000000000 : ℝ), (31500865174437/100000000000000 : ℝ), (10004151330813/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5721486307/10000000000 : ℝ)|^35 ≤ (48490832149229/100000000000000 : ℝ)^27
        have hw : |(5721486307/10000000000 : ℝ)|=(5721486307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4101961963/10000000000 : ℝ)|^35 ≤ (31500865174437/100000000000000 : ℝ)^27
        have hw : |(4101961963/10000000000 : ℝ)|=(4101961963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2890238089/10000000000 : ℝ)|^35 ≤ (10004151330813/50000000000000 : ℝ)^27
        have hw : |(2890238089/10000000000 : ℝ)|=(2890238089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309055_s5_s5_7 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-605140451/2500000000 : ℝ)*x 0 + (5140658287/10000000000 : ℝ)*x 1 + (1277757223/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (605140451/2500000000 : ℝ)^35 ≤ (15899110240373/100000000000000 : ℝ)^27 := by
    have hnat : (605140451 : ℕ)^35*100000000000000^27 ≤ 15899110240373^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      605140451 2500000000 15899110240373 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5140658287/10000000000 : ℝ)^35 ≤ (42207988734849/100000000000000 : ℝ)^27 := by
    have hnat : (5140658287 : ℕ)^35*100000000000000^27 ≤ 42207988734849^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5140658287 10000000000 42207988734849 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1277757223/2500000000 : ℝ)^35 ≤ (4189290100877/10000000000000 : ℝ)^27 := by
    have hnat : (1277757223 : ℕ)^35*10000000000000^27 ≤ 4189290100877^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1277757223 2500000000 4189290100877 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-605140451/2500000000 : ℝ), (5140658287/10000000000 : ℝ), (1277757223/2500000000 : ℝ)] ![(15899110240373/100000000000000 : ℝ), (42207988734849/100000000000000 : ℝ), (4189290100877/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-605140451/2500000000 : ℝ)|^35 ≤ (15899110240373/100000000000000 : ℝ)^27
        have hw : |(-605140451/2500000000 : ℝ)|=(605140451/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5140658287/10000000000 : ℝ)|^35 ≤ (42207988734849/100000000000000 : ℝ)^27
        have hw : |(5140658287/10000000000 : ℝ)|=(5140658287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1277757223/2500000000 : ℝ)|^35 ≤ (4189290100877/10000000000000 : ℝ)^27
        have hw : |(1277757223/2500000000 : ℝ)|=(1277757223/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309055_s5_s5_8 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4673026989/10000000000 : ℝ)*x 0 + (-29097621/200000000 : ℝ)*x 1 + (3129757967/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4673026989/10000000000 : ℝ)^35 ≤ (37299369110459/100000000000000 : ℝ)^27 := by
    have hnat : (4673026989 : ℕ)^35*100000000000000^27 ≤ 37299369110459^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4673026989 10000000000 37299369110459 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (29097621/200000000 : ℝ)^35 ≤ (8218193682001/100000000000000 : ℝ)^27 := by
    have hnat : (29097621 : ℕ)^35*100000000000000^27 ≤ 8218193682001^27*200000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      29097621 200000000 8218193682001 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3129757967/5000000000 : ℝ)^35 ≤ (27241218595693/50000000000000 : ℝ)^27 := by
    have hnat : (3129757967 : ℕ)^35*50000000000000^27 ≤ 27241218595693^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3129757967 5000000000 27241218595693 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4673026989/10000000000 : ℝ), (-29097621/200000000 : ℝ), (3129757967/5000000000 : ℝ)] ![(37299369110459/100000000000000 : ℝ), (8218193682001/100000000000000 : ℝ), (27241218595693/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4673026989/10000000000 : ℝ)|^35 ≤ (37299369110459/100000000000000 : ℝ)^27
        have hw : |(4673026989/10000000000 : ℝ)|=(4673026989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-29097621/200000000 : ℝ)|^35 ≤ (8218193682001/100000000000000 : ℝ)^27
        have hw : |(-29097621/200000000 : ℝ)|=(29097621/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3129757967/5000000000 : ℝ)|^35 ≤ (27241218595693/50000000000000 : ℝ)^27
        have hw : |(3129757967/5000000000 : ℝ)|=(3129757967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309055_s5_s5_9 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (187006639/400000000 : ℝ)*x 0 + (2892773619/5000000000 : ℝ)*x 1 + (-2131498747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (187006639/400000000 : ℝ)^35 ≤ (18660751171967/50000000000000 : ℝ)^27 := by
    have hnat : (187006639 : ℕ)^35*50000000000000^27 ≤ 18660751171967^27*400000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      187006639 400000000 18660751171967 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2892773619/5000000000 : ℝ)^35 ≤ (24597897481653/50000000000000 : ℝ)^27 := by
    have hnat : (2892773619 : ℕ)^35*50000000000000^27 ≤ 24597897481653^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2892773619 5000000000 24597897481653 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2131498747/10000000000 : ℝ)^35 ≤ (13482702684839/100000000000000 : ℝ)^27 := by
    have hnat : (2131498747 : ℕ)^35*100000000000000^27 ≤ 13482702684839^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2131498747 10000000000 13482702684839 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(187006639/400000000 : ℝ), (2892773619/5000000000 : ℝ), (-2131498747/10000000000 : ℝ)] ![(18660751171967/50000000000000 : ℝ), (24597897481653/50000000000000 : ℝ), (13482702684839/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(187006639/400000000 : ℝ)|^35 ≤ (18660751171967/50000000000000 : ℝ)^27
        have hw : |(187006639/400000000 : ℝ)|=(187006639/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2892773619/5000000000 : ℝ)|^35 ≤ (24597897481653/50000000000000 : ℝ)^27
        have hw : |(2892773619/5000000000 : ℝ)|=(2892773619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2131498747/10000000000 : ℝ)|^35 ≤ (13482702684839/100000000000000 : ℝ)^27
        have hw : |(-2131498747/10000000000 : ℝ)|=(2131498747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309055_s5_s5_13 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5504630987/10000000000 : ℝ)*x 0 + (2398735919/5000000000 : ℝ)*x 1 + (293530443/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5504630987/10000000000 : ℝ)^35 ≤ (46121873427053/100000000000000 : ℝ)^27 := by
    have hnat : (5504630987 : ℕ)^35*100000000000000^27 ≤ 46121873427053^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5504630987 10000000000 46121873427053 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2398735919/5000000000 : ℝ)^35 ≤ (38592027862037/100000000000000 : ℝ)^27 := by
    have hnat : (2398735919 : ℕ)^35*100000000000000^27 ≤ 38592027862037^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2398735919 5000000000 38592027862037 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (293530443/1250000000 : ℝ)^35 ≤ (15286098687859/100000000000000 : ℝ)^27 := by
    have hnat : (293530443 : ℕ)^35*100000000000000^27 ≤ 15286098687859^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      293530443 1250000000 15286098687859 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5504630987/10000000000 : ℝ), (2398735919/5000000000 : ℝ), (293530443/1250000000 : ℝ)] ![(46121873427053/100000000000000 : ℝ), (38592027862037/100000000000000 : ℝ), (15286098687859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5504630987/10000000000 : ℝ)|^35 ≤ (46121873427053/100000000000000 : ℝ)^27
        have hw : |(5504630987/10000000000 : ℝ)|=(5504630987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2398735919/5000000000 : ℝ)|^35 ≤ (38592027862037/100000000000000 : ℝ)^27
        have hw : |(2398735919/5000000000 : ℝ)|=(2398735919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(293530443/1250000000 : ℝ)|^35 ≤ (15286098687859/100000000000000 : ℝ)^27
        have hw : |(293530443/1250000000 : ℝ)|=(293530443/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309055_s5_s5_14 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-26133699/125000000 : ℝ)*x 0 + (535930291/1000000000 : ℝ)*x 1 + (1287355409/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26133699/125000000 : ℝ)^35 ≤ (6574543130341/50000000000000 : ℝ)^27 := by
    have hnat : (26133699 : ℕ)^35*50000000000000^27 ≤ 6574543130341^27*125000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26133699 125000000 6574543130341 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (535930291/1000000000 : ℝ)^35 ≤ (22274814828983/50000000000000 : ℝ)^27 := by
    have hnat : (535930291 : ℕ)^35*50000000000000^27 ≤ 22274814828983^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535930291 1000000000 22274814828983 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1287355409/2500000000 : ℝ)^35 ≤ (42301284070879/100000000000000 : ℝ)^27 := by
    have hnat : (1287355409 : ℕ)^35*100000000000000^27 ≤ 42301284070879^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1287355409 2500000000 42301284070879 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-26133699/125000000 : ℝ), (535930291/1000000000 : ℝ), (1287355409/2500000000 : ℝ)] ![(6574543130341/50000000000000 : ℝ), (22274814828983/50000000000000 : ℝ), (42301284070879/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-26133699/125000000 : ℝ)|^35 ≤ (6574543130341/50000000000000 : ℝ)^27
        have hw : |(-26133699/125000000 : ℝ)|=(26133699/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(535930291/1000000000 : ℝ)|^35 ≤ (22274814828983/50000000000000 : ℝ)^27
        have hw : |(535930291/1000000000 : ℝ)|=(535930291/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1287355409/2500000000 : ℝ)|^35 ≤ (42301284070879/100000000000000 : ℝ)^27
        have hw : |(1287355409/2500000000 : ℝ)|=(1287355409/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309055_s5_s5_15 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (447883723/1000000000 : ℝ)*x 0 + (-1728170721/10000000000 : ℝ)*x 1 + (6254393239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (447883723/1000000000 : ℝ)^35 ≤ (7060522471297/20000000000000 : ℝ)^27 := by
    have hnat : (447883723 : ℕ)^35*20000000000000^27 ≤ 7060522471297^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447883723 1000000000 7060522471297 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1728170721/10000000000 : ℝ)^35 ≤ (2568185547793/25000000000000 : ℝ)^27 := by
    have hnat : (1728170721 : ℕ)^35*25000000000000^27 ≤ 2568185547793^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1728170721 10000000000 2568185547793 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6254393239/10000000000 : ℝ)^35 ≤ (10884929087127/20000000000000 : ℝ)^27 := by
    have hnat : (6254393239 : ℕ)^35*20000000000000^27 ≤ 10884929087127^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6254393239 10000000000 10884929087127 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(447883723/1000000000 : ℝ), (-1728170721/10000000000 : ℝ), (6254393239/10000000000 : ℝ)] ![(7060522471297/20000000000000 : ℝ), (2568185547793/25000000000000 : ℝ), (10884929087127/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(447883723/1000000000 : ℝ)|^35 ≤ (7060522471297/20000000000000 : ℝ)^27
        have hw : |(447883723/1000000000 : ℝ)|=(447883723/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1728170721/10000000000 : ℝ)|^35 ≤ (2568185547793/25000000000000 : ℝ)^27
        have hw : |(-1728170721/10000000000 : ℝ)|=(1728170721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6254393239/10000000000 : ℝ)|^35 ≤ (10884929087127/20000000000000 : ℝ)^27
        have hw : |(6254393239/10000000000 : ℝ)|=(6254393239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309055_s5_s5_16 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5149370679/10000000000 : ℝ)*x 0 + (1339382149/2500000000 : ℝ)*x 1 + (-2093107051/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5149370679/10000000000 : ℝ)^35 ≤ (10575185360597/25000000000000 : ℝ)^27 := by
    have hnat : (5149370679 : ℕ)^35*25000000000000^27 ≤ 10575185360597^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5149370679 10000000000 10575185360597 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1339382149/2500000000 : ℝ)^35 ≤ (2226525567947/5000000000000 : ℝ)^27 := by
    have hnat : (1339382149 : ℕ)^35*5000000000000^27 ≤ 2226525567947^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1339382149 2500000000 2226525567947 5000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2093107051/10000000000 : ℝ)^35 ≤ (2633749437299/20000000000000 : ℝ)^27 := by
    have hnat : (2093107051 : ℕ)^35*20000000000000^27 ≤ 2633749437299^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2093107051 10000000000 2633749437299 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5149370679/10000000000 : ℝ), (1339382149/2500000000 : ℝ), (-2093107051/10000000000 : ℝ)] ![(10575185360597/25000000000000 : ℝ), (2226525567947/5000000000000 : ℝ), (2633749437299/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5149370679/10000000000 : ℝ)|^35 ≤ (10575185360597/25000000000000 : ℝ)^27
        have hw : |(5149370679/10000000000 : ℝ)|=(5149370679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1339382149/2500000000 : ℝ)|^35 ≤ (2226525567947/5000000000000 : ℝ)^27
        have hw : |(1339382149/2500000000 : ℝ)|=(1339382149/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2093107051/10000000000 : ℝ)|^35 ≤ (2633749437299/20000000000000 : ℝ)^27
        have hw : |(-2093107051/10000000000 : ℝ)|=(2093107051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309055_s5_s5_20 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1561073901/2500000000 : ℝ)*x 0 + (3981670731/10000000000 : ℝ)*x 1 + (2359435681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1561073901/2500000000 : ℝ)^35 ≤ (27155384948347/50000000000000 : ℝ)^27 := by
    have hnat : (1561073901 : ℕ)^35*50000000000000^27 ≤ 27155384948347^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1561073901 2500000000 27155384948347 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3981670731/10000000000 : ℝ)^35 ≤ (30308621553301/100000000000000 : ℝ)^27 := by
    have hnat : (3981670731 : ℕ)^35*100000000000000^27 ≤ 30308621553301^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3981670731 10000000000 30308621553301 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2359435681/10000000000 : ℝ)^35 ≤ (1922576065903/12500000000000 : ℝ)^27 := by
    have hnat : (2359435681 : ℕ)^35*12500000000000^27 ≤ 1922576065903^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2359435681 10000000000 1922576065903 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1561073901/2500000000 : ℝ), (3981670731/10000000000 : ℝ), (2359435681/10000000000 : ℝ)] ![(27155384948347/50000000000000 : ℝ), (30308621553301/100000000000000 : ℝ), (1922576065903/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1561073901/2500000000 : ℝ)|^35 ≤ (27155384948347/50000000000000 : ℝ)^27
        have hw : |(1561073901/2500000000 : ℝ)|=(1561073901/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3981670731/10000000000 : ℝ)|^35 ≤ (30308621553301/100000000000000 : ℝ)^27
        have hw : |(3981670731/10000000000 : ℝ)|=(3981670731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2359435681/10000000000 : ℝ)|^35 ≤ (1922576065903/12500000000000 : ℝ)^27
        have hw : |(2359435681/10000000000 : ℝ)|=(2359435681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309055_s5_s5_21 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1059655849/5000000000 : ℝ)*x 0 + (1445529461/2500000000 : ℝ)*x 1 + (937692293/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059655849/5000000000 : ℝ)^35 ≤ (836428607147/6250000000000 : ℝ)^27 := by
    have hnat : (1059655849 : ℕ)^35*6250000000000^27 ≤ 836428607147^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059655849 5000000000 836428607147 6250000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1445529461/2500000000 : ℝ)^35 ≤ (49157997116699/100000000000000 : ℝ)^27 := by
    have hnat : (1445529461 : ℕ)^35*100000000000000^27 ≤ 49157997116699^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1445529461 2500000000 49157997116699 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (937692293/2000000000 : ℝ)^35 ≤ (37459145152239/100000000000000 : ℝ)^27 := by
    have hnat : (937692293 : ℕ)^35*100000000000000^27 ≤ 37459145152239^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      937692293 2000000000 37459145152239 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1059655849/5000000000 : ℝ), (1445529461/2500000000 : ℝ), (937692293/2000000000 : ℝ)] ![(836428607147/6250000000000 : ℝ), (49157997116699/100000000000000 : ℝ), (37459145152239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1059655849/5000000000 : ℝ)|^35 ≤ (836428607147/6250000000000 : ℝ)^27
        have hw : |(-1059655849/5000000000 : ℝ)|=(1059655849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1445529461/2500000000 : ℝ)|^35 ≤ (49157997116699/100000000000000 : ℝ)^27
        have hw : |(1445529461/2500000000 : ℝ)|=(1445529461/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(937692293/2000000000 : ℝ)|^35 ≤ (37459145152239/100000000000000 : ℝ)^27
        have hw : |(937692293/2000000000 : ℝ)|=(937692293/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309055_s5_s5_22 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2559308019/5000000000 : ℝ)*x 0 + (-1453463617/10000000000 : ℝ)*x 1 + (146049313/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2559308019/5000000000 : ℝ)^35 ≤ (10493383384733/25000000000000 : ℝ)^27 := by
    have hnat : (2559308019 : ℕ)^35*25000000000000^27 ≤ 10493383384733^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2559308019 5000000000 10493383384733 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1453463617/10000000000 : ℝ)^35 ≤ (4103908087893/50000000000000 : ℝ)^27 := by
    have hnat : (1453463617 : ℕ)^35*50000000000000^27 ≤ 4103908087893^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1453463617 10000000000 4103908087893 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (146049313/250000000 : ℝ)^35 ≤ (12454662568349/25000000000000 : ℝ)^27 := by
    have hnat : (146049313 : ℕ)^35*25000000000000^27 ≤ 12454662568349^27*250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      146049313 250000000 12454662568349 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2559308019/5000000000 : ℝ), (-1453463617/10000000000 : ℝ), (146049313/250000000 : ℝ)] ![(10493383384733/25000000000000 : ℝ), (4103908087893/50000000000000 : ℝ), (12454662568349/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2559308019/5000000000 : ℝ)|^35 ≤ (10493383384733/25000000000000 : ℝ)^27
        have hw : |(2559308019/5000000000 : ℝ)|=(2559308019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1453463617/10000000000 : ℝ)|^35 ≤ (4103908087893/50000000000000 : ℝ)^27
        have hw : |(-1453463617/10000000000 : ℝ)|=(1453463617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(146049313/250000000 : ℝ)|^35 ≤ (12454662568349/25000000000000 : ℝ)^27
        have hw : |(146049313/250000000 : ℝ)|=(146049313/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309055_s5_s5_23 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4448234121/10000000000 : ℝ)*x 0 + (5786967111/10000000000 : ℝ)*x 1 + (-1204357437/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4448234121/10000000000 : ℝ)^35 ≤ (17495120630669/50000000000000 : ℝ)^27 := by
    have hnat : (4448234121 : ℕ)^35*50000000000000^27 ≤ 17495120630669^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4448234121 10000000000 17495120630669 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5786967111/10000000000 : ℝ)^35 ≤ (24605723180177/50000000000000 : ℝ)^27 := by
    have hnat : (5786967111 : ℕ)^35*50000000000000^27 ≤ 24605723180177^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5786967111 10000000000 24605723180177 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1204357437/5000000000 : ℝ)^35 ≤ (3949578091587/25000000000000 : ℝ)^27 := by
    have hnat : (1204357437 : ℕ)^35*25000000000000^27 ≤ 3949578091587^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1204357437 5000000000 3949578091587 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4448234121/10000000000 : ℝ), (5786967111/10000000000 : ℝ), (-1204357437/5000000000 : ℝ)] ![(17495120630669/50000000000000 : ℝ), (24605723180177/50000000000000 : ℝ), (3949578091587/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4448234121/10000000000 : ℝ)|^35 ≤ (17495120630669/50000000000000 : ℝ)^27
        have hw : |(4448234121/10000000000 : ℝ)|=(4448234121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5786967111/10000000000 : ℝ)|^35 ≤ (24605723180177/50000000000000 : ℝ)^27
        have hw : |(5786967111/10000000000 : ℝ)|=(5786967111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1204357437/5000000000 : ℝ)|^35 ≤ (3949578091587/25000000000000 : ℝ)^27
        have hw : |(-1204357437/5000000000 : ℝ)|=(1204357437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309055_s5_s5_27 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (315791619/500000000 : ℝ)*x 0 + (3395919137/10000000000 : ℝ)*x 1 + (2914016749/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (315791619/500000000 : ℝ)^35 ≤ (55118694169753/100000000000000 : ℝ)^27 := by
    have hnat : (315791619 : ℕ)^35*100000000000000^27 ≤ 55118694169753^27*500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      315791619 500000000 55118694169753 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3395919137/10000000000 : ℝ)^35 ≤ (6164839100191/25000000000000 : ℝ)^27 := by
    have hnat : (3395919137 : ℕ)^35*25000000000000^27 ≤ 6164839100191^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3395919137 10000000000 6164839100191 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2914016749/10000000000 : ℝ)^35 ≤ (20221949409281/100000000000000 : ℝ)^27 := by
    have hnat : (2914016749 : ℕ)^35*100000000000000^27 ≤ 20221949409281^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2914016749 10000000000 20221949409281 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(315791619/500000000 : ℝ), (3395919137/10000000000 : ℝ), (2914016749/10000000000 : ℝ)] ![(55118694169753/100000000000000 : ℝ), (6164839100191/25000000000000 : ℝ), (20221949409281/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(315791619/500000000 : ℝ)|^35 ≤ (55118694169753/100000000000000 : ℝ)^27
        have hw : |(315791619/500000000 : ℝ)|=(315791619/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3395919137/10000000000 : ℝ)|^35 ≤ (6164839100191/25000000000000 : ℝ)^27
        have hw : |(3395919137/10000000000 : ℝ)|=(3395919137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2914016749/10000000000 : ℝ)|^35 ≤ (20221949409281/100000000000000 : ℝ)^27
        have hw : |(2914016749/10000000000 : ℝ)|=(2914016749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c309055_s5 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev4 : (0 : ℝ) ≤ ((4221/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4221/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(34687/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(34687/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(17117/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(17117/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((22321/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(22321/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(463/2000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(463/2000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22599/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(22599/100000 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (77509/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (77509/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
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
  rcases hprev4 with ⟨ratio_s4_0,ratio_s4_1,ratio_s4_2⟩
  have s5_pow0 : (4221/12500 : ℝ) ^ (69/16 : ℝ) ≤ (926145615522463569/100000000000000000000 : ℝ) := by
    have hpowers : (4221/12500 : ℝ)^69 ≤ (926145615522463569/100000000000000000000 : ℝ)^16 := by
      have hnat : (4221 : ℕ)^69*100000000000000000000^16 ≤ 926145615522463569^16*12500^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4221 12500 926145615522463569 100000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4221/12500 : ℝ)) (X := (926145615522463569/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s5_corner0a : (100926145615522463569/100000000000000000000 : ℝ) ≤ (10021399866475657/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (100926145615522463569/100000000000000000000 : ℝ)^16 ≤ (10021399866475657/10000000000000000 : ℝ)^69 := by
      have hnat : (100926145615522463569 : ℕ)^16*10000000000000000^69 ≤ 10021399866475657^69*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100926145615522463569 100000000000000000000 10021399866475657 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10021399866475657/10000000000000000 : ℝ)) (X := (100926145615522463569/100000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s5_corner0b : (50926145615522463569/50000000000000000000 : ℝ) ≤ (2008529884294117/2000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (50926145615522463569/50000000000000000000 : ℝ)^16 ≤ (2008529884294117/2000000000000000 : ℝ)^69 := by
      have hnat : (50926145615522463569 : ℕ)^16*2000000000000000^69 ≤ 2008529884294117^69*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50926145615522463569 50000000000000000000 2008529884294117 2000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2008529884294117/2000000000000000 : ℝ)) (X := (50926145615522463569/50000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s5_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(7133288825219/1125600000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1328097187183/211050000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (4221/12500 : ℝ)) (alpha := (7133288825219/1125600000000000 : ℝ)) (beta := (1328097187183/211050000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow0,s5_corner0a]) (by linarith only [s5_pow0,s5_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (4221/12500 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(7133288825219/1125600000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1328097187183/211050000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s5_pow1 : (34687/100000 : ℝ) ^ (69/16 : ℝ) ≤ (519923050386246327/50000000000000000000 : ℝ) := by
    have hpowers : (34687/100000 : ℝ)^69 ≤ (519923050386246327/50000000000000000000 : ℝ)^16 := by
      have hnat : (34687 : ℕ)^69*50000000000000000000^16 ≤ 519923050386246327^16*100000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        34687 100000 519923050386246327 50000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (34687/100000 : ℝ)) (X := (519923050386246327/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s5_corner1a : (50519923050386246327/50000000000000000000 : ℝ) ≤ (10024016663830529/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (50519923050386246327/50000000000000000000 : ℝ)^16 ≤ (10024016663830529/10000000000000000 : ℝ)^69 := by
      have hnat : (50519923050386246327 : ℕ)^16*10000000000000000^69 ≤ 10024016663830529^69*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50519923050386246327 50000000000000000000 10024016663830529 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10024016663830529/10000000000000000 : ℝ)) (X := (50519923050386246327/50000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s5_corner1b : (25519923050386246327/25000000000000000000 : ℝ) ≤ (5023922109592367/5000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (25519923050386246327/25000000000000000000 : ℝ)^16 ≤ (5023922109592367/5000000000000000 : ℝ)^69 := by
      have hnat : (25519923050386246327 : ℕ)^16*5000000000000000^69 ≤ 5023922109592367^69*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25519923050386246327 25000000000000000000 5023922109592367 5000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5023922109592367/5000000000000000 : ℝ)) (X := (25519923050386246327/25000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s5_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(24016663830529/3468700000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(4765511070841/693740000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (34687/100000 : ℝ)) (alpha := (24016663830529/3468700000000000 : ℝ)) (beta := (4765511070841/693740000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow1,s5_corner1a]) (by linarith only [s5_pow1,s5_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (34687/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(24016663830529/3468700000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(4765511070841/693740000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s5_pow2 : (17117/50000 : ℝ) ^ (69/16 : ℝ) ≤ (61408518094472689/6250000000000000000 : ℝ) := by
    have hpowers : (17117/50000 : ℝ)^69 ≤ (61408518094472689/6250000000000000000 : ℝ)^16 := by
      have hnat : (17117 : ℕ)^69*6250000000000000000^16 ≤ 61408518094472689^16*50000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17117 50000 61408518094472689 6250000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17117/50000 : ℝ)) (X := (61408518094472689/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s5_corner2a : (6311408518094472689/6250000000000000000 : ℝ) ≤ (5011348985566737/5000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (6311408518094472689/6250000000000000000 : ℝ)^16 ≤ (5011348985566737/5000000000000000 : ℝ)^69 := by
      have hnat : (6311408518094472689 : ℕ)^16*5000000000000000^69 ≤ 5011348985566737^69*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6311408518094472689 6250000000000000000 5011348985566737 5000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5011348985566737/5000000000000000 : ℝ)) (X := (6311408518094472689/6250000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s5_corner2b : (3186408518094472689/3125000000000000000 : ℝ) ≤ (10045226935639829/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (3186408518094472689/3125000000000000000 : ℝ)^16 ≤ (10045226935639829/10000000000000000 : ℝ)^69 := by
      have hnat : (3186408518094472689 : ℕ)^16*10000000000000000^69 ≤ 10045226935639829^69*3125000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3186408518094472689 3125000000000000000 10045226935639829 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10045226935639829/10000000000000000 : ℝ)) (X := (3186408518094472689/3125000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s5_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(11348985566737/1711700000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(4505792901271/684680000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (17117/50000 : ℝ)) (alpha := (11348985566737/1711700000000000 : ℝ)) (beta := (4505792901271/684680000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow2,s5_corner2a]) (by linarith only [s5_pow2,s5_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (17117/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(11348985566737/1711700000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(4505792901271/684680000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s5_0 : ((-2516597773/10000000000 : ℝ)*X 0 0+(340750523/625000000 : ℝ)*X 0 1+(4714330949/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309055_s5_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_1 : ((2356046457/5000000000 : ℝ)*X 1 0+(-1780948911/10000000000 : ℝ)*X 1 1+(3001891541/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309055_s5_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_2 : ((4714229887/10000000000 : ℝ)*X 2 0+(1362558307/2500000000 : ℝ)*X 2 1+(-2518951149/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309055_s5_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_6 : ((5721486307/10000000000 : ℝ)*X 0 0+(4101961963/10000000000 : ℝ)*X 0 1+(2890238089/10000000000 : ℝ)*X 0 2+(5721486307/10000000000 : ℝ)*X 1 0+(4101961963/10000000000 : ℝ)*X 1 1+(2890238089/10000000000 : ℝ)*X 1 2+(5721486307/10000000000 : ℝ)*X 2 0+(4101961963/10000000000 : ℝ)*X 2 1+(2890238089/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309055_s5_s5_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_7 : ((-605140451/2500000000 : ℝ)*X 0 0+(5140658287/10000000000 : ℝ)*X 0 1+(1277757223/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309055_s5_s5_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_8 : ((4673026989/10000000000 : ℝ)*X 1 0+(-29097621/200000000 : ℝ)*X 1 1+(3129757967/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309055_s5_s5_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_9 : ((187006639/400000000 : ℝ)*X 2 0+(2892773619/5000000000 : ℝ)*X 2 1+(-2131498747/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309055_s5_s5_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_13 : ((5504630987/10000000000 : ℝ)*X 0 0+(2398735919/5000000000 : ℝ)*X 0 1+(293530443/1250000000 : ℝ)*X 0 2+(5504630987/10000000000 : ℝ)*X 1 0+(2398735919/5000000000 : ℝ)*X 1 1+(293530443/1250000000 : ℝ)*X 1 2+(5504630987/10000000000 : ℝ)*X 2 0+(2398735919/5000000000 : ℝ)*X 2 1+(293530443/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309055_s5_s5_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_14 : ((-26133699/125000000 : ℝ)*X 0 0+(535930291/1000000000 : ℝ)*X 0 1+(1287355409/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309055_s5_s5_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_15 : ((447883723/1000000000 : ℝ)*X 1 0+(-1728170721/10000000000 : ℝ)*X 1 1+(6254393239/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309055_s5_s5_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_16 : ((5149370679/10000000000 : ℝ)*X 2 0+(1339382149/2500000000 : ℝ)*X 2 1+(-2093107051/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309055_s5_s5_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_20 : ((1561073901/2500000000 : ℝ)*X 0 0+(3981670731/10000000000 : ℝ)*X 0 1+(2359435681/10000000000 : ℝ)*X 0 2+(1561073901/2500000000 : ℝ)*X 1 0+(3981670731/10000000000 : ℝ)*X 1 1+(2359435681/10000000000 : ℝ)*X 1 2+(1561073901/2500000000 : ℝ)*X 2 0+(3981670731/10000000000 : ℝ)*X 2 1+(2359435681/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309055_s5_s5_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_21 : ((-1059655849/5000000000 : ℝ)*X 0 0+(1445529461/2500000000 : ℝ)*X 0 1+(937692293/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309055_s5_s5_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_22 : ((2559308019/5000000000 : ℝ)*X 1 0+(-1453463617/10000000000 : ℝ)*X 1 1+(146049313/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309055_s5_s5_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_23 : ((4448234121/10000000000 : ℝ)*X 2 0+(5786967111/10000000000 : ℝ)*X 2 1+(-1204357437/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309055_s5_s5_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_27 : ((315791619/500000000 : ℝ)*X 0 0+(3395919137/10000000000 : ℝ)*X 0 1+(2914016749/10000000000 : ℝ)*X 0 2+(315791619/500000000 : ℝ)*X 1 0+(3395919137/10000000000 : ℝ)*X 1 1+(2914016749/10000000000 : ℝ)*X 1 2+(315791619/500000000 : ℝ)*X 2 0+(3395919137/10000000000 : ℝ)*X 2 1+(2914016749/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309055_s5_s5_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s5_0 : (0 : ℝ) ≤ ((22321/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(22321/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (98116711957602491127259/12709533593750000000000000000 : ℝ) := by norm_num
    linear_combination (1627676540467/1000000000000 : ℝ)*(base49) + (4115307/1000000000000 : ℝ)*(base59) + (486867/125000000000 : ℝ)*(base60) + (11270777276811/1000000000000 : ℝ)*(major_s5_0) + (11270777276811/1000000000000 : ℝ)*(major_s5_1) + (11270777276811/1000000000000 : ℝ)*(major_s5_2) + (65265971/1000000000000 : ℝ)*(sp_s5_0) + (2543997/62500000000 : ℝ)*(sp_s5_6) + (3865985555641/250000000000 : ℝ)*(sp_s5_7) + (483248246289/31250000000 : ℝ)*(sp_s5_8) + (15463832145081/1000000000000 : ℝ)*(sp_s5_9) + (7077503787819/1000000000000 : ℝ)*(sp_s5_13) + (63607287/1000000000000 : ℝ)*(sp_s5_15) + (87671727/500000000000 : ℝ)*(sp_s5_23) + (7077544491771/1000000000000 : ℝ)*(f.failure) + (3092801497707/200000000000 : ℝ)*(f.sum) + (2188871613031055711/7421717237500000000000000000000 : ℝ)*base62 + (250729319861189/684680000000000000000000000 : ℝ)*base65 + (98685516776031/138748000000000000000000000 : ℝ)*base67 + (554307581223877/1711700000000000000000000000 : ℝ)*base69 + (1552417807603542109/6422298400000000000000000000000 : ℝ)*base70 + (10653011051089/17587500000000000000000000 : ℝ)*base73 + (1923361050959399/3468700000000000000000000000 : ℝ)*base75 + (210384097421803/375200000000000000000000000 : ℝ)*base77 + (503410610956829879/4880460900000000000000000000000 : ℝ)*base79 + (43563/100000000000000000 : ℝ)*base86 + (43563/100000000000000000 : ℝ)*base88 + (43563/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s5_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(463/2000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(463/2000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (833481275400841370048915061047/83538849225300000000000000000000000 : ℝ) := by norm_num
    linear_combination (754824908657/500000000000 : ℝ)*(base49) + (1854967/500000000000 : ℝ)*(base60) + (10904356152691/1000000000000 : ℝ)*(major_s5_0) + (10904356152691/1000000000000 : ℝ)*(major_s5_1) + (10904356152691/1000000000000 : ℝ)*(major_s5_2) + (120647529/1000000000000 : ℝ)*(sp_s5_1) + (9488241/250000000000 : ℝ)*(sp_s5_2) + (49586879/500000000000 : ℝ)*(sp_s5_7) + (12967281/500000000000 : ℝ)*(sp_s5_8) + (14961161406433/1000000000000 : ℝ)*(sp_s5_14) + (14961113998101/1000000000000 : ℝ)*(sp_s5_15) + (3740305656807/250000000000 : ℝ)*(sp_s5_16) + (3423669420469/500000000000 : ℝ)*(sp_s5_20) + (27389631/250000000000 : ℝ)*(sp_s5_27) + (3423724199731/500000000000 : ℝ)*(f.failure) + (14961260580191/1000000000000 : ℝ)*(f.sum) + (10349220081876875927/14843434475000000000000000000000 : ℝ)*base62 + (100378525895721/136936000000000000000000000 : ℝ)*base65 + (132464237545897/693740000000000000000000000 : ℝ)*base67 + (1142931282035153/1711700000000000000000000000 : ℝ)*base68 + (7811107317908434513/19266895200000000000000000000000 : ℝ)*base71 + (25510546837921/105525000000000000000000000 : ℝ)*base72 + (961005665788701/3468700000000000000000000000 : ℝ)*base74 + (243671889959431/1125600000000000000000000000 : ℝ)*base76 + (1249852910579194633/14641382700000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (12557/50000000000000000 : ℝ)*base87 + (12557/50000000000000000 : ℝ)*base89 + (12557/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s5_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22599/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(22599/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1631760754356060049420507935629/111385132300400000000000000000000000 : ℝ) := by norm_num
    linear_combination (9854598851/1000000000000 : ℝ)*(base40) + (1582432447311/1000000000000 : ℝ)*(base49) + (10837528602113/1000000000000 : ℝ)*(major_s5_0) + (10837528602113/1000000000000 : ℝ)*(major_s5_1) + (10837528602113/1000000000000 : ℝ)*(major_s5_2) + (263681973/1000000000000 : ℝ)*(sp_s5_0) + (26204217/200000000000 : ℝ)*(sp_s5_1) + (126361057/1000000000000 : ℝ)*(sp_s5_2) + (87803219/1000000000000 : ℝ)*(sp_s5_9) + (91125443/500000000000 : ℝ)*(sp_s5_20) + (14869304955099/1000000000000 : ℝ)*(sp_s5_21) + (14869437615987/1000000000000 : ℝ)*(sp_s5_22) + (3717338618199/250000000000 : ℝ)*(sp_s5_23) + (6805301433023/1000000000000 : ℝ)*(sp_s5_27) + (1701370920977/250000000000 : ℝ)*(f.failure) + (929348039817/62500000000 : ℝ)*(f.sum) + (11247152479102481957/29686868950000000000000000000000 : ℝ)*base62 + (572146223154893/684680000000000000000000000 : ℝ)*base64 + (258397980625903/693740000000000000000000000 : ℝ)*base66 + (1732363517748319/1711700000000000000000000000 : ℝ)*base68 + (3069336098351879941/19266895200000000000000000000000 : ℝ)*base70 + (44773967464909/52762500000000000000000000 : ℝ)*base72 + (3479629003223303/3468700000000000000000000000 : ℝ)*base74 + (879226546787213/1125600000000000000000000000 : ℝ)*base76 + (3057052931096780671/14641382700000000000000000000000 : ℝ)*base79 + (681/25000000000000000 : ℝ)*base86 + (681/25000000000000000 : ℝ)*base88 + (681/25000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s5_0,ratio_s5_1,ratio_s5_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev4 : (0 : ℝ) ≤ ((4221/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4221/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(34687/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(34687/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(17117/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(17117/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((22321/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(22321/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(463/2000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(463/2000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22599/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(22599/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c309055_s5 p hpa hpb X hX hprev4

#print axioms solution
