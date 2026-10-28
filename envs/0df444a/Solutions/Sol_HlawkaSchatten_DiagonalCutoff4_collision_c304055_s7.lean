-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c304055_s7
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:45:33.815253+00:00
-- url     : https://prove2.me/submissions/401e33e7-438d-4a7e-aa5d-d3755e9b925f

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
theorem collision_support_c304055_s7_s7_0 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-11832487/50000000 : ℝ)*x 0 + (5640739871/10000000000 : ℝ)*x 1 + (4792346711/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (11832487/50000000 : ℝ)^133 ≤ (7495023459269/50000000000000 : ℝ)^101 := by
    have hnat : (11832487 : ℕ)^133*50000000000000^101 ≤ 7495023459269^101*50000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11832487 50000000 7495023459269 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5640739871/10000000000 : ℝ)^133 ≤ (47049115295277/100000000000000 : ℝ)^101 := by
    have hnat : (5640739871 : ℕ)^133*100000000000000^101 ≤ 47049115295277^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5640739871 10000000000 47049115295277 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4792346711/10000000000 : ℝ)^133 ≤ (18980418885841/50000000000000 : ℝ)^101 := by
    have hnat : (4792346711 : ℕ)^133*50000000000000^101 ≤ 18980418885841^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4792346711 10000000000 18980418885841 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-11832487/50000000 : ℝ), (5640739871/10000000000 : ℝ), (4792346711/10000000000 : ℝ)] ![(7495023459269/50000000000000 : ℝ), (47049115295277/100000000000000 : ℝ), (18980418885841/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-11832487/50000000 : ℝ)|^133 ≤ (7495023459269/50000000000000 : ℝ)^101
        have hw : |(-11832487/50000000 : ℝ)|=(11832487/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5640739871/10000000000 : ℝ)|^133 ≤ (47049115295277/100000000000000 : ℝ)^101
        have hw : |(5640739871/10000000000 : ℝ)|=(5640739871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4792346711/10000000000 : ℝ)|^133 ≤ (18980418885841/50000000000000 : ℝ)^101
        have hw : |(4792346711/10000000000 : ℝ)|=(4792346711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304055_s7_s7_1 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (191908549/400000000 : ℝ)*x 0 + (-76763413/500000000 : ℝ)*x 1 + (6219254559/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (191908549/400000000 : ℝ)^133 ≤ (38016829977393/100000000000000 : ℝ)^101 := by
    have hnat : (191908549 : ℕ)^133*100000000000000^101 ≤ 38016829977393^101*400000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      191908549 400000000 38016829977393 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (76763413/500000000 : ℝ)^133 ≤ (4239470998901/50000000000000 : ℝ)^101 := by
    have hnat : (76763413 : ℕ)^133*50000000000000^101 ≤ 4239470998901^101*500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      76763413 500000000 4239470998901 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6219254559/10000000000 : ℝ)^133 ≤ (21401691201/40000000000 : ℝ)^101 := by
    have hnat : (6219254559 : ℕ)^133*40000000000^101 ≤ 21401691201^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6219254559 10000000000 21401691201 40000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(191908549/400000000 : ℝ), (-76763413/500000000 : ℝ), (6219254559/10000000000 : ℝ)] ![(38016829977393/100000000000000 : ℝ), (4239470998901/50000000000000 : ℝ), (21401691201/40000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(191908549/400000000 : ℝ)|^133 ≤ (38016829977393/100000000000000 : ℝ)^101
        have hw : |(191908549/400000000 : ℝ)|=(191908549/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-76763413/500000000 : ℝ)|^133 ≤ (4239470998901/50000000000000 : ℝ)^101
        have hw : |(-76763413/500000000 : ℝ)|=(76763413/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6219254559/10000000000 : ℝ)|^133 ≤ (21401691201/40000000000 : ℝ)^101
        have hw : |(6219254559/10000000000 : ℝ)|=(6219254559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304055_s7_s7_2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4783004183/10000000000 : ℝ)*x 0 + (2814107539/5000000000 : ℝ)*x 1 + (-2394610831/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4783004183/10000000000 : ℝ)^133 ≤ (37863417792731/100000000000000 : ℝ)^101 := by
    have hnat : (4783004183 : ℕ)^133*100000000000000^101 ≤ 37863417792731^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4783004183 10000000000 37863417792731 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2814107539/5000000000 : ℝ)^133 ≤ (23455798046191/50000000000000 : ℝ)^101 := by
    have hnat : (2814107539 : ℕ)^133*50000000000000^101 ≤ 23455798046191^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2814107539 5000000000 23455798046191 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2394610831/10000000000 : ℝ)^133 ≤ (7612493044701/50000000000000 : ℝ)^101 := by
    have hnat : (2394610831 : ℕ)^133*50000000000000^101 ≤ 7612493044701^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2394610831 10000000000 7612493044701 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4783004183/10000000000 : ℝ), (2814107539/5000000000 : ℝ), (-2394610831/10000000000 : ℝ)] ![(37863417792731/100000000000000 : ℝ), (23455798046191/50000000000000 : ℝ), (7612493044701/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4783004183/10000000000 : ℝ)|^133 ≤ (37863417792731/100000000000000 : ℝ)^101
        have hw : |(4783004183/10000000000 : ℝ)|=(4783004183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2814107539/5000000000 : ℝ)|^133 ≤ (23455798046191/50000000000000 : ℝ)^101
        have hw : |(2814107539/5000000000 : ℝ)|=(2814107539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2394610831/10000000000 : ℝ)|^133 ≤ (7612493044701/50000000000000 : ℝ)^101
        have hw : |(-2394610831/10000000000 : ℝ)|=(2394610831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304055_s7_s7_6 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (733440473/1250000000 : ℝ)*x 0 + (4112444187/10000000000 : ℝ)*x 1 + (287962351/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (733440473/1250000000 : ℝ)^133 ≤ (49555746405047/100000000000000 : ℝ)^101 := by
    have hnat : (733440473 : ℕ)^133*100000000000000^101 ≤ 49555746405047^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      733440473 1250000000 49555746405047 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4112444187/10000000000 : ℝ)^133 ≤ (31033779900447/100000000000000 : ℝ)^101 := by
    have hnat : (4112444187 : ℕ)^133*100000000000000^101 ≤ 31033779900447^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4112444187 10000000000 31033779900447 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (287962351/1000000000 : ℝ)^133 ≤ (19410473680711/100000000000000 : ℝ)^101 := by
    have hnat : (287962351 : ℕ)^133*100000000000000^101 ≤ 19410473680711^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      287962351 1000000000 19410473680711 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(733440473/1250000000 : ℝ), (4112444187/10000000000 : ℝ), (287962351/1000000000 : ℝ)] ![(49555746405047/100000000000000 : ℝ), (31033779900447/100000000000000 : ℝ), (19410473680711/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(733440473/1250000000 : ℝ)|^133 ≤ (49555746405047/100000000000000 : ℝ)^101
        have hw : |(733440473/1250000000 : ℝ)|=(733440473/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4112444187/10000000000 : ℝ)|^133 ≤ (31033779900447/100000000000000 : ℝ)^101
        have hw : |(4112444187/10000000000 : ℝ)|=(4112444187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(287962351/1000000000 : ℝ)|^133 ≤ (19410473680711/100000000000000 : ℝ)^101
        have hw : |(287962351/1000000000 : ℝ)|=(287962351/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304055_s7_s7_7 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2101721753/10000000000 : ℝ)*x 0 + (2482945211/5000000000 : ℝ)*x 1 + (5672381383/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2101721753/10000000000 : ℝ)^133 ≤ (3205424812637/25000000000000 : ℝ)^101 := by
    have hnat : (2101721753 : ℕ)^133*25000000000000^101 ≤ 3205424812637^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2101721753 10000000000 3205424812637 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2482945211/5000000000 : ℝ)^133 ≤ (49726673161/125000000000 : ℝ)^101 := by
    have hnat : (2482945211 : ℕ)^133*125000000000^101 ≤ 49726673161^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2482945211 5000000000 49726673161 125000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5672381383/10000000000 : ℝ)^133 ≤ (1895878488151/4000000000000 : ℝ)^101 := by
    have hnat : (5672381383 : ℕ)^133*4000000000000^101 ≤ 1895878488151^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5672381383 10000000000 1895878488151 4000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2101721753/10000000000 : ℝ), (2482945211/5000000000 : ℝ), (5672381383/10000000000 : ℝ)] ![(3205424812637/25000000000000 : ℝ), (49726673161/125000000000 : ℝ), (1895878488151/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2101721753/10000000000 : ℝ)|^133 ≤ (3205424812637/25000000000000 : ℝ)^101
        have hw : |(-2101721753/10000000000 : ℝ)|=(2101721753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2482945211/5000000000 : ℝ)|^133 ≤ (49726673161/125000000000 : ℝ)^101
        have hw : |(2482945211/5000000000 : ℝ)|=(2482945211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5672381383/10000000000 : ℝ)|^133 ≤ (1895878488151/4000000000000 : ℝ)^101
        have hw : |(5672381383/10000000000 : ℝ)|=(5672381383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304055_s7_s7_8 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (922757567/2000000000 : ℝ)*x 0 + (-833659851/10000000000 : ℝ)*x 1 + (6792937183/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (922757567/2000000000 : ℝ)^133 ≤ (18054706552487/50000000000000 : ℝ)^101 := by
    have hnat : (922757567 : ℕ)^133*50000000000000^101 ≤ 18054706552487^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      922757567 2000000000 18054706552487 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (833659851/10000000000 : ℝ)^133 ≤ (3794232844291/100000000000000 : ℝ)^101 := by
    have hnat : (833659851 : ℕ)^133*100000000000000^101 ≤ 3794232844291^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      833659851 10000000000 3794232844291 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6792937183/10000000000 : ℝ)^133 ≤ (60096354040189/100000000000000 : ℝ)^101 := by
    have hnat : (6792937183 : ℕ)^133*100000000000000^101 ≤ 60096354040189^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6792937183 10000000000 60096354040189 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(922757567/2000000000 : ℝ), (-833659851/10000000000 : ℝ), (6792937183/10000000000 : ℝ)] ![(18054706552487/50000000000000 : ℝ), (3794232844291/100000000000000 : ℝ), (60096354040189/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(922757567/2000000000 : ℝ)|^133 ≤ (18054706552487/50000000000000 : ℝ)^101
        have hw : |(922757567/2000000000 : ℝ)|=(922757567/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-833659851/10000000000 : ℝ)|^133 ≤ (3794232844291/100000000000000 : ℝ)^101
        have hw : |(-833659851/10000000000 : ℝ)|=(833659851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6792937183/10000000000 : ℝ)|^133 ≤ (60096354040189/100000000000000 : ℝ)^101
        have hw : |(6792937183/10000000000 : ℝ)|=(6792937183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304055_s7_s7_9 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2299486867/5000000000 : ℝ)*x 0 + (398800919/625000000 : ℝ)*x 1 + (-1565734367/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2299486867/5000000000 : ℝ)^133 ≤ (287654525291/800000000000 : ℝ)^101 := by
    have hnat : (2299486867 : ℕ)^133*800000000000^101 ≤ 287654525291^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2299486867 5000000000 287654525291 800000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (398800919/625000000 : ℝ)^133 ≤ (55341982145477/100000000000000 : ℝ)^101 := by
    have hnat : (398800919 : ℕ)^133*100000000000000^101 ≤ 55341982145477^101*625000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      398800919 625000000 55341982145477 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1565734367/10000000000 : ℝ)^133 ≤ (271912567757/3125000000000 : ℝ)^101 := by
    have hnat : (1565734367 : ℕ)^133*3125000000000^101 ≤ 271912567757^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1565734367 10000000000 271912567757 3125000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2299486867/5000000000 : ℝ), (398800919/625000000 : ℝ), (-1565734367/10000000000 : ℝ)] ![(287654525291/800000000000 : ℝ), (55341982145477/100000000000000 : ℝ), (271912567757/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2299486867/5000000000 : ℝ)|^133 ≤ (287654525291/800000000000 : ℝ)^101
        have hw : |(2299486867/5000000000 : ℝ)|=(2299486867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(398800919/625000000 : ℝ)|^133 ≤ (55341982145477/100000000000000 : ℝ)^101
        have hw : |(398800919/625000000 : ℝ)|=(398800919/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1565734367/10000000000 : ℝ)|^133 ≤ (271912567757/3125000000000 : ℝ)^101
        have hw : |(-1565734367/10000000000 : ℝ)|=(1565734367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304055_s7_s7_13 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5294865031/10000000000 : ℝ)*x 0 + (1391589661/2500000000 : ℝ)*x 1 + (450773699/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294865031/10000000000 : ℝ)^133 ≤ (43287586810259/100000000000000 : ℝ)^101 := by
    have hnat : (5294865031 : ℕ)^133*100000000000000^101 ≤ 43287586810259^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294865031 10000000000 43287586810259 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1391589661/2500000000 : ℝ)^133 ≤ (11558462908179/25000000000000 : ℝ)^101 := by
    have hnat : (1391589661 : ℕ)^133*25000000000000^101 ≤ 11558462908179^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1391589661 2500000000 11558462908179 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (450773699/2500000000 : ℝ)^133 ≤ (654910095829/6250000000000 : ℝ)^101 := by
    have hnat : (450773699 : ℕ)^133*6250000000000^101 ≤ 654910095829^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450773699 2500000000 654910095829 6250000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294865031/10000000000 : ℝ), (1391589661/2500000000 : ℝ), (450773699/2500000000 : ℝ)] ![(43287586810259/100000000000000 : ℝ), (11558462908179/25000000000000 : ℝ), (654910095829/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294865031/10000000000 : ℝ)|^133 ≤ (43287586810259/100000000000000 : ℝ)^101
        have hw : |(5294865031/10000000000 : ℝ)|=(5294865031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1391589661/2500000000 : ℝ)|^133 ≤ (11558462908179/25000000000000 : ℝ)^101
        have hw : |(1391589661/2500000000 : ℝ)|=(1391589661/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(450773699/2500000000 : ℝ)|^133 ≤ (654910095829/6250000000000 : ℝ)^101
        have hw : |(450773699/2500000000 : ℝ)|=(450773699/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304055_s7_s7_14 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-726113389/5000000000 : ℝ)*x 0 + (166966297/312500000 : ℝ)*x 1 + (2877768767/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (726113389/5000000000 : ℝ)^133 ≤ (157605147441/2000000000000 : ℝ)^101 := by
    have hnat : (726113389 : ℕ)^133*2000000000000^101 ≤ 157605147441^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      726113389 5000000000 157605147441 2000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (166966297/312500000 : ℝ)^133 ≤ (43805686502413/100000000000000 : ℝ)^101 := by
    have hnat : (166966297 : ℕ)^133*100000000000000^101 ≤ 43805686502413^101*312500000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166966297 312500000 43805686502413 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2877768767/5000000000 : ℝ)^133 ≤ (48314056107237/100000000000000 : ℝ)^101 := by
    have hnat : (2877768767 : ℕ)^133*100000000000000^101 ≤ 48314056107237^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2877768767 5000000000 48314056107237 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-726113389/5000000000 : ℝ), (166966297/312500000 : ℝ), (2877768767/5000000000 : ℝ)] ![(157605147441/2000000000000 : ℝ), (43805686502413/100000000000000 : ℝ), (48314056107237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-726113389/5000000000 : ℝ)|^133 ≤ (157605147441/2000000000000 : ℝ)^101
        have hw : |(-726113389/5000000000 : ℝ)|=(726113389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(166966297/312500000 : ℝ)|^133 ≤ (43805686502413/100000000000000 : ℝ)^101
        have hw : |(166966297/312500000 : ℝ)|=(166966297/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2877768767/5000000000 : ℝ)|^133 ≤ (48314056107237/100000000000000 : ℝ)^101
        have hw : |(2877768767/5000000000 : ℝ)|=(2877768767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304055_s7_s7_15 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4288451489/10000000000 : ℝ)*x 0 + (-338598891/2500000000 : ℝ)*x 1 + (3393048311/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4288451489/10000000000 : ℝ)^133 ≤ (32794548094921/100000000000000 : ℝ)^101 := by
    have hnat : (4288451489 : ℕ)^133*100000000000000^101 ≤ 32794548094921^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4288451489 10000000000 32794548094921 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (338598891/2500000000 : ℝ)^133 ≤ (3594388363027/50000000000000 : ℝ)^101 := by
    have hnat : (338598891 : ℕ)^133*50000000000000^101 ≤ 3594388363027^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338598891 2500000000 3594388363027 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3393048311/5000000000 : ℝ)^133 ≤ (15004168790517/25000000000000 : ℝ)^101 := by
    have hnat : (3393048311 : ℕ)^133*25000000000000^101 ≤ 15004168790517^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3393048311 5000000000 15004168790517 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4288451489/10000000000 : ℝ), (-338598891/2500000000 : ℝ), (3393048311/5000000000 : ℝ)] ![(32794548094921/100000000000000 : ℝ), (3594388363027/50000000000000 : ℝ), (15004168790517/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4288451489/10000000000 : ℝ)|^133 ≤ (32794548094921/100000000000000 : ℝ)^101
        have hw : |(4288451489/10000000000 : ℝ)|=(4288451489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-338598891/2500000000 : ℝ)|^133 ≤ (3594388363027/50000000000000 : ℝ)^101
        have hw : |(-338598891/2500000000 : ℝ)|=(338598891/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3393048311/5000000000 : ℝ)|^133 ≤ (15004168790517/25000000000000 : ℝ)^101
        have hw : |(3393048311/5000000000 : ℝ)|=(3393048311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304055_s7_s7_16 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5748166571/10000000000 : ℝ)*x 0 + (333144219/625000000 : ℝ)*x 1 + (-92661181/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5748166571/10000000000 : ℝ)^133 ≤ (48232594314509/100000000000000 : ℝ)^101 := by
    have hnat : (5748166571 : ℕ)^133*100000000000000^101 ≤ 48232594314509^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5748166571 10000000000 48232594314509 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (333144219/625000000 : ℝ)^133 ≤ (21834775367083/50000000000000 : ℝ)^101 := by
    have hnat : (333144219 : ℕ)^133*50000000000000^101 ≤ 21834775367083^101*625000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      333144219 625000000 21834775367083 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (92661181/625000000 : ℝ)^133 ≤ (1619570986541/20000000000000 : ℝ)^101 := by
    have hnat : (92661181 : ℕ)^133*20000000000000^101 ≤ 1619570986541^101*625000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      92661181 625000000 1619570986541 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5748166571/10000000000 : ℝ), (333144219/625000000 : ℝ), (-92661181/625000000 : ℝ)] ![(48232594314509/100000000000000 : ℝ), (21834775367083/50000000000000 : ℝ), (1619570986541/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5748166571/10000000000 : ℝ)|^133 ≤ (48232594314509/100000000000000 : ℝ)^101
        have hw : |(5748166571/10000000000 : ℝ)|=(5748166571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(333144219/625000000 : ℝ)|^133 ≤ (21834775367083/50000000000000 : ℝ)^101
        have hw : |(333144219/625000000 : ℝ)|=(333144219/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-92661181/625000000 : ℝ)|^133 ≤ (1619570986541/20000000000000 : ℝ)^101
        have hw : |(-92661181/625000000 : ℝ)|=(92661181/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304055_s7_s7_20 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3486261397/5000000000 : ℝ)*x 0 + (744485679/2000000000 : ℝ)*x 1 + (1817005243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3486261397/5000000000 : ℝ)^133 ≤ (62197211547107/100000000000000 : ℝ)^101 := by
    have hnat : (3486261397 : ℕ)^133*100000000000000^101 ≤ 62197211547107^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3486261397 5000000000 62197211547107 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (744485679/2000000000 : ℝ)^133 ≤ (27217644871751/100000000000000 : ℝ)^101 := by
    have hnat : (744485679 : ℕ)^133*100000000000000^101 ≤ 27217644871751^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      744485679 2000000000 27217644871751 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1817005243/10000000000 : ℝ)^133 ≤ (2117028712159/20000000000000 : ℝ)^101 := by
    have hnat : (1817005243 : ℕ)^133*20000000000000^101 ≤ 2117028712159^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1817005243 10000000000 2117028712159 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3486261397/5000000000 : ℝ), (744485679/2000000000 : ℝ), (1817005243/10000000000 : ℝ)] ![(62197211547107/100000000000000 : ℝ), (27217644871751/100000000000000 : ℝ), (2117028712159/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3486261397/5000000000 : ℝ)|^133 ≤ (62197211547107/100000000000000 : ℝ)^101
        have hw : |(3486261397/5000000000 : ℝ)|=(3486261397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(744485679/2000000000 : ℝ)|^133 ≤ (27217644871751/100000000000000 : ℝ)^101
        have hw : |(744485679/2000000000 : ℝ)|=(744485679/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1817005243/10000000000 : ℝ)|^133 ≤ (2117028712159/20000000000000 : ℝ)^101
        have hw : |(1817005243/10000000000 : ℝ)|=(1817005243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304055_s7_s7_21 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-353542087/2500000000 : ℝ)*x 0 + (1557996789/2500000000 : ℝ)*x 1 + (304191021/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (353542087/2500000000 : ℝ)^133 ≤ (951180554709/12500000000000 : ℝ)^101 := by
    have hnat : (353542087 : ℕ)^133*12500000000000^101 ≤ 951180554709^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      353542087 2500000000 951180554709 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1557996789/2500000000 : ℝ)^133 ≤ (53648518520541/100000000000000 : ℝ)^101 := by
    have hnat : (1557996789 : ℕ)^133*100000000000000^101 ≤ 53648518520541^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1557996789 2500000000 53648518520541 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (304191021/625000000 : ℝ)^133 ≤ (38742037026927/100000000000000 : ℝ)^101 := by
    have hnat : (304191021 : ℕ)^133*100000000000000^101 ≤ 38742037026927^101*625000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      304191021 625000000 38742037026927 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-353542087/2500000000 : ℝ), (1557996789/2500000000 : ℝ), (304191021/625000000 : ℝ)] ![(951180554709/12500000000000 : ℝ), (53648518520541/100000000000000 : ℝ), (38742037026927/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-353542087/2500000000 : ℝ)|^133 ≤ (951180554709/12500000000000 : ℝ)^101
        have hw : |(-353542087/2500000000 : ℝ)|=(353542087/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1557996789/2500000000 : ℝ)|^133 ≤ (53648518520541/100000000000000 : ℝ)^101
        have hw : |(1557996789/2500000000 : ℝ)|=(1557996789/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(304191021/625000000 : ℝ)|^133 ≤ (38742037026927/100000000000000 : ℝ)^101
        have hw : |(304191021/625000000 : ℝ)|=(304191021/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304055_s7_s7_22 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1160207883/2000000000 : ℝ)*x 0 + (-808354011/10000000000 : ℝ)*x 1 + (2842644493/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1160207883/2000000000 : ℝ)^133 ≤ (48817660860413/100000000000000 : ℝ)^101 := by
    have hnat : (1160207883 : ℕ)^133*100000000000000^101 ≤ 48817660860413^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1160207883 2000000000 48817660860413 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (808354011/10000000000 : ℝ)^133 ≤ (3643302007321/100000000000000 : ℝ)^101 := by
    have hnat : (808354011 : ℕ)^133*100000000000000^101 ≤ 3643302007321^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      808354011 10000000000 3643302007321 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2842644493/5000000000 : ℝ)^133 ≤ (11884759278917/25000000000000 : ℝ)^101 := by
    have hnat : (2842644493 : ℕ)^133*25000000000000^101 ≤ 11884759278917^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2842644493 5000000000 11884759278917 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1160207883/2000000000 : ℝ), (-808354011/10000000000 : ℝ), (2842644493/5000000000 : ℝ)] ![(48817660860413/100000000000000 : ℝ), (3643302007321/100000000000000 : ℝ), (11884759278917/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1160207883/2000000000 : ℝ)|^133 ≤ (48817660860413/100000000000000 : ℝ)^101
        have hw : |(1160207883/2000000000 : ℝ)|=(1160207883/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-808354011/10000000000 : ℝ)|^133 ≤ (3643302007321/100000000000000 : ℝ)^101
        have hw : |(-808354011/10000000000 : ℝ)|=(808354011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2842644493/5000000000 : ℝ)|^133 ≤ (11884759278917/25000000000000 : ℝ)^101
        have hw : |(2842644493/5000000000 : ℝ)|=(2842644493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304055_s7_s7_23 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1059951189/2500000000 : ℝ)*x 0 + (800765111/1250000000 : ℝ)*x 1 + (-200662187/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059951189/2500000000 : ℝ)^133 ≤ (32305555896407/100000000000000 : ℝ)^101 := by
    have hnat : (1059951189 : ℕ)^133*100000000000000^101 ≤ 32305555896407^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059951189 2500000000 32305555896407 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (800765111/1250000000 : ℝ)^133 ≤ (55631188632323/100000000000000 : ℝ)^101 := by
    have hnat : (800765111 : ℕ)^133*100000000000000^101 ≤ 55631188632323^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      800765111 1250000000 55631188632323 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (200662187/1000000000 : ℝ)^133 ≤ (12063255454519/100000000000000 : ℝ)^101 := by
    have hnat : (200662187 : ℕ)^133*100000000000000^101 ≤ 12063255454519^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200662187 1000000000 12063255454519 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1059951189/2500000000 : ℝ), (800765111/1250000000 : ℝ), (-200662187/1000000000 : ℝ)] ![(32305555896407/100000000000000 : ℝ), (55631188632323/100000000000000 : ℝ), (12063255454519/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1059951189/2500000000 : ℝ)|^133 ≤ (32305555896407/100000000000000 : ℝ)^101
        have hw : |(1059951189/2500000000 : ℝ)|=(1059951189/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(800765111/1250000000 : ℝ)|^133 ≤ (55631188632323/100000000000000 : ℝ)^101
        have hw : |(800765111/1250000000 : ℝ)|=(800765111/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-200662187/1000000000 : ℝ)|^133 ≤ (12063255454519/100000000000000 : ℝ)^101
        have hw : |(-200662187/1000000000 : ℝ)|=(200662187/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304055_s7_s7_27 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1760329829/2500000000 : ℝ)*x 0 + (2991826211/10000000000 : ℝ)*x 1 + (510977133/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1760329829/2500000000 : ℝ)^133 ≤ (63006595338843/100000000000000 : ℝ)^101 := by
    have hnat : (1760329829 : ℕ)^133*100000000000000^101 ≤ 63006595338843^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1760329829 2500000000 63006595338843 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2991826211/10000000000 : ℝ)^133 ≤ (5103127357183/25000000000000 : ℝ)^101 := by
    have hnat : (2991826211 : ℕ)^133*25000000000000^101 ≤ 5103127357183^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2991826211 10000000000 5103127357183 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (510977133/2000000000 : ℝ)^133 ≤ (663235808673/4000000000000 : ℝ)^101 := by
    have hnat : (510977133 : ℕ)^133*4000000000000^101 ≤ 663235808673^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      510977133 2000000000 663235808673 4000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1760329829/2500000000 : ℝ), (2991826211/10000000000 : ℝ), (510977133/2000000000 : ℝ)] ![(63006595338843/100000000000000 : ℝ), (5103127357183/25000000000000 : ℝ), (663235808673/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1760329829/2500000000 : ℝ)|^133 ≤ (63006595338843/100000000000000 : ℝ)^101
        have hw : |(1760329829/2500000000 : ℝ)|=(1760329829/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2991826211/10000000000 : ℝ)|^133 ≤ (5103127357183/25000000000000 : ℝ)^101
        have hw : |(2991826211/10000000000 : ℝ)|=(2991826211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(510977133/2000000000 : ℝ)|^133 ≤ (663235808673/4000000000000 : ℝ)^101
        have hw : |(510977133/2000000000 : ℝ)|=(510977133/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c304055_s7 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev6 : (0 : ℝ) ≤ ((13061/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(13061/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13279/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(13279/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(54167/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(54167/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((7001/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7001/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(35929/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(35929/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(35643/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(35643/100000 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76617/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76617/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
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
  rcases hprev6 with ⟨ratio_s6_0,ratio_s6_1,ratio_s6_2⟩
  have s7_pow0 : (13061/25000 : ℝ) ^ (33/8 : ℝ) ≤ (3434553138586296129/50000000000000000000 : ℝ) := by
    have hpowers : (13061/25000 : ℝ)^33 ≤ (3434553138586296129/50000000000000000000 : ℝ)^8 := by
      have hnat : (13061 : ℕ)^33*50000000000000000000^8 ≤ 3434553138586296129^8*25000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13061 25000 3434553138586296129 50000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13061/25000 : ℝ)) (X := (3434553138586296129/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s7_corner0a : (53434553138586296129/50000000000000000000 : ℝ) ≤ (10162357463743379/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (53434553138586296129/50000000000000000000 : ℝ)^8 ≤ (10162357463743379/10000000000000000 : ℝ)^33 := by
      have hnat : (53434553138586296129 : ℕ)^8*10000000000000000^33 ≤ 10162357463743379^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        53434553138586296129 50000000000000000000 10162357463743379 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10162357463743379/10000000000000000 : ℝ)) (X := (53434553138586296129/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s7_corner0b : (28434553138586296129/25000000000000000000 : ℝ) ≤ (5158495674603029/5000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (28434553138586296129/25000000000000000000 : ℝ)^8 ≤ (5158495674603029/5000000000000000 : ℝ)^33 := by
      have hnat : (28434553138586296129 : ℕ)^8*5000000000000000^33 ≤ 5158495674603029^33*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28434553138586296129 25000000000000000000 5158495674603029 5000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5158495674603029/5000000000000000 : ℝ)) (X := (28434553138586296129/25000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s7_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(162357463743379/5224400000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(154633885462679/5224400000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (13061/25000 : ℝ)) (alpha := (162357463743379/5224400000000000 : ℝ)) (beta := (154633885462679/5224400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s7_pow0,s7_corner0a]) (by linarith only [s7_pow0,s7_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (13061/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s6_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(162357463743379/5224400000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(154633885462679/5224400000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s7_pow1 : (13279/25000 : ℝ) ^ (33/8 : ℝ) ≤ (7354524841066606427/100000000000000000000 : ℝ) := by
    have hpowers : (13279/25000 : ℝ)^33 ≤ (7354524841066606427/100000000000000000000 : ℝ)^8 := by
      have hnat : (13279 : ℕ)^33*100000000000000000000^8 ≤ 7354524841066606427^8*25000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13279 25000 7354524841066606427 100000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13279/25000 : ℝ)) (X := (7354524841066606427/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s7_corner1a : (107354524841066606427/100000000000000000000 : ℝ) ≤ (1271691047662731/1250000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (107354524841066606427/100000000000000000000 : ℝ)^8 ≤ (1271691047662731/1250000000000000 : ℝ)^33 := by
      have hnat : (107354524841066606427 : ℕ)^8*1250000000000000^33 ≤ 1271691047662731^33*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        107354524841066606427 100000000000000000000 1271691047662731 1250000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1271691047662731/1250000000000000 : ℝ)) (X := (107354524841066606427/100000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s7_corner1b : (57354524841066606427/50000000000000000000 : ℝ) ≤ (2584567813097157/2500000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (57354524841066606427/50000000000000000000 : ℝ)^8 ≤ (2584567813097157/2500000000000000 : ℝ)^33 := by
      have hnat : (57354524841066606427 : ℕ)^8*2500000000000000^33 ≤ 2584567813097157^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        57354524841066606427 50000000000000000000 2584567813097157 2500000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2584567813097157/2500000000000000 : ℝ)) (X := (57354524841066606427/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s7_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(21691047662731/663950000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(1176734793477/37940000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (13279/25000 : ℝ)) (alpha := (21691047662731/663950000000000 : ℝ)) (beta := (1176734793477/37940000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s7_pow1,s7_corner1a]) (by linarith only [s7_pow1,s7_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (13279/25000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s6_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(21691047662731/663950000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(1176734793477/37940000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s7_pow2 : (54167/100000 : ℝ) ^ (33/8 : ℝ) ≤ (7973628188303192907/100000000000000000000 : ℝ) := by
    have hpowers : (54167/100000 : ℝ)^33 ≤ (7973628188303192907/100000000000000000000 : ℝ)^8 := by
      have hnat : (54167 : ℕ)^33*100000000000000000000^8 ≤ 7973628188303192907^8*100000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        54167 100000 7973628188303192907 100000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (54167/100000 : ℝ)) (X := (7973628188303192907/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s7_corner2a : (107973628188303192907/100000000000000000000 : ℝ) ≤ (10187720391691859/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (107973628188303192907/100000000000000000000 : ℝ)^8 ≤ (10187720391691859/10000000000000000 : ℝ)^33 := by
      have hnat : (107973628188303192907 : ℕ)^8*10000000000000000^33 ≤ 10187720391691859^33*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        107973628188303192907 100000000000000000000 10187720391691859 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10187720391691859/10000000000000000 : ℝ)) (X := (107973628188303192907/100000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s7_corner2b : (57973628188303192907/50000000000000000000 : ℝ) ≤ (518260729094931/500000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (57973628188303192907/50000000000000000000 : ℝ)^8 ≤ (518260729094931/500000000000000 : ℝ)^33 := by
      have hnat : (57973628188303192907 : ℕ)^8*500000000000000^33 ≤ 518260729094931^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        57973628188303192907 50000000000000000000 518260729094931 500000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (518260729094931/500000000000000 : ℝ)) (X := (57973628188303192907/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s7_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(187720391691859/5416700000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(177494190206761/5416700000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (54167/100000 : ℝ)) (alpha := (187720391691859/5416700000000000 : ℝ)) (beta := (177494190206761/5416700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s7_pow2,s7_corner2a]) (by linarith only [s7_pow2,s7_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (54167/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s6_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(187720391691859/5416700000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(177494190206761/5416700000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s7_0 : ((-11832487/50000000 : ℝ)*X 0 0+(5640739871/10000000000 : ℝ)*X 0 1+(4792346711/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304055_s7_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_1 : ((191908549/400000000 : ℝ)*X 1 0+(-76763413/500000000 : ℝ)*X 1 1+(6219254559/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304055_s7_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_2 : ((4783004183/10000000000 : ℝ)*X 2 0+(2814107539/5000000000 : ℝ)*X 2 1+(-2394610831/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304055_s7_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_6 : ((733440473/1250000000 : ℝ)*X 0 0+(4112444187/10000000000 : ℝ)*X 0 1+(287962351/1000000000 : ℝ)*X 0 2+(733440473/1250000000 : ℝ)*X 1 0+(4112444187/10000000000 : ℝ)*X 1 1+(287962351/1000000000 : ℝ)*X 1 2+(733440473/1250000000 : ℝ)*X 2 0+(4112444187/10000000000 : ℝ)*X 2 1+(287962351/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304055_s7_s7_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_7 : ((-2101721753/10000000000 : ℝ)*X 0 0+(2482945211/5000000000 : ℝ)*X 0 1+(5672381383/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304055_s7_s7_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_8 : ((922757567/2000000000 : ℝ)*X 1 0+(-833659851/10000000000 : ℝ)*X 1 1+(6792937183/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304055_s7_s7_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_9 : ((2299486867/5000000000 : ℝ)*X 2 0+(398800919/625000000 : ℝ)*X 2 1+(-1565734367/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304055_s7_s7_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_13 : ((5294865031/10000000000 : ℝ)*X 0 0+(1391589661/2500000000 : ℝ)*X 0 1+(450773699/2500000000 : ℝ)*X 0 2+(5294865031/10000000000 : ℝ)*X 1 0+(1391589661/2500000000 : ℝ)*X 1 1+(450773699/2500000000 : ℝ)*X 1 2+(5294865031/10000000000 : ℝ)*X 2 0+(1391589661/2500000000 : ℝ)*X 2 1+(450773699/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304055_s7_s7_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_14 : ((-726113389/5000000000 : ℝ)*X 0 0+(166966297/312500000 : ℝ)*X 0 1+(2877768767/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304055_s7_s7_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_15 : ((4288451489/10000000000 : ℝ)*X 1 0+(-338598891/2500000000 : ℝ)*X 1 1+(3393048311/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304055_s7_s7_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_16 : ((5748166571/10000000000 : ℝ)*X 2 0+(333144219/625000000 : ℝ)*X 2 1+(-92661181/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304055_s7_s7_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_20 : ((3486261397/5000000000 : ℝ)*X 0 0+(744485679/2000000000 : ℝ)*X 0 1+(1817005243/10000000000 : ℝ)*X 0 2+(3486261397/5000000000 : ℝ)*X 1 0+(744485679/2000000000 : ℝ)*X 1 1+(1817005243/10000000000 : ℝ)*X 1 2+(3486261397/5000000000 : ℝ)*X 2 0+(744485679/2000000000 : ℝ)*X 2 1+(1817005243/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304055_s7_s7_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_21 : ((-353542087/2500000000 : ℝ)*X 0 0+(1557996789/2500000000 : ℝ)*X 0 1+(304191021/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304055_s7_s7_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_22 : ((1160207883/2000000000 : ℝ)*X 1 0+(-808354011/10000000000 : ℝ)*X 1 1+(2842644493/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304055_s7_s7_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_23 : ((1059951189/2500000000 : ℝ)*X 2 0+(800765111/1250000000 : ℝ)*X 2 1+(-200662187/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304055_s7_s7_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_27 : ((1760329829/2500000000 : ℝ)*X 0 0+(2991826211/10000000000 : ℝ)*X 0 1+(510977133/2000000000 : ℝ)*X 0 2+(1760329829/2500000000 : ℝ)*X 1 0+(2991826211/10000000000 : ℝ)*X 1 1+(510977133/2000000000 : ℝ)*X 1 2+(1760329829/2500000000 : ℝ)*X 2 0+(2991826211/10000000000 : ℝ)*X 2 1+(510977133/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304055_s7_s7_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s7_0 : (0 : ℝ) ≤ ((7001/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7001/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1829429617084874734584260121/141495037400000000000000000000000 : ℝ) := by norm_num
    linear_combination (29265880691/62500000000 : ℝ)*(base49) + (573739/250000000000 : ℝ)*(base60) + (5225030275803/1000000000000 : ℝ)*(major_s7_0) + (5225030275803/1000000000000 : ℝ)*(major_s7_1) + (5225030275803/1000000000000 : ℝ)*(major_s7_2) + (43973493/1000000000000 : ℝ)*(sp_s7_0) + (27462893/1000000000000 : ℝ)*(sp_s7_6) + (1401008385943/200000000000 : ℝ)*(sp_s7_7) + (7005001944027/1000000000000 : ℝ)*(sp_s7_8) + (7004938918553/1000000000000 : ℝ)*(sp_s7_9) + (3444926302999/1000000000000 : ℝ)*(sp_s7_13) + (16572737/1000000000000 : ℝ)*(sp_s7_14) + (100531919/1000000000000 : ℝ)*(sp_s7_15) + (10222337/62500000000 : ℝ)*(sp_s7_23) + (3444953765891/1000000000000 : ℝ)*(f.failure) + (1401020495189/200000000000 : ℝ)*(f.sum) + (5615964631146855711/14385671860000000000000000000000 : ℝ)*base62 + (1179350903664323/5416700000000000000000000000 : ℝ)*base65 + (23445369608329/37940000000000000000000000 : ℝ)*base67 + (1233694021300613/5416700000000000000000000000 : ℝ)*base68 + (83480734698937571389/282990074800000000000000000000000 : ℝ)*base70 + (1084805471614683/5224400000000000000000000000 : ℝ)*base72 + (27174608336417/165987500000000000000000000 : ℝ)*base75 + (1563470046196137/5224400000000000000000000000 : ℝ)*base77 + (133771174483757471/9910686800000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (10031/12500000000000000 : ℝ)*base86 + (10031/12500000000000000 : ℝ)*base88 + (10031/12500000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s7_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(35929/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(35929/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (206070365052268036147210629/17686879675000000000000000000000 : ℝ) := by norm_num
    linear_combination (2897433/1000000000000 : ℝ)*(base39) + (196144487331/500000000000 : ℝ)*(base49) + (293267/250000000000 : ℝ)*(base60) + (5058495943441/1000000000000 : ℝ)*(major_s7_0) + (5058495943441/1000000000000 : ℝ)*(major_s7_1) + (5058495943441/1000000000000 : ℝ)*(major_s7_2) + (2601621/500000000000 : ℝ)*(sp_s7_1) + (239827/10000000000 : ℝ)*(sp_s7_7) + (70949867/1000000000000 : ℝ)*(sp_s7_8) + (6781809250049/1000000000000 : ℝ)*(sp_s7_14) + (6781757079639/1000000000000 : ℝ)*(sp_s7_15) + (1695458308187/250000000000 : ℝ)*(sp_s7_16) + (66701591537/20000000000 : ℝ)*(sp_s7_20) + (75193603/1000000000000 : ℝ)*(sp_s7_27) + (3335154770453/1000000000000 : ℝ)*(f.failure) + (1695458308187/250000000000 : ℝ)*(f.sum) + (1745052485648021847/14385671860000000000000000000000 : ℝ)*base63 + (4126654260777329/5416700000000000000000000000 : ℝ)*base64 + (18513330783291/37940000000000000000000000 : ℝ)*base66 + (296540670107561/5416700000000000000000000000 : ℝ)*base68 + (64451985763449385143/282990074800000000000000000000000 : ℝ)*base70 + (2244068075039959/5224400000000000000000000000 : ℝ)*base73 + (94187835113249/663950000000000000000000000 : ℝ)*base74 + (480765825711861/5224400000000000000000000000 : ℝ)*base76 + (5494005038972618083/9910686800000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (5927/12500000000000000 : ℝ)*base87 + (5927/12500000000000000 : ℝ)*base89 + (5927/12500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s7_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(35643/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(35643/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (39132423193074759/10000000000000000000000 : ℝ) := by norm_num
    linear_combination (12076321093/100000000000 : ℝ)*(base40) + (357516079973/1000000000000 : ℝ)*(base49) + (1766661/1000000000000 : ℝ)*(base59) + (120583260373/25000000000 : ℝ)*(major_s7_0) + (120583260373/25000000000 : ℝ)*(major_s7_1) + (120583260373/25000000000 : ℝ)*(major_s7_2) + (10031771/1000000000000 : ℝ)*(sp_s7_0) + (10309781/1000000000000 : ℝ)*(sp_s7_2) + (7951637/1000000000000 : ℝ)*(sp_s7_9) + (4332561/100000000000 : ℝ)*(sp_s7_20) + (1293308693113/200000000000 : ℝ)*(sp_s7_21) + (808319187167/125000000000 : ℝ)*(sp_s7_22) + (3233267617959/500000000000 : ℝ)*(sp_s7_23) + (3180062702477/1000000000000 : ℝ)*(sp_s7_27) + (3180106028087/1000000000000 : ℝ)*(f.failure) + (808319187167/125000000000 : ℝ)*(f.sum) + (104262997871460643/899104491250000000000000000000 : ℝ)*base63 + (98781997423007/270835000000000000000000000 : ℝ)*base64 + (267416483363/4742500000000000000000000 : ℝ)*base66 + (50039613746469/135417500000000000000000000 : ℝ)*base68 + (429719192542584467/3537375935000000000000000000000 : ℝ)*base71 + (14642911848581/32652500000000000000000000 : ℝ)*base72 + (9138956099643/26558000000000000000000000 : ℝ)*base74 + (156312551659/326525000000000000000000 : ℝ)*base76 + (59410404586316317/123883585000000000000000000000 : ℝ)*base79 + (1433/12500000000000000 : ℝ)*base87 + (1433/12500000000000000 : ℝ)*base89 + (1433/12500000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s7_0,ratio_s7_1,ratio_s7_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev6 : (0 : ℝ) ≤ ((13061/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(13061/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13279/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(13279/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(54167/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(54167/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((7001/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7001/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(35929/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(35929/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(35643/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(35643/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c304055_s7 p hpa hpb X hX hprev6

#print axioms solution
