-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c318023_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:22:40.025186+00:00
-- url     : https://prove2.me/submissions/0ef04e86-599a-4292-a7e2-82b68fdc329a

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
theorem collision_support_c318023_s1_s1_0 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-418185817/1250000000 : ℝ)*x 0 + (431087/800000 : ℝ)*x 1 + (3651846589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (418185817/1250000000 : ℝ)^5 ≤ (12721669605447/50000000000000 : ℝ)^4 := by
    have hnat : (418185817 : ℕ)^5*50000000000000^4 ≤ 12721669605447^4*1250000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      418185817 1250000000 12721669605447 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (431087/800000 : ℝ)^5 ≤ (46168277763547/100000000000000 : ℝ)^4 := by
    have hnat : (431087 : ℕ)^5*100000000000000^4 ≤ 46168277763547^4*800000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431087 800000 46168277763547 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3651846589/10000000000 : ℝ)^5 ≤ (1419419150893/5000000000000 : ℝ)^4 := by
    have hnat : (3651846589 : ℕ)^5*5000000000000^4 ≤ 1419419150893^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3651846589 10000000000 1419419150893 5000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-418185817/1250000000 : ℝ), (431087/800000 : ℝ), (3651846589/10000000000 : ℝ)] ![(12721669605447/50000000000000 : ℝ), (46168277763547/100000000000000 : ℝ), (1419419150893/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-418185817/1250000000 : ℝ)|^5 ≤ (12721669605447/50000000000000 : ℝ)^4
        have hw : |(-418185817/1250000000 : ℝ)|=(418185817/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(431087/800000 : ℝ)|^5 ≤ (46168277763547/100000000000000 : ℝ)^4
        have hw : |(431087/800000 : ℝ)|=(431087/800000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3651846589/10000000000 : ℝ)|^5 ≤ (1419419150893/5000000000000 : ℝ)^4
        have hw : |(3651846589/10000000000 : ℝ)|=(3651846589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318023_s1_s1_1 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (5794587009/10000000000 : ℝ)*x 0 + (-759092947/10000000000 : ℝ)*x 1 + (5322250049/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5794587009/10000000000 : ℝ)^5 ≤ (3159789327437/6250000000000 : ℝ)^4 := by
    have hnat : (5794587009 : ℕ)^5*6250000000000^4 ≤ 3159789327437^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5794587009 10000000000 3159789327437 6250000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (759092947/10000000000 : ℝ)^5 ≤ (1992226440397/50000000000000 : ℝ)^4 := by
    have hnat : (759092947 : ℕ)^5*50000000000000^4 ≤ 1992226440397^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      759092947 10000000000 1992226440397 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5322250049/10000000000 : ℝ)^5 ≤ (4545891786811/10000000000000 : ℝ)^4 := by
    have hnat : (5322250049 : ℕ)^5*10000000000000^4 ≤ 4545891786811^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5322250049 10000000000 4545891786811 10000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5794587009/10000000000 : ℝ), (-759092947/10000000000 : ℝ), (5322250049/10000000000 : ℝ)] ![(3159789327437/6250000000000 : ℝ), (1992226440397/50000000000000 : ℝ), (4545891786811/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5794587009/10000000000 : ℝ)|^5 ≤ (3159789327437/6250000000000 : ℝ)^4
        have hw : |(5794587009/10000000000 : ℝ)|=(5794587009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-759092947/10000000000 : ℝ)|^5 ≤ (1992226440397/50000000000000 : ℝ)^4
        have hw : |(-759092947/10000000000 : ℝ)|=(759092947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5322250049/10000000000 : ℝ)|^5 ≤ (4545891786811/10000000000000 : ℝ)^4
        have hw : |(5322250049/10000000000 : ℝ)|=(5322250049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318023_s1_s1_2 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (3135269887/10000000000 : ℝ)*x 0 + (1444200413/2500000000 : ℝ)*x 1 + (-342237953/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3135269887/10000000000 : ℝ)^5 ≤ (1466302859179/6250000000000 : ℝ)^4 := by
    have hnat : (3135269887 : ℕ)^5*6250000000000^4 ≤ 1466302859179^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3135269887 10000000000 1466302859179 6250000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1444200413/2500000000 : ℝ)^5 ≤ (3147671034217/6250000000000 : ℝ)^4 := by
    have hnat : (1444200413 : ℕ)^5*6250000000000^4 ≤ 3147671034217^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1444200413 2500000000 3147671034217 6250000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (342237953/1000000000 : ℝ)^5 ≤ (3272052211743/12500000000000 : ℝ)^4 := by
    have hnat : (342237953 : ℕ)^5*12500000000000^4 ≤ 3272052211743^4*1000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      342237953 1000000000 3272052211743 12500000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3135269887/10000000000 : ℝ), (1444200413/2500000000 : ℝ), (-342237953/1000000000 : ℝ)] ![(1466302859179/6250000000000 : ℝ), (3147671034217/6250000000000 : ℝ), (3272052211743/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3135269887/10000000000 : ℝ)|^5 ≤ (1466302859179/6250000000000 : ℝ)^4
        have hw : |(3135269887/10000000000 : ℝ)|=(3135269887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1444200413/2500000000 : ℝ)|^5 ≤ (3147671034217/6250000000000 : ℝ)^4
        have hw : |(1444200413/2500000000 : ℝ)|=(1444200413/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-342237953/1000000000 : ℝ)|^5 ≤ (3272052211743/12500000000000 : ℝ)^4
        have hw : |(-342237953/1000000000 : ℝ)|=(342237953/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318023_s1_s1_6 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (3940980977/10000000000 : ℝ)*x 0 + (4871458399/10000000000 : ℝ)*x 1 + (1809868949/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3940980977/10000000000 : ℝ)^5 ≤ (31225213979447/100000000000000 : ℝ)^4 := by
    have hnat : (3940980977 : ℕ)^5*100000000000000^4 ≤ 31225213979447^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3940980977 10000000000 31225213979447 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4871458399/10000000000 : ℝ)^5 ≤ (10174515936079/25000000000000 : ℝ)^4 := by
    have hnat : (4871458399 : ℕ)^5*25000000000000^4 ≤ 10174515936079^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4871458399 10000000000 10174515936079 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1809868949/5000000000 : ℝ)^5 ≤ (438698785409/1562500000000 : ℝ)^4 := by
    have hnat : (1809868949 : ℕ)^5*1562500000000^4 ≤ 438698785409^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1809868949 5000000000 438698785409 1562500000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3940980977/10000000000 : ℝ), (4871458399/10000000000 : ℝ), (1809868949/5000000000 : ℝ)] ![(31225213979447/100000000000000 : ℝ), (10174515936079/25000000000000 : ℝ), (438698785409/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3940980977/10000000000 : ℝ)|^5 ≤ (31225213979447/100000000000000 : ℝ)^4
        have hw : |(3940980977/10000000000 : ℝ)|=(3940980977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4871458399/10000000000 : ℝ)|^5 ≤ (10174515936079/25000000000000 : ℝ)^4
        have hw : |(4871458399/10000000000 : ℝ)|=(4871458399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1809868949/5000000000 : ℝ)|^5 ≤ (438698785409/1562500000000 : ℝ)^4
        have hw : |(1809868949/5000000000 : ℝ)|=(1809868949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318023_s1_s1_7 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-1698583857/5000000000 : ℝ)*x 0 + (5376853591/10000000000 : ℝ)*x 1 + (72281359/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1698583857/5000000000 : ℝ)^5 ≤ (25935596146277/100000000000000 : ℝ)^4 := by
    have hnat : (1698583857 : ℕ)^5*100000000000000^4 ≤ 25935596146277^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1698583857 5000000000 25935596146277 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5376853591/10000000000 : ℝ)^5 ≤ (4604264492539/10000000000000 : ℝ)^4 := by
    have hnat : (5376853591 : ℕ)^5*10000000000000^4 ≤ 4604264492539^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376853591 10000000000 4604264492539 10000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (72281359/200000000 : ℝ)^5 ≤ (1120870356147/4000000000000 : ℝ)^4 := by
    have hnat : (72281359 : ℕ)^5*4000000000000^4 ≤ 1120870356147^4*200000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      72281359 200000000 1120870356147 4000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1698583857/5000000000 : ℝ), (5376853591/10000000000 : ℝ), (72281359/200000000 : ℝ)] ![(25935596146277/100000000000000 : ℝ), (4604264492539/10000000000000 : ℝ), (1120870356147/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1698583857/5000000000 : ℝ)|^5 ≤ (25935596146277/100000000000000 : ℝ)^4
        have hw : |(-1698583857/5000000000 : ℝ)|=(1698583857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5376853591/10000000000 : ℝ)|^5 ≤ (4604264492539/10000000000000 : ℝ)^4
        have hw : |(5376853591/10000000000 : ℝ)|=(5376853591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(72281359/200000000 : ℝ)|^5 ≤ (1120870356147/4000000000000 : ℝ)^4
        have hw : |(72281359/200000000 : ℝ)|=(72281359/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318023_s1_s1_8 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (5723883511/10000000000 : ℝ)*x 0 + (-379217937/10000000000 : ℝ)*x 1 + (2804456299/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5723883511/10000000000 : ℝ)^5 ≤ (49786716319739/100000000000000 : ℝ)^4 := by
    have hnat : (5723883511 : ℕ)^5*100000000000000^4 ≤ 49786716319739^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5723883511 10000000000 49786716319739 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (379217937/10000000000 : ℝ)^5 ≤ (836721817643/50000000000000 : ℝ)^4 := by
    have hnat : (379217937 : ℕ)^5*50000000000000^4 ≤ 836721817643^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      379217937 10000000000 836721817643 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2804456299/5000000000 : ℝ)^5 ≤ (12134960007743/25000000000000 : ℝ)^4 := by
    have hnat : (2804456299 : ℕ)^5*25000000000000^4 ≤ 12134960007743^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2804456299 5000000000 12134960007743 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5723883511/10000000000 : ℝ), (-379217937/10000000000 : ℝ), (2804456299/5000000000 : ℝ)] ![(49786716319739/100000000000000 : ℝ), (836721817643/50000000000000 : ℝ), (12134960007743/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5723883511/10000000000 : ℝ)|^5 ≤ (49786716319739/100000000000000 : ℝ)^4
        have hw : |(5723883511/10000000000 : ℝ)|=(5723883511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-379217937/10000000000 : ℝ)|^5 ≤ (836721817643/50000000000000 : ℝ)^4
        have hw : |(-379217937/10000000000 : ℝ)|=(379217937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2804456299/5000000000 : ℝ)|^5 ≤ (12134960007743/25000000000000 : ℝ)^4
        have hw : |(2804456299/5000000000 : ℝ)|=(2804456299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318023_s1_s1_9 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (1479319097/5000000000 : ℝ)*x 0 + (154070139/250000000 : ℝ)*x 1 + (-3147539473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1479319097/5000000000 : ℝ)^5 ≤ (4364101269701/20000000000000 : ℝ)^4 := by
    have hnat : (1479319097 : ℕ)^5*20000000000000^4 ≤ 4364101269701^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1479319097 5000000000 4364101269701 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (154070139/250000000 : ℝ)^5 ≤ (27301913507273/50000000000000 : ℝ)^4 := by
    have hnat : (154070139 : ℕ)^5*50000000000000^4 ≤ 27301913507273^4*250000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      154070139 250000000 27301913507273 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3147539473/10000000000 : ℝ)^5 ≤ (23575666619157/100000000000000 : ℝ)^4 := by
    have hnat : (3147539473 : ℕ)^5*100000000000000^4 ≤ 23575666619157^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3147539473 10000000000 23575666619157 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1479319097/5000000000 : ℝ), (154070139/250000000 : ℝ), (-3147539473/10000000000 : ℝ)] ![(4364101269701/20000000000000 : ℝ), (27301913507273/50000000000000 : ℝ), (23575666619157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1479319097/5000000000 : ℝ)|^5 ≤ (4364101269701/20000000000000 : ℝ)^4
        have hw : |(1479319097/5000000000 : ℝ)|=(1479319097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(154070139/250000000 : ℝ)|^5 ≤ (27301913507273/50000000000000 : ℝ)^4
        have hw : |(154070139/250000000 : ℝ)|=(154070139/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3147539473/10000000000 : ℝ)|^5 ≤ (23575666619157/100000000000000 : ℝ)^4
        have hw : |(-3147539473/10000000000 : ℝ)|=(3147539473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318023_s1_s1_12 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (1897772927/5000000000 : ℝ)*x 0 + (122898349/250000000 : ℝ)*x 1 + (743861573/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1897772927/5000000000 : ℝ)^5 ≤ (14895764840029/50000000000000 : ℝ)^4 := by
    have hnat : (1897772927 : ℕ)^5*50000000000000^4 ≤ 14895764840029^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1897772927 5000000000 14895764840029 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (122898349/250000000 : ℝ)^5 ≤ (10290762580943/25000000000000 : ℝ)^4 := by
    have hnat : (122898349 : ℕ)^5*25000000000000^4 ≤ 10290762580943^4*250000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      122898349 250000000 10290762580943 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (743861573/2000000000 : ℝ)^5 ≤ (3630677498397/12500000000000 : ℝ)^4 := by
    have hnat : (743861573 : ℕ)^5*12500000000000^4 ≤ 3630677498397^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      743861573 2000000000 3630677498397 12500000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1897772927/5000000000 : ℝ), (122898349/250000000 : ℝ), (743861573/2000000000 : ℝ)] ![(14895764840029/50000000000000 : ℝ), (10290762580943/25000000000000 : ℝ), (3630677498397/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1897772927/5000000000 : ℝ)|^5 ≤ (14895764840029/50000000000000 : ℝ)^4
        have hw : |(1897772927/5000000000 : ℝ)|=(1897772927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(122898349/250000000 : ℝ)|^5 ≤ (10290762580943/25000000000000 : ℝ)^4
        have hw : |(122898349/250000000 : ℝ)|=(122898349/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(743861573/2000000000 : ℝ)|^5 ≤ (3630677498397/12500000000000 : ℝ)^4
        have hw : |(743861573/2000000000 : ℝ)|=(743861573/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318023_s1_s1_13 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-68318897/200000000 : ℝ)*x 0 + (5353369709/10000000000 : ℝ)*x 1 + (1810743137/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (68318897/200000000 : ℝ)^5 ≤ (13057455889689/50000000000000 : ℝ)^4 := by
    have hnat : (68318897 : ℕ)^5*50000000000000^4 ≤ 13057455889689^4*200000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68318897 200000000 13057455889689 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5353369709/10000000000 : ℝ)^5 ≤ (45791413172471/100000000000000 : ℝ)^4 := by
    have hnat : (5353369709 : ℕ)^5*100000000000000^4 ≤ 45791413172471^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353369709 10000000000 45791413172471 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1810743137/5000000000 : ℝ)^5 ≤ (14046837511799/50000000000000 : ℝ)^4 := by
    have hnat : (1810743137 : ℕ)^5*50000000000000^4 ≤ 14046837511799^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1810743137 5000000000 14046837511799 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-68318897/200000000 : ℝ), (5353369709/10000000000 : ℝ), (1810743137/5000000000 : ℝ)] ![(13057455889689/50000000000000 : ℝ), (45791413172471/100000000000000 : ℝ), (14046837511799/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-68318897/200000000 : ℝ)|^5 ≤ (13057455889689/50000000000000 : ℝ)^4
        have hw : |(-68318897/200000000 : ℝ)|=(68318897/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5353369709/10000000000 : ℝ)|^5 ≤ (45791413172471/100000000000000 : ℝ)^4
        have hw : |(5353369709/10000000000 : ℝ)|=(5353369709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1810743137/5000000000 : ℝ)|^5 ≤ (14046837511799/50000000000000 : ℝ)^4
        have hw : |(1810743137/5000000000 : ℝ)|=(1810743137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318023_s1_s1_14 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (2918744747/5000000000 : ℝ)*x 0 + (-9397123/125000000 : ℝ)*x 1 + (52828437/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2918744747/5000000000 : ℝ)^5 ≤ (51024956124263/100000000000000 : ℝ)^4 := by
    have hnat : (2918744747 : ℕ)^5*100000000000000^4 ≤ 51024956124263^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2918744747 5000000000 51024956124263 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9397123/125000000 : ℝ)^5 ≤ (1968231270157/50000000000000 : ℝ)^4 := by
    have hnat : (9397123 : ℕ)^5*50000000000000^4 ≤ 1968231270157^4*125000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9397123 125000000 1968231270157 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (52828437/100000000 : ℝ)^5 ≤ (2814911332461/6250000000000 : ℝ)^4 := by
    have hnat : (52828437 : ℕ)^5*6250000000000^4 ≤ 2814911332461^4*100000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52828437 100000000 2814911332461 6250000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2918744747/5000000000 : ℝ), (-9397123/125000000 : ℝ), (52828437/100000000 : ℝ)] ![(51024956124263/100000000000000 : ℝ), (1968231270157/50000000000000 : ℝ), (2814911332461/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2918744747/5000000000 : ℝ)|^5 ≤ (51024956124263/100000000000000 : ℝ)^4
        have hw : |(2918744747/5000000000 : ℝ)|=(2918744747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-9397123/125000000 : ℝ)|^5 ≤ (1968231270157/50000000000000 : ℝ)^4
        have hw : |(-9397123/125000000 : ℝ)|=(9397123/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(52828437/100000000 : ℝ)|^5 ≤ (2814911332461/6250000000000 : ℝ)^4
        have hw : |(52828437/100000000 : ℝ)|=(52828437/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318023_s1_s1_15 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (3070888393/10000000000 : ℝ)*x 0 + (2886253513/5000000000 : ℝ)*x 1 + (-3489932381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3070888393/10000000000 : ℝ)^5 ≤ (5715050204121/25000000000000 : ℝ)^4 := by
    have hnat : (3070888393 : ℕ)^5*25000000000000^4 ≤ 5715050204121^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3070888393 10000000000 5715050204121 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2886253513/5000000000 : ℝ)^5 ≤ (3144746229491/6250000000000 : ℝ)^4 := by
    have hnat : (2886253513 : ℕ)^5*6250000000000^4 ≤ 3144746229491^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2886253513 5000000000 3144746229491 6250000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3489932381/10000000000 : ℝ)^5 ≤ (26823859490231/100000000000000 : ℝ)^4 := by
    have hnat : (3489932381 : ℕ)^5*100000000000000^4 ≤ 26823859490231^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3489932381 10000000000 26823859490231 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3070888393/10000000000 : ℝ), (2886253513/5000000000 : ℝ), (-3489932381/10000000000 : ℝ)] ![(5715050204121/25000000000000 : ℝ), (3144746229491/6250000000000 : ℝ), (26823859490231/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3070888393/10000000000 : ℝ)|^5 ≤ (5715050204121/25000000000000 : ℝ)^4
        have hw : |(3070888393/10000000000 : ℝ)|=(3070888393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2886253513/5000000000 : ℝ)|^5 ≤ (3144746229491/6250000000000 : ℝ)^4
        have hw : |(2886253513/5000000000 : ℝ)|=(2886253513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3489932381/10000000000 : ℝ)|^5 ≤ (26823859490231/100000000000000 : ℝ)^4
        have hw : |(-3489932381/10000000000 : ℝ)|=(3489932381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318023_s1_s1_17 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-33/10000000000 : ℝ)*x 0 + (9999999999/10000000000 : ℝ)*x 1 + (0 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33/10000000000 : ℝ)^5 ≤ (1251/50000000000000 : ℝ)^4 := by
    have hnat : (33 : ℕ)^5*50000000000000^4 ≤ 1251^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33 10000000000 1251 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9999999999/10000000000 : ℝ)^5 ≤ (99999999987501/100000000000000 : ℝ)^4 := by
    have hnat : (9999999999 : ℕ)^5*100000000000000^4 ≤ 99999999987501^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9999999999 10000000000 99999999987501 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (0 : ℝ)^5 ≤ (0 : ℝ)^4 := by
    have hnat : (0 : ℕ)^5*1^4 ≤ 0^4*1^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-33/10000000000 : ℝ), (9999999999/10000000000 : ℝ), (0 : ℝ)] ![(1251/50000000000000 : ℝ), (99999999987501/100000000000000 : ℝ), (0 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-33/10000000000 : ℝ)|^5 ≤ (1251/50000000000000 : ℝ)^4
        have hw : |(-33/10000000000 : ℝ)|=(33/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(9999999999/10000000000 : ℝ)|^5 ≤ (99999999987501/100000000000000 : ℝ)^4
        have hw : |(9999999999/10000000000 : ℝ)|=(9999999999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(0 : ℝ)|^5 ≤ (0 : ℝ)^4
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318023_s1_s1_19 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (480213373/1250000000 : ℝ)*x 0 + (2465567937/5000000000 : ℝ)*x 1 + (365640193/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (480213373/1250000000 : ℝ)^5 ≤ (30245118918259/100000000000000 : ℝ)^4 := by
    have hnat : (480213373 : ℕ)^5*100000000000000^4 ≤ 30245118918259^4*1250000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      480213373 1250000000 30245118918259 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2465567937/5000000000 : ℝ)^5 ≤ (41322226294671/100000000000000 : ℝ)^4 := by
    have hnat : (2465567937 : ℕ)^5*100000000000000^4 ≤ 41322226294671^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2465567937 5000000000 41322226294671 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (365640193/1000000000 : ℝ)^5 ≤ (1421632738591/5000000000000 : ℝ)^4 := by
    have hnat : (365640193 : ℕ)^5*5000000000000^4 ≤ 1421632738591^4*1000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      365640193 1000000000 1421632738591 5000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(480213373/1250000000 : ℝ), (2465567937/5000000000 : ℝ), (365640193/1000000000 : ℝ)] ![(30245118918259/100000000000000 : ℝ), (41322226294671/100000000000000 : ℝ), (1421632738591/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(480213373/1250000000 : ℝ)|^5 ≤ (30245118918259/100000000000000 : ℝ)^4
        have hw : |(480213373/1250000000 : ℝ)|=(480213373/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2465567937/5000000000 : ℝ)|^5 ≤ (41322226294671/100000000000000 : ℝ)^4
        have hw : |(2465567937/5000000000 : ℝ)|=(2465567937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(365640193/1000000000 : ℝ)|^5 ≤ (1421632738591/5000000000000 : ℝ)^4
        have hw : |(365640193/1000000000 : ℝ)|=(365640193/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318023_s1_s1_20 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-3104671183/10000000000 : ℝ)*x 0 + (549457689/1000000000 : ℝ)*x 1 + (470965863/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3104671183/10000000000 : ℝ)^5 ≤ (23174987752531/100000000000000 : ℝ)^4 := by
    have hnat : (3104671183 : ℕ)^5*100000000000000^4 ≤ 23174987752531^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3104671183 10000000000 23174987752531 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (549457689/1000000000 : ℝ)^5 ≤ (47306173360217/100000000000000 : ℝ)^4 := by
    have hnat : (549457689 : ℕ)^5*100000000000000^4 ≤ 47306173360217^4*1000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549457689 1000000000 47306173360217 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (470965863/1250000000 : ℝ)^5 ≤ (7379709717017/25000000000000 : ℝ)^4 := by
    have hnat : (470965863 : ℕ)^5*25000000000000^4 ≤ 7379709717017^4*1250000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      470965863 1250000000 7379709717017 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3104671183/10000000000 : ℝ), (549457689/1000000000 : ℝ), (470965863/1250000000 : ℝ)] ![(23174987752531/100000000000000 : ℝ), (47306173360217/100000000000000 : ℝ), (7379709717017/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3104671183/10000000000 : ℝ)|^5 ≤ (23174987752531/100000000000000 : ℝ)^4
        have hw : |(-3104671183/10000000000 : ℝ)|=(3104671183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(549457689/1000000000 : ℝ)|^5 ≤ (47306173360217/100000000000000 : ℝ)^4
        have hw : |(549457689/1000000000 : ℝ)|=(549457689/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(470965863/1250000000 : ℝ)|^5 ≤ (7379709717017/25000000000000 : ℝ)^4
        have hw : |(470965863/1250000000 : ℝ)|=(470965863/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318023_s1_s1_21 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (6239058809/10000000000 : ℝ)*x 0 + (-452925977/10000000000 : ℝ)*x 1 + (5039543909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6239058809/10000000000 : ℝ)^5 ≤ (3465603443331/6250000000000 : ℝ)^4 := by
    have hnat : (6239058809 : ℕ)^5*6250000000000^4 ≤ 3465603443331^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6239058809 10000000000 3465603443331 6250000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (452925977/10000000000 : ℝ)^5 ≤ (2089459883133/100000000000000 : ℝ)^4 := by
    have hnat : (452925977 : ℕ)^5*100000000000000^4 ≤ 2089459883133^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      452925977 10000000000 2089459883133 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5039543909/10000000000 : ℝ)^5 ≤ (8492177001861/20000000000000 : ℝ)^4 := by
    have hnat : (5039543909 : ℕ)^5*20000000000000^4 ≤ 8492177001861^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5039543909 10000000000 8492177001861 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6239058809/10000000000 : ℝ), (-452925977/10000000000 : ℝ), (5039543909/10000000000 : ℝ)] ![(3465603443331/6250000000000 : ℝ), (2089459883133/100000000000000 : ℝ), (8492177001861/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6239058809/10000000000 : ℝ)|^5 ≤ (3465603443331/6250000000000 : ℝ)^4
        have hw : |(6239058809/10000000000 : ℝ)|=(6239058809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-452925977/10000000000 : ℝ)|^5 ≤ (2089459883133/100000000000000 : ℝ)^4
        have hw : |(-452925977/10000000000 : ℝ)|=(452925977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5039543909/10000000000 : ℝ)|^5 ≤ (8492177001861/20000000000000 : ℝ)^4
        have hw : |(5039543909/10000000000 : ℝ)|=(5039543909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318023_s1_s1_22 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (139757871/500000000 : ℝ)*x 0 + (6089097413/10000000000 : ℝ)*x 1 + (-3392111173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (139757871/500000000 : ℝ)^5 ≤ (2540492123941/12500000000000 : ℝ)^4 := by
    have hnat : (139757871 : ℕ)^5*12500000000000^4 ≤ 2540492123941^4*500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      139757871 500000000 2540492123941 12500000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6089097413/10000000000 : ℝ)^5 ≤ (26894356459441/50000000000000 : ℝ)^4 := by
    have hnat : (6089097413 : ℕ)^5*50000000000000^4 ≤ 26894356459441^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6089097413 10000000000 26894356459441 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3392111173/10000000000 : ℝ)^5 ≤ (25887350075263/100000000000000 : ℝ)^4 := by
    have hnat : (3392111173 : ℕ)^5*100000000000000^4 ≤ 25887350075263^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3392111173 10000000000 25887350075263 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(139757871/500000000 : ℝ), (6089097413/10000000000 : ℝ), (-3392111173/10000000000 : ℝ)] ![(2540492123941/12500000000000 : ℝ), (26894356459441/50000000000000 : ℝ), (25887350075263/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(139757871/500000000 : ℝ)|^5 ≤ (2540492123941/12500000000000 : ℝ)^4
        have hw : |(139757871/500000000 : ℝ)|=(139757871/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6089097413/10000000000 : ℝ)|^5 ≤ (26894356459441/50000000000000 : ℝ)^4
        have hw : |(6089097413/10000000000 : ℝ)|=(6089097413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3392111173/10000000000 : ℝ)|^5 ≤ (25887350075263/100000000000000 : ℝ)^4
        have hw : |(-3392111173/10000000000 : ℝ)|=(3392111173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318023_s1_s1_25 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (2166508957/5000000000 : ℝ)*x 0 + (2302013627/5000000000 : ℝ)*x 1 + (874989109/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2166508957/5000000000 : ℝ)^5 ≤ (35155081223207/100000000000000 : ℝ)^4 := by
    have hnat : (2166508957 : ℕ)^5*100000000000000^4 ≤ 35155081223207^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2166508957 5000000000 35155081223207 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2302013627/5000000000 : ℝ)^5 ≤ (18962358874157/50000000000000 : ℝ)^4 := by
    have hnat : (2302013627 : ℕ)^5*50000000000000^4 ≤ 18962358874157^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2302013627 5000000000 18962358874157 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (874989109/2500000000 : ℝ)^5 ≤ (6730050252559/25000000000000 : ℝ)^4 := by
    have hnat : (874989109 : ℕ)^5*25000000000000^4 ≤ 6730050252559^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      874989109 2500000000 6730050252559 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2166508957/5000000000 : ℝ), (2302013627/5000000000 : ℝ), (874989109/2500000000 : ℝ)] ![(35155081223207/100000000000000 : ℝ), (18962358874157/50000000000000 : ℝ), (6730050252559/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2166508957/5000000000 : ℝ)|^5 ≤ (35155081223207/100000000000000 : ℝ)^4
        have hw : |(2166508957/5000000000 : ℝ)|=(2166508957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2302013627/5000000000 : ℝ)|^5 ≤ (18962358874157/50000000000000 : ℝ)^4
        have hw : |(2302013627/5000000000 : ℝ)|=(2302013627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(874989109/2500000000 : ℝ)|^5 ≤ (6730050252559/25000000000000 : ℝ)^4
        have hw : |(874989109/2500000000 : ℝ)|=(874989109/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c318023_s1 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((2093/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2093/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(18093/50000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(18093/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(36893/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(36893/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((3657/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3657/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(759/100000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(759/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2163/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(2163/10000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (39911/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (39911/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (39911/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (39911/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (39911/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (39911/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (2093/3125 : ℝ) ^ (39/8 : ℝ) ≤ (7084776214092618659/50000000000000000000 : ℝ) := by
    have hpowers : (2093/3125 : ℝ)^39 ≤ (7084776214092618659/50000000000000000000 : ℝ)^8 := by
      have hnat : (2093 : ℕ)^39*50000000000000000000^8 ≤ 7084776214092618659^8*3125^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2093 3125 7084776214092618659 50000000000000000000 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2093/3125 : ℝ)) (X := (7084776214092618659/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (57084776214092618659/50000000000000000000 : ℝ) ≤ (10275552664330947/10000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (57084776214092618659/50000000000000000000 : ℝ)^8 ≤ (10275552664330947/10000000000000000 : ℝ)^39 := by
      have hnat : (57084776214092618659 : ℕ)^8*10000000000000000^39 ≤ 10275552664330947^39*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        57084776214092618659 50000000000000000000 10275552664330947 10000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10275552664330947/10000000000000000 : ℝ)) (X := (57084776214092618659/50000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (32084776214092618659/25000000000000000000 : ℝ) ≤ (5262565238647407/5000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (32084776214092618659/25000000000000000000 : ℝ)^8 ≤ (5262565238647407/5000000000000000 : ℝ)^39 := by
      have hnat : (32084776214092618659 : ℕ)^8*5000000000000000^39 ≤ 5262565238647407^39*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        32084776214092618659 25000000000000000000 5262565238647407 5000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5262565238647407/5000000000000000 : ℝ)) (X := (32084776214092618659/25000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(275552664330947/6697600000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(249577812963867/6697600000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (2093/3125 : ℝ)) (alpha := (275552664330947/6697600000000000 : ℝ)) (beta := (249577812963867/6697600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (2093/3125 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(275552664330947/6697600000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(249577812963867/6697600000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (18093/50000 : ℝ) ^ (39/8 : ℝ) ≤ (352253507533437967/50000000000000000000 : ℝ) := by
    have hpowers : (18093/50000 : ℝ)^39 ≤ (352253507533437967/50000000000000000000 : ℝ)^8 := by
      have hnat : (18093 : ℕ)^39*50000000000000000000^8 ≤ 352253507533437967^8*50000^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18093 50000 352253507533437967 50000000000000000000 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18093/50000 : ℝ)) (X := (352253507533437967/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (50352253507533437967/50000000000000000000 : ℝ) ≤ (2002882226439859/2000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (50352253507533437967/50000000000000000000 : ℝ)^8 ≤ (2002882226439859/2000000000000000 : ℝ)^39 := by
      have hnat : (50352253507533437967 : ℕ)^8*2000000000000000^39 ≤ 2002882226439859^39*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50352253507533437967 50000000000000000000 2002882226439859 2000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2002882226439859/2000000000000000 : ℝ)) (X := (50352253507533437967/50000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (25352253507533437967/25000000000000000000 : ℝ) ≤ (5014371174580267/5000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (25352253507533437967/25000000000000000000 : ℝ)^8 ≤ (5014371174580267/5000000000000000 : ℝ)^39 := by
      have hnat : (25352253507533437967 : ℕ)^8*5000000000000000^39 ≤ 5014371174580267^39*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25352253507533437967 25000000000000000000 5014371174580267 5000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5014371174580267/5000000000000000 : ℝ)) (X := (25352253507533437967/25000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(2882226439859/723720000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(4777072320413/1206200000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (18093/50000 : ℝ)) (alpha := (2882226439859/723720000000000 : ℝ)) (beta := (4777072320413/1206200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (18093/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(2882226439859/723720000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(4777072320413/1206200000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (36893/50000 : ℝ) ^ (39/8 : ℝ) ≤ (4543631349091339931/20000000000000000000 : ℝ) := by
    have hpowers : (36893/50000 : ℝ)^39 ≤ (4543631349091339931/20000000000000000000 : ℝ)^8 := by
      have hnat : (36893 : ℕ)^39*20000000000000000000^8 ≤ 4543631349091339931^8*50000^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        36893 50000 4543631349091339931 20000000000000000000 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (36893/50000 : ℝ)) (X := (4543631349091339931/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (24543631349091339931/20000000000000000000 : ℝ) ≤ (1042888089093183/1000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (24543631349091339931/20000000000000000000 : ℝ)^8 ≤ (1042888089093183/1000000000000000 : ℝ)^39 := by
      have hnat : (24543631349091339931 : ℕ)^8*1000000000000000^39 ≤ 1042888089093183^39*20000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24543631349091339931 20000000000000000000 1042888089093183 1000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1042888089093183/1000000000000000 : ℝ)) (X := (24543631349091339931/20000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (14543631349091339931/10000000000000000000 : ℝ) ≤ (10798633241362387/10000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (14543631349091339931/10000000000000000000 : ℝ)^8 ≤ (10798633241362387/10000000000000000 : ℝ)^39 := by
      have hnat : (14543631349091339931 : ℕ)^8*10000000000000000^39 ≤ 10798633241362387^39*10000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14543631349091339931 10000000000000000000 10798633241362387 10000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10798633241362387/10000000000000000 : ℝ)) (X := (14543631349091339931/10000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(42888089093183/737860000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(369752350430557/7378600000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (36893/50000 : ℝ)) (alpha := (42888089093183/737860000000000 : ℝ)) (beta := (369752350430557/7378600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (36893/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(42888089093183/737860000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(369752350430557/7378600000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-418185817/1250000000 : ℝ)*X 0 0+(431087/800000 : ℝ)*X 0 1+(3651846589/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318023_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((5794587009/10000000000 : ℝ)*X 1 0+(-759092947/10000000000 : ℝ)*X 1 1+(5322250049/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318023_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((3135269887/10000000000 : ℝ)*X 2 0+(1444200413/2500000000 : ℝ)*X 2 1+(-342237953/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318023_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((3940980977/10000000000 : ℝ)*X 0 0+(4871458399/10000000000 : ℝ)*X 0 1+(1809868949/5000000000 : ℝ)*X 0 2+(3940980977/10000000000 : ℝ)*X 1 0+(4871458399/10000000000 : ℝ)*X 1 1+(1809868949/5000000000 : ℝ)*X 1 2+(3940980977/10000000000 : ℝ)*X 2 0+(4871458399/10000000000 : ℝ)*X 2 1+(1809868949/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318023_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-1698583857/5000000000 : ℝ)*X 0 0+(5376853591/10000000000 : ℝ)*X 0 1+(72281359/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318023_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((5723883511/10000000000 : ℝ)*X 1 0+(-379217937/10000000000 : ℝ)*X 1 1+(2804456299/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318023_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((1479319097/5000000000 : ℝ)*X 2 0+(154070139/250000000 : ℝ)*X 2 1+(-3147539473/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318023_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_12 : ((1897772927/5000000000 : ℝ)*X 0 0+(122898349/250000000 : ℝ)*X 0 1+(743861573/2000000000 : ℝ)*X 0 2+(1897772927/5000000000 : ℝ)*X 1 0+(122898349/250000000 : ℝ)*X 1 1+(743861573/2000000000 : ℝ)*X 1 2+(1897772927/5000000000 : ℝ)*X 2 0+(122898349/250000000 : ℝ)*X 2 1+(743861573/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318023_s1_s1_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((-68318897/200000000 : ℝ)*X 0 0+(5353369709/10000000000 : ℝ)*X 0 1+(1810743137/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318023_s1_s1_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((2918744747/5000000000 : ℝ)*X 1 0+(-9397123/125000000 : ℝ)*X 1 1+(52828437/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318023_s1_s1_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((3070888393/10000000000 : ℝ)*X 2 0+(2886253513/5000000000 : ℝ)*X 2 1+(-3489932381/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318023_s1_s1_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_17 : ((-33/10000000000 : ℝ)*X 0 0+(9999999999/10000000000 : ℝ)*X 0 1+(-33/10000000000 : ℝ)*X 2 0+(9999999999/10000000000 : ℝ)*X 2 1+(-1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318023_s1_s1_17 p hpa hpb (pair X 1)
    change _ ≤ P 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_19 : ((480213373/1250000000 : ℝ)*X 0 0+(2465567937/5000000000 : ℝ)*X 0 1+(365640193/1000000000 : ℝ)*X 0 2+(480213373/1250000000 : ℝ)*X 1 0+(2465567937/5000000000 : ℝ)*X 1 1+(365640193/1000000000 : ℝ)*X 1 2+(480213373/1250000000 : ℝ)*X 2 0+(2465567937/5000000000 : ℝ)*X 2 1+(365640193/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318023_s1_s1_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((-3104671183/10000000000 : ℝ)*X 0 0+(549457689/1000000000 : ℝ)*X 0 1+(470965863/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318023_s1_s1_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((6239058809/10000000000 : ℝ)*X 1 0+(-452925977/10000000000 : ℝ)*X 1 1+(5039543909/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318023_s1_s1_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((139757871/500000000 : ℝ)*X 2 0+(6089097413/10000000000 : ℝ)*X 2 1+(-3392111173/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318023_s1_s1_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_25 : ((2166508957/5000000000 : ℝ)*X 0 0+(2302013627/5000000000 : ℝ)*X 0 1+(874989109/2500000000 : ℝ)*X 0 2+(2166508957/5000000000 : ℝ)*X 1 0+(2302013627/5000000000 : ℝ)*X 1 1+(874989109/2500000000 : ℝ)*X 1 2+(2166508957/5000000000 : ℝ)*X 2 0+(2302013627/5000000000 : ℝ)*X 2 1+(874989109/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318023_s1_s1_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((3657/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3657/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (5678748216025370129923254845693/372556818015200000000000000000000000 : ℝ) := by norm_num
    linear_combination (182952209833/1000000000000 : ℝ)*(base40) + (33760007997/100000000000 : ℝ)*(base50) + (2713621/500000000000 : ℝ)*(base60) + (9610646277389/1000000000000 : ℝ)*(major_s1_0) + (92985507758779/125000000000 : ℝ)*(major_s1_1) + (9610646277389/1000000000000 : ℝ)*(major_s1_2) + (577467407/200000000000 : ℝ)*(sp_s1_0) + (7279959/31250000000 : ℝ)*(sp_s1_1) + (6974634714307/500000000000 : ℝ)*(sp_s1_7) + (6977112741261/500000000000 : ℝ)*(sp_s1_8) + (1395445844121/100000000000 : ℝ)*(sp_s1_9) + (5266829032683/1000000000000 : ℝ)*(sp_s1_12) + (2301675561/1000000000000 : ℝ)*(sp_s1_13) + (734273415792843/1000000000000 : ℝ)*(sp_s1_17) + (5266829032683/1000000000000 : ℝ)*(f.failure) + (1395445844121/100000000000 : ℝ)*(f.sum) + (4584055988644563487/13350100980000000000000000000000 : ℝ)*base62 + (3440205659950073/7378600000000000000000000000 : ℝ)*base65 + (70047028136413/150775000000000000000000000 : ℝ)*base67 + (41613703751411/737860000000000000000000000 : ℝ)*base69 + (133438013083390178043/247094556800000000000000000000000 : ℝ)*base71 + (612365911412383/6697600000000000000000000000 : ℝ)*base73 + (6792874018201/180930000000000000000000000 : ℝ)*base74 + (3026007324132263/6697600000000000000000000000 : ℝ)*base77 + (1452315555892252509/8078645120000000000000000000000 : ℝ)*base79 + (2783/4000000000000000 : ℝ)*base86 + (2783/4000000000000000 : ℝ)*base88 + (2783/4000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(759/100000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(759/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (266051509436062478730303554421/74511363603040000000000000000000000 : ℝ) := by norm_num
    linear_combination (205617438673/1000000000000 : ℝ)*(base40) + (6356446429/8000000000 : ℝ)*(base49) + (156817/200000000000 : ℝ)*(base60) + (294466731633/100000000000 : ℝ)*(major_s1_0) + (294466731633/100000000000 : ℝ)*(major_s1_1) + (294466731633/100000000000 : ℝ)*(major_s1_2) + (2528847/1000000000000 : ℝ)*(sp_s1_0) + (319592897/1000000000000 : ℝ)*(sp_s1_6) + (18443261/1000000000000 : ℝ)*(sp_s1_8) + (161471051/500000000000 : ℝ)*(sp_s1_12) + (2137796757983/500000000000 : ℝ)*(sp_s1_13) + (267223600097/62500000000 : ℝ)*(sp_s1_14) + (4275596044813/1000000000000 : ℝ)*(sp_s1_15) + (1613094862633/1000000000000 : ℝ)*(sp_s1_19) + (12607323419/7812500000 : ℝ)*(f.failure) + (4275596044813/1000000000000 : ℝ)*(f.sum) + (1000240317640738243/4450033660000000000000000000000 : ℝ)*base63 + (387749865053807/737860000000000000000000000 : ℝ)*base65 + (9709257644801/24124000000000000000000000 : ℝ)*base67 + (297014377342851/368930000000000000000000000 : ℝ)*base69 + (6705464051123558967/24709455680000000000000000000000 : ℝ)*base71 + (280431310710507/669760000000000000000000000 : ℝ)*base73 + (68218132946559/120620000000000000000000000 : ℝ)*base75 + (601798445622323/669760000000000000000000000 : ℝ)*base77 + (1313259059951875499/4039322560000000000000000000000 : ℝ)*base78 + (63/62500000000000 : ℝ)*base86 + (63/62500000000000 : ℝ)*base88 + (63/62500000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2163/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(2163/10000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (157489277813845858659256533953/11642400562975000000000000000000000 : ℝ) := by norm_num
    linear_combination (111805999723/100000000000 : ℝ)*(base40) + (65897571319/100000000000 : ℝ)*(base50) + (366659127283/31250000000 : ℝ)*(major_s1_0) + (442695044023649/500000000000 : ℝ)*(major_s1_1) + (366659127283/31250000000 : ℝ)*(major_s1_2) + (712572867/1000000000000 : ℝ)*(sp_s1_2) + (95267911/1000000000000 : ℝ)*(sp_s1_6) + (182559857/250000000000 : ℝ)*(sp_s1_9) + (673288637/1000000000000 : ℝ)*(sp_s1_14) + (436828497987121/500000000000 : ℝ)*(sp_s1_17) + (8518103636011/500000000000 : ℝ)*(sp_s1_20) + (8517766991693/500000000000 : ℝ)*(sp_s1_21) + (17034764459727/1000000000000 : ℝ)*(sp_s1_22) + (6429877097101/1000000000000 : ℝ)*(sp_s1_25) + (1607493091253/250000000000 : ℝ)*(f.failure) + (8518103636011/500000000000 : ℝ)*(f.sum) + (5418069474334207601/13350100980000000000000000000000 : ℝ)*base62 + (169380493235383/1844650000000000000000000000 : ℝ)*base65 + (290498535902343/603100000000000000000000000 : ℝ)*base67 + (36188741259577/73786000000000000000000000 : ℝ)*base68 + (852624948711495731/7721704900000000000000000000000 : ℝ)*base71 + (86036631652479/209300000000000000000000000 : ℝ)*base72 + (140349324959827/361860000000000000000000000 : ℝ)*base74 + (11459390809121/209300000000000000000000000 : ℝ)*base77 + (7833683011296461/15778603750000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (353/1000000000000000 : ℝ)*base86 + (353/1000000000000000 : ℝ)*base88 + (353/1000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((2093/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2093/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(18093/50000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(18093/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(36893/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(36893/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((3657/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3657/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(759/100000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(759/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2163/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(2163/10000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c318023_s1 p hpa hpb X hX hprev0

#print axioms solution
