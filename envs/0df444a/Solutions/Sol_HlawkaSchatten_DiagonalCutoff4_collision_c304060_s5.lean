-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c304060_s5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:47:44.405243+00:00
-- url     : https://prove2.me/submissions/f82e21df-49da-4065-8f92-69ef01113d43

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
theorem collision_support_c304060_s5_s5_0 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-288884751/1250000000 : ℝ)*x 0 + (2070321007/5000000000 : ℝ)*x 1 + (-3138360543/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (288884751/1250000000 : ℝ)^133 ≤ (14529508231569/100000000000000 : ℝ)^101 := by
    have hnat : (288884751 : ℕ)^133*100000000000000^101 ≤ 14529508231569^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      288884751 1250000000 14529508231569 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2070321007/5000000000 : ℝ)^133 ≤ (125257167263/400000000000 : ℝ)^101 := by
    have hnat : (2070321007 : ℕ)^133*400000000000^101 ≤ 125257167263^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2070321007 5000000000 125257167263 400000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3138360543/5000000000 : ℝ)^133 ≤ (13539049984903/25000000000000 : ℝ)^101 := by
    have hnat : (3138360543 : ℕ)^133*25000000000000^101 ≤ 13539049984903^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3138360543 5000000000 13539049984903 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-288884751/1250000000 : ℝ), (2070321007/5000000000 : ℝ), (-3138360543/5000000000 : ℝ)] ![(14529508231569/100000000000000 : ℝ), (125257167263/400000000000 : ℝ), (13539049984903/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-288884751/1250000000 : ℝ)|^133 ≤ (14529508231569/100000000000000 : ℝ)^101
        have hw : |(-288884751/1250000000 : ℝ)|=(288884751/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2070321007/5000000000 : ℝ)|^133 ≤ (125257167263/400000000000 : ℝ)^101
        have hw : |(2070321007/5000000000 : ℝ)|=(2070321007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3138360543/5000000000 : ℝ)|^133 ≤ (13539049984903/25000000000000 : ℝ)^101
        have hw : |(-3138360543/5000000000 : ℝ)|=(3138360543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304060_s5_s5_2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (237383953/500000000 : ℝ)*x 0 + (72463423/125000000 : ℝ)*x 1 + (1106966397/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (237383953/500000000 : ℝ)^133 ≤ (18747803813819/50000000000000 : ℝ)^101 := by
    have hnat : (237383953 : ℕ)^133*50000000000000^101 ≤ 18747803813819^101*500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      237383953 500000000 18747803813819 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (72463423/125000000 : ℝ)^133 ≤ (1219343020267/2500000000000 : ℝ)^101 := by
    have hnat : (72463423 : ℕ)^133*2500000000000^101 ≤ 1219343020267^101*125000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      72463423 125000000 1219343020267 2500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1106966397/5000000000 : ℝ)^133 ≤ (6865335774739/50000000000000 : ℝ)^101 := by
    have hnat : (1106966397 : ℕ)^133*50000000000000^101 ≤ 6865335774739^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1106966397 5000000000 6865335774739 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(237383953/500000000 : ℝ), (72463423/125000000 : ℝ), (1106966397/5000000000 : ℝ)] ![(18747803813819/50000000000000 : ℝ), (1219343020267/2500000000000 : ℝ), (6865335774739/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(237383953/500000000 : ℝ)|^133 ≤ (18747803813819/50000000000000 : ℝ)^101
        have hw : |(237383953/500000000 : ℝ)|=(237383953/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(72463423/125000000 : ℝ)|^133 ≤ (1219343020267/2500000000000 : ℝ)^101
        have hw : |(72463423/125000000 : ℝ)|=(72463423/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1106966397/5000000000 : ℝ)|^133 ≤ (6865335774739/50000000000000 : ℝ)^101
        have hw : |(1106966397/5000000000 : ℝ)|=(1106966397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304060_s5_s5_6 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (6716688809/10000000000 : ℝ)*x 0 + (4464566013/10000000000 : ℝ)*x 1 + (-303013903/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6716688809/10000000000 : ℝ)^133 ≤ (11841930909693/20000000000000 : ℝ)^101 := by
    have hnat : (6716688809 : ℕ)^133*20000000000000^101 ≤ 11841930909693^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6716688809 10000000000 11841930909693 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4464566013/10000000000 : ℝ)^133 ≤ (34579460938251/100000000000000 : ℝ)^101 := by
    have hnat : (4464566013 : ℕ)^133*100000000000000^101 ≤ 34579460938251^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4464566013 10000000000 34579460938251 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (303013903/2500000000 : ℝ)^133 ≤ (6210884494881/100000000000000 : ℝ)^101 := by
    have hnat : (303013903 : ℕ)^133*100000000000000^101 ≤ 6210884494881^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      303013903 2500000000 6210884494881 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6716688809/10000000000 : ℝ), (4464566013/10000000000 : ℝ), (-303013903/2500000000 : ℝ)] ![(11841930909693/20000000000000 : ℝ), (34579460938251/100000000000000 : ℝ), (6210884494881/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6716688809/10000000000 : ℝ)|^133 ≤ (11841930909693/20000000000000 : ℝ)^101
        have hw : |(6716688809/10000000000 : ℝ)|=(6716688809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4464566013/10000000000 : ℝ)|^133 ≤ (34579460938251/100000000000000 : ℝ)^101
        have hw : |(4464566013/10000000000 : ℝ)|=(4464566013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-303013903/2500000000 : ℝ)|^133 ≤ (6210884494881/100000000000000 : ℝ)^101
        have hw : |(-303013903/2500000000 : ℝ)|=(303013903/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304060_s5_s5_7 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2124405977/10000000000 : ℝ)*x 0 + (3786968523/10000000000 : ℝ)*x 1 + (-3355989777/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2124405977/10000000000 : ℝ)^133 ≤ (3251060508989/25000000000000 : ℝ)^101 := by
    have hnat : (2124405977 : ℕ)^133*25000000000000^101 ≤ 3251060508989^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124405977 10000000000 3251060508989 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3786968523/10000000000 : ℝ)^133 ≤ (27840763642193/100000000000000 : ℝ)^101 := by
    have hnat : (3786968523 : ℕ)^133*100000000000000^101 ≤ 27840763642193^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3786968523 10000000000 27840763642193 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3355989777/5000000000 : ℝ)^133 ≤ (7394374288669/12500000000000 : ℝ)^101 := by
    have hnat : (3355989777 : ℕ)^133*12500000000000^101 ≤ 7394374288669^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3355989777 5000000000 7394374288669 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2124405977/10000000000 : ℝ), (3786968523/10000000000 : ℝ), (-3355989777/5000000000 : ℝ)] ![(3251060508989/25000000000000 : ℝ), (27840763642193/100000000000000 : ℝ), (7394374288669/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2124405977/10000000000 : ℝ)|^133 ≤ (3251060508989/25000000000000 : ℝ)^101
        have hw : |(-2124405977/10000000000 : ℝ)|=(2124405977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3786968523/10000000000 : ℝ)|^133 ≤ (27840763642193/100000000000000 : ℝ)^101
        have hw : |(3786968523/10000000000 : ℝ)|=(3786968523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3355989777/5000000000 : ℝ)|^133 ≤ (7394374288669/12500000000000 : ℝ)^101
        have hw : |(-3355989777/5000000000 : ℝ)|=(3355989777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304060_s5_s5_8 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1018827223/2500000000 : ℝ)*x 0 + (-171188889/1000000000 : ℝ)*x 1 + (-674585547/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1018827223/2500000000 : ℝ)^133 ≤ (30665287258389/100000000000000 : ℝ)^101 := by
    have hnat : (1018827223 : ℕ)^133*100000000000000^101 ≤ 30665287258389^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1018827223 2500000000 30665287258389 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (171188889/1000000000 : ℝ)^133 ≤ (1957250194111/20000000000000 : ℝ)^101 := by
    have hnat : (171188889 : ℕ)^133*20000000000000^101 ≤ 1957250194111^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171188889 1000000000 1957250194111 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674585547/1000000000 : ℝ)^133 ≤ (14887115438483/25000000000000 : ℝ)^101 := by
    have hnat : (674585547 : ℕ)^133*25000000000000^101 ≤ 14887115438483^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674585547 1000000000 14887115438483 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1018827223/2500000000 : ℝ), (-171188889/1000000000 : ℝ), (-674585547/1000000000 : ℝ)] ![(30665287258389/100000000000000 : ℝ), (1957250194111/20000000000000 : ℝ), (14887115438483/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1018827223/2500000000 : ℝ)|^133 ≤ (30665287258389/100000000000000 : ℝ)^101
        have hw : |(1018827223/2500000000 : ℝ)|=(1018827223/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-171188889/1000000000 : ℝ)|^133 ≤ (1957250194111/20000000000000 : ℝ)^101
        have hw : |(-171188889/1000000000 : ℝ)|=(171188889/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-674585547/1000000000 : ℝ)|^133 ≤ (14887115438483/25000000000000 : ℝ)^101
        have hw : |(-674585547/1000000000 : ℝ)|=(674585547/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304060_s5_s5_9 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (34930217/80000000 : ℝ)*x 0 + (3391292421/5000000000 : ℝ)*x 1 + (1246407921/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (34930217/80000000 : ℝ)^133 ≤ (33580499590803/100000000000000 : ℝ)^101 := by
    have hnat : (34930217 : ℕ)^133*100000000000000^101 ≤ 33580499590803^101*80000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34930217 80000000 33580499590803 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3391292421/5000000000 : ℝ)^133 ≤ (59975779819273/100000000000000 : ℝ)^101 := by
    have hnat : (3391292421 : ℕ)^133*100000000000000^101 ≤ 59975779819273^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3391292421 5000000000 59975779819273 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1246407921/10000000000 : ℝ)^133 ≤ (1288744114909/20000000000000 : ℝ)^101 := by
    have hnat : (1246407921 : ℕ)^133*20000000000000^101 ≤ 1288744114909^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1246407921 10000000000 1288744114909 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(34930217/80000000 : ℝ), (3391292421/5000000000 : ℝ), (1246407921/10000000000 : ℝ)] ![(33580499590803/100000000000000 : ℝ), (59975779819273/100000000000000 : ℝ), (1288744114909/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(34930217/80000000 : ℝ)|^133 ≤ (33580499590803/100000000000000 : ℝ)^101
        have hw : |(34930217/80000000 : ℝ)|=(34930217/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3391292421/5000000000 : ℝ)|^133 ≤ (59975779819273/100000000000000 : ℝ)^101
        have hw : |(3391292421/5000000000 : ℝ)|=(3391292421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1246407921/10000000000 : ℝ)|^133 ≤ (1288744114909/20000000000000 : ℝ)^101
        have hw : |(1246407921/10000000000 : ℝ)|=(1246407921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304060_s5_s5_13 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (25190471/40000000 : ℝ)*x 0 + (670102751/1250000000 : ℝ)*x 1 + (-434202523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (25190471/40000000 : ℝ)^133 ≤ (54393747948073/100000000000000 : ℝ)^101 := by
    have hnat : (25190471 : ℕ)^133*100000000000000^101 ≤ 54393747948073^101*40000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25190471 40000000 54393747948073 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (670102751/1250000000 : ℝ)^133 ≤ (43999051332447/100000000000000 : ℝ)^101 := by
    have hnat : (670102751 : ℕ)^133*100000000000000^101 ≤ 43999051332447^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      670102751 1250000000 43999051332447 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (434202523/10000000000 : ℝ)^133 ≤ (1607200706289/100000000000000 : ℝ)^101 := by
    have hnat : (434202523 : ℕ)^133*100000000000000^101 ≤ 1607200706289^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434202523 10000000000 1607200706289 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(25190471/40000000 : ℝ), (670102751/1250000000 : ℝ), (-434202523/10000000000 : ℝ)] ![(54393747948073/100000000000000 : ℝ), (43999051332447/100000000000000 : ℝ), (1607200706289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(25190471/40000000 : ℝ)|^133 ≤ (54393747948073/100000000000000 : ℝ)^101
        have hw : |(25190471/40000000 : ℝ)|=(25190471/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(670102751/1250000000 : ℝ)|^133 ≤ (43999051332447/100000000000000 : ℝ)^101
        have hw : |(670102751/1250000000 : ℝ)|=(670102751/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-434202523/10000000000 : ℝ)|^133 ≤ (1607200706289/100000000000000 : ℝ)^101
        have hw : |(-434202523/10000000000 : ℝ)|=(434202523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304060_s5_s5_14 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-721036563/5000000000 : ℝ)*x 0 + (1074766793/2500000000 : ℝ)*x 1 + (-1680917883/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (721036563/5000000000 : ℝ)^133 ≤ (7807784338691/100000000000000 : ℝ)^101 := by
    have hnat : (721036563 : ℕ)^133*100000000000000^101 ≤ 7807784338691^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      721036563 5000000000 7807784338691 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1074766793/2500000000 : ℝ)^133 ≤ (2056343149903/6250000000000 : ℝ)^101 := by
    have hnat : (1074766793 : ℕ)^133*6250000000000^101 ≤ 2056343149903^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074766793 2500000000 2056343149903 6250000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1680917883/2500000000 : ℝ)^133 ≤ (59290725240917/100000000000000 : ℝ)^101 := by
    have hnat : (1680917883 : ℕ)^133*100000000000000^101 ≤ 59290725240917^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1680917883 2500000000 59290725240917 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-721036563/5000000000 : ℝ), (1074766793/2500000000 : ℝ), (-1680917883/2500000000 : ℝ)] ![(7807784338691/100000000000000 : ℝ), (2056343149903/6250000000000 : ℝ), (59290725240917/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-721036563/5000000000 : ℝ)|^133 ≤ (7807784338691/100000000000000 : ℝ)^101
        have hw : |(-721036563/5000000000 : ℝ)|=(721036563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1074766793/2500000000 : ℝ)|^133 ≤ (2056343149903/6250000000000 : ℝ)^101
        have hw : |(1074766793/2500000000 : ℝ)|=(1074766793/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1680917883/2500000000 : ℝ)|^133 ≤ (59290725240917/100000000000000 : ℝ)^101
        have hw : |(-1680917883/2500000000 : ℝ)|=(1680917883/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304060_s5_s5_15 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4024761353/10000000000 : ℝ)*x 0 + (-952464239/5000000000 : ℝ)*x 1 + (-6661499697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4024761353/10000000000 : ℝ)^133 ≤ (7541353420401/25000000000000 : ℝ)^101 := by
    have hnat : (4024761353 : ℕ)^133*25000000000000^101 ≤ 7541353420401^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4024761353 10000000000 7541353420401 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (952464239/5000000000 : ℝ)^133 ≤ (5632373247983/50000000000000 : ℝ)^101 := by
    have hnat : (952464239 : ℕ)^133*50000000000000^101 ≤ 5632373247983^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      952464239 5000000000 5632373247983 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6661499697/10000000000 : ℝ)^133 ≤ (14642459952729/25000000000000 : ℝ)^101 := by
    have hnat : (6661499697 : ℕ)^133*25000000000000^101 ≤ 14642459952729^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6661499697 10000000000 14642459952729 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4024761353/10000000000 : ℝ), (-952464239/5000000000 : ℝ), (-6661499697/10000000000 : ℝ)] ![(7541353420401/25000000000000 : ℝ), (5632373247983/50000000000000 : ℝ), (14642459952729/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4024761353/10000000000 : ℝ)|^133 ≤ (7541353420401/25000000000000 : ℝ)^101
        have hw : |(4024761353/10000000000 : ℝ)|=(4024761353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-952464239/5000000000 : ℝ)|^133 ≤ (5632373247983/50000000000000 : ℝ)^101
        have hw : |(-952464239/5000000000 : ℝ)|=(952464239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6661499697/10000000000 : ℝ)|^133 ≤ (14642459952729/25000000000000 : ℝ)^101
        have hw : |(-6661499697/10000000000 : ℝ)|=(6661499697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304060_s5_s5_16 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2837991929/5000000000 : ℝ)*x 0 + (2751372971/5000000000 : ℝ)*x 1 + (266152277/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2837991929/5000000000 : ℝ)^133 ≤ (47436604610451/100000000000000 : ℝ)^101 := by
    have hnat : (2837991929 : ℕ)^133*100000000000000^101 ≤ 47436604610451^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2837991929 5000000000 47436604610451 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2751372971/5000000000 : ℝ)^133 ≤ (22769674427361/50000000000000 : ℝ)^101 := by
    have hnat : (2751372971 : ℕ)^133*50000000000000^101 ≤ 22769674427361^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2751372971 5000000000 22769674427361 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (266152277/2000000000 : ℝ)^133 ≤ (7024046522601/100000000000000 : ℝ)^101 := by
    have hnat : (266152277 : ℕ)^133*100000000000000^101 ≤ 7024046522601^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266152277 2000000000 7024046522601 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2837991929/5000000000 : ℝ), (2751372971/5000000000 : ℝ), (266152277/2000000000 : ℝ)] ![(47436604610451/100000000000000 : ℝ), (22769674427361/50000000000000 : ℝ), (7024046522601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2837991929/5000000000 : ℝ)|^133 ≤ (47436604610451/100000000000000 : ℝ)^101
        have hw : |(2837991929/5000000000 : ℝ)|=(2837991929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2751372971/5000000000 : ℝ)|^133 ≤ (22769674427361/50000000000000 : ℝ)^101
        have hw : |(2751372971/5000000000 : ℝ)|=(2751372971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(266152277/2000000000 : ℝ)|^133 ≤ (7024046522601/100000000000000 : ℝ)^101
        have hw : |(266152277/2000000000 : ℝ)|=(266152277/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304060_s5_s5_20 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3838073037/5000000000 : ℝ)*x 0 + (758948567/2000000000 : ℝ)*x 1 + (-20521637/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3838073037/5000000000 : ℝ)^133 ≤ (35295795243349/50000000000000 : ℝ)^101 := by
    have hnat : (3838073037 : ℕ)^133*50000000000000^101 ≤ 35295795243349^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3838073037 5000000000 35295795243349 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (758948567/2000000000 : ℝ)^133 ≤ (279160511343/1000000000000 : ℝ)^101 := by
    have hnat : (758948567 : ℕ)^133*1000000000000^101 ≤ 279160511343^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      758948567 2000000000 279160511343 1000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (20521637/500000000 : ℝ)^133 ≤ (746179183217/50000000000000 : ℝ)^101 := by
    have hnat : (20521637 : ℕ)^133*50000000000000^101 ≤ 746179183217^101*500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20521637 500000000 746179183217 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3838073037/5000000000 : ℝ), (758948567/2000000000 : ℝ), (-20521637/500000000 : ℝ)] ![(35295795243349/50000000000000 : ℝ), (279160511343/1000000000000 : ℝ), (746179183217/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3838073037/5000000000 : ℝ)|^133 ≤ (35295795243349/50000000000000 : ℝ)^101
        have hw : |(3838073037/5000000000 : ℝ)|=(3838073037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(758948567/2000000000 : ℝ)|^133 ≤ (279160511343/1000000000000 : ℝ)^101
        have hw : |(758948567/2000000000 : ℝ)|=(758948567/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-20521637/500000000 : ℝ)|^133 ≤ (746179183217/50000000000000 : ℝ)^101
        have hw : |(-20521637/500000000 : ℝ)|=(20521637/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304060_s5_s5_21 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-593001889/5000000000 : ℝ)*x 0 + (5132646127/10000000000 : ℝ)*x 1 + (-3061415607/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (593001889/5000000000 : ℝ)^133 ≤ (6035693870937/100000000000000 : ℝ)^101 := by
    have hnat : (593001889 : ℕ)^133*100000000000000^101 ≤ 6035693870937^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      593001889 5000000000 6035693870937 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5132646127/10000000000 : ℝ)^133 ≤ (10387434182729/25000000000000 : ℝ)^101 := by
    have hnat : (5132646127 : ℕ)^133*25000000000000^101 ≤ 10387434182729^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5132646127 10000000000 10387434182729 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3061415607/5000000000 : ℝ)^133 ≤ (26207284695391/50000000000000 : ℝ)^101 := by
    have hnat : (3061415607 : ℕ)^133*50000000000000^101 ≤ 26207284695391^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3061415607 5000000000 26207284695391 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-593001889/5000000000 : ℝ), (5132646127/10000000000 : ℝ), (-3061415607/5000000000 : ℝ)] ![(6035693870937/100000000000000 : ℝ), (10387434182729/25000000000000 : ℝ), (26207284695391/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-593001889/5000000000 : ℝ)|^133 ≤ (6035693870937/100000000000000 : ℝ)^101
        have hw : |(-593001889/5000000000 : ℝ)|=(593001889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5132646127/10000000000 : ℝ)|^133 ≤ (10387434182729/25000000000000 : ℝ)^101
        have hw : |(5132646127/10000000000 : ℝ)|=(5132646127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3061415607/5000000000 : ℝ)|^133 ≤ (26207284695391/50000000000000 : ℝ)^101
        have hw : |(-3061415607/5000000000 : ℝ)|=(3061415607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304060_s5_s5_22 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (564109021/1000000000 : ℝ)*x 0 + (-871890521/5000000000 : ℝ)*x 1 + (-1052137113/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (564109021/1000000000 : ℝ)^133 ≤ (2940810207811/6250000000000 : ℝ)^101 := by
    have hnat : (564109021 : ℕ)^133*6250000000000^101 ≤ 2940810207811^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      564109021 1000000000 2940810207811 6250000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (871890521/5000000000 : ℝ)^133 ≤ (10027035907727/100000000000000 : ℝ)^101 := by
    have hnat : (871890521 : ℕ)^133*100000000000000^101 ≤ 10027035907727^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      871890521 5000000000 10027035907727 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052137113/2000000000 : ℝ)^133 ≤ (8584000151201/20000000000000 : ℝ)^101 := by
    have hnat : (1052137113 : ℕ)^133*20000000000000^101 ≤ 8584000151201^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052137113 2000000000 8584000151201 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(564109021/1000000000 : ℝ), (-871890521/5000000000 : ℝ), (-1052137113/2000000000 : ℝ)] ![(2940810207811/6250000000000 : ℝ), (10027035907727/100000000000000 : ℝ), (8584000151201/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(564109021/1000000000 : ℝ)|^133 ≤ (2940810207811/6250000000000 : ℝ)^101
        have hw : |(564109021/1000000000 : ℝ)|=(564109021/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-871890521/5000000000 : ℝ)|^133 ≤ (10027035907727/100000000000000 : ℝ)^101
        have hw : |(-871890521/5000000000 : ℝ)|=(871890521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1052137113/2000000000 : ℝ)|^133 ≤ (8584000151201/20000000000000 : ℝ)^101
        have hw : |(-1052137113/2000000000 : ℝ)|=(1052137113/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304060_s5_s5_23 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (52711863/125000000 : ℝ)*x 0 + (315843999/500000000 : ℝ)*x 1 + (540577487/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (52711863/125000000 : ℝ)^133 ≤ (16038212154169/50000000000000 : ℝ)^101 := by
    have hnat : (52711863 : ℕ)^133*50000000000000^101 ≤ 16038212154169^101*125000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52711863 125000000 16038212154169 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (315843999/500000000 : ℝ)^133 ≤ (54612937452537/100000000000000 : ℝ)^101 := by
    have hnat : (315843999 : ℕ)^133*100000000000000^101 ≤ 54612937452537^101*500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      315843999 500000000 54612937452537 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (540577487/2500000000 : ℝ)^133 ≤ (13310638228367/100000000000000 : ℝ)^101 := by
    have hnat : (540577487 : ℕ)^133*100000000000000^101 ≤ 13310638228367^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540577487 2500000000 13310638228367 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(52711863/125000000 : ℝ), (315843999/500000000 : ℝ), (540577487/2500000000 : ℝ)] ![(16038212154169/50000000000000 : ℝ), (54612937452537/100000000000000 : ℝ), (13310638228367/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(52711863/125000000 : ℝ)|^133 ≤ (16038212154169/50000000000000 : ℝ)^101
        have hw : |(52711863/125000000 : ℝ)|=(52711863/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(315843999/500000000 : ℝ)|^133 ≤ (54612937452537/100000000000000 : ℝ)^101
        have hw : |(315843999/500000000 : ℝ)|=(315843999/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(540577487/2500000000 : ℝ)|^133 ≤ (13310638228367/100000000000000 : ℝ)^101
        have hw : |(540577487/2500000000 : ℝ)|=(540577487/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304060_s5_s5_27 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (7876999889/10000000000 : ℝ)*x 0 + (70132047/200000000 : ℝ)*x 1 + (-237318949/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7876999889/10000000000 : ℝ)^133 ≤ (36516964892289/50000000000000 : ℝ)^101 := by
    have hnat : (7876999889 : ℕ)^133*50000000000000^101 ≤ 36516964892289^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7876999889 10000000000 36516964892289 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (70132047/200000000 : ℝ)^133 ≤ (6289732249217/25000000000000 : ℝ)^101 := by
    have hnat : (70132047 : ℕ)^133*25000000000000^101 ≤ 6289732249217^101*200000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70132047 200000000 6289732249217 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (237318949/5000000000 : ℝ)^133 ≤ (1807141199327/100000000000000 : ℝ)^101 := by
    have hnat : (237318949 : ℕ)^133*100000000000000^101 ≤ 1807141199327^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      237318949 5000000000 1807141199327 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7876999889/10000000000 : ℝ), (70132047/200000000 : ℝ), (-237318949/5000000000 : ℝ)] ![(36516964892289/50000000000000 : ℝ), (6289732249217/25000000000000 : ℝ), (1807141199327/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7876999889/10000000000 : ℝ)|^133 ≤ (36516964892289/50000000000000 : ℝ)^101
        have hw : |(7876999889/10000000000 : ℝ)|=(7876999889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(70132047/200000000 : ℝ)|^133 ≤ (6289732249217/25000000000000 : ℝ)^101
        have hw : |(70132047/200000000 : ℝ)|=(70132047/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-237318949/5000000000 : ℝ)|^133 ≤ (1807141199327/100000000000000 : ℝ)^101
        have hw : |(-237318949/5000000000 : ℝ)|=(237318949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c304060_s5 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev4 : (0 : ℝ) ≤ ((17889/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(17889/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(921/1250 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(921/1250 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-29713/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-29713/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((45543/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(45543/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9887/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(9887/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-4149/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-4149/12500 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76617/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76617/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
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
  rcases hprev4 with ⟨ratio_s4_0,ratio_s4_1,ratio_s4_2⟩
  have s5_pow0 : (17889/25000 : ℝ) ^ (33/8 : ℝ) ≤ (6285719361502113059/25000000000000000000 : ℝ) := by
    have hpowers : (17889/25000 : ℝ)^33 ≤ (6285719361502113059/25000000000000000000 : ℝ)^8 := by
      have hnat : (17889 : ℕ)^33*25000000000000000000^8 ≤ 6285719361502113059^8*25000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17889 25000 6285719361502113059 25000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17889/25000 : ℝ)) (X := (6285719361502113059/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s5_corner0a : (31285719361502113059/25000000000000000000 : ℝ) ≤ (5279388392335511/5000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (31285719361502113059/25000000000000000000 : ℝ)^8 ≤ (5279388392335511/5000000000000000 : ℝ)^33 := by
      have hnat : (31285719361502113059 : ℕ)^8*5000000000000000^33 ≤ 5279388392335511^33*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31285719361502113059 25000000000000000000 5279388392335511 5000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5279388392335511/5000000000000000 : ℝ)) (X := (31285719361502113059/25000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s5_corner0b : (18785719361502113059/12500000000000000000 : ℝ) ≤ (11037968943399197/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (18785719361502113059/12500000000000000000 : ℝ)^8 ≤ (11037968943399197/10000000000000000 : ℝ)^33 := by
      have hnat : (18785719361502113059 : ℕ)^8*10000000000000000^33 ≤ 11037968943399197^33*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18785719361502113059 12500000000000000000 11037968943399197 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11037968943399197/10000000000000000 : ℝ)) (X := (18785719361502113059/12500000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s5_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(93129464111837/1192600000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(19167686349127/286224000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (17889/25000 : ℝ)) (alpha := (93129464111837/1192600000000000 : ℝ)) (beta := (19167686349127/286224000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow0,s5_corner0a]) (by linarith only [s5_pow0,s5_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (17889/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(93129464111837/1192600000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(19167686349127/286224000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s5_pow1 : (921/1250 : ℝ) ^ (33/8 : ℝ) ≤ (7091811434999311643/25000000000000000000 : ℝ) := by
    have hpowers : (921/1250 : ℝ)^33 ≤ (7091811434999311643/25000000000000000000 : ℝ)^8 := by
      have hnat : (921 : ℕ)^33*25000000000000000000^8 ≤ 7091811434999311643^8*1250^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        921 1250 7091811434999311643 25000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (921/1250 : ℝ)) (X := (7091811434999311643/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s5_corner1a : (32091811434999311643/25000000000000000000 : ℝ) ≤ (5312047345667611/5000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (32091811434999311643/25000000000000000000 : ℝ)^8 ≤ (5312047345667611/5000000000000000 : ℝ)^33 := by
      have hnat : (32091811434999311643 : ℕ)^8*5000000000000000^33 ≤ 5312047345667611^33*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        32091811434999311643 25000000000000000000 5312047345667611 5000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5312047345667611/5000000000000000 : ℝ)) (X := (32091811434999311643/25000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s5_corner1b : (19591811434999311643/12500000000000000000 : ℝ) ≤ (2230193886218239/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (19591811434999311643/12500000000000000000 : ℝ)^8 ≤ (2230193886218239/2000000000000000 : ℝ)^33 := by
      have hnat : (19591811434999311643 : ℕ)^8*2000000000000000^33 ≤ 2230193886218239^33*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19591811434999311643 12500000000000000000 2230193886218239 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2230193886218239/2000000000000000 : ℝ)) (X := (19591811434999311643/12500000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s5_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(312047345667611/3684000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(175624913251991/2456000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (921/1250 : ℝ)) (alpha := (312047345667611/3684000000000000 : ℝ)) (beta := (175624913251991/2456000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow1,s5_corner1a]) (by linarith only [s5_pow1,s5_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (921/1250 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(312047345667611/3684000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(175624913251991/2456000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s5_pow2 : (29713/50000 : ℝ) ^ (33/8 : ℝ) ≤ (5842827452570097301/50000000000000000000 : ℝ) := by
    have hpowers : (29713/50000 : ℝ)^33 ≤ (5842827452570097301/50000000000000000000 : ℝ)^8 := by
      have hnat : (29713 : ℕ)^33*50000000000000000000^8 ≤ 5842827452570097301^8*50000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        29713 50000 5842827452570097301 50000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (29713/50000 : ℝ)) (X := (5842827452570097301/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s5_corner2a : (55842827452570097301/50000000000000000000 : ℝ) ≤ (2054308806127961/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (55842827452570097301/50000000000000000000 : ℝ)^8 ≤ (2054308806127961/2000000000000000 : ℝ)^33 := by
      have hnat : (55842827452570097301 : ℕ)^8*2000000000000000^33 ≤ 2054308806127961^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        55842827452570097301 50000000000000000000 2054308806127961 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2054308806127961/2000000000000000 : ℝ)) (X := (55842827452570097301/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s5_corner2b : (30842827452570097301/25000000000000000000 : ℝ) ≤ (2104468953220663/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (30842827452570097301/25000000000000000000 : ℝ)^8 ≤ (2104468953220663/2000000000000000 : ℝ)^33 := by
      have hnat : (30842827452570097301 : ℕ)^8*2000000000000000^33 ≤ 2104468953220663^33*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        30842827452570097301 25000000000000000000 2104468953220663 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2104468953220663/2000000000000000 : ℝ)) (X := (30842827452570097301/25000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s5_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(54308806127961/1188520000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(25080073546351/594260000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (29713/50000 : ℝ)) (alpha := (54308806127961/1188520000000000 : ℝ)) (beta := (25080073546351/594260000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow2,s5_corner2a]) (by linarith only [s5_pow2,s5_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (29713/50000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(54308806127961/1188520000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(25080073546351/594260000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s5_0 : ((-288884751/1250000000 : ℝ)*X 0 0+(2070321007/5000000000 : ℝ)*X 0 1+(-3138360543/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304060_s5_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_2 : ((237383953/500000000 : ℝ)*X 2 0+(72463423/125000000 : ℝ)*X 2 1+(1106966397/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304060_s5_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_6 : ((6716688809/10000000000 : ℝ)*X 0 0+(4464566013/10000000000 : ℝ)*X 0 1+(-303013903/2500000000 : ℝ)*X 0 2+(6716688809/10000000000 : ℝ)*X 1 0+(4464566013/10000000000 : ℝ)*X 1 1+(-303013903/2500000000 : ℝ)*X 1 2+(6716688809/10000000000 : ℝ)*X 2 0+(4464566013/10000000000 : ℝ)*X 2 1+(-303013903/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304060_s5_s5_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_7 : ((-2124405977/10000000000 : ℝ)*X 0 0+(3786968523/10000000000 : ℝ)*X 0 1+(-3355989777/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304060_s5_s5_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_8 : ((1018827223/2500000000 : ℝ)*X 1 0+(-171188889/1000000000 : ℝ)*X 1 1+(-674585547/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304060_s5_s5_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_9 : ((34930217/80000000 : ℝ)*X 2 0+(3391292421/5000000000 : ℝ)*X 2 1+(1246407921/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304060_s5_s5_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_13 : ((25190471/40000000 : ℝ)*X 0 0+(670102751/1250000000 : ℝ)*X 0 1+(-434202523/10000000000 : ℝ)*X 0 2+(25190471/40000000 : ℝ)*X 1 0+(670102751/1250000000 : ℝ)*X 1 1+(-434202523/10000000000 : ℝ)*X 1 2+(25190471/40000000 : ℝ)*X 2 0+(670102751/1250000000 : ℝ)*X 2 1+(-434202523/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304060_s5_s5_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_14 : ((-721036563/5000000000 : ℝ)*X 0 0+(1074766793/2500000000 : ℝ)*X 0 1+(-1680917883/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304060_s5_s5_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_15 : ((4024761353/10000000000 : ℝ)*X 1 0+(-952464239/5000000000 : ℝ)*X 1 1+(-6661499697/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304060_s5_s5_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_16 : ((2837991929/5000000000 : ℝ)*X 2 0+(2751372971/5000000000 : ℝ)*X 2 1+(266152277/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304060_s5_s5_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_20 : ((3838073037/5000000000 : ℝ)*X 0 0+(758948567/2000000000 : ℝ)*X 0 1+(-20521637/500000000 : ℝ)*X 0 2+(3838073037/5000000000 : ℝ)*X 1 0+(758948567/2000000000 : ℝ)*X 1 1+(-20521637/500000000 : ℝ)*X 1 2+(3838073037/5000000000 : ℝ)*X 2 0+(758948567/2000000000 : ℝ)*X 2 1+(-20521637/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304060_s5_s5_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_21 : ((-593001889/5000000000 : ℝ)*X 0 0+(5132646127/10000000000 : ℝ)*X 0 1+(-3061415607/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304060_s5_s5_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_22 : ((564109021/1000000000 : ℝ)*X 1 0+(-871890521/5000000000 : ℝ)*X 1 1+(-1052137113/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304060_s5_s5_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_23 : ((52711863/125000000 : ℝ)*X 2 0+(315843999/500000000 : ℝ)*X 2 1+(540577487/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304060_s5_s5_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_27 : ((7876999889/10000000000 : ℝ)*X 0 0+(70132047/200000000 : ℝ)*X 0 1+(-237318949/5000000000 : ℝ)*X 0 2+(7876999889/10000000000 : ℝ)*X 1 0+(70132047/200000000 : ℝ)*X 1 1+(-237318949/5000000000 : ℝ)*X 1 2+(7876999889/10000000000 : ℝ)*X 2 0+(70132047/200000000 : ℝ)*X 2 1+(-237318949/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304060_s5_s5_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s5_0 : (0 : ℝ) ≤ ((45543/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(45543/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1688714905767631444791940101147/217575344132000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8284461/1000000000000 : ℝ)*(base39) + (3792437/1000000000000 : ℝ)*(base49) + (523240064677/1000000000000 : ℝ)*(base59) + (5414573283443/1000000000000 : ℝ)*(major_s5_0) + (5414573283443/1000000000000 : ℝ)*(major_s5_1) + (5414573283443/1000000000000 : ℝ)*(major_s5_2) + (7259202133421/1000000000000 : ℝ)*(sp_s5_7) + (7258728946753/1000000000000 : ℝ)*(sp_s5_8) + (18147722429/2500000000 : ℝ)*(sp_s5_9) + (3569922783007/1000000000000 : ℝ)*(sp_s5_13) + (19063279/1000000000000 : ℝ)*(sp_s5_14) + (466777469/1000000000000 : ℝ)*(sp_s5_15) + (12736239/500000000000 : ℝ)*(sp_s5_22) + (1322251/10000000000 : ℝ)*(sp_s5_23) + (3569922783007/1000000000000 : ℝ)*(f.failure) + (72592211967/10000000000 : ℝ)*(f.sum) + (30067196998697010349/109462692000000000000000000000000 : ℝ)*base63 + (51944453378361/118852000000000000000000000 : ℝ)*base65 + (544595939186187/2456000000000000000000000000 : ℝ)*base66 + (366871215436447/1188520000000000000000000000 : ℝ)*base69 + (13920451163912032753/35435723800000000000000000000000 : ℝ)*base71 + (692273074092887/1431120000000000000000000000 : ℝ)*base72 + (996027920364673/3684000000000000000000000000 : ℝ)*base75 + (245754904104231/1192600000000000000000000000 : ℝ)*base77 + (30354959352729416543/43935384000000000000000000000000 : ℝ)*base78 + (7787/12500000000000000 : ℝ)*base86 + (7787/12500000000000000 : ℝ)*base88 + (7787/12500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s5_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9887/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(9887/20000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (44273957543047823933743129857/3399614752062500000000000000000000 : ℝ) := by norm_num
    linear_combination (2281657/1000000000000 : ℝ)*(base18) + (70605883259/1000000000000 : ℝ)*(base39) + (225275125869/1000000000000 : ℝ)*(base59) + (685430761767/125000000000 : ℝ)*(major_s5_0) + (685430761767/125000000000 : ℝ)*(major_s5_1) + (685430761767/125000000000 : ℝ)*(major_s5_2) + (33020317/1000000000000 : ℝ)*(sp_s5_2) + (4250399/200000000000 : ℝ)*(sp_s5_6) + (94735579/1000000000000 : ℝ)*(sp_s5_7) + (7351461280993/1000000000000 : ℝ)*(sp_s5_14) + (3675776867457/500000000000 : ℝ)*(sp_s5_15) + (1470304599251/200000000000 : ℝ)*(sp_s5_16) + (723013281001/200000000000 : ℝ)*(sp_s5_20) + (244173619/1000000000000 : ℝ)*(sp_s5_27) + (3615331830619/1000000000000 : ℝ)*(f.failure) + (1837889004143/250000000000 : ℝ)*(f.sum) + (560275228800623623/4560945500000000000000000000000 : ℝ)*base62 + (28933785415183/297130000000000000000000000 : ℝ)*base65 + (121808041628897/307000000000000000000000000 : ℝ)*base67 + (3344397061739/14856500000000000000000000 : ℝ)*base68 + (1631777233373786087/4429465475000000000000000000000 : ℝ)*base71 + (10413896194541/11926000000000000000000000 : ℝ)*base72 + (82476778296221/153500000000000000000000000 : ℝ)*base74 + (8290018818237/18634375000000000000000000 : ℝ)*base76 + (973915944351878189/1830641000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (5621/12500000000000000 : ℝ)*base87 + (5621/12500000000000000 : ℝ)*base89 + (5621/12500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s5_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-4149/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-4149/12500 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (25908174973145088734607788177/3399614752062500000000000000000000 : ℝ) := by norm_num
    linear_combination (1645953/200000000000 : ℝ)*(base11) + (244131/250000000000 : ℝ)*(base15) + (522423379103/1000000000000 : ℝ)*(base39) + (83662158943/500000000000 : ℝ)*(base59) + (543618277237/125000000000 : ℝ)*(major_s5_0) + (543618277237/125000000000 : ℝ)*(major_s5_1) + (543618277237/125000000000 : ℝ)*(major_s5_2) + (10803323/500000000000 : ℝ)*(sp_s5_0) + (5952309/500000000000 : ℝ)*(sp_s5_2) + (8750987/200000000000 : ℝ)*(sp_s5_9) + (583052382173/100000000000 : ℝ)*(sp_s5_21) + (2915276340809/500000000000 : ℝ)*(sp_s5_22) + (5830497998589/1000000000000 : ℝ)*(sp_s5_23) + (2867336237339/1000000000000 : ℝ)*(sp_s5_27) + (2867336237339/1000000000000 : ℝ)*(f.failure) + (5830553658141/1000000000000 : ℝ)*(f.sum) + (5481630714985191859/13682836500000000000000000000000 : ℝ)*base62 + (577843727021/1485650000000000000000000 : ℝ)*base65 + (23684860007467/307000000000000000000000000 : ℝ)*base67 + (307153295334149/297130000000000000000000000 : ℝ)*base68 + (592164647716450661/2214732737500000000000000000000 : ℝ)*base71 + (18654261186217/178890000000000000000000000 : ℝ)*base72 + (348561202329493/460500000000000000000000000 : ℝ)*base74 + (109903797594081/149075000000000000000000000 : ℝ)*base76 + (2383475945491618837/5491923000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (10101/12500000000000000 : ℝ)*base87 + (10101/12500000000000000 : ℝ)*base89 + (10101/12500000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s5_0,ratio_s5_1,ratio_s5_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev4 : (0 : ℝ) ≤ ((17889/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(17889/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(921/1250 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(921/1250 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-29713/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-29713/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((45543/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(45543/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9887/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(9887/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-4149/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-4149/12500 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c304060_s5 p hpa hpb X hX hprev4

#print axioms solution
