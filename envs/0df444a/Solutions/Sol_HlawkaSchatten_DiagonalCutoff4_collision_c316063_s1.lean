-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c316063_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:07:58.28396+00:00
-- url     : https://prove2.me/submissions/b54299a0-2c92-4807-a71f-a8fdc6418f52

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
theorem collision_support_c316063_s1_s1_0 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-726803539/10000000000 : ℝ)*x 0 + (5408111/9765625 : ℝ)*x 1 + (2837729237/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (726803539/10000000000 : ℝ)^77 ≤ (913507946203/25000000000000 : ℝ)^61 := by
    have hnat : (726803539 : ℕ)^77*25000000000000^61 ≤ 913507946203^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      726803539 10000000000 913507946203 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5408111/9765625 : ℝ)^77 ≤ (23713538230763/50000000000000 : ℝ)^61 := by
    have hnat : (5408111 : ℕ)^77*50000000000000^61 ≤ 23713538230763^61*9765625^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408111 9765625 23713538230763 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2837729237/5000000000 : ℝ)^77 ≤ (6114861467477/12500000000000 : ℝ)^61 := by
    have hnat : (2837729237 : ℕ)^77*12500000000000^61 ≤ 6114861467477^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2837729237 5000000000 6114861467477 12500000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-726803539/10000000000 : ℝ), (5408111/9765625 : ℝ), (2837729237/5000000000 : ℝ)] ![(913507946203/25000000000000 : ℝ), (23713538230763/50000000000000 : ℝ), (6114861467477/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-726803539/10000000000 : ℝ)|^77 ≤ (913507946203/25000000000000 : ℝ)^61
        have hw : |(-726803539/10000000000 : ℝ)|=(726803539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5408111/9765625 : ℝ)|^77 ≤ (23713538230763/50000000000000 : ℝ)^61
        have hw : |(5408111/9765625 : ℝ)|=(5408111/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2837729237/5000000000 : ℝ)|^77 ≤ (6114861467477/12500000000000 : ℝ)^61
        have hw : |(2837729237/5000000000 : ℝ)|=(2837729237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316063_s1_s1_1 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (86524617/156250000 : ℝ)*x 0 + (-359460773/5000000000 : ℝ)*x 1 + (113607537/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (86524617/156250000 : ℝ)^77 ≤ (47423507155403/100000000000000 : ℝ)^61 := by
    have hnat : (86524617 : ℕ)^77*100000000000000^61 ≤ 47423507155403^61*156250000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86524617 156250000 47423507155403 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (359460773/5000000000 : ℝ)^77 ≤ (3604082135267/100000000000000 : ℝ)^61 := by
    have hnat : (359460773 : ℕ)^77*100000000000000^61 ≤ 3604082135267^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      359460773 5000000000 3604082135267 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (113607537/200000000 : ℝ)^77 ≤ (48972410694391/100000000000000 : ℝ)^61 := by
    have hnat : (113607537 : ℕ)^77*100000000000000^61 ≤ 48972410694391^61*200000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113607537 200000000 48972410694391 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(86524617/156250000 : ℝ), (-359460773/5000000000 : ℝ), (113607537/200000000 : ℝ)] ![(47423507155403/100000000000000 : ℝ), (3604082135267/100000000000000 : ℝ), (48972410694391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(86524617/156250000 : ℝ)|^77 ≤ (47423507155403/100000000000000 : ℝ)^61
        have hw : |(86524617/156250000 : ℝ)|=(86524617/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-359460773/5000000000 : ℝ)|^77 ≤ (3604082135267/100000000000000 : ℝ)^61
        have hw : |(-359460773/5000000000 : ℝ)|=(359460773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(113607537/200000000 : ℝ)|^77 ≤ (48972410694391/100000000000000 : ℝ)^61
        have hw : |(113607537/200000000 : ℝ)|=(113607537/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316063_s1_s1_2 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5584732913/10000000000 : ℝ)*x 0 + (1415537029/2500000000 : ℝ)*x 1 + (-133829771/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5584732913/10000000000 : ℝ)^77 ≤ (47933857882051/100000000000000 : ℝ)^61 := by
    have hnat : (5584732913 : ℕ)^77*100000000000000^61 ≤ 47933857882051^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5584732913 10000000000 47933857882051 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1415537029/2500000000 : ℝ)^77 ≤ (12193529265203/25000000000000 : ℝ)^61 := by
    have hnat : (1415537029 : ℕ)^77*25000000000000^61 ≤ 12193529265203^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1415537029 2500000000 12193529265203 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (133829771/2000000000 : ℝ)^77 ≤ (3292025038899/100000000000000 : ℝ)^61 := by
    have hnat : (133829771 : ℕ)^77*100000000000000^61 ≤ 3292025038899^61*2000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133829771 2000000000 3292025038899 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5584732913/10000000000 : ℝ), (1415537029/2500000000 : ℝ), (-133829771/2000000000 : ℝ)] ![(47933857882051/100000000000000 : ℝ), (12193529265203/25000000000000 : ℝ), (3292025038899/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5584732913/10000000000 : ℝ)|^77 ≤ (47933857882051/100000000000000 : ℝ)^61
        have hw : |(5584732913/10000000000 : ℝ)|=(5584732913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1415537029/2500000000 : ℝ)|^77 ≤ (12193529265203/25000000000000 : ℝ)^61
        have hw : |(1415537029/2500000000 : ℝ)|=(1415537029/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-133829771/2000000000 : ℝ)|^77 ≤ (3292025038899/100000000000000 : ℝ)^61
        have hw : |(-133829771/2000000000 : ℝ)|=(133829771/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316063_s1_s1_7 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1191445649/10000000000 : ℝ)*x 0 + (3301059219/10000000000 : ℝ)*x 1 + (3705029161/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1191445649/10000000000 : ℝ)^77 ≤ (1704798522029/25000000000000 : ℝ)^61 := by
    have hnat : (1191445649 : ℕ)^77*25000000000000^61 ≤ 1704798522029^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1191445649 10000000000 1704798522029 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3301059219/10000000000 : ℝ)^77 ≤ (24683028648477/100000000000000 : ℝ)^61 := by
    have hnat : (3301059219 : ℕ)^77*100000000000000^61 ≤ 24683028648477^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3301059219 10000000000 24683028648477 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3705029161/5000000000 : ℝ)^77 ≤ (68497777259101/100000000000000 : ℝ)^61 := by
    have hnat : (3705029161 : ℕ)^77*100000000000000^61 ≤ 68497777259101^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3705029161 5000000000 68497777259101 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1191445649/10000000000 : ℝ), (3301059219/10000000000 : ℝ), (3705029161/5000000000 : ℝ)] ![(1704798522029/25000000000000 : ℝ), (24683028648477/100000000000000 : ℝ), (68497777259101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1191445649/10000000000 : ℝ)|^77 ≤ (1704798522029/25000000000000 : ℝ)^61
        have hw : |(-1191445649/10000000000 : ℝ)|=(1191445649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3301059219/10000000000 : ℝ)|^77 ≤ (24683028648477/100000000000000 : ℝ)^61
        have hw : |(3301059219/10000000000 : ℝ)|=(3301059219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3705029161/5000000000 : ℝ)|^77 ≤ (68497777259101/100000000000000 : ℝ)^61
        have hw : |(3705029161/5000000000 : ℝ)|=(3705029161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316063_s1_s1_8 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (786526449/2000000000 : ℝ)*x 0 + (-9222599/500000000 : ℝ)*x 1 + (3707933691/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (786526449/2000000000 : ℝ)^77 ≤ (30787240776251/100000000000000 : ℝ)^61 := by
    have hnat : (786526449 : ℕ)^77*100000000000000^61 ≤ 30787240776251^61*2000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      786526449 2000000000 30787240776251 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9222599/500000000 : ℝ)^77 ≤ (647191858307/100000000000000 : ℝ)^61 := by
    have hnat : (9222599 : ℕ)^77*100000000000000^61 ≤ 647191858307^61*500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9222599 500000000 647191858307 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3707933691/5000000000 : ℝ)^77 ≤ (68565567354483/100000000000000 : ℝ)^61 := by
    have hnat : (3707933691 : ℕ)^77*100000000000000^61 ≤ 68565567354483^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3707933691 5000000000 68565567354483 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(786526449/2000000000 : ℝ), (-9222599/500000000 : ℝ), (3707933691/5000000000 : ℝ)] ![(30787240776251/100000000000000 : ℝ), (647191858307/100000000000000 : ℝ), (68565567354483/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(786526449/2000000000 : ℝ)|^77 ≤ (30787240776251/100000000000000 : ℝ)^61
        have hw : |(786526449/2000000000 : ℝ)|=(786526449/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-9222599/500000000 : ℝ)|^77 ≤ (647191858307/100000000000000 : ℝ)^61
        have hw : |(-9222599/500000000 : ℝ)|=(9222599/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3707933691/5000000000 : ℝ)|^77 ≤ (68565567354483/100000000000000 : ℝ)^61
        have hw : |(3707933691/5000000000 : ℝ)|=(3707933691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316063_s1_s1_9 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (114909103/312500000 : ℝ)*x 0 + (7664128621/10000000000 : ℝ)*x 1 + (-21052089/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (114909103/312500000 : ℝ)^77 ≤ (3535479880711/12500000000000 : ℝ)^61 := by
    have hnat : (114909103 : ℕ)^77*12500000000000^61 ≤ 3535479880711^61*312500000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114909103 312500000 3535479880711 12500000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7664128621/10000000000 : ℝ)^77 ≤ (35737810815869/50000000000000 : ℝ)^61 := by
    have hnat : (7664128621 : ℕ)^77*50000000000000^61 ≤ 35737810815869^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7664128621 10000000000 35737810815869 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21052089/2500000000 : ℝ)^77 ≤ (120269654179/50000000000000 : ℝ)^61 := by
    have hnat : (21052089 : ℕ)^77*50000000000000^61 ≤ 120269654179^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21052089 2500000000 120269654179 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(114909103/312500000 : ℝ), (7664128621/10000000000 : ℝ), (-21052089/2500000000 : ℝ)] ![(3535479880711/12500000000000 : ℝ), (35737810815869/50000000000000 : ℝ), (120269654179/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(114909103/312500000 : ℝ)|^77 ≤ (3535479880711/12500000000000 : ℝ)^61
        have hw : |(114909103/312500000 : ℝ)|=(114909103/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7664128621/10000000000 : ℝ)|^77 ≤ (35737810815869/50000000000000 : ℝ)^61
        have hw : |(7664128621/10000000000 : ℝ)|=(7664128621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-21052089/2500000000 : ℝ)|^77 ≤ (120269654179/50000000000000 : ℝ)^61
        have hw : |(-21052089/2500000000 : ℝ)|=(21052089/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316063_s1_s1_13 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1862718321/5000000000 : ℝ)*x 0 + (13373337/19531250 : ℝ)*x 1 + (12135331/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1862718321/5000000000 : ℝ)^77 ≤ (28754052778767/100000000000000 : ℝ)^61 := by
    have hnat : (1862718321 : ℕ)^77*100000000000000^61 ≤ 28754052778767^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1862718321 5000000000 28754052778767 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (13373337/19531250 : ℝ)^77 ≤ (61996156511297/100000000000000 : ℝ)^61 := by
    have hnat : (13373337 : ℕ)^77*100000000000000^61 ≤ 61996156511297^61*19531250^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13373337 19531250 61996156511297 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (12135331/80000000 : ℝ)^77 ≤ (1849958139187/20000000000000 : ℝ)^61 := by
    have hnat : (12135331 : ℕ)^77*20000000000000^61 ≤ 1849958139187^61*80000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12135331 80000000 1849958139187 20000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1862718321/5000000000 : ℝ), (13373337/19531250 : ℝ), (12135331/80000000 : ℝ)] ![(28754052778767/100000000000000 : ℝ), (61996156511297/100000000000000 : ℝ), (1849958139187/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1862718321/5000000000 : ℝ)|^77 ≤ (28754052778767/100000000000000 : ℝ)^61
        have hw : |(1862718321/5000000000 : ℝ)|=(1862718321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(13373337/19531250 : ℝ)|^77 ≤ (61996156511297/100000000000000 : ℝ)^61
        have hw : |(13373337/19531250 : ℝ)|=(13373337/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(12135331/80000000 : ℝ)|^77 ≤ (1849958139187/20000000000000 : ℝ)^61
        have hw : |(12135331/80000000 : ℝ)|=(12135331/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316063_s1_s1_14 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-8668291/500000000 : ℝ)*x 0 + (1929292777/5000000000 : ℝ)*x 1 + (7482504273/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8668291/500000000 : ℝ)^77 ≤ (299241803531/50000000000000 : ℝ)^61 := by
    have hnat : (8668291 : ℕ)^77*50000000000000^61 ≤ 299241803531^61*500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8668291 500000000 299241803531 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1929292777/5000000000 : ℝ)^77 ≤ (15028660434591/50000000000000 : ℝ)^61 := by
    have hnat : (1929292777 : ℕ)^77*50000000000000^61 ≤ 15028660434591^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1929292777 5000000000 15028660434591 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7482504273/10000000000 : ℝ)^77 ≤ (4334012219591/6250000000000 : ℝ)^61 := by
    have hnat : (7482504273 : ℕ)^77*6250000000000^61 ≤ 4334012219591^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7482504273 10000000000 4334012219591 6250000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-8668291/500000000 : ℝ), (1929292777/5000000000 : ℝ), (7482504273/10000000000 : ℝ)] ![(299241803531/50000000000000 : ℝ), (15028660434591/50000000000000 : ℝ), (4334012219591/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-8668291/500000000 : ℝ)|^77 ≤ (299241803531/50000000000000 : ℝ)^61
        have hw : |(-8668291/500000000 : ℝ)|=(8668291/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1929292777/5000000000 : ℝ)|^77 ≤ (15028660434591/50000000000000 : ℝ)^61
        have hw : |(1929292777/5000000000 : ℝ)|=(1929292777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7482504273/10000000000 : ℝ)|^77 ≤ (4334012219591/6250000000000 : ℝ)^61
        have hw : |(7482504273/10000000000 : ℝ)|=(7482504273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316063_s1_s1_15 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3191411849/10000000000 : ℝ)*x 0 + (-603674891/5000000000 : ℝ)*x 1 + (7488388863/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3191411849/10000000000 : ℝ)^77 ≤ (5913165081357/25000000000000 : ℝ)^61 := by
    have hnat : (3191411849 : ℕ)^77*25000000000000^61 ≤ 5913165081357^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3191411849 10000000000 5913165081357 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (603674891/5000000000 : ℝ)^77 ≤ (1733574286071/25000000000000 : ℝ)^61 := by
    have hnat : (603674891 : ℕ)^77*25000000000000^61 ≤ 1733574286071^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      603674891 5000000000 1733574286071 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7488388863/10000000000 : ℝ)^77 ≤ (69413042513757/100000000000000 : ℝ)^61 := by
    have hnat : (7488388863 : ℕ)^77*100000000000000^61 ≤ 69413042513757^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7488388863 10000000000 69413042513757 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3191411849/10000000000 : ℝ), (-603674891/5000000000 : ℝ), (7488388863/10000000000 : ℝ)] ![(5913165081357/25000000000000 : ℝ), (1733574286071/25000000000000 : ℝ), (69413042513757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3191411849/10000000000 : ℝ)|^77 ≤ (5913165081357/25000000000000 : ℝ)^61
        have hw : |(3191411849/10000000000 : ℝ)|=(3191411849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-603674891/5000000000 : ℝ)|^77 ≤ (1733574286071/25000000000000 : ℝ)^61
        have hw : |(-603674891/5000000000 : ℝ)|=(603674891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7488388863/10000000000 : ℝ)|^77 ≤ (69413042513757/100000000000000 : ℝ)^61
        have hw : |(7488388863/10000000000 : ℝ)|=(7488388863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316063_s1_s1_16 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (14758393/20000000 : ℝ)*x 0 + (4007258489/10000000000 : ℝ)*x 1 + (-109633837/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (14758393/20000000 : ℝ)^77 ≤ (68137862397051/100000000000000 : ℝ)^61 := by
    have hnat : (14758393 : ℕ)^77*100000000000000^61 ≤ 68137862397051^61*20000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14758393 20000000 68137862397051 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4007258489/10000000000 : ℝ)^77 ≤ (31526530027853/100000000000000 : ℝ)^61 := by
    have hnat : (4007258489 : ℕ)^77*100000000000000^61 ≤ 31526530027853^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4007258489 10000000000 31526530027853 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (109633837/10000000000 : ℝ)^77 ≤ (6712151053/2000000000000 : ℝ)^61 := by
    have hnat : (109633837 : ℕ)^77*2000000000000^61 ≤ 6712151053^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109633837 10000000000 6712151053 2000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(14758393/20000000 : ℝ), (4007258489/10000000000 : ℝ), (-109633837/10000000000 : ℝ)] ![(68137862397051/100000000000000 : ℝ), (31526530027853/100000000000000 : ℝ), (6712151053/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(14758393/20000000 : ℝ)|^77 ≤ (68137862397051/100000000000000 : ℝ)^61
        have hw : |(14758393/20000000 : ℝ)|=(14758393/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4007258489/10000000000 : ℝ)|^77 ≤ (31526530027853/100000000000000 : ℝ)^61
        have hw : |(4007258489/10000000000 : ℝ)|=(4007258489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-109633837/10000000000 : ℝ)|^77 ≤ (6712151053/2000000000000 : ℝ)^61
        have hw : |(-109633837/10000000000 : ℝ)|=(109633837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316063_s1_s1_20 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7385050293/10000000000 : ℝ)*x 0 + (1541758921/5000000000 : ℝ)*x 1 + (1503430409/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7385050293/10000000000 : ℝ)^77 ≤ (68206099856987/100000000000000 : ℝ)^61 := by
    have hnat : (7385050293 : ℕ)^77*100000000000000^61 ≤ 68206099856987^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7385050293 10000000000 68206099856987 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1541758921/5000000000 : ℝ)^77 ≤ (11323895968257/50000000000000 : ℝ)^61 := by
    have hnat : (1541758921 : ℕ)^77*50000000000000^61 ≤ 11323895968257^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1541758921 5000000000 11323895968257 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1503430409/10000000000 : ℝ)^77 ≤ (9146108200263/100000000000000 : ℝ)^61 := by
    have hnat : (1503430409 : ℕ)^77*100000000000000^61 ≤ 9146108200263^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1503430409 10000000000 9146108200263 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7385050293/10000000000 : ℝ), (1541758921/5000000000 : ℝ), (1503430409/10000000000 : ℝ)] ![(68206099856987/100000000000000 : ℝ), (11323895968257/50000000000000 : ℝ), (9146108200263/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7385050293/10000000000 : ℝ)|^77 ≤ (68206099856987/100000000000000 : ℝ)^61
        have hw : |(7385050293/10000000000 : ℝ)|=(7385050293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1541758921/5000000000 : ℝ)|^77 ≤ (11323895968257/50000000000000 : ℝ)^61
        have hw : |(1541758921/5000000000 : ℝ)|=(1541758921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1503430409/10000000000 : ℝ)|^77 ≤ (9146108200263/100000000000000 : ℝ)^61
        have hw : |(1503430409/10000000000 : ℝ)|=(1503430409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316063_s1_s1_21 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-76384703/5000000000 : ℝ)*x 0 + (1689469451/2500000000 : ℝ)*x 1 + (1173945379/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (76384703/5000000000 : ℝ)^77 ≤ (102034739897/20000000000000 : ℝ)^61 := by
    have hnat : (76384703 : ℕ)^77*20000000000000^61 ≤ 102034739897^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      76384703 5000000000 102034739897 20000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1689469451/2500000000 : ℝ)^77 ≤ (7622201671939/12500000000000 : ℝ)^61 := by
    have hnat : (1689469451 : ℕ)^77*12500000000000^61 ≤ 7622201671939^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1689469451 2500000000 7622201671939 12500000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1173945379/2500000000 : ℝ)^77 ≤ (19256106459067/50000000000000 : ℝ)^61 := by
    have hnat : (1173945379 : ℕ)^77*50000000000000^61 ≤ 19256106459067^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1173945379 2500000000 19256106459067 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-76384703/5000000000 : ℝ), (1689469451/2500000000 : ℝ), (1173945379/2500000000 : ℝ)] ![(102034739897/20000000000000 : ℝ), (7622201671939/12500000000000 : ℝ), (19256106459067/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-76384703/5000000000 : ℝ)|^77 ≤ (102034739897/20000000000000 : ℝ)^61
        have hw : |(-76384703/5000000000 : ℝ)|=(76384703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1689469451/2500000000 : ℝ)|^77 ≤ (7622201671939/12500000000000 : ℝ)^61
        have hw : |(1689469451/2500000000 : ℝ)|=(1689469451/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1173945379/2500000000 : ℝ)|^77 ≤ (19256106459067/50000000000000 : ℝ)^61
        have hw : |(1173945379/2500000000 : ℝ)|=(1173945379/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316063_s1_s1_22 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7383298379/10000000000 : ℝ)*x 0 + (-16138773/2000000000 : ℝ)*x 1 + (4013284581/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7383298379/10000000000 : ℝ)^77 ≤ (68185676368723/100000000000000 : ℝ)^61 := by
    have hnat : (7383298379 : ℕ)^77*100000000000000^61 ≤ 68185676368723^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7383298379 10000000000 68185676368723 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16138773/2000000000 : ℝ)^77 ≤ (227937131917/100000000000000 : ℝ)^61 := by
    have hnat : (16138773 : ℕ)^77*100000000000000^61 ≤ 227937131917^61*2000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16138773 2000000000 227937131917 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4013284581/10000000000 : ℝ)^77 ≤ (31586386494131/100000000000000 : ℝ)^61 := by
    have hnat : (4013284581 : ℕ)^77*100000000000000^61 ≤ 31586386494131^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4013284581 10000000000 31586386494131 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7383298379/10000000000 : ℝ), (-16138773/2000000000 : ℝ), (4013284581/10000000000 : ℝ)] ![(68185676368723/100000000000000 : ℝ), (227937131917/100000000000000 : ℝ), (31586386494131/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7383298379/10000000000 : ℝ)|^77 ≤ (68185676368723/100000000000000 : ℝ)^61
        have hw : |(7383298379/10000000000 : ℝ)|=(7383298379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-16138773/2000000000 : ℝ)|^77 ≤ (227937131917/100000000000000 : ℝ)^61
        have hw : |(-16138773/2000000000 : ℝ)|=(16138773/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4013284581/10000000000 : ℝ)|^77 ≤ (31586386494131/100000000000000 : ℝ)^61
        have hw : |(4013284581/10000000000 : ℝ)|=(4013284581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316063_s1_s1_23 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1540313519/5000000000 : ℝ)*x 0 + (3797879577/5000000000 : ℝ)*x 1 + (-587965469/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1540313519/5000000000 : ℝ)^77 ≤ (11310496871299/50000000000000 : ℝ)^61 := by
    have hnat : (1540313519 : ℕ)^77*50000000000000^61 ≤ 11310496871299^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1540313519 5000000000 11310496871299 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3797879577/5000000000 : ℝ)^77 ≤ (35335854614003/50000000000000 : ℝ)^61 := by
    have hnat : (3797879577 : ℕ)^77*50000000000000^61 ≤ 35335854614003^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3797879577 5000000000 35335854614003 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (587965469/5000000000 : ℝ)^77 ≤ (6707297023411/100000000000000 : ℝ)^61 := by
    have hnat : (587965469 : ℕ)^77*100000000000000^61 ≤ 6707297023411^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      587965469 5000000000 6707297023411 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1540313519/5000000000 : ℝ), (3797879577/5000000000 : ℝ), (-587965469/5000000000 : ℝ)] ![(11310496871299/50000000000000 : ℝ), (35335854614003/50000000000000 : ℝ), (6707297023411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1540313519/5000000000 : ℝ)|^77 ≤ (11310496871299/50000000000000 : ℝ)^61
        have hw : |(1540313519/5000000000 : ℝ)|=(1540313519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3797879577/5000000000 : ℝ)|^77 ≤ (35335854614003/50000000000000 : ℝ)^61
        have hw : |(3797879577/5000000000 : ℝ)|=(3797879577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-587965469/5000000000 : ℝ)|^77 ≤ (6707297023411/100000000000000 : ℝ)^61
        have hw : |(-587965469/5000000000 : ℝ)|=(587965469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316063_s1_s1_27 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7540232969/10000000000 : ℝ)*x 0 + (1226558503/5000000000 : ℝ)*x 1 + (1987727373/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7540232969/10000000000 : ℝ)^77 ≤ (17505051781239/25000000000000 : ℝ)^61 := by
    have hnat : (7540232969 : ℕ)^77*25000000000000^61 ≤ 17505051781239^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7540232969 10000000000 17505051781239 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1226558503/5000000000 : ℝ)^77 ≤ (16968535642177/100000000000000 : ℝ)^61 := by
    have hnat : (1226558503 : ℕ)^77*100000000000000^61 ≤ 16968535642177^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1226558503 5000000000 16968535642177 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1987727373/10000000000 : ℝ)^77 ≤ (3252814305551/25000000000000 : ℝ)^61 := by
    have hnat : (1987727373 : ℕ)^77*25000000000000^61 ≤ 3252814305551^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1987727373 10000000000 3252814305551 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7540232969/10000000000 : ℝ), (1226558503/5000000000 : ℝ), (1987727373/10000000000 : ℝ)] ![(17505051781239/25000000000000 : ℝ), (16968535642177/100000000000000 : ℝ), (3252814305551/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7540232969/10000000000 : ℝ)|^77 ≤ (17505051781239/25000000000000 : ℝ)^61
        have hw : |(7540232969/10000000000 : ℝ)|=(7540232969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1226558503/5000000000 : ℝ)|^77 ≤ (16968535642177/100000000000000 : ℝ)^61
        have hw : |(1226558503/5000000000 : ℝ)|=(1226558503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1987727373/10000000000 : ℝ)|^77 ≤ (3252814305551/25000000000000 : ℝ)^61
        have hw : |(1987727373/10000000000 : ℝ)|=(1987727373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c316063_s1 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((2444/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2444/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19463/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(19463/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1889/2500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(1889/2500 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((58269/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(58269/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(11721/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(11721/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(11237/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(11237/20000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (1587/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (1587/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (1587/2000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (1587/2000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (1587/2000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (1587/2000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (173433/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  have s1_pow0 : (2444/3125 : ℝ) ^ (19/4 : ℝ) ≤ (7778271769695904699/25000000000000000000 : ℝ) := by
    have hpowers : (2444/3125 : ℝ)^19 ≤ (7778271769695904699/25000000000000000000 : ℝ)^4 := by
      have hnat : (2444 : ℕ)^19*25000000000000000000^4 ≤ 7778271769695904699^4*3125^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2444 3125 7778271769695904699 25000000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2444/3125 : ℝ)) (X := (7778271769695904699/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner0a : (32778271769695904699/25000000000000000000 : ℝ) ≤ (5293435094529383/5000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (32778271769695904699/25000000000000000000 : ℝ)^4 ≤ (5293435094529383/5000000000000000 : ℝ)^19 := by
      have hnat : (32778271769695904699 : ℕ)^4*5000000000000000^19 ≤ 5293435094529383^19*25000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        32778271769695904699 25000000000000000000 5293435094529383 5000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5293435094529383/5000000000000000 : ℝ)) (X := (32778271769695904699/25000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner0b : (20278271769695904699/12500000000000000000 : ℝ) ≤ (5536126291458683/5000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (20278271769695904699/12500000000000000000 : ℝ)^4 ≤ (5536126291458683/5000000000000000 : ℝ)^19 := by
      have hnat : (20278271769695904699 : ℕ)^4*5000000000000000^19 ≤ 5536126291458683^19*12500000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20278271769695904699 12500000000000000000 5536126291458683 5000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5536126291458683/5000000000000000 : ℝ)) (X := (20278271769695904699/12500000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(293435094529383/3910400000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(2426911969293/39104000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (2444/3125 : ℝ)) (alpha := (293435094529383/3910400000000000 : ℝ)) (beta := (2426911969293/39104000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (2444/3125 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(293435094529383/3910400000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(2426911969293/39104000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (19463/25000 : ℝ) ^ (19/4 : ℝ) ≤ (30446082956760205433/100000000000000000000 : ℝ) := by
    have hpowers : (19463/25000 : ℝ)^19 ≤ (30446082956760205433/100000000000000000000 : ℝ)^4 := by
      have hnat : (19463 : ℕ)^19*100000000000000000000^4 ≤ 30446082956760205433^4*25000^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19463 25000 30446082956760205433 100000000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19463/25000 : ℝ)) (X := (30446082956760205433/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner1a : (130446082956760205433/100000000000000000000 : ℝ) ≤ (42302035313689/40000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (130446082956760205433/100000000000000000000 : ℝ)^4 ≤ (42302035313689/40000000000000 : ℝ)^19 := by
      have hnat : (130446082956760205433 : ℕ)^4*40000000000000^19 ≤ 42302035313689^19*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        130446082956760205433 100000000000000000000 42302035313689 40000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (42302035313689/40000000000000 : ℝ)) (X := (130446082956760205433/100000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner1b : (80446082956760205433/50000000000000000000 : ℝ) ≤ (2210604383424387/2000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (80446082956760205433/50000000000000000000 : ℝ)^4 ≤ (2210604383424387/2000000000000000 : ℝ)^19 := by
      have hnat : (80446082956760205433 : ℕ)^4*2000000000000000^19 ≤ 2210604383424387^19*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        80446082956760205433 50000000000000000000 2210604383424387 2000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2210604383424387/2000000000000000 : ℝ)) (X := (80446082956760205433/50000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(2302035313689/31140800000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(95502617739937/1557040000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (19463/25000 : ℝ)) (alpha := (2302035313689/31140800000000 : ℝ)) (beta := (95502617739937/1557040000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (19463/25000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(2302035313689/31140800000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(95502617739937/1557040000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (1889/2500 : ℝ) ^ (19/4 : ℝ) ≤ (6604299616243598307/25000000000000000000 : ℝ) := by
    have hpowers : (1889/2500 : ℝ)^19 ≤ (6604299616243598307/25000000000000000000 : ℝ)^4 := by
      have hnat : (1889 : ℕ)^19*25000000000000000000^4 ≤ 6604299616243598307^4*2500^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1889 2500 6604299616243598307 25000000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1889/2500 : ℝ)) (X := (6604299616243598307/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner2a : (31604299616243598307/25000000000000000000 : ℝ) ≤ (10505890649630739/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (31604299616243598307/25000000000000000000 : ℝ)^4 ≤ (10505890649630739/10000000000000000 : ℝ)^19 := by
      have hnat : (31604299616243598307 : ℕ)^4*10000000000000000^19 ≤ 10505890649630739^19*25000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31604299616243598307 25000000000000000000 10505890649630739 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10505890649630739/10000000000000000 : ℝ)) (X := (31604299616243598307/25000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner2b : (19104299616243598307/12500000000000000000 : ℝ) ≤ (5467054400586049/5000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (19104299616243598307/12500000000000000000 : ℝ)^4 ≤ (5467054400586049/5000000000000000 : ℝ)^19 := by
      have hnat : (19104299616243598307 : ℕ)^4*5000000000000000^19 ≤ 5467054400586049^19*12500000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19104299616243598307 12500000000000000000 5467054400586049 5000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5467054400586049/5000000000000000 : ℝ)) (X := (19104299616243598307/12500000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(505890649630739/7556000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(428218151541359/7556000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (1889/2500 : ℝ)) (alpha := (505890649630739/7556000000000000 : ℝ)) (beta := (428218151541359/7556000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1889/2500 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(505890649630739/7556000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(428218151541359/7556000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-726803539/10000000000 : ℝ)*X 0 0+(5408111/9765625 : ℝ)*X 0 1+(2837729237/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316063_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((86524617/156250000 : ℝ)*X 1 0+(-359460773/5000000000 : ℝ)*X 1 1+(113607537/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316063_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((5584732913/10000000000 : ℝ)*X 2 0+(1415537029/2500000000 : ℝ)*X 2 1+(-133829771/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316063_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-1191445649/10000000000 : ℝ)*X 0 0+(3301059219/10000000000 : ℝ)*X 0 1+(3705029161/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316063_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((786526449/2000000000 : ℝ)*X 1 0+(-9222599/500000000 : ℝ)*X 1 1+(3707933691/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316063_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((114909103/312500000 : ℝ)*X 2 0+(7664128621/10000000000 : ℝ)*X 2 1+(-21052089/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316063_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((1862718321/5000000000 : ℝ)*X 0 0+(13373337/19531250 : ℝ)*X 0 1+(12135331/80000000 : ℝ)*X 0 2+(1862718321/5000000000 : ℝ)*X 1 0+(13373337/19531250 : ℝ)*X 1 1+(12135331/80000000 : ℝ)*X 1 2+(1862718321/5000000000 : ℝ)*X 2 0+(13373337/19531250 : ℝ)*X 2 1+(12135331/80000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316063_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-8668291/500000000 : ℝ)*X 0 0+(1929292777/5000000000 : ℝ)*X 0 1+(7482504273/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316063_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((3191411849/10000000000 : ℝ)*X 1 0+(-603674891/5000000000 : ℝ)*X 1 1+(7488388863/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316063_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((14758393/20000000 : ℝ)*X 2 0+(4007258489/10000000000 : ℝ)*X 2 1+(-109633837/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316063_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((7385050293/10000000000 : ℝ)*X 0 0+(1541758921/5000000000 : ℝ)*X 0 1+(1503430409/10000000000 : ℝ)*X 0 2+(7385050293/10000000000 : ℝ)*X 1 0+(1541758921/5000000000 : ℝ)*X 1 1+(1503430409/10000000000 : ℝ)*X 1 2+(7385050293/10000000000 : ℝ)*X 2 0+(1541758921/5000000000 : ℝ)*X 2 1+(1503430409/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316063_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-76384703/5000000000 : ℝ)*X 0 0+(1689469451/2500000000 : ℝ)*X 0 1+(1173945379/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316063_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((7383298379/10000000000 : ℝ)*X 1 0+(-16138773/2000000000 : ℝ)*X 1 1+(4013284581/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316063_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((1540313519/5000000000 : ℝ)*X 2 0+(3797879577/5000000000 : ℝ)*X 2 1+(-587965469/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316063_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((7540232969/10000000000 : ℝ)*X 0 0+(1226558503/5000000000 : ℝ)*X 0 1+(1987727373/10000000000 : ℝ)*X 0 2+(7540232969/10000000000 : ℝ)*X 1 0+(1226558503/5000000000 : ℝ)*X 1 1+(1987727373/10000000000 : ℝ)*X 1 2+(7540232969/10000000000 : ℝ)*X 2 0+(1226558503/5000000000 : ℝ)*X 2 1+(1987727373/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316063_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((58269/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(58269/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (623940958704816704493813270141/71884114806400000000000000000000000 : ℝ) := by norm_num
    linear_combination (652315824021/1000000000000 : ℝ)*(base7) + (680231/1000000000000 : ℝ)*(base50) + (79703380017/1000000000000 : ℝ)*(base60) + (2046107434911/1000000000000 : ℝ)*(major_s1_0) + (2046107434911/1000000000000 : ℝ)*(major_s1_1) + (2046107434911/1000000000000 : ℝ)*(major_s1_2) + (1521939/250000000000 : ℝ)*(sp_s1_0) + (256073477771/100000000000 : ℝ)*(sp_s1_7) + (1280392251229/500000000000 : ℝ)*(sp_s1_8) + (2560783415089/1000000000000 : ℝ)*(sp_s1_9) + (1806632683107/1000000000000 : ℝ)*(sp_s1_13) + (8790193/200000000000 : ℝ)*(sp_s1_14) + (313973/1000000000000 : ℝ)*(sp_s1_22) + (1401343/1000000000000 : ℝ)*(sp_s1_23) + (1154316859087/1000000000000 : ℝ)*(f.failure) + (160049051027/62500000000 : ℝ)*(f.sum) + (42739638596369825527/147062428000000000000000000000000 : ℝ)*base63 + (1396028002051151/7556000000000000000000000000 : ℝ)*base64 + (121912546306671/1557040000000000000000000000 : ℝ)*base67 + (2685707021921629/7556000000000000000000000000 : ℝ)*base69 + (83559286456674603/36933728000000000000000000000000 : ℝ)*base70 + (23426328267873/195520000000000000000000000 : ℝ)*base72 + (350430504056369/778520000000000000000000000 : ℝ)*base74 + (1836973569511047/3910400000000000000000000000 : ℝ)*base76 + (402203785368415021/3805405760000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (84359/100000000000000000 : ℝ)*base87 + (84359/100000000000000000 : ℝ)*base89 + (84359/100000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(11721/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(11721/20000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (617067730847615964566616069429/89855143508000000000000000000000000 : ℝ) := by norm_num
    linear_combination (679319538637/1000000000000 : ℝ)*(base7) + (8639/200000000000 : ℝ)*(base39) + (585541/1000000000000 : ℝ)*(base49) + (489822797721/250000000000 : ℝ)*(major_s1_0) + (489822797721/250000000000 : ℝ)*(major_s1_1) + (489822797721/250000000000 : ℝ)*(major_s1_2) + (24639/10000000000 : ℝ)*(sp_s1_1) + (14043587/500000000000 : ℝ)*(sp_s1_8) + (2420518921921/1000000000000 : ℝ)*(sp_s1_14) + (2420488875051/1000000000000 : ℝ)*(sp_s1_15) + (1210259713063/500000000000 : ℝ)*(sp_s1_16) + (1784632087131/1000000000000 : ℝ)*(sp_s1_20) + (100841/200000000000 : ℝ)*(sp_s1_21) + (26699537/1000000000000 : ℝ)*(sp_s1_27) + (34541851501/31250000000 : ℝ)*(f.failure) + (1210259713063/500000000000 : ℝ)*(f.sum) + (9102210624730717497/36765607000000000000000000000000 : ℝ)*base63 + (809146926458639/1889000000000000000000000000 : ℝ)*base65 + (307154604927459/389260000000000000000000000 : ℝ)*base67 + (2133072359547319/1889000000000000000000000000 : ℝ)*base69 + (547234027994877267/9233432000000000000000000000000 : ℝ)*base71 + (76505260917697/48880000000000000000000000 : ℝ)*base73 + (131955529845457/194630000000000000000000000 : ℝ)*base75 + (525589028685263/977600000000000000000000000 : ℝ)*base77 + (599358296636359691/951351440000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (257/3125000000000000 : ℝ)*base87 + (257/3125000000000000 : ℝ)*base89 + (257/3125000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(11237/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(11237/20000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (96117147322996673531871361449/6911934116000000000000000000000000 : ℝ) := by norm_num
    linear_combination (83543482691/125000000000 : ℝ)*(base7) + (157913264957/1000000000000 : ℝ)*(base40) + (144803/125000000000 : ℝ)*(base49) + (36351/125000000000 : ℝ)*(base59) + (1866707360193/1000000000000 : ℝ)*(major_s1_0) + (1866707360193/1000000000000 : ℝ)*(major_s1_1) + (1866707360193/1000000000000 : ℝ)*(major_s1_2) + (1698383/125000000000 : ℝ)*(sp_s1_1) + (5325849/200000000000 : ℝ)*(sp_s1_2) + (68875937/1000000000000 : ℝ)*(sp_s1_9) + (458784732989/200000000000 : ℝ)*(sp_s1_21) + (2293910077881/1000000000000 : ℝ)*(sp_s1_22) + (1146914079881/500000000000 : ℝ)*(sp_s1_23) + (172145569941/100000000000 : ℝ)*(sp_s1_27) + (1053107837881/1000000000000 : ℝ)*(f.failure) + (458784732989/200000000000 : ℝ)*(f.sum) + (58159874916365514199/147062428000000000000000000000000 : ℝ)*base62 + (7202851344821713/7556000000000000000000000000 : ℝ)*base64 + (1262071330133359/1557040000000000000000000000 : ℝ)*base66 + (6428868164334973/7556000000000000000000000000 : ℝ)*base68 + (608959990576974153/2841056000000000000000000000000 : ℝ)*base70 + (12841428919899/15040000000000000000000000 : ℝ)*base72 + (298295545938691/778520000000000000000000000 : ℝ)*base74 + (77220222159363/300800000000000000000000000 : ℝ)*base77 + (196728534679265601/292723520000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (27583/100000000000000000 : ℝ)*base86 + (27583/100000000000000000 : ℝ)*base88 + (27583/100000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((2444/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2444/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19463/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(19463/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1889/2500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(1889/2500 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((58269/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(58269/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(11721/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(11721/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(11237/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(11237/20000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c316063_s1 p hpa hpb X hX hprev0

#print axioms solution
