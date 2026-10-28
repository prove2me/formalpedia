-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c304076_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:49:22.854792+00:00
-- url     : https://prove2.me/submissions/348cb909-23d7-492c-ae69-2dc0b0bdc71f

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
theorem collision_support_c304076_s2_s2_0 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-853983259/5000000000 : ℝ)*x 0 + (-615119183/1000000000 : ℝ)*x 1 + (4748943609/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (853983259/5000000000 : ℝ)^133 ≤ (1219591832461/12500000000000 : ℝ)^101 := by
    have hnat : (853983259 : ℕ)^133*12500000000000^101 ≤ 1219591832461^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      853983259 5000000000 1219591832461 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (615119183/1000000000 : ℝ)^133 ≤ (1647953311243/3125000000000 : ℝ)^101 := by
    have hnat : (615119183 : ℕ)^133*3125000000000^101 ≤ 1647953311243^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      615119183 1000000000 1647953311243 3125000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4748943609/10000000000 : ℝ)^133 ≤ (4688594921261/12500000000000 : ℝ)^101 := by
    have hnat : (4748943609 : ℕ)^133*12500000000000^101 ≤ 4688594921261^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4748943609 10000000000 4688594921261 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-853983259/5000000000 : ℝ), (-615119183/1000000000 : ℝ), (4748943609/10000000000 : ℝ)] ![(1219591832461/12500000000000 : ℝ), (1647953311243/3125000000000 : ℝ), (4688594921261/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-853983259/5000000000 : ℝ)|^133 ≤ (1219591832461/12500000000000 : ℝ)^101
        have hw : |(-853983259/5000000000 : ℝ)|=(853983259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-615119183/1000000000 : ℝ)|^133 ≤ (1647953311243/3125000000000 : ℝ)^101
        have hw : |(-615119183/1000000000 : ℝ)|=(615119183/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4748943609/10000000000 : ℝ)|^133 ≤ (4688594921261/12500000000000 : ℝ)^101
        have hw : |(4748943609/10000000000 : ℝ)|=(4748943609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304076_s2_s2_1 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (24909693/39062500 : ℝ)*x 0 + (69822197/200000000 : ℝ)*x 1 + (727772927/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (24909693/39062500 : ℝ)^133 ≤ (55297063871797/100000000000000 : ℝ)^101 := by
    have hnat : (24909693 : ℕ)^133*100000000000000^101 ≤ 55297063871797^101*39062500^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24909693 39062500 55297063871797 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (69822197/200000000 : ℝ)^133 ≤ (25012659749103/100000000000000 : ℝ)^101 := by
    have hnat : (69822197 : ℕ)^133*100000000000000^101 ≤ 25012659749103^101*200000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69822197 200000000 25012659749103 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (727772927/2500000000 : ℝ)^133 ≤ (19690276369961/100000000000000 : ℝ)^101 := by
    have hnat : (727772927 : ℕ)^133*100000000000000^101 ≤ 19690276369961^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      727772927 2500000000 19690276369961 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(24909693/39062500 : ℝ), (69822197/200000000 : ℝ), (727772927/2500000000 : ℝ)] ![(55297063871797/100000000000000 : ℝ), (25012659749103/100000000000000 : ℝ), (19690276369961/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(24909693/39062500 : ℝ)|^133 ≤ (55297063871797/100000000000000 : ℝ)^101
        have hw : |(24909693/39062500 : ℝ)|=(24909693/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(69822197/200000000 : ℝ)|^133 ≤ (25012659749103/100000000000000 : ℝ)^101
        have hw : |(69822197/200000000 : ℝ)|=(69822197/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(727772927/2500000000 : ℝ)|^133 ≤ (19690276369961/100000000000000 : ℝ)^101
        have hw : |(727772927/2500000000 : ℝ)|=(727772927/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304076_s2_s2_2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (57899031/125000000 : ℝ)*x 0 + (-2418878733/5000000000 : ℝ)*x 1 + (-3518178403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (57899031/125000000 : ℝ)^133 ≤ (1451857051609/4000000000000 : ℝ)^101 := by
    have hnat : (57899031 : ℕ)^133*4000000000000^101 ≤ 1451857051609^101*125000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      57899031 125000000 1451857051609 4000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2418878733/5000000000 : ℝ)^133 ≤ (1537408719951/4000000000000 : ℝ)^101 := by
    have hnat : (2418878733 : ℕ)^133*4000000000000^101 ≤ 1537408719951^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2418878733 5000000000 1537408719951 4000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3518178403/10000000000 : ℝ)^133 ≤ (25268355694933/100000000000000 : ℝ)^101 := by
    have hnat : (3518178403 : ℕ)^133*100000000000000^101 ≤ 25268355694933^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3518178403 10000000000 25268355694933 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(57899031/125000000 : ℝ), (-2418878733/5000000000 : ℝ), (-3518178403/10000000000 : ℝ)] ![(1451857051609/4000000000000 : ℝ), (1537408719951/4000000000000 : ℝ), (25268355694933/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(57899031/125000000 : ℝ)|^133 ≤ (1451857051609/4000000000000 : ℝ)^101
        have hw : |(57899031/125000000 : ℝ)|=(57899031/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2418878733/5000000000 : ℝ)|^133 ≤ (1537408719951/4000000000000 : ℝ)^101
        have hw : |(-2418878733/5000000000 : ℝ)|=(2418878733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3518178403/10000000000 : ℝ)|^133 ≤ (25268355694933/100000000000000 : ℝ)^101
        have hw : |(-3518178403/10000000000 : ℝ)|=(3518178403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304076_s2_s2_7 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1317940577/10000000000 : ℝ)*x 0 + (-6720543573/10000000000 : ℝ)*x 1 + (548621373/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1317940577/10000000000 : ℝ)^133 ≤ (693507150961/10000000000000 : ℝ)^101 := by
    have hnat : (1317940577 : ℕ)^133*10000000000000^101 ≤ 693507150961^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1317940577 10000000000 693507150961 10000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6720543573/10000000000 : ℝ)^133 ≤ (59254405764277/100000000000000 : ℝ)^101 := by
    have hnat : (6720543573 : ℕ)^133*100000000000000^101 ≤ 59254405764277^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6720543573 10000000000 59254405764277 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (548621373/1250000000 : ℝ)^133 ≤ (33810522712053/100000000000000 : ℝ)^101 := by
    have hnat : (548621373 : ℕ)^133*100000000000000^101 ≤ 33810522712053^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548621373 1250000000 33810522712053 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1317940577/10000000000 : ℝ), (-6720543573/10000000000 : ℝ), (548621373/1250000000 : ℝ)] ![(693507150961/10000000000000 : ℝ), (59254405764277/100000000000000 : ℝ), (33810522712053/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1317940577/10000000000 : ℝ)|^133 ≤ (693507150961/10000000000000 : ℝ)^101
        have hw : |(-1317940577/10000000000 : ℝ)|=(1317940577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6720543573/10000000000 : ℝ)|^133 ≤ (59254405764277/100000000000000 : ℝ)^101
        have hw : |(-6720543573/10000000000 : ℝ)|=(6720543573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(548621373/1250000000 : ℝ)|^133 ≤ (33810522712053/100000000000000 : ℝ)^101
        have hw : |(548621373/1250000000 : ℝ)|=(548621373/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304076_s2_s2_8 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1588788267/2500000000 : ℝ)*x 0 + (104128647/312500000 : ℝ)*x 1 + (1552060763/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1588788267/2500000000 : ℝ)^133 ≤ (6881135539469/12500000000000 : ℝ)^101 := by
    have hnat : (1588788267 : ℕ)^133*12500000000000^101 ≤ 6881135539469^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1588788267 2500000000 6881135539469 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (104128647/312500000 : ℝ)^133 ≤ (23523548898807/100000000000000 : ℝ)^101 := by
    have hnat : (104128647 : ℕ)^133*100000000000000^101 ≤ 23523548898807^101*312500000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104128647 312500000 23523548898807 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1552060763/5000000000 : ℝ)^133 ≤ (2678420847039/12500000000000 : ℝ)^101 := by
    have hnat : (1552060763 : ℕ)^133*12500000000000^101 ≤ 2678420847039^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1552060763 5000000000 2678420847039 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1588788267/2500000000 : ℝ), (104128647/312500000 : ℝ), (1552060763/5000000000 : ℝ)] ![(6881135539469/12500000000000 : ℝ), (23523548898807/100000000000000 : ℝ), (2678420847039/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1588788267/2500000000 : ℝ)|^133 ≤ (6881135539469/12500000000000 : ℝ)^101
        have hw : |(1588788267/2500000000 : ℝ)|=(1588788267/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(104128647/312500000 : ℝ)|^133 ≤ (23523548898807/100000000000000 : ℝ)^101
        have hw : |(104128647/312500000 : ℝ)|=(104128647/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1552060763/5000000000 : ℝ)|^133 ≤ (2678420847039/12500000000000 : ℝ)^101
        have hw : |(1552060763/5000000000 : ℝ)|=(1552060763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304076_s2_s2_9 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4718977309/10000000000 : ℝ)*x 0 + (-2490711559/5000000000 : ℝ)*x 1 + (-3260204813/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4718977309/10000000000 : ℝ)^133 ≤ (929934961197/2500000000000 : ℝ)^101 := by
    have hnat : (4718977309 : ℕ)^133*2500000000000^101 ≤ 929934961197^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4718977309 10000000000 929934961197 2500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2490711559/5000000000 : ℝ)^133 ≤ (39945274537889/100000000000000 : ℝ)^101 := by
    have hnat : (2490711559 : ℕ)^133*100000000000000^101 ≤ 39945274537889^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2490711559 5000000000 39945274537889 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3260204813/10000000000 : ℝ)^133 ≤ (5714331752561/25000000000000 : ℝ)^101 := by
    have hnat : (3260204813 : ℕ)^133*25000000000000^101 ≤ 5714331752561^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3260204813 10000000000 5714331752561 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4718977309/10000000000 : ℝ), (-2490711559/5000000000 : ℝ), (-3260204813/10000000000 : ℝ)] ![(929934961197/2500000000000 : ℝ), (39945274537889/100000000000000 : ℝ), (5714331752561/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4718977309/10000000000 : ℝ)|^133 ≤ (929934961197/2500000000000 : ℝ)^101
        have hw : |(4718977309/10000000000 : ℝ)|=(4718977309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2490711559/5000000000 : ℝ)|^133 ≤ (39945274537889/100000000000000 : ℝ)^101
        have hw : |(-2490711559/5000000000 : ℝ)|=(2490711559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3260204813/10000000000 : ℝ)|^133 ≤ (5714331752561/25000000000000 : ℝ)^101
        have hw : |(-3260204813/10000000000 : ℝ)|=(3260204813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304076_s2_s2_13 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1706014999/5000000000 : ℝ)*x 0 + (22033761/10000000000 : ℝ)*x 1 + (8094338091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1706014999/5000000000 : ℝ)^133 ≤ (24269258810979/100000000000000 : ℝ)^101 := by
    have hnat : (1706014999 : ℕ)^133*100000000000000^101 ≤ 24269258810979^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1706014999 5000000000 24269258810979 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (22033761/10000000000 : ℝ)^133 ≤ (15858603417/50000000000000 : ℝ)^101 := by
    have hnat : (22033761 : ℕ)^133*50000000000000^101 ≤ 15858603417^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22033761 10000000000 15858603417 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8094338091/10000000000 : ℝ)^133 ≤ (4731188998187/6250000000000 : ℝ)^101 := by
    have hnat : (8094338091 : ℕ)^133*6250000000000^101 ≤ 4731188998187^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8094338091 10000000000 4731188998187 6250000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1706014999/5000000000 : ℝ), (22033761/10000000000 : ℝ), (8094338091/10000000000 : ℝ)] ![(24269258810979/100000000000000 : ℝ), (15858603417/50000000000000 : ℝ), (4731188998187/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1706014999/5000000000 : ℝ)|^133 ≤ (24269258810979/100000000000000 : ℝ)^101
        have hw : |(1706014999/5000000000 : ℝ)|=(1706014999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(22033761/10000000000 : ℝ)|^133 ≤ (15858603417/50000000000000 : ℝ)^101
        have hw : |(22033761/10000000000 : ℝ)|=(22033761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8094338091/10000000000 : ℝ)|^133 ≤ (4731188998187/6250000000000 : ℝ)^101
        have hw : |(8094338091/10000000000 : ℝ)|=(8094338091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304076_s2_s2_14 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1030665493/10000000000 : ℝ)*x 0 + (-1201846811/2000000000 : ℝ)*x 1 + (2673291683/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1030665493/10000000000 : ℝ)^133 ≤ (2508488830029/50000000000000 : ℝ)^101 := by
    have hnat : (1030665493 : ℕ)^133*50000000000000^101 ≤ 2508488830029^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030665493 10000000000 2508488830029 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1201846811/2000000000 : ℝ)^133 ≤ (5113779633871/10000000000000 : ℝ)^101 := by
    have hnat : (1201846811 : ℕ)^133*10000000000000^101 ≤ 5113779633871^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1201846811 2000000000 5113779633871 10000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2673291683/5000000000 : ℝ)^133 ≤ (43845225993983/100000000000000 : ℝ)^101 := by
    have hnat : (2673291683 : ℕ)^133*100000000000000^101 ≤ 43845225993983^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673291683 5000000000 43845225993983 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1030665493/10000000000 : ℝ), (-1201846811/2000000000 : ℝ), (2673291683/5000000000 : ℝ)] ![(2508488830029/50000000000000 : ℝ), (5113779633871/10000000000000 : ℝ), (43845225993983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1030665493/10000000000 : ℝ)|^133 ≤ (2508488830029/50000000000000 : ℝ)^101
        have hw : |(-1030665493/10000000000 : ℝ)|=(1030665493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1201846811/2000000000 : ℝ)|^133 ≤ (5113779633871/10000000000000 : ℝ)^101
        have hw : |(-1201846811/2000000000 : ℝ)|=(1201846811/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2673291683/5000000000 : ℝ)|^133 ≤ (43845225993983/100000000000000 : ℝ)^101
        have hw : |(2673291683/5000000000 : ℝ)|=(2673291683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304076_s2_s2_15 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (7152761797/10000000000 : ℝ)*x 0 + (2842300719/10000000000 : ℝ)*x 1 + (1278391359/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7152761797/10000000000 : ℝ)^133 ≤ (32161510954987/50000000000000 : ℝ)^101 := by
    have hnat : (7152761797 : ℕ)^133*50000000000000^101 ≤ 32161510954987^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7152761797 10000000000 32161510954987 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2842300719/10000000000 : ℝ)^133 ≤ (2384983574431/12500000000000 : ℝ)^101 := by
    have hnat : (2842300719 : ℕ)^133*12500000000000^101 ≤ 2384983574431^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2842300719 10000000000 2384983574431 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1278391359/5000000000 : ℝ)^133 ≤ (16597109483437/100000000000000 : ℝ)^101 := by
    have hnat : (1278391359 : ℕ)^133*100000000000000^101 ≤ 16597109483437^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1278391359 5000000000 16597109483437 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7152761797/10000000000 : ℝ), (2842300719/10000000000 : ℝ), (1278391359/5000000000 : ℝ)] ![(32161510954987/50000000000000 : ℝ), (2384983574431/12500000000000 : ℝ), (16597109483437/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7152761797/10000000000 : ℝ)|^133 ≤ (32161510954987/50000000000000 : ℝ)^101
        have hw : |(7152761797/10000000000 : ℝ)|=(7152761797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2842300719/10000000000 : ℝ)|^133 ≤ (2384983574431/12500000000000 : ℝ)^101
        have hw : |(2842300719/10000000000 : ℝ)|=(2842300719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1278391359/5000000000 : ℝ)|^133 ≤ (16597109483437/100000000000000 : ℝ)^101
        have hw : |(1278391359/5000000000 : ℝ)|=(1278391359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304076_s2_s2_16 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2693262999/5000000000 : ℝ)*x 0 + (-4708331943/10000000000 : ℝ)*x 1 + (-2791944547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2693262999/5000000000 : ℝ)^133 ≤ (44277068828937/100000000000000 : ℝ)^101 := by
    have hnat : (2693262999 : ℕ)^133*100000000000000^101 ≤ 44277068828937^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693262999 5000000000 44277068828937 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4708331943/10000000000 : ℝ)^133 ≤ (4635867458761/12500000000000 : ℝ)^101 := by
    have hnat : (4708331943 : ℕ)^133*12500000000000^101 ≤ 4635867458761^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4708331943 10000000000 4635867458761 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2791944547/10000000000 : ℝ)^133 ≤ (2329498935069/12500000000000 : ℝ)^101 := by
    have hnat : (2791944547 : ℕ)^133*12500000000000^101 ≤ 2329498935069^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2791944547 10000000000 2329498935069 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2693262999/5000000000 : ℝ), (-4708331943/10000000000 : ℝ), (-2791944547/10000000000 : ℝ)] ![(44277068828937/100000000000000 : ℝ), (4635867458761/12500000000000 : ℝ), (2329498935069/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2693262999/5000000000 : ℝ)|^133 ≤ (44277068828937/100000000000000 : ℝ)^101
        have hw : |(2693262999/5000000000 : ℝ)|=(2693262999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4708331943/10000000000 : ℝ)|^133 ≤ (4635867458761/12500000000000 : ℝ)^101
        have hw : |(-4708331943/10000000000 : ℝ)|=(4708331943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2791944547/10000000000 : ℝ)|^133 ≤ (2329498935069/12500000000000 : ℝ)^101
        have hw : |(-2791944547/10000000000 : ℝ)|=(2791944547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304076_s2_s2_20 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1370357061/5000000000 : ℝ)*x 0 + (-57629/10000000000 : ℝ)*x 1 + (4293063747/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1370357061/5000000000 : ℝ)^133 ≤ (18187003877237/100000000000000 : ℝ)^101 := by
    have hnat : (1370357061 : ℕ)^133*100000000000000^101 ≤ 18187003877237^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1370357061 5000000000 18187003877237 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (57629/10000000000 : ℝ)^133 ≤ (197/1562500000 : ℝ)^101 := by
    have hnat : (57629 : ℕ)^133*1562500000^101 ≤ 197^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      57629 10000000000 197 1562500000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4293063747/5000000000 : ℝ)^133 ≤ (81812983504789/100000000000000 : ℝ)^101 := by
    have hnat : (4293063747 : ℕ)^133*100000000000000^101 ≤ 81812983504789^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4293063747 5000000000 81812983504789 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1370357061/5000000000 : ℝ), (-57629/10000000000 : ℝ), (4293063747/5000000000 : ℝ)] ![(18187003877237/100000000000000 : ℝ), (197/1562500000 : ℝ), (81812983504789/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1370357061/5000000000 : ℝ)|^133 ≤ (18187003877237/100000000000000 : ℝ)^101
        have hw : |(1370357061/5000000000 : ℝ)|=(1370357061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-57629/10000000000 : ℝ)|^133 ≤ (197/1562500000 : ℝ)^101
        have hw : |(-57629/10000000000 : ℝ)|=(57629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4293063747/5000000000 : ℝ)|^133 ≤ (81812983504789/100000000000000 : ℝ)^101
        have hw : |(4293063747/5000000000 : ℝ)|=(4293063747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304076_s2_s2_21 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1237360167/10000000000 : ℝ)*x 0 + (-6694873683/10000000000 : ℝ)*x 1 + (4472583303/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1237360167/10000000000 : ℝ)^133 ≤ (1276439245403/20000000000000 : ℝ)^101 := by
    have hnat : (1237360167 : ℕ)^133*20000000000000^101 ≤ 1276439245403^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1237360167 10000000000 1276439245403 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6694873683/10000000000 : ℝ)^133 ≤ (29478274514177/50000000000000 : ℝ)^101 := by
    have hnat : (6694873683 : ℕ)^133*50000000000000^101 ≤ 29478274514177^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6694873683 10000000000 29478274514177 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4472583303/10000000000 : ℝ)^133 ≤ (277290037791/800000000000 : ℝ)^101 := by
    have hnat : (4472583303 : ℕ)^133*800000000000^101 ≤ 277290037791^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4472583303 10000000000 277290037791 800000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1237360167/10000000000 : ℝ), (-6694873683/10000000000 : ℝ), (4472583303/10000000000 : ℝ)] ![(1276439245403/20000000000000 : ℝ), (29478274514177/50000000000000 : ℝ), (277290037791/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1237360167/10000000000 : ℝ)|^133 ≤ (1276439245403/20000000000000 : ℝ)^101
        have hw : |(-1237360167/10000000000 : ℝ)|=(1237360167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6694873683/10000000000 : ℝ)|^133 ≤ (29478274514177/50000000000000 : ℝ)^101
        have hw : |(-6694873683/10000000000 : ℝ)|=(6694873683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4472583303/10000000000 : ℝ)|^133 ≤ (277290037791/800000000000 : ℝ)^101
        have hw : |(4472583303/10000000000 : ℝ)|=(4472583303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304076_s2_s2_22 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1389213421/2000000000 : ℝ)*x 0 + (2973695837/10000000000 : ℝ)*x 1 + (1351811683/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1389213421/2000000000 : ℝ)^133 ≤ (30943317388839/50000000000000 : ℝ)^101 := by
    have hnat : (1389213421 : ℕ)^133*50000000000000^101 ≤ 30943317388839^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1389213421 2000000000 30943317388839 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2973695837/10000000000 : ℝ)^133 ≤ (5062443757123/25000000000000 : ℝ)^101 := by
    have hnat : (2973695837 : ℕ)^133*25000000000000^101 ≤ 5062443757123^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2973695837 10000000000 5062443757123 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1351811683/5000000000 : ℝ)^133 ≤ (17863590181371/100000000000000 : ℝ)^101 := by
    have hnat : (1351811683 : ℕ)^133*100000000000000^101 ≤ 17863590181371^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351811683 5000000000 17863590181371 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1389213421/2000000000 : ℝ), (2973695837/10000000000 : ℝ), (1351811683/5000000000 : ℝ)] ![(30943317388839/50000000000000 : ℝ), (5062443757123/25000000000000 : ℝ), (17863590181371/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1389213421/2000000000 : ℝ)|^133 ≤ (30943317388839/50000000000000 : ℝ)^101
        have hw : |(1389213421/2000000000 : ℝ)|=(1389213421/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2973695837/10000000000 : ℝ)|^133 ≤ (5062443757123/25000000000000 : ℝ)^101
        have hw : |(2973695837/10000000000 : ℝ)|=(2973695837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1351811683/5000000000 : ℝ)|^133 ≤ (17863590181371/100000000000000 : ℝ)^101
        have hw : |(1351811683/5000000000 : ℝ)|=(1351811683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304076_s2_s2_23 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4395077491/10000000000 : ℝ)*x 0 + (-2627938461/5000000000 : ℝ)*x 1 + (-1651819627/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4395077491/10000000000 : ℝ)^133 ≤ (529257534739/1562500000000 : ℝ)^101 := by
    have hnat : (4395077491 : ℕ)^133*1562500000000^101 ≤ 529257534739^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4395077491 10000000000 529257534739 1562500000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2627938461/5000000000 : ℝ)^133 ≤ (10717086590397/25000000000000 : ℝ)^101 := by
    have hnat : (2627938461 : ℕ)^133*25000000000000^101 ≤ 10717086590397^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627938461 5000000000 10717086590397 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1651819627/5000000000 : ℝ)^133 ≤ (4651834281907/20000000000000 : ℝ)^101 := by
    have hnat : (1651819627 : ℕ)^133*20000000000000^101 ≤ 4651834281907^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1651819627 5000000000 4651834281907 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4395077491/10000000000 : ℝ), (-2627938461/5000000000 : ℝ), (-1651819627/5000000000 : ℝ)] ![(529257534739/1562500000000 : ℝ), (10717086590397/25000000000000 : ℝ), (4651834281907/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4395077491/10000000000 : ℝ)|^133 ≤ (529257534739/1562500000000 : ℝ)^101
        have hw : |(4395077491/10000000000 : ℝ)|=(4395077491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2627938461/5000000000 : ℝ)|^133 ≤ (10717086590397/25000000000000 : ℝ)^101
        have hw : |(-2627938461/5000000000 : ℝ)|=(2627938461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1651819627/5000000000 : ℝ)|^133 ≤ (4651834281907/20000000000000 : ℝ)^101
        have hw : |(-1651819627/5000000000 : ℝ)|=(1651819627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304076_s2_s2_27 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2378382517/5000000000 : ℝ)*x 0 + (2713211/2000000000 : ℝ)*x 1 + (3494597371/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2378382517/5000000000 : ℝ)^133 ≤ (587345773683/1562500000000 : ℝ)^101 := by
    have hnat : (2378382517 : ℕ)^133*1562500000000^101 ≤ 587345773683^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2378382517 5000000000 587345773683 1562500000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2713211/2000000000 : ℝ)^133 ≤ (4186624603/25000000000000 : ℝ)^101 := by
    have hnat : (2713211 : ℕ)^133*25000000000000^101 ≤ 4186624603^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713211 2000000000 4186624603 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3494597371/5000000000 : ℝ)^133 ≤ (31196561983871/50000000000000 : ℝ)^101 := by
    have hnat : (3494597371 : ℕ)^133*50000000000000^101 ≤ 31196561983871^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3494597371 5000000000 31196561983871 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2378382517/5000000000 : ℝ), (2713211/2000000000 : ℝ), (3494597371/5000000000 : ℝ)] ![(587345773683/1562500000000 : ℝ), (4186624603/25000000000000 : ℝ), (31196561983871/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2378382517/5000000000 : ℝ)|^133 ≤ (587345773683/1562500000000 : ℝ)^101
        have hw : |(2378382517/5000000000 : ℝ)|=(2378382517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2713211/2000000000 : ℝ)|^133 ≤ (4186624603/25000000000000 : ℝ)^101
        have hw : |(2713211/2000000000 : ℝ)|=(2713211/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3494597371/5000000000 : ℝ)|^133 ≤ (31196561983871/50000000000000 : ℝ)^101
        have hw : |(3494597371/5000000000 : ℝ)|=(3494597371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c304076_s2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((39627/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(39627/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-17193/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-17193/20000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22287/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(22287/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((58781/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(58781/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-7323/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-7323/12500 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(31883/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(31883/50000 : ℝ)*X 1 2) := by
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
  have main1 : (76617/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76617/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76617/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76617/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base54 : ((-1 : ℝ)*N 2+(1 : ℝ)*P 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 2]
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (39627/50000 : ℝ) ^ (33/8 : ℝ) ≤ (19161628476593335893/50000000000000000000 : ℝ) := by
    have hpowers : (39627/50000 : ℝ)^33 ≤ (19161628476593335893/50000000000000000000 : ℝ)^8 := by
      have hnat : (39627 : ℕ)^33*50000000000000000000^8 ≤ 19161628476593335893^8*50000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        39627 50000 19161628476593335893 50000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (39627/50000 : ℝ)) (X := (19161628476593335893/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s2_corner0a : (69161628476593335893/50000000000000000000 : ℝ) ≤ (1352279382578119/1250000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (69161628476593335893/50000000000000000000 : ℝ)^8 ≤ (1352279382578119/1250000000000000 : ℝ)^33 := by
      have hnat : (69161628476593335893 : ℕ)^8*1250000000000000^33 ≤ 1352279382578119^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        69161628476593335893 50000000000000000000 1352279382578119 1250000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1352279382578119/1250000000000000 : ℝ)) (X := (69161628476593335893/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s2_corner0b : (44161628476593335893/25000000000000000000 : ℝ) ≤ (11479005386189441/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (44161628476593335893/25000000000000000000 : ℝ)^8 ≤ (11479005386189441/10000000000000000 : ℝ)^33 := by
      have hnat : (44161628476593335893 : ℕ)^8*10000000000000000^33 ≤ 11479005386189441^33*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        44161628476593335893 25000000000000000000 11479005386189441 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11479005386189441/10000000000000000 : ℝ)) (X := (44161628476593335893/25000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(102279382578119/990675000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(10488417866103/125800000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (39627/50000 : ℝ)) (alpha := (102279382578119/990675000000000 : ℝ)) (beta := (10488417866103/125800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (39627/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(102279382578119/990675000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(10488417866103/125800000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (17193/20000 : ℝ) ^ (33/8 : ℝ) ≤ (53589151224275861947/100000000000000000000 : ℝ) := by
    have hpowers : (17193/20000 : ℝ)^33 ≤ (53589151224275861947/100000000000000000000 : ℝ)^8 := by
      have hnat : (17193 : ℕ)^33*100000000000000000000^8 ≤ 53589151224275861947^8*20000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17193 20000 53589151224275861947 100000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17193/20000 : ℝ)) (X := (53589151224275861947/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s2_corner1a : (153589151224275861947/100000000000000000000 : ℝ) ≤ (1387037892804327/1250000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (153589151224275861947/100000000000000000000 : ℝ)^8 ≤ (1387037892804327/1250000000000000 : ℝ)^33 := by
      have hnat : (153589151224275861947 : ℕ)^8*1250000000000000^33 ≤ 1387037892804327^33*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        153589151224275861947 100000000000000000000 1387037892804327 1250000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1387037892804327/1250000000000000 : ℝ)) (X := (153589151224275861947/100000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s2_corner1b : (103589151224275861947/50000000000000000000 : ℝ) ≤ (372854631155359/312500000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (103589151224275861947/50000000000000000000 : ℝ)^8 ≤ (372854631155359/312500000000000 : ℝ)^33 := by
      have hnat : (103589151224275861947 : ℕ)^8*312500000000000^33 ≤ 372854631155359^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        103589151224275861947 50000000000000000000 372854631155359 312500000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (372854631155359/312500000000000 : ℝ)) (X := (103589151224275861947/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(137037892804327/1074562500000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(104380631817109/1074562500000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (17193/20000 : ℝ)) (alpha := (137037892804327/1074562500000000 : ℝ)) (beta := (104380631817109/1074562500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (17193/20000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(137037892804327/1074562500000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(104380631817109/1074562500000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (22287/25000 : ℝ) ^ (33/8 : ℝ) ≤ (62260179455316020947/100000000000000000000 : ℝ) := by
    have hpowers : (22287/25000 : ℝ)^33 ≤ (62260179455316020947/100000000000000000000 : ℝ)^8 := by
      have hnat : (22287 : ℕ)^33*100000000000000000000^8 ≤ 62260179455316020947^8*25000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22287 25000 62260179455316020947 100000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (22287/25000 : ℝ)) (X := (62260179455316020947/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s2_corner2a : (162260179455316020947/100000000000000000000 : ℝ) ≤ (11245026240356627/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (162260179455316020947/100000000000000000000 : ℝ)^8 ≤ (11245026240356627/10000000000000000 : ℝ)^33 := by
      have hnat : (162260179455316020947 : ℕ)^8*10000000000000000^33 ≤ 11245026240356627^33*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        162260179455316020947 100000000000000000000 11245026240356627 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11245026240356627/10000000000000000 : ℝ)) (X := (162260179455316020947/100000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s2_corner2b : (112260179455316020947/50000000000000000000 : ℝ) ≤ (12166142632579063/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (112260179455316020947/50000000000000000000 : ℝ)^8 ≤ (12166142632579063/10000000000000000 : ℝ)^33 := by
      have hnat : (112260179455316020947 : ℕ)^8*10000000000000000^33 ≤ 12166142632579063^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        112260179455316020947 50000000000000000000 12166142632579063 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12166142632579063/10000000000000000 : ℝ)) (X := (112260179455316020947/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1245026240356627/8914800000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(230279098055609/2228700000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (22287/25000 : ℝ)) (alpha := (1245026240356627/8914800000000000 : ℝ)) (beta := (230279098055609/2228700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (22287/25000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1245026240356627/8914800000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(230279098055609/2228700000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-853983259/5000000000 : ℝ)*X 0 0+(-615119183/1000000000 : ℝ)*X 0 1+(4748943609/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304076_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((24909693/39062500 : ℝ)*X 1 0+(69822197/200000000 : ℝ)*X 1 1+(727772927/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304076_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((57899031/125000000 : ℝ)*X 2 0+(-2418878733/5000000000 : ℝ)*X 2 1+(-3518178403/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304076_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-1317940577/10000000000 : ℝ)*X 0 0+(-6720543573/10000000000 : ℝ)*X 0 1+(548621373/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304076_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((1588788267/2500000000 : ℝ)*X 1 0+(104128647/312500000 : ℝ)*X 1 1+(1552060763/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304076_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((4718977309/10000000000 : ℝ)*X 2 0+(-2490711559/5000000000 : ℝ)*X 2 1+(-3260204813/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304076_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((1706014999/5000000000 : ℝ)*X 0 0+(22033761/10000000000 : ℝ)*X 0 1+(8094338091/10000000000 : ℝ)*X 0 2+(1706014999/5000000000 : ℝ)*X 1 0+(22033761/10000000000 : ℝ)*X 1 1+(8094338091/10000000000 : ℝ)*X 1 2+(1706014999/5000000000 : ℝ)*X 2 0+(22033761/10000000000 : ℝ)*X 2 1+(8094338091/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304076_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-1030665493/10000000000 : ℝ)*X 0 0+(-1201846811/2000000000 : ℝ)*X 0 1+(2673291683/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304076_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((7152761797/10000000000 : ℝ)*X 1 0+(2842300719/10000000000 : ℝ)*X 1 1+(1278391359/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304076_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((2693262999/5000000000 : ℝ)*X 2 0+(-4708331943/10000000000 : ℝ)*X 2 1+(-2791944547/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304076_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((1370357061/5000000000 : ℝ)*X 0 0+(-57629/10000000000 : ℝ)*X 0 1+(4293063747/5000000000 : ℝ)*X 0 2+(1370357061/5000000000 : ℝ)*X 1 0+(-57629/10000000000 : ℝ)*X 1 1+(4293063747/5000000000 : ℝ)*X 1 2+(1370357061/5000000000 : ℝ)*X 2 0+(-57629/10000000000 : ℝ)*X 2 1+(4293063747/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304076_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-1237360167/10000000000 : ℝ)*X 0 0+(-6694873683/10000000000 : ℝ)*X 0 1+(4472583303/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304076_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((1389213421/2000000000 : ℝ)*X 1 0+(2973695837/10000000000 : ℝ)*X 1 1+(1351811683/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304076_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((4395077491/10000000000 : ℝ)*X 2 0+(-2627938461/5000000000 : ℝ)*X 2 1+(-1651819627/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304076_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((2378382517/5000000000 : ℝ)*X 0 0+(2713211/2000000000 : ℝ)*X 0 1+(3494597371/5000000000 : ℝ)*X 0 2+(2378382517/5000000000 : ℝ)*X 1 0+(2713211/2000000000 : ℝ)*X 1 1+(3494597371/5000000000 : ℝ)*X 1 2+(2378382517/5000000000 : ℝ)*X 2 0+(2713211/2000000000 : ℝ)*X 2 1+(3494597371/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304076_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((58781/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(58781/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (16413371059331110980310533623/2067577526437500000000000000000000 : ℝ) := by norm_num
    linear_combination (220111925791/200000000000 : ℝ)*(base40) + (122469727/500000000 : ℝ)*(base54) + (1073905671527/125000000000 : ℝ)*(major_s2_0) + (1073905671527/125000000000 : ℝ)*(major_s2_1) + (1043288239777/125000000000 : ℝ)*(major_s2_2) + (292684727/500000000000 : ℝ)*(sp_s2_2) + (2879509332253/250000000000 : ℝ)*(sp_s2_7) + (2879524779171/250000000000 : ℝ)*(sp_s2_8) + (1127247701311/100000000000 : ℝ)*(sp_s2_9) + (5419345171849/1000000000000 : ℝ)*(sp_s2_13) + (73576203/1000000000000 : ℝ)*(sp_s2_20) + (92567213/1000000000000 : ℝ)*(sp_s2_21) + (30779541/1000000000000 : ℝ)*(sp_s2_22) + (6402983/50000000000 : ℝ)*(sp_s2_23) + (1416089550513/250000000000 : ℝ)*(f.failure) + (460725195849/40000000000 : ℝ)*(f.sum) + (816218248087407821/7982924812500000000000000000000 : ℝ)*base62 + (290574093539327/1114350000000000000000000000 : ℝ)*base65 + (1894783750381/8395019531250000000000000 : ℝ)*base66 + (47966297212537/139293750000000000000000000 : ℝ)*base68 + (628802061699017/173169990000000000000000000000 : ℝ)*base70 + (7506785342433/31450000000000000000000000 : ℝ)*base72 + (277678661316263/2149125000000000000000000000 : ℝ)*base74 + (46485014863111/990675000000000000000000000 : ℝ)*base76 + (1858530267412856383/2703599250000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (967/3125000000000000 : ℝ)*base87 + (967/3125000000000000 : ℝ)*base89 + (967/3125000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-7323/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-7323/12500 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (29131190591395989591846601/3785038950000000000000000000000 : ℝ) := by norm_num
    linear_combination (8941253/1000000000000 : ℝ)*(base13) + (216161/31250000000 : ℝ)*(base21) + (1123033547501/1000000000000 : ℝ)*(base40) + (8489607/1000000000000 : ℝ)*(base54) + (643600880347/100000000000 : ℝ)*(major_s2_0) + (643600880347/100000000000 : ℝ)*(major_s2_1) + (6436000313863/1000000000000 : ℝ)*(major_s2_2) + (38033099/500000000000 : ℝ)*(sp_s2_0) + (76387327/1000000000000 : ℝ)*(sp_s2_13) + (4314278481763/500000000000 : ℝ)*(sp_s2_14) + (8628538368107/1000000000000 : ℝ)*(sp_s2_15) + (4314313282109/500000000000 : ℝ)*(sp_s2_16) + (2121644096777/500000000000 : ℝ)*(sp_s2_20) + (10360287/100000000000 : ℝ)*(sp_s2_22) + (4243373070487/1000000000000 : ℝ)*(f.failure) + (8628641970977/1000000000000 : ℝ)*(f.sum) + (2265856855225071739/17030239600000000000000000000000 : ℝ)*base62 + (350533526341003/2228700000000000000000000000 : ℝ)*base64 + (150336573850663/859650000000000000000000000 : ℝ)*base66 + (697559016196861/8914800000000000000000000000 : ℝ)*base69 + (444764056266926239/1731699900000000000000000000000 : ℝ)*base71 + (5164979974441/12580000000000000000000000 : ℝ)*base72 + (64410381287423/429825000000000000000000000 : ℝ)*base75 + (64712337941183/396270000000000000000000000 : ℝ)*base77 + (585640784221783309/1081439700000000000000000000000 : ℝ)*base78 + (11967/12500000000000000 : ℝ)*base86 + (11967/12500000000000000 : ℝ)*base88 + (11967/12500000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(31883/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(31883/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (97517792611485326803252039921/8270310105750000000000000000000000 : ℝ) := by norm_num
    linear_combination (2352439/500000000000 : ℝ)*(base3) + (1834468082229/1000000000000 : ℝ)*(base40) + (2926877/500000000000 : ℝ)*(base43) + (7250167/1000000000000 : ℝ)*(base49) + (594045004627/62500000000 : ℝ)*(major_s2_0) + (9504714220277/1000000000000 : ℝ)*(major_s2_1) + (594045004627/62500000000 : ℝ)*(major_s2_2) + (22466969/200000000000 : ℝ)*(sp_s2_1) + (322714569/1000000000000 : ℝ)*(sp_s2_7) + (539699741/1000000000000 : ℝ)*(sp_s2_15) + (12742479613777/1000000000000 : ℝ)*(sp_s2_21) + (12742160852393/1000000000000 : ℝ)*(sp_s2_22) + (6371401164173/500000000000 : ℝ)*(sp_s2_23) + (78332791633/12500000000 : ℝ)*(sp_s2_27) + (6266628035519/1000000000000 : ℝ)*(f.failure) + (12742808182101/1000000000000 : ℝ)*(f.sum) + (5210311017601712701/15965849625000000000000000000000 : ℝ)*base63 + (47814905182553/139293750000000000000000000 : ℝ)*base65 + (1939141345030541/4298250000000000000000000000 : ℝ)*base67 + (72126470334197/278587500000000000000000000 : ℝ)*base69 + (1198532316604913/86584995000000000000000000000 : ℝ)*base71 + (2876962722251/7862500000000000000000000 : ℝ)*base73 + (1229906950865639/2149125000000000000000000000 : ℝ)*base75 + (199018295543059/495337500000000000000000000 : ℝ)*base77 + (85922912469610531/675899812500000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base84 + (4721/12500000000000000 : ℝ)*base87 + (17221/12500000000000000 : ℝ)*base89 + (4721/12500000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((39627/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(39627/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-17193/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-17193/20000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22287/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(22287/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((58781/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(58781/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-7323/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-7323/12500 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(31883/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(31883/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c304076_s2 p hpa hpb X hX hprev1

#print axioms solution
