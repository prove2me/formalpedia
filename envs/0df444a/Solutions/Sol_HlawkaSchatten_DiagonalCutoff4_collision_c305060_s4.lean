-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c305060_s4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:31:31.716182+00:00
-- url     : https://prove2.me/submissions/f3974c31-58a9-440a-a70c-195f34e6483c

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
theorem collision_support_c305060_s4_s4_0 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1124850093/5000000000 : ℝ)*x 0 + (2079804927/5000000000 : ℝ)*x 1 + (-6284424569/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1124850093/5000000000 : ℝ)^67 ≤ (14088658124099/100000000000000 : ℝ)^51 := by
    have hnat : (1124850093 : ℕ)^67*100000000000000^51 ≤ 14088658124099^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124850093 5000000000 14088658124099 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2079804927/5000000000 : ℝ)^67 ≤ (15794638571011/50000000000000 : ℝ)^51 := by
    have hnat : (2079804927 : ℕ)^67*50000000000000^51 ≤ 15794638571011^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079804927 5000000000 15794638571011 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6284424569/10000000000 : ℝ)^67 ≤ (54322064706863/100000000000000 : ℝ)^51 := by
    have hnat : (6284424569 : ℕ)^67*100000000000000^51 ≤ 54322064706863^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6284424569 10000000000 54322064706863 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1124850093/5000000000 : ℝ), (2079804927/5000000000 : ℝ), (-6284424569/10000000000 : ℝ)] ![(14088658124099/100000000000000 : ℝ), (15794638571011/50000000000000 : ℝ), (54322064706863/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1124850093/5000000000 : ℝ)|^67 ≤ (14088658124099/100000000000000 : ℝ)^51
        have hw : |(-1124850093/5000000000 : ℝ)|=(1124850093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2079804927/5000000000 : ℝ)|^67 ≤ (15794638571011/50000000000000 : ℝ)^51
        have hw : |(2079804927/5000000000 : ℝ)|=(2079804927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6284424569/10000000000 : ℝ)|^67 ≤ (54322064706863/100000000000000 : ℝ)^51
        have hw : |(-6284424569/10000000000 : ℝ)|=(6284424569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305060_s4_s4_1 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4462825833/10000000000 : ℝ)*x 0 + (-647998939/2500000000 : ℝ)*x 1 + (-2877078247/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4462825833/10000000000 : ℝ)^67 ≤ (866210917437/2500000000000 : ℝ)^51 := by
    have hnat : (4462825833 : ℕ)^67*2500000000000^51 ≤ 866210917437^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4462825833 10000000000 866210917437 2500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (647998939/2500000000 : ℝ)^67 ≤ (530305872901/3125000000000 : ℝ)^51 := by
    have hnat : (647998939 : ℕ)^67*3125000000000^51 ≤ 530305872901^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647998939 2500000000 530305872901 3125000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2877078247/5000000000 : ℝ)^67 ≤ (12095443837031/25000000000000 : ℝ)^51 := by
    have hnat : (2877078247 : ℕ)^67*25000000000000^51 ≤ 12095443837031^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2877078247 5000000000 12095443837031 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4462825833/10000000000 : ℝ), (-647998939/2500000000 : ℝ), (-2877078247/5000000000 : ℝ)] ![(866210917437/2500000000000 : ℝ), (530305872901/3125000000000 : ℝ), (12095443837031/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4462825833/10000000000 : ℝ)|^67 ≤ (866210917437/2500000000000 : ℝ)^51
        have hw : |(4462825833/10000000000 : ℝ)|=(4462825833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-647998939/2500000000 : ℝ)|^67 ≤ (530305872901/3125000000000 : ℝ)^51
        have hw : |(-647998939/2500000000 : ℝ)|=(647998939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2877078247/5000000000 : ℝ)|^67 ≤ (12095443837031/25000000000000 : ℝ)^51
        have hw : |(-2877078247/5000000000 : ℝ)|=(2877078247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305060_s4_s4_2 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (592661447/1250000000 : ℝ)*x 0 + (291617363/500000000 : ℝ)*x 1 + (536342763/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (592661447/1250000000 : ℝ)^67 ≤ (37516056916479/100000000000000 : ℝ)^51 := by
    have hnat : (592661447 : ℕ)^67*100000000000000^51 ≤ 37516056916479^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      592661447 1250000000 37516056916479 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (291617363/500000000 : ℝ)^67 ≤ (49247305300913/100000000000000 : ℝ)^51 := by
    have hnat : (291617363 : ℕ)^67*100000000000000^51 ≤ 49247305300913^51*500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      291617363 500000000 49247305300913 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (536342763/2500000000 : ℝ)^67 ≤ (13236637766883/100000000000000 : ℝ)^51 := by
    have hnat : (536342763 : ℕ)^67*100000000000000^51 ≤ 13236637766883^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536342763 2500000000 13236637766883 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(592661447/1250000000 : ℝ), (291617363/500000000 : ℝ), (536342763/2500000000 : ℝ)] ![(37516056916479/100000000000000 : ℝ), (49247305300913/100000000000000 : ℝ), (13236637766883/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(592661447/1250000000 : ℝ)|^67 ≤ (37516056916479/100000000000000 : ℝ)^51
        have hw : |(592661447/1250000000 : ℝ)|=(592661447/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(291617363/500000000 : ℝ)|^67 ≤ (49247305300913/100000000000000 : ℝ)^51
        have hw : |(291617363/500000000 : ℝ)|=(291617363/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(536342763/2500000000 : ℝ)|^67 ≤ (13236637766883/100000000000000 : ℝ)^51
        have hw : |(536342763/2500000000 : ℝ)|=(536342763/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305060_s4_s4_6 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (339186139/500000000 : ℝ)*x 0 + (1108805001/2500000000 : ℝ)*x 1 + (-555149241/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (339186139/500000000 : ℝ)^67 ≤ (15015346035829/25000000000000 : ℝ)^51 := by
    have hnat : (339186139 : ℕ)^67*25000000000000^51 ≤ 15015346035829^51*500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339186139 500000000 15015346035829 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1108805001/2500000000 : ℝ)^67 ≤ (6873428998843/20000000000000 : ℝ)^51 := by
    have hnat : (1108805001 : ℕ)^67*20000000000000^51 ≤ 6873428998843^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1108805001 2500000000 6873428998843 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (555149241/5000000000 : ℝ)^67 ≤ (5571470847797/100000000000000 : ℝ)^51 := by
    have hnat : (555149241 : ℕ)^67*100000000000000^51 ≤ 5571470847797^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      555149241 5000000000 5571470847797 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(339186139/500000000 : ℝ), (1108805001/2500000000 : ℝ), (-555149241/5000000000 : ℝ)] ![(15015346035829/25000000000000 : ℝ), (6873428998843/20000000000000 : ℝ), (5571470847797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(339186139/500000000 : ℝ)|^67 ≤ (15015346035829/25000000000000 : ℝ)^51
        have hw : |(339186139/500000000 : ℝ)|=(339186139/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1108805001/2500000000 : ℝ)|^67 ≤ (6873428998843/20000000000000 : ℝ)^51
        have hw : |(1108805001/2500000000 : ℝ)|=(1108805001/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-555149241/5000000000 : ℝ)|^67 ≤ (5571470847797/100000000000000 : ℝ)^51
        have hw : |(-555149241/5000000000 : ℝ)|=(555149241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305060_s4_s4_7 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1020449009/5000000000 : ℝ)*x 0 + (379824523/1000000000 : ℝ)*x 1 + (-210668421/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1020449009/5000000000 : ℝ)^67 ≤ (12396373534453/100000000000000 : ℝ)^51 := by
    have hnat : (1020449009 : ℕ)^67*100000000000000^51 ≤ 12396373534453^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1020449009 5000000000 12396373534453 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (379824523/1000000000 : ℝ)^67 ≤ (1752134694877/6250000000000 : ℝ)^51 := by
    have hnat : (379824523 : ℕ)^67*6250000000000^51 ≤ 1752134694877^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      379824523 1000000000 1752134694877 6250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210668421/312500000 : ℝ)^67 ≤ (14892367832941/25000000000000 : ℝ)^51 := by
    have hnat : (210668421 : ℕ)^67*25000000000000^51 ≤ 14892367832941^51*312500000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210668421 312500000 14892367832941 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1020449009/5000000000 : ℝ), (379824523/1000000000 : ℝ), (-210668421/312500000 : ℝ)] ![(12396373534453/100000000000000 : ℝ), (1752134694877/6250000000000 : ℝ), (14892367832941/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1020449009/5000000000 : ℝ)|^67 ≤ (12396373534453/100000000000000 : ℝ)^51
        have hw : |(-1020449009/5000000000 : ℝ)|=(1020449009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(379824523/1000000000 : ℝ)|^67 ≤ (1752134694877/6250000000000 : ℝ)^51
        have hw : |(379824523/1000000000 : ℝ)|=(379824523/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-210668421/312500000 : ℝ)|^67 ≤ (14892367832941/25000000000000 : ℝ)^51
        have hw : |(-210668421/312500000 : ℝ)|=(210668421/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305060_s4_s4_8 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4078362857/10000000000 : ℝ)*x 0 + (-1645654799/10000000000 : ℝ)*x 1 + (-6767766567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4078362857/10000000000 : ℝ)^67 ≤ (30781186005409/100000000000000 : ℝ)^51 := by
    have hnat : (4078362857 : ℕ)^67*100000000000000^51 ≤ 30781186005409^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4078362857 10000000000 30781186005409 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1645654799/10000000000 : ℝ)^67 ≤ (4671477185307/50000000000000 : ℝ)^51 := by
    have hnat : (1645654799 : ℕ)^67*50000000000000^51 ≤ 4671477185307^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1645654799 10000000000 4671477185307 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6767766567/10000000000 : ℝ)^67 ≤ (29937929806197/50000000000000 : ℝ)^51 := by
    have hnat : (6767766567 : ℕ)^67*50000000000000^51 ≤ 29937929806197^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6767766567 10000000000 29937929806197 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4078362857/10000000000 : ℝ), (-1645654799/10000000000 : ℝ), (-6767766567/10000000000 : ℝ)] ![(30781186005409/100000000000000 : ℝ), (4671477185307/50000000000000 : ℝ), (29937929806197/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4078362857/10000000000 : ℝ)|^67 ≤ (30781186005409/100000000000000 : ℝ)^51
        have hw : |(4078362857/10000000000 : ℝ)|=(4078362857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1645654799/10000000000 : ℝ)|^67 ≤ (4671477185307/50000000000000 : ℝ)^51
        have hw : |(-1645654799/10000000000 : ℝ)|=(1645654799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6767766567/10000000000 : ℝ)|^67 ≤ (29937929806197/50000000000000 : ℝ)^51
        have hw : |(-6767766567/10000000000 : ℝ)|=(6767766567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305060_s4_s4_9 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (435946903/1000000000 : ℝ)*x 0 + (6794503621/10000000000 : ℝ)*x 1 + (12066443/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (435946903/1000000000 : ℝ)^67 ≤ (33598100523347/100000000000000 : ℝ)^51 := by
    have hnat : (435946903 : ℕ)^67*100000000000000^51 ≤ 33598100523347^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435946903 1000000000 33598100523347 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6794503621/10000000000 : ℝ)^67 ≤ (30093405815643/50000000000000 : ℝ)^51 := by
    have hnat : (6794503621 : ℕ)^67*50000000000000^51 ≤ 30093405815643^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6794503621 10000000000 30093405815643 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (12066443/100000000 : ℝ)^67 ≤ (6215087833739/100000000000000 : ℝ)^51 := by
    have hnat : (12066443 : ℕ)^67*100000000000000^51 ≤ 6215087833739^51*100000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12066443 100000000 6215087833739 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(435946903/1000000000 : ℝ), (6794503621/10000000000 : ℝ), (12066443/100000000 : ℝ)] ![(33598100523347/100000000000000 : ℝ), (30093405815643/50000000000000 : ℝ), (6215087833739/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(435946903/1000000000 : ℝ)|^67 ≤ (33598100523347/100000000000000 : ℝ)^51
        have hw : |(435946903/1000000000 : ℝ)|=(435946903/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6794503621/10000000000 : ℝ)|^67 ≤ (30093405815643/50000000000000 : ℝ)^51
        have hw : |(6794503621/10000000000 : ℝ)|=(6794503621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(12066443/100000000 : ℝ)|^67 ≤ (6215087833739/100000000000000 : ℝ)^51
        have hw : |(12066443/100000000 : ℝ)|=(12066443/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305060_s4_s4_13 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6309991453/10000000000 : ℝ)*x 0 + (674013977/1250000000 : ℝ)*x 1 + (-292242121/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6309991453/10000000000 : ℝ)^67 ≤ (2730629032923/5000000000000 : ℝ)^51 := by
    have hnat : (6309991453 : ℕ)^67*5000000000000^51 ≤ 2730629032923^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6309991453 10000000000 2730629032923 5000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674013977/1250000000 : ℝ)^67 ≤ (44422686128583/100000000000000 : ℝ)^51 := by
    have hnat : (674013977 : ℕ)^67*100000000000000^51 ≤ 44422686128583^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674013977 1250000000 44422686128583 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (292242121/10000000000 : ℝ)^67 ≤ (120591649471/12500000000000 : ℝ)^51 := by
    have hnat : (292242121 : ℕ)^67*12500000000000^51 ≤ 120591649471^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      292242121 10000000000 120591649471 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6309991453/10000000000 : ℝ), (674013977/1250000000 : ℝ), (-292242121/10000000000 : ℝ)] ![(2730629032923/5000000000000 : ℝ), (44422686128583/100000000000000 : ℝ), (120591649471/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6309991453/10000000000 : ℝ)|^67 ≤ (2730629032923/5000000000000 : ℝ)^51
        have hw : |(6309991453/10000000000 : ℝ)|=(6309991453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674013977/1250000000 : ℝ)|^67 ≤ (44422686128583/100000000000000 : ℝ)^51
        have hw : |(674013977/1250000000 : ℝ)|=(674013977/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-292242121/10000000000 : ℝ)|^67 ≤ (120591649471/12500000000000 : ℝ)^51
        have hw : |(-292242121/10000000000 : ℝ)|=(292242121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305060_s4_s4_14 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1338765077/10000000000 : ℝ)*x 0 + (869836659/2000000000 : ℝ)*x 1 + (-269009063/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338765077/10000000000 : ℝ)^67 ≤ (7124088021597/100000000000000 : ℝ)^51 := by
    have hnat : (1338765077 : ℕ)^67*100000000000000^51 ≤ 7124088021597^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338765077 10000000000 7124088021597 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (869836659/2000000000 : ℝ)^67 ≤ (33493998244599/100000000000000 : ℝ)^51 := by
    have hnat : (869836659 : ℕ)^67*100000000000000^51 ≤ 33493998244599^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      869836659 2000000000 33493998244599 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269009063/400000000 : ℝ)^67 ≤ (59381913714897/100000000000000 : ℝ)^51 := by
    have hnat : (269009063 : ℕ)^67*100000000000000^51 ≤ 59381913714897^51*400000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269009063 400000000 59381913714897 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1338765077/10000000000 : ℝ), (869836659/2000000000 : ℝ), (-269009063/400000000 : ℝ)] ![(7124088021597/100000000000000 : ℝ), (33493998244599/100000000000000 : ℝ), (59381913714897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1338765077/10000000000 : ℝ)|^67 ≤ (7124088021597/100000000000000 : ℝ)^51
        have hw : |(-1338765077/10000000000 : ℝ)|=(1338765077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(869836659/2000000000 : ℝ)|^67 ≤ (33493998244599/100000000000000 : ℝ)^51
        have hw : |(869836659/2000000000 : ℝ)|=(869836659/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-269009063/400000000 : ℝ)|^67 ≤ (59381913714897/100000000000000 : ℝ)^51
        have hw : |(-269009063/400000000 : ℝ)|=(269009063/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305060_s4_s4_15 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (251831807/625000000 : ℝ)*x 0 + (-1735161603/10000000000 : ℝ)*x 1 + (-6751607071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (251831807/625000000 : ℝ)^67 ≤ (15147861793197/50000000000000 : ℝ)^51 := by
    have hnat : (251831807 : ℕ)^67*50000000000000^51 ≤ 15147861793197^51*625000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      251831807 625000000 15147861793197 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1735161603/10000000000 : ℝ)^67 ≤ (10016165109543/100000000000000 : ℝ)^51 := by
    have hnat : (1735161603 : ℕ)^67*100000000000000^51 ≤ 10016165109543^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1735161603 10000000000 10016165109543 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6751607071/10000000000 : ℝ)^67 ≤ (3730506956109/6250000000000 : ℝ)^51 := by
    have hnat : (6751607071 : ℕ)^67*6250000000000^51 ≤ 3730506956109^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6751607071 10000000000 3730506956109 6250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(251831807/625000000 : ℝ), (-1735161603/10000000000 : ℝ), (-6751607071/10000000000 : ℝ)] ![(15147861793197/50000000000000 : ℝ), (10016165109543/100000000000000 : ℝ), (3730506956109/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(251831807/625000000 : ℝ)|^67 ≤ (15147861793197/50000000000000 : ℝ)^51
        have hw : |(251831807/625000000 : ℝ)|=(251831807/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1735161603/10000000000 : ℝ)|^67 ≤ (10016165109543/100000000000000 : ℝ)^51
        have hw : |(-1735161603/10000000000 : ℝ)|=(1735161603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6751607071/10000000000 : ℝ)|^67 ≤ (3730506956109/6250000000000 : ℝ)^51
        have hw : |(-6751607071/10000000000 : ℝ)|=(6751607071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305060_s4_s4_16 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (714812469/1250000000 : ℝ)*x 0 + (550853967/1000000000 : ℝ)*x 1 + (611402107/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (714812469/1250000000 : ℝ)^67 ≤ (23994147311319/50000000000000 : ℝ)^51 := by
    have hnat : (714812469 : ℕ)^67*50000000000000^51 ≤ 23994147311319^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      714812469 1250000000 23994147311319 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (550853967/1000000000 : ℝ)^67 ≤ (45687040306821/100000000000000 : ℝ)^51 := by
    have hnat : (550853967 : ℕ)^67*100000000000000^51 ≤ 45687040306821^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550853967 1000000000 45687040306821 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (611402107/5000000000 : ℝ)^67 ≤ (252986602383/4000000000000 : ℝ)^51 := by
    have hnat : (611402107 : ℕ)^67*4000000000000^51 ≤ 252986602383^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      611402107 5000000000 252986602383 4000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(714812469/1250000000 : ℝ), (550853967/1000000000 : ℝ), (611402107/5000000000 : ℝ)] ![(23994147311319/50000000000000 : ℝ), (45687040306821/100000000000000 : ℝ), (252986602383/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(714812469/1250000000 : ℝ)|^67 ≤ (23994147311319/50000000000000 : ℝ)^51
        have hw : |(714812469/1250000000 : ℝ)|=(714812469/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(550853967/1000000000 : ℝ)|^67 ≤ (45687040306821/100000000000000 : ℝ)^51
        have hw : |(550853967/1000000000 : ℝ)|=(550853967/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(611402107/5000000000 : ℝ)|^67 ≤ (252986602383/4000000000000 : ℝ)^51
        have hw : |(611402107/5000000000 : ℝ)|=(611402107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305060_s4_s4_20 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7763225859/10000000000 : ℝ)*x 0 + (3710256697/10000000000 : ℝ)*x 1 + (-325509849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7763225859/10000000000 : ℝ)^67 ≤ (17926094113387/25000000000000 : ℝ)^51 := by
    have hnat : (7763225859 : ℕ)^67*25000000000000^51 ≤ 17926094113387^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7763225859 10000000000 17926094113387 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3710256697/10000000000 : ℝ)^67 ≤ (27184102758079/100000000000000 : ℝ)^51 := by
    have hnat : (3710256697 : ℕ)^67*100000000000000^51 ≤ 27184102758079^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3710256697 10000000000 27184102758079 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (325509849/10000000000 : ℝ)^67 ≤ (1111520782577/100000000000000 : ℝ)^51 := by
    have hnat : (325509849 : ℕ)^67*100000000000000^51 ≤ 1111520782577^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      325509849 10000000000 1111520782577 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7763225859/10000000000 : ℝ), (3710256697/10000000000 : ℝ), (-325509849/10000000000 : ℝ)] ![(17926094113387/25000000000000 : ℝ), (27184102758079/100000000000000 : ℝ), (1111520782577/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7763225859/10000000000 : ℝ)|^67 ≤ (17926094113387/25000000000000 : ℝ)^51
        have hw : |(7763225859/10000000000 : ℝ)|=(7763225859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3710256697/10000000000 : ℝ)|^67 ≤ (27184102758079/100000000000000 : ℝ)^51
        have hw : |(3710256697/10000000000 : ℝ)|=(3710256697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-325509849/10000000000 : ℝ)|^67 ≤ (1111520782577/100000000000000 : ℝ)^51
        have hw : |(-325509849/10000000000 : ℝ)|=(325509849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305060_s4_s4_21 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-133737127/1250000000 : ℝ)*x 0 + (1310546903/2500000000 : ℝ)*x 1 + (-6068745957/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133737127/1250000000 : ℝ)^67 ≤ (1326666676609/25000000000000 : ℝ)^51 := by
    have hnat : (133737127 : ℕ)^67*25000000000000^51 ≤ 1326666676609^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133737127 1250000000 1326666676609 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310546903/2500000000 : ℝ)^67 ≤ (21403584149201/50000000000000 : ℝ)^51 := by
    have hnat : (1310546903 : ℕ)^67*50000000000000^51 ≤ 21403584149201^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310546903 2500000000 21403584149201 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6068745957/10000000000 : ℝ)^67 ≤ (51886164974087/100000000000000 : ℝ)^51 := by
    have hnat : (6068745957 : ℕ)^67*100000000000000^51 ≤ 51886164974087^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6068745957 10000000000 51886164974087 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-133737127/1250000000 : ℝ), (1310546903/2500000000 : ℝ), (-6068745957/10000000000 : ℝ)] ![(1326666676609/25000000000000 : ℝ), (21403584149201/50000000000000 : ℝ), (51886164974087/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-133737127/1250000000 : ℝ)|^67 ≤ (1326666676609/25000000000000 : ℝ)^51
        have hw : |(-133737127/1250000000 : ℝ)|=(133737127/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310546903/2500000000 : ℝ)|^67 ≤ (21403584149201/50000000000000 : ℝ)^51
        have hw : |(1310546903/2500000000 : ℝ)|=(1310546903/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6068745957/10000000000 : ℝ)|^67 ≤ (51886164974087/100000000000000 : ℝ)^51
        have hw : |(-6068745957/10000000000 : ℝ)|=(6068745957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305060_s4_s4_22 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5706258603/10000000000 : ℝ)*x 0 + (-1573418207/10000000000 : ℝ)*x 1 + (-1322915127/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5706258603/10000000000 : ℝ)^67 ≤ (9570677548701/20000000000000 : ℝ)^51 := by
    have hnat : (5706258603 : ℕ)^67*20000000000000^51 ≤ 9570677548701^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5706258603 10000000000 9570677548701 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1573418207/10000000000 : ℝ)^67 ≤ (8807927177597/100000000000000 : ℝ)^51 := by
    have hnat : (1573418207 : ℕ)^67*100000000000000^51 ≤ 8807927177597^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1573418207 10000000000 8807927177597 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1322915127/2500000000 : ℝ)^67 ≤ (21669342531633/50000000000000 : ℝ)^51 := by
    have hnat : (1322915127 : ℕ)^67*50000000000000^51 ≤ 21669342531633^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322915127 2500000000 21669342531633 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5706258603/10000000000 : ℝ), (-1573418207/10000000000 : ℝ), (-1322915127/2500000000 : ℝ)] ![(9570677548701/20000000000000 : ℝ), (8807927177597/100000000000000 : ℝ), (21669342531633/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5706258603/10000000000 : ℝ)|^67 ≤ (9570677548701/20000000000000 : ℝ)^51
        have hw : |(5706258603/10000000000 : ℝ)|=(5706258603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1573418207/10000000000 : ℝ)|^67 ≤ (8807927177597/100000000000000 : ℝ)^51
        have hw : |(-1573418207/10000000000 : ℝ)|=(1573418207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1322915127/2500000000 : ℝ)|^67 ≤ (21669342531633/50000000000000 : ℝ)^51
        have hw : |(-1322915127/2500000000 : ℝ)|=(1322915127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305060_s4_s4_23 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4209773003/10000000000 : ℝ)*x 0 + (6381263439/10000000000 : ℝ)*x 1 + (2051985283/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4209773003/10000000000 : ℝ)^67 ≤ (2005668093887/6250000000000 : ℝ)^51 := by
    have hnat : (4209773003 : ℕ)^67*6250000000000^51 ≤ 2005668093887^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4209773003 10000000000 2005668093887 6250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6381263439/10000000000 : ℝ)^67 ≤ (27712195176841/50000000000000 : ℝ)^51 := by
    have hnat : (6381263439 : ℕ)^67*50000000000000^51 ≤ 27712195176841^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6381263439 10000000000 27712195176841 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2051985283/10000000000 : ℝ)^67 ≤ (6242460066071/50000000000000 : ℝ)^51 := by
    have hnat : (2051985283 : ℕ)^67*50000000000000^51 ≤ 6242460066071^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2051985283 10000000000 6242460066071 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4209773003/10000000000 : ℝ), (6381263439/10000000000 : ℝ), (2051985283/10000000000 : ℝ)] ![(2005668093887/6250000000000 : ℝ), (27712195176841/50000000000000 : ℝ), (6242460066071/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4209773003/10000000000 : ℝ)|^67 ≤ (2005668093887/6250000000000 : ℝ)^51
        have hw : |(4209773003/10000000000 : ℝ)|=(4209773003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6381263439/10000000000 : ℝ)|^67 ≤ (27712195176841/50000000000000 : ℝ)^51
        have hw : |(6381263439/10000000000 : ℝ)|=(6381263439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2051985283/10000000000 : ℝ)|^67 ≤ (6242460066071/50000000000000 : ℝ)^51
        have hw : |(2051985283/10000000000 : ℝ)|=(2051985283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305060_s4_s4_27 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7970406689/10000000000 : ℝ)*x 0 + (21369091/62500000 : ℝ)*x 1 + (-378453211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7970406689/10000000000 : ℝ)^67 ≤ (37114396404927/50000000000000 : ℝ)^51 := by
    have hnat : (7970406689 : ℕ)^67*50000000000000^51 ≤ 37114396404927^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7970406689 10000000000 37114396404927 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21369091/62500000 : ℝ)^67 ≤ (24416334850123/100000000000000 : ℝ)^51 := by
    have hnat : (21369091 : ℕ)^67*100000000000000^51 ≤ 24416334850123^51*62500000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21369091 62500000 24416334850123 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (378453211/10000000000 : ℝ)^67 ≤ (1354872328617/100000000000000 : ℝ)^51 := by
    have hnat : (378453211 : ℕ)^67*100000000000000^51 ≤ 1354872328617^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      378453211 10000000000 1354872328617 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7970406689/10000000000 : ℝ), (21369091/62500000 : ℝ), (-378453211/10000000000 : ℝ)] ![(37114396404927/50000000000000 : ℝ), (24416334850123/100000000000000 : ℝ), (1354872328617/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7970406689/10000000000 : ℝ)|^67 ≤ (37114396404927/50000000000000 : ℝ)^51
        have hw : |(7970406689/10000000000 : ℝ)|=(7970406689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(21369091/62500000 : ℝ)|^67 ≤ (24416334850123/100000000000000 : ℝ)^51
        have hw : |(21369091/62500000 : ℝ)|=(21369091/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-378453211/10000000000 : ℝ)|^67 ≤ (1354872328617/100000000000000 : ℝ)^51
        have hw : |(-378453211/10000000000 : ℝ)|=(378453211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c305060_s4 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev3 : (0 : ℝ) ≤ ((73437/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(73437/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(75101/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(75101/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-61741/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-61741/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((4789/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4789/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(25967/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(25967/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-7097/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-7097/20000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76771/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76771/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76771/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76771/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76771/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76771/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base12 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).1]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
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
  rcases hprev3 with ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩
  have s4_pow0 : (73437/100000 : ℝ) ^ (133/32 : ℝ) ≤ (13857309592903705877/50000000000000000000 : ℝ) := by
    have hpowers : (73437/100000 : ℝ)^133 ≤ (13857309592903705877/50000000000000000000 : ℝ)^32 := by
      have hnat : (73437 : ℕ)^133*50000000000000000000^32 ≤ 13857309592903705877^32*100000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        73437 100000 13857309592903705877 50000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (73437/100000 : ℝ)) (X := (13857309592903705877/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s4_corner0a : (63857309592903705877/50000000000000000000 : ℝ) ≤ (10606244908729697/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (63857309592903705877/50000000000000000000 : ℝ)^32 ≤ (10606244908729697/10000000000000000 : ℝ)^133 := by
      have hnat : (63857309592903705877 : ℕ)^32*10000000000000000^133 ≤ 10606244908729697^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        63857309592903705877 50000000000000000000 10606244908729697 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10606244908729697/10000000000000000 : ℝ)) (X := (63857309592903705877/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s4_corner0b : (38857309592903705877/25000000000000000000 : ℝ) ≤ (2223888739612349/2000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (38857309592903705877/25000000000000000000 : ℝ)^32 ≤ (2223888739612349/2000000000000000 : ℝ)^133 := by
      have hnat : (38857309592903705877 : ℕ)^32*2000000000000000^133 ≤ 2223888739612349^133*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        38857309592903705877 25000000000000000000 2223888739612349 2000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2223888739612349/2000000000000000 : ℝ)) (X := (38857309592903705877/25000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s4_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(606244908729697/7343700000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(32074924333253/458981250000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (73437/100000 : ℝ)) (alpha := (606244908729697/7343700000000000 : ℝ)) (beta := (32074924333253/458981250000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow0,s4_corner0a]) (by linarith only [s4_pow0,s4_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (73437/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(606244908729697/7343700000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(32074924333253/458981250000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow1 : (75101/100000 : ℝ) ^ (133/32 : ℝ) ≤ (30419531643287144573/100000000000000000000 : ℝ) := by
    have hpowers : (75101/100000 : ℝ)^133 ≤ (30419531643287144573/100000000000000000000 : ℝ)^32 := by
      have hnat : (75101 : ℕ)^133*100000000000000000000^32 ≤ 30419531643287144573^32*100000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        75101 100000 30419531643287144573 100000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (75101/100000 : ℝ)) (X := (30419531643287144573/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s4_corner1a : (130419531643287144573/100000000000000000000 : ℝ) ≤ (10659862718567717/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (130419531643287144573/100000000000000000000 : ℝ)^32 ≤ (10659862718567717/10000000000000000 : ℝ)^133 := by
      have hnat : (130419531643287144573 : ℕ)^32*10000000000000000^133 ≤ 10659862718567717^133*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        130419531643287144573 100000000000000000000 10659862718567717 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10659862718567717/10000000000000000 : ℝ)) (X := (130419531643287144573/100000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s4_corner1b : (80419531643287144573/50000000000000000000 : ℝ) ≤ (560567761990509/500000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (80419531643287144573/50000000000000000000 : ℝ)^32 ≤ (560567761990509/500000000000000 : ℝ)^133 := by
      have hnat : (80419531643287144573 : ℕ)^32*500000000000000^133 ≤ 560567761990509^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        80419531643287144573 50000000000000000000 560567761990509 500000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (560567761990509/500000000000000 : ℝ)) (X := (80419531643287144573/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s4_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(659862718567717/7510100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(551492521242463/7510100000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (75101/100000 : ℝ)) (alpha := (659862718567717/7510100000000000 : ℝ)) (beta := (551492521242463/7510100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow1,s4_corner1a]) (by linarith only [s4_pow1,s4_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (75101/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(659862718567717/7510100000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(551492521242463/7510100000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow2 : (61741/100000 : ℝ) ^ (133/32 : ℝ) ≤ (2695266834393237591/20000000000000000000 : ℝ) := by
    have hpowers : (61741/100000 : ℝ)^133 ≤ (2695266834393237591/20000000000000000000 : ℝ)^32 := by
      have hnat : (61741 : ℕ)^133*20000000000000000000^32 ≤ 2695266834393237591^32*100000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        61741 100000 2695266834393237591 20000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (61741/100000 : ℝ)) (X := (2695266834393237591/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s4_corner2a : (22695266834393237591/20000000000000000000 : ℝ) ≤ (5154425910727113/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (22695266834393237591/20000000000000000000 : ℝ)^32 ≤ (5154425910727113/5000000000000000 : ℝ)^133 := by
      have hnat : (22695266834393237591 : ℕ)^32*5000000000000000^133 ≤ 5154425910727113^133*20000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22695266834393237591 20000000000000000000 5154425910727113 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5154425910727113/5000000000000000 : ℝ)) (X := (22695266834393237591/20000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s4_corner2b : (12695266834393237591/10000000000000000000 : ℝ) ≤ (661936605241231/625000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (12695266834393237591/10000000000000000000 : ℝ)^32 ≤ (661936605241231/625000000000000 : ℝ)^133 := by
      have hnat : (12695266834393237591 : ℕ)^32*625000000000000^133 ≤ 661936605241231^133*10000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12695266834393237591 10000000000000000000 661936605241231 625000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (661936605241231/625000000000000 : ℝ)) (X := (12695266834393237591/10000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s4_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(154425910727113/3087050000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(28213386240547/617410000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (61741/100000 : ℝ)) (alpha := (154425910727113/3087050000000000 : ℝ)) (beta := (28213386240547/617410000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow2,s4_corner2a]) (by linarith only [s4_pow2,s4_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (61741/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(154425910727113/3087050000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(28213386240547/617410000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s4_0 : ((-1124850093/5000000000 : ℝ)*X 0 0+(2079804927/5000000000 : ℝ)*X 0 1+(-6284424569/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305060_s4_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_1 : ((4462825833/10000000000 : ℝ)*X 1 0+(-647998939/2500000000 : ℝ)*X 1 1+(-2877078247/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305060_s4_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_2 : ((592661447/1250000000 : ℝ)*X 2 0+(291617363/500000000 : ℝ)*X 2 1+(536342763/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305060_s4_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_6 : ((339186139/500000000 : ℝ)*X 0 0+(1108805001/2500000000 : ℝ)*X 0 1+(-555149241/5000000000 : ℝ)*X 0 2+(339186139/500000000 : ℝ)*X 1 0+(1108805001/2500000000 : ℝ)*X 1 1+(-555149241/5000000000 : ℝ)*X 1 2+(339186139/500000000 : ℝ)*X 2 0+(1108805001/2500000000 : ℝ)*X 2 1+(-555149241/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305060_s4_s4_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_7 : ((-1020449009/5000000000 : ℝ)*X 0 0+(379824523/1000000000 : ℝ)*X 0 1+(-210668421/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305060_s4_s4_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_8 : ((4078362857/10000000000 : ℝ)*X 1 0+(-1645654799/10000000000 : ℝ)*X 1 1+(-6767766567/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305060_s4_s4_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_9 : ((435946903/1000000000 : ℝ)*X 2 0+(6794503621/10000000000 : ℝ)*X 2 1+(12066443/100000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305060_s4_s4_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_13 : ((6309991453/10000000000 : ℝ)*X 0 0+(674013977/1250000000 : ℝ)*X 0 1+(-292242121/10000000000 : ℝ)*X 0 2+(6309991453/10000000000 : ℝ)*X 1 0+(674013977/1250000000 : ℝ)*X 1 1+(-292242121/10000000000 : ℝ)*X 1 2+(6309991453/10000000000 : ℝ)*X 2 0+(674013977/1250000000 : ℝ)*X 2 1+(-292242121/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305060_s4_s4_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_14 : ((-1338765077/10000000000 : ℝ)*X 0 0+(869836659/2000000000 : ℝ)*X 0 1+(-269009063/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305060_s4_s4_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_15 : ((251831807/625000000 : ℝ)*X 1 0+(-1735161603/10000000000 : ℝ)*X 1 1+(-6751607071/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305060_s4_s4_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_16 : ((714812469/1250000000 : ℝ)*X 2 0+(550853967/1000000000 : ℝ)*X 2 1+(611402107/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305060_s4_s4_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_20 : ((7763225859/10000000000 : ℝ)*X 0 0+(3710256697/10000000000 : ℝ)*X 0 1+(-325509849/10000000000 : ℝ)*X 0 2+(7763225859/10000000000 : ℝ)*X 1 0+(3710256697/10000000000 : ℝ)*X 1 1+(-325509849/10000000000 : ℝ)*X 1 2+(7763225859/10000000000 : ℝ)*X 2 0+(3710256697/10000000000 : ℝ)*X 2 1+(-325509849/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305060_s4_s4_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_21 : ((-133737127/1250000000 : ℝ)*X 0 0+(1310546903/2500000000 : ℝ)*X 0 1+(-6068745957/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305060_s4_s4_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_22 : ((5706258603/10000000000 : ℝ)*X 1 0+(-1573418207/10000000000 : ℝ)*X 1 1+(-1322915127/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305060_s4_s4_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_23 : ((4209773003/10000000000 : ℝ)*X 2 0+(6381263439/10000000000 : ℝ)*X 2 1+(2051985283/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305060_s4_s4_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_27 : ((7970406689/10000000000 : ℝ)*X 0 0+(21369091/62500000 : ℝ)*X 0 1+(-378453211/10000000000 : ℝ)*X 0 2+(7970406689/10000000000 : ℝ)*X 1 0+(21369091/62500000 : ℝ)*X 1 1+(-378453211/10000000000 : ℝ)*X 1 2+(7970406689/10000000000 : ℝ)*X 2 0+(21369091/62500000 : ℝ)*X 2 1+(-378453211/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305060_s4_s4_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s4_0 : (0 : ℝ) ≤ ((4789/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4789/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (22639798940509563085586294623/1364236689625468750000000000000000 : ℝ) := by norm_num
    linear_combination (207531/125000000000 : ℝ)*(base5) + (11681469/1000000000000 : ℝ)*(base39) + (3837077/1000000000000 : ℝ)*(base49) + (489766235131/1000000000000 : ℝ)*(base59) + (541586176471/100000000000 : ℝ)*(major_s4_0) + (541586176471/100000000000 : ℝ)*(major_s4_1) + (541586176471/100000000000 : ℝ)*(major_s4_2) + (8036717/125000000000 : ℝ)*(sp_s4_1) + (1822568125977/250000000000 : ℝ)*(sp_s4_7) + (7289286705793/1000000000000 : ℝ)*(sp_s4_8) + (1822521308927/250000000000 : ℝ)*(sp_s4_9) + (44268047919/12500000000 : ℝ)*(sp_s4_13) + (46075219/50000000000 : ℝ)*(sp_s4_15) + (188928449/1000000000000 : ℝ)*(sp_s4_23) + (442680686721/125000000000 : ℝ)*(f.failure) + (1822568125977/250000000000 : ℝ)*(f.sum) + (1332853357489096277/46368108410000000000000000000000 : ℝ)*base63 + (15960746625407/61741000000000000000000000 : ℝ)*base65 + (417776765109831/751010000000000000000000000 : ℝ)*base66 + (112287993276977/617410000000000000000000000 : ℝ)*base69 + (1103590691576861573/11335184542500000000000000000000 : ℝ)*base70 + (203247788994863/734370000000000000000000000 : ℝ)*base73 + (6926432282843/37550500000000000000000000 : ℝ)*base75 + (1713169193753/91796250000000000000000000 : ℝ)*base77 + (104039204303313949/424245549000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (739/1562500000000000 : ℝ)*base86 + (739/1562500000000000 : ℝ)*base88 + (739/1562500000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s4_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(25967/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(25967/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4316268447487727193087/384351031250000000000000000 : ℝ) := by norm_num
    linear_combination (186167/500000000000 : ℝ)*(base5) + (7600299/1000000000000 : ℝ)*(base12) + (18342025521/125000000000 : ℝ)*(base59) + (3297433139/625000000 : ℝ)*(major_s4_0) + (3297433139/625000000 : ℝ)*(major_s4_1) + (3297433139/625000000 : ℝ)*(major_s4_2) + (6942007/250000000000 : ℝ)*(sp_s4_2) + (7767101/1000000000000 : ℝ)*(sp_s4_6) + (10910483/200000000000 : ℝ)*(sp_s4_7) + (7101800564101/1000000000000 : ℝ)*(sp_s4_14) + (443866419801/62500000000 : ℝ)*(sp_s4_15) + (3550917660561/500000000000 : ℝ)*(sp_s4_16) + (3449727137903/1000000000000 : ℝ)*(sp_s4_20) + (184307303/1000000000000 : ℝ)*(sp_s4_27) + (3449919584641/1000000000000 : ℝ)*(f.failure) + (443866419801/62500000000 : ℝ)*(f.sum) + (986216051709881/122992330000000000000000000000 : ℝ)*base62 + (334438467573/532250000000000000000000 : ℝ)*base65 + (17110802006151/57770000000000000000000000 : ℝ)*base66 + (9467030993/166328125000000000000000 : ℝ)*base68 + (6603740570713939/17181030000000000000000000000 : ℝ)*base71 + (1196642936753/4035000000000000000000000 : ℝ)*base73 + (446606763277/3610625000000000000000000 : ℝ)*base74 + (325614843677/1614000000000000000000000 : ℝ)*base76 + (2138877196428329/23310195000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (661/3125000000000000 : ℝ)*base86 + (661/3125000000000000 : ℝ)*base88 + (661/3125000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s4_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-7097/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-7097/20000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (28943329754412374828832686697/3118255290572500000000000000000000 : ℝ) := by norm_num
    linear_combination (98969/10000000000 : ℝ)*(base11) + (247289/1000000000000 : ℝ)*(base15) + (90398021061/200000000000 : ℝ)*(base39) + (104819062651/1000000000000 : ℝ)*(base59) + (4179191172077/1000000000000 : ℝ)*(major_s4_0) + (4179191172077/1000000000000 : ℝ)*(major_s4_1) + (4179191172077/1000000000000 : ℝ)*(major_s4_2) + (26068131/1000000000000 : ℝ)*(sp_s4_0) + (4534809/500000000000 : ℝ)*(sp_s4_2) + (54634349/1000000000000 : ℝ)*(sp_s4_9) + (1406389942823/250000000000 : ℝ)*(sp_s4_21) + (2812797744517/500000000000 : ℝ)*(sp_s4_22) + (1125106406471/200000000000 : ℝ)*(sp_s4_23) + (2732783513861/1000000000000 : ℝ)*(sp_s4_27) + (2732783513861/1000000000000 : ℝ)*(f.failure) + (5625595736323/1000000000000 : ℝ)*(f.sum) + (44970642250064296839/463681084100000000000000000000000 : ℝ)*base62 + (23160055243977/617410000000000000000000000 : ℝ)*base64 + (2000860221806191/7510100000000000000000000000 : ℝ)*base67 + (849716456057327/1543525000000000000000000000 : ℝ)*base68 + (216909348996224127959/453407381700000000000000000000000 : ℝ)*base71 + (1942957332977303/3671850000000000000000000000 : ℝ)*base73 + (99807160471111/7510100000000000000000000000 : ℝ)*base74 + (1124475342911489/7343700000000000000000000000 : ℝ)*base77 + (12233654419069475591/42424554900000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (547/1562500000000000 : ℝ)*base87 + (547/1562500000000000 : ℝ)*base89 + (547/1562500000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s4_0,ratio_s4_1,ratio_s4_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev3 : (0 : ℝ) ≤ ((73437/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(73437/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(75101/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(75101/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-61741/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-61741/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((4789/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4789/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(25967/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(25967/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-7097/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-7097/20000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c305060_s4 p hpa hpb X hX hprev3

#print axioms solution
