-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c305082_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:34:02.056388+00:00
-- url     : https://prove2.me/submissions/c8328958-9348-4658-a33e-3ae6611a99e8

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
theorem collision_support_c305082_s1_s1_0 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3780297471/10000000000 : ℝ)*x 0 + (3194903779/10000000000 : ℝ)*x 1 + (5882496499/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3780297471/10000000000 : ℝ)^67 ≤ (6965064042901/25000000000000 : ℝ)^51 := by
    have hnat : (3780297471 : ℕ)^67*25000000000000^51 ≤ 6965064042901^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3780297471 10000000000 6965064042901 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3194903779/10000000000 : ℝ)^67 ≤ (22335390924609/100000000000000 : ℝ)^51 := by
    have hnat : (3194903779 : ℕ)^67*100000000000000^51 ≤ 22335390924609^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3194903779 10000000000 22335390924609 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5882496499/10000000000 : ℝ)^67 ≤ (49804352888261/100000000000000 : ℝ)^51 := by
    have hnat : (5882496499 : ℕ)^67*100000000000000^51 ≤ 49804352888261^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5882496499 10000000000 49804352888261 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3780297471/10000000000 : ℝ), (3194903779/10000000000 : ℝ), (5882496499/10000000000 : ℝ)] ![(6965064042901/25000000000000 : ℝ), (22335390924609/100000000000000 : ℝ), (49804352888261/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3780297471/10000000000 : ℝ)|^67 ≤ (6965064042901/25000000000000 : ℝ)^51
        have hw : |(-3780297471/10000000000 : ℝ)|=(3780297471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3194903779/10000000000 : ℝ)|^67 ≤ (22335390924609/100000000000000 : ℝ)^51
        have hw : |(3194903779/10000000000 : ℝ)|=(3194903779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5882496499/10000000000 : ℝ)|^67 ≤ (49804352888261/100000000000000 : ℝ)^51
        have hw : |(5882496499/10000000000 : ℝ)|=(5882496499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305082_s1_s1_2 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (629504197/1000000000 : ℝ)*x 0 + (2599784677/5000000000 : ℝ)*x 1 + (-72917003/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (629504197/1000000000 : ℝ)^67 ≤ (13610666268707/25000000000000 : ℝ)^51 := by
    have hnat : (629504197 : ℕ)^67*25000000000000^51 ≤ 13610666268707^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      629504197 1000000000 13610666268707 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2599784677/5000000000 : ℝ)^67 ≤ (42350554502389/100000000000000 : ℝ)^51 := by
    have hnat : (2599784677 : ℕ)^67*100000000000000^51 ≤ 42350554502389^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2599784677 5000000000 42350554502389 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (72917003/1000000000 : ℝ)^67 ≤ (1603390202653/50000000000000 : ℝ)^51 := by
    have hnat : (72917003 : ℕ)^67*50000000000000^51 ≤ 1603390202653^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      72917003 1000000000 1603390202653 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(629504197/1000000000 : ℝ), (2599784677/5000000000 : ℝ), (-72917003/1000000000 : ℝ)] ![(13610666268707/25000000000000 : ℝ), (42350554502389/100000000000000 : ℝ), (1603390202653/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(629504197/1000000000 : ℝ)|^67 ≤ (13610666268707/25000000000000 : ℝ)^51
        have hw : |(629504197/1000000000 : ℝ)|=(629504197/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2599784677/5000000000 : ℝ)|^67 ≤ (42350554502389/100000000000000 : ℝ)^51
        have hw : |(2599784677/5000000000 : ℝ)|=(2599784677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-72917003/1000000000 : ℝ)|^67 ≤ (1603390202653/50000000000000 : ℝ)^51
        have hw : |(-72917003/1000000000 : ℝ)|=(72917003/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305082_s1_s1_7 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-182194323/625000000 : ℝ)*x 0 + (2344672987/10000000000 : ℝ)*x 1 + (3615763719/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (182194323/625000000 : ℝ)^67 ≤ (9900870945303/50000000000000 : ℝ)^51 := by
    have hnat : (182194323 : ℕ)^67*50000000000000^51 ≤ 9900870945303^51*625000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      182194323 625000000 9900870945303 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2344672987/10000000000 : ℝ)^67 ≤ (464848095661/3125000000000 : ℝ)^51 := by
    have hnat : (2344672987 : ℕ)^67*3125000000000^51 ≤ 464848095661^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2344672987 10000000000 464848095661 3125000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3615763719/5000000000 : ℝ)^67 ≤ (16330779757341/25000000000000 : ℝ)^51 := by
    have hnat : (3615763719 : ℕ)^67*25000000000000^51 ≤ 16330779757341^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3615763719 5000000000 16330779757341 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-182194323/625000000 : ℝ), (2344672987/10000000000 : ℝ), (3615763719/5000000000 : ℝ)] ![(9900870945303/50000000000000 : ℝ), (464848095661/3125000000000 : ℝ), (16330779757341/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-182194323/625000000 : ℝ)|^67 ≤ (9900870945303/50000000000000 : ℝ)^51
        have hw : |(-182194323/625000000 : ℝ)|=(182194323/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2344672987/10000000000 : ℝ)|^67 ≤ (464848095661/3125000000000 : ℝ)^51
        have hw : |(2344672987/10000000000 : ℝ)|=(2344672987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3615763719/5000000000 : ℝ)|^67 ≤ (16330779757341/25000000000000 : ℝ)^51
        have hw : |(3615763719/5000000000 : ℝ)|=(3615763719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305082_s1_s1_8 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1025883891/2500000000 : ℝ)*x 0 + (-1708213433/10000000000 : ℝ)*x 1 + (3352900129/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1025883891/2500000000 : ℝ)^67 ≤ (6206204251921/20000000000000 : ℝ)^51 := by
    have hnat : (1025883891 : ℕ)^67*20000000000000^51 ≤ 6206204251921^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025883891 2500000000 6206204251921 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1708213433/10000000000 : ℝ)^67 ≤ (9812304955321/100000000000000 : ℝ)^51 := by
    have hnat : (1708213433 : ℕ)^67*100000000000000^51 ≤ 9812304955321^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1708213433 10000000000 9812304955321 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3352900129/5000000000 : ℝ)^67 ≤ (59156673771683/100000000000000 : ℝ)^51 := by
    have hnat : (3352900129 : ℕ)^67*100000000000000^51 ≤ 59156673771683^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3352900129 5000000000 59156673771683 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1025883891/2500000000 : ℝ), (-1708213433/10000000000 : ℝ), (3352900129/5000000000 : ℝ)] ![(6206204251921/20000000000000 : ℝ), (9812304955321/100000000000000 : ℝ), (59156673771683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1025883891/2500000000 : ℝ)|^67 ≤ (6206204251921/20000000000000 : ℝ)^51
        have hw : |(1025883891/2500000000 : ℝ)|=(1025883891/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1708213433/10000000000 : ℝ)|^67 ≤ (9812304955321/100000000000000 : ℝ)^51
        have hw : |(-1708213433/10000000000 : ℝ)|=(1708213433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3352900129/5000000000 : ℝ)|^67 ≤ (59156673771683/100000000000000 : ℝ)^51
        have hw : |(3352900129/5000000000 : ℝ)|=(3352900129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305082_s1_s1_9 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (641043571/1250000000 : ℝ)*x 0 + (6604951851/10000000000 : ℝ)*x 1 + (-154956497/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (641043571/1250000000 : ℝ)^67 ≤ (41590112616119/100000000000000 : ℝ)^51 := by
    have hnat : (641043571 : ℕ)^67*100000000000000^51 ≤ 41590112616119^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      641043571 1250000000 41590112616119 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6604951851/10000000000 : ℝ)^67 ≤ (57990676560419/100000000000000 : ℝ)^51 := by
    have hnat : (6604951851 : ℕ)^67*100000000000000^51 ≤ 57990676560419^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6604951851 10000000000 57990676560419 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (154956497/10000000000 : ℝ)^67 ≤ (419210806289/100000000000000 : ℝ)^51 := by
    have hnat : (154956497 : ℕ)^67*100000000000000^51 ≤ 419210806289^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      154956497 10000000000 419210806289 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(641043571/1250000000 : ℝ), (6604951851/10000000000 : ℝ), (-154956497/10000000000 : ℝ)] ![(41590112616119/100000000000000 : ℝ), (57990676560419/100000000000000 : ℝ), (419210806289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(641043571/1250000000 : ℝ)|^67 ≤ (41590112616119/100000000000000 : ℝ)^51
        have hw : |(641043571/1250000000 : ℝ)|=(641043571/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6604951851/10000000000 : ℝ)|^67 ≤ (57990676560419/100000000000000 : ℝ)^51
        have hw : |(6604951851/10000000000 : ℝ)|=(6604951851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-154956497/10000000000 : ℝ)|^67 ≤ (419210806289/100000000000000 : ℝ)^51
        have hw : |(-154956497/10000000000 : ℝ)|=(154956497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305082_s1_s1_13 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (13259499/10000000000 : ℝ)*x 0 + (8163135093/10000000000 : ℝ)*x 1 + (827213349/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13259499/10000000000 : ℝ)^67 ≤ (3317573239/20000000000000 : ℝ)^51 := by
    have hnat : (13259499 : ℕ)^67*20000000000000^51 ≤ 3317573239^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13259499 10000000000 3317573239 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8163135093/10000000000 : ℝ)^67 ≤ (7659567941747/10000000000000 : ℝ)^51 := by
    have hnat : (8163135093 : ℕ)^67*10000000000000^51 ≤ 7659567941747^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8163135093 10000000000 7659567941747 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (827213349/2500000000 : ℝ)^67 ≤ (23387732705213/100000000000000 : ℝ)^51 := by
    have hnat : (827213349 : ℕ)^67*100000000000000^51 ≤ 23387732705213^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      827213349 2500000000 23387732705213 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(13259499/10000000000 : ℝ), (8163135093/10000000000 : ℝ), (827213349/2500000000 : ℝ)] ![(3317573239/20000000000000 : ℝ), (7659567941747/10000000000000 : ℝ), (23387732705213/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(13259499/10000000000 : ℝ)|^67 ≤ (3317573239/20000000000000 : ℝ)^51
        have hw : |(13259499/10000000000 : ℝ)|=(13259499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8163135093/10000000000 : ℝ)|^67 ≤ (7659567941747/10000000000000 : ℝ)^51
        have hw : |(8163135093/10000000000 : ℝ)|=(8163135093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(827213349/2500000000 : ℝ)|^67 ≤ (23387732705213/100000000000000 : ℝ)^51
        have hw : |(827213349/2500000000 : ℝ)|=(827213349/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305082_s1_s1_14 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3039780311/10000000000 : ℝ)*x 0 + (2400919931/10000000000 : ℝ)*x 1 + (1774276933/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3039780311/10000000000 : ℝ)^67 ≤ (20921682767417/100000000000000 : ℝ)^51 := by
    have hnat : (3039780311 : ℕ)^67*100000000000000^51 ≤ 20921682767417^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3039780311 10000000000 20921682767417 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2400919931/10000000000 : ℝ)^67 ≤ (959105490513/6250000000000 : ℝ)^51 := by
    have hnat : (2400919931 : ℕ)^67*6250000000000^51 ≤ 959105490513^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2400919931 10000000000 959105490513 6250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1774276933/2500000000 : ℝ)^67 ≤ (63732629374677/100000000000000 : ℝ)^51 := by
    have hnat : (1774276933 : ℕ)^67*100000000000000^51 ≤ 63732629374677^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1774276933 2500000000 63732629374677 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3039780311/10000000000 : ℝ), (2400919931/10000000000 : ℝ), (1774276933/2500000000 : ℝ)] ![(20921682767417/100000000000000 : ℝ), (959105490513/6250000000000 : ℝ), (63732629374677/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3039780311/10000000000 : ℝ)|^67 ≤ (20921682767417/100000000000000 : ℝ)^51
        have hw : |(-3039780311/10000000000 : ℝ)|=(3039780311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2400919931/10000000000 : ℝ)|^67 ≤ (959105490513/6250000000000 : ℝ)^51
        have hw : |(2400919931/10000000000 : ℝ)|=(2400919931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1774276933/2500000000 : ℝ)|^67 ≤ (63732629374677/100000000000000 : ℝ)^51
        have hw : |(1774276933/2500000000 : ℝ)|=(1774276933/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305082_s1_s1_15 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6523595647/10000000000 : ℝ)*x 0 + (-523748131/2000000000 : ℝ)*x 1 + (444981563/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6523595647/10000000000 : ℝ)^67 ≤ (7131762979/12500000000 : ℝ)^51 := by
    have hnat : (6523595647 : ℕ)^67*12500000000^51 ≤ 7131762979^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6523595647 10000000000 7131762979 12500000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (523748131/2000000000 : ℝ)^67 ≤ (1075011943199/6250000000000 : ℝ)^51 := by
    have hnat : (523748131 : ℕ)^67*6250000000000^51 ≤ 1075011943199^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523748131 2000000000 1075011943199 6250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (444981563/1250000000 : ℝ)^67 ≤ (25745705062679/100000000000000 : ℝ)^51 := by
    have hnat : (444981563 : ℕ)^67*100000000000000^51 ≤ 25745705062679^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      444981563 1250000000 25745705062679 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6523595647/10000000000 : ℝ), (-523748131/2000000000 : ℝ), (444981563/1250000000 : ℝ)] ![(7131762979/12500000000 : ℝ), (1075011943199/6250000000000 : ℝ), (25745705062679/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6523595647/10000000000 : ℝ)|^67 ≤ (7131762979/12500000000 : ℝ)^51
        have hw : |(6523595647/10000000000 : ℝ)|=(6523595647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-523748131/2000000000 : ℝ)|^67 ≤ (1075011943199/6250000000000 : ℝ)^51
        have hw : |(-523748131/2000000000 : ℝ)|=(523748131/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(444981563/1250000000 : ℝ)|^67 ≤ (25745705062679/100000000000000 : ℝ)^51
        have hw : |(444981563/1250000000 : ℝ)|=(444981563/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305082_s1_s1_16 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1536923139/2000000000 : ℝ)*x 0 + (3692270877/10000000000 : ℝ)*x 1 + (-554311769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1536923139/2000000000 : ℝ)^67 ≤ (70752030397633/100000000000000 : ℝ)^51 := by
    have hnat : (1536923139 : ℕ)^67*100000000000000^51 ≤ 70752030397633^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1536923139 2000000000 70752030397633 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3692270877/10000000000 : ℝ)^67 ≤ (5402223015041/20000000000000 : ℝ)^51 := by
    have hnat : (3692270877 : ℕ)^67*20000000000000^51 ≤ 5402223015041^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3692270877 10000000000 5402223015041 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (554311769/10000000000 : ℝ)^67 ≤ (1118427257689/50000000000000 : ℝ)^51 := by
    have hnat : (554311769 : ℕ)^67*50000000000000^51 ≤ 1118427257689^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      554311769 10000000000 1118427257689 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1536923139/2000000000 : ℝ), (3692270877/10000000000 : ℝ), (-554311769/10000000000 : ℝ)] ![(70752030397633/100000000000000 : ℝ), (5402223015041/20000000000000 : ℝ), (1118427257689/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1536923139/2000000000 : ℝ)|^67 ≤ (70752030397633/100000000000000 : ℝ)^51
        have hw : |(1536923139/2000000000 : ℝ)|=(1536923139/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3692270877/10000000000 : ℝ)|^67 ≤ (5402223015041/20000000000000 : ℝ)^51
        have hw : |(3692270877/10000000000 : ℝ)|=(3692270877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-554311769/10000000000 : ℝ)|^67 ≤ (1118427257689/50000000000000 : ℝ)^51
        have hw : |(-554311769/10000000000 : ℝ)|=(554311769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305082_s1_s1_20 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-4905151/2500000000 : ℝ)*x 0 + (4325943893/10000000000 : ℝ)*x 1 + (1469673573/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4905151/2500000000 : ℝ)^67 ≤ (3469582731/12500000000000 : ℝ)^51 := by
    have hnat : (4905151 : ℕ)^67*12500000000000^51 ≤ 3469582731^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4905151 2500000000 3469582731 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4325943893/10000000000 : ℝ)^67 ≤ (16629537973047/50000000000000 : ℝ)^51 := by
    have hnat : (4325943893 : ℕ)^67*50000000000000^51 ≤ 16629537973047^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4325943893 10000000000 16629537973047 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1469673573/2000000000 : ℝ)^67 ≤ (6671316738831/10000000000000 : ℝ)^51 := by
    have hnat : (1469673573 : ℕ)^67*10000000000000^51 ≤ 6671316738831^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1469673573 2000000000 6671316738831 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4905151/2500000000 : ℝ), (4325943893/10000000000 : ℝ), (1469673573/2000000000 : ℝ)] ![(3469582731/12500000000000 : ℝ), (16629537973047/50000000000000 : ℝ), (6671316738831/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4905151/2500000000 : ℝ)|^67 ≤ (3469582731/12500000000000 : ℝ)^51
        have hw : |(-4905151/2500000000 : ℝ)|=(4905151/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4325943893/10000000000 : ℝ)|^67 ≤ (16629537973047/50000000000000 : ℝ)^51
        have hw : |(4325943893/10000000000 : ℝ)|=(4325943893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1469673573/2000000000 : ℝ)|^67 ≤ (6671316738831/10000000000000 : ℝ)^51
        have hw : |(1469673573/2000000000 : ℝ)|=(1469673573/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305082_s1_s1_21 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-4706339613/10000000000 : ℝ)*x 0 + (3765265167/10000000000 : ℝ)*x 1 + (4510162101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4706339613/10000000000 : ℝ)^67 ≤ (4644143945169/12500000000000 : ℝ)^51 := by
    have hnat : (4706339613 : ℕ)^67*12500000000000^51 ≤ 4644143945169^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4706339613 10000000000 4644143945169 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3765265167/10000000000 : ℝ)^67 ≤ (86608764731/312500000000 : ℝ)^51 := by
    have hnat : (3765265167 : ℕ)^67*312500000000^51 ≤ 86608764731^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3765265167 10000000000 86608764731 312500000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4510162101/10000000000 : ℝ)^67 ≤ (35132043708729/100000000000000 : ℝ)^51 := by
    have hnat : (4510162101 : ℕ)^67*100000000000000^51 ≤ 35132043708729^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4510162101 10000000000 35132043708729 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4706339613/10000000000 : ℝ), (3765265167/10000000000 : ℝ), (4510162101/10000000000 : ℝ)] ![(4644143945169/12500000000000 : ℝ), (86608764731/312500000000 : ℝ), (35132043708729/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4706339613/10000000000 : ℝ)|^67 ≤ (4644143945169/12500000000000 : ℝ)^51
        have hw : |(-4706339613/10000000000 : ℝ)|=(4706339613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3765265167/10000000000 : ℝ)|^67 ≤ (86608764731/312500000000 : ℝ)^51
        have hw : |(3765265167/10000000000 : ℝ)|=(3765265167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4510162101/10000000000 : ℝ)|^67 ≤ (35132043708729/100000000000000 : ℝ)^51
        have hw : |(4510162101/10000000000 : ℝ)|=(4510162101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305082_s1_s1_22 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4647581991/10000000000 : ℝ)*x 0 + (-3620692091/10000000000 : ℝ)*x 1 + (4704080613/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4647581991/10000000000 : ℝ)^67 ≤ (36544978146173/100000000000000 : ℝ)^51 := by
    have hnat : (4647581991 : ℕ)^67*100000000000000^51 ≤ 36544978146173^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4647581991 10000000000 36544978146173 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3620692091/10000000000 : ℝ)^67 ≤ (329066205017/1250000000000 : ℝ)^51 := by
    have hnat : (3620692091 : ℕ)^67*1250000000000^51 ≤ 329066205017^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3620692091 10000000000 329066205017 1250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4704080613/10000000000 : ℝ)^67 ≤ (37129725431313/100000000000000 : ℝ)^51 := by
    have hnat : (4704080613 : ℕ)^67*100000000000000^51 ≤ 37129725431313^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4704080613 10000000000 37129725431313 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4647581991/10000000000 : ℝ), (-3620692091/10000000000 : ℝ), (4704080613/10000000000 : ℝ)] ![(36544978146173/100000000000000 : ℝ), (329066205017/1250000000000 : ℝ), (37129725431313/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4647581991/10000000000 : ℝ)|^67 ≤ (36544978146173/100000000000000 : ℝ)^51
        have hw : |(4647581991/10000000000 : ℝ)|=(4647581991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3620692091/10000000000 : ℝ)|^67 ≤ (329066205017/1250000000000 : ℝ)^51
        have hw : |(-3620692091/10000000000 : ℝ)|=(3620692091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4704080613/10000000000 : ℝ)|^67 ≤ (37129725431313/100000000000000 : ℝ)^51
        have hw : |(4704080613/10000000000 : ℝ)|=(4704080613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305082_s1_s1_23 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1882849901/2500000000 : ℝ)*x 0 + (1975571453/5000000000 : ℝ)*x 1 + (-423251517/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1882849901/2500000000 : ℝ)^67 ≤ (68904638255233/100000000000000 : ℝ)^51 := by
    have hnat : (1882849901 : ℕ)^67*100000000000000^51 ≤ 68904638255233^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1882849901 2500000000 68904638255233 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1975571453/5000000000 : ℝ)^67 ≤ (738149601279/2500000000000 : ℝ)^51 := by
    have hnat : (1975571453 : ℕ)^67*2500000000000^51 ≤ 738149601279^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1975571453 5000000000 738149601279 2500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (423251517/10000000000 : ℝ)^67 ≤ (196172210079/12500000000000 : ℝ)^51 := by
    have hnat : (423251517 : ℕ)^67*12500000000000^51 ≤ 196172210079^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423251517 10000000000 196172210079 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1882849901/2500000000 : ℝ), (1975571453/5000000000 : ℝ), (-423251517/10000000000 : ℝ)] ![(68904638255233/100000000000000 : ℝ), (738149601279/2500000000000 : ℝ), (196172210079/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1882849901/2500000000 : ℝ)|^67 ≤ (68904638255233/100000000000000 : ℝ)^51
        have hw : |(1882849901/2500000000 : ℝ)|=(1882849901/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1975571453/5000000000 : ℝ)|^67 ≤ (738149601279/2500000000000 : ℝ)^51
        have hw : |(1975571453/5000000000 : ℝ)|=(1975571453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-423251517/10000000000 : ℝ)|^67 ≤ (196172210079/12500000000000 : ℝ)^51
        have hw : |(-423251517/10000000000 : ℝ)|=(423251517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305082_s1_s1_27 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-130498513/10000000000 : ℝ)*x 0 + (3598334801/5000000000 : ℝ)*x 1 + (4473339039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (130498513/10000000000 : ℝ)^67 ≤ (334520698197/100000000000000 : ℝ)^51 := by
    have hnat : (130498513 : ℕ)^67*100000000000000^51 ≤ 334520698197^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130498513 10000000000 334520698197 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3598334801/5000000000 : ℝ)^67 ≤ (64909773677753/100000000000000 : ℝ)^51 := by
    have hnat : (3598334801 : ℕ)^67*100000000000000^51 ≤ 64909773677753^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3598334801 5000000000 64909773677753 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4473339039/10000000000 : ℝ)^67 ≤ (868892640227/2500000000000 : ℝ)^51 := by
    have hnat : (4473339039 : ℕ)^67*2500000000000^51 ≤ 868892640227^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4473339039 10000000000 868892640227 2500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-130498513/10000000000 : ℝ), (3598334801/5000000000 : ℝ), (4473339039/10000000000 : ℝ)] ![(334520698197/100000000000000 : ℝ), (64909773677753/100000000000000 : ℝ), (868892640227/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-130498513/10000000000 : ℝ)|^67 ≤ (334520698197/100000000000000 : ℝ)^51
        have hw : |(-130498513/10000000000 : ℝ)|=(130498513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3598334801/5000000000 : ℝ)|^67 ≤ (64909773677753/100000000000000 : ℝ)^51
        have hw : |(3598334801/5000000000 : ℝ)|=(3598334801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4473339039/10000000000 : ℝ)|^67 ≤ (868892640227/2500000000000 : ℝ)^51
        have hw : |(4473339039/10000000000 : ℝ)|=(4473339039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c305082_s1 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((84353/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(84353/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((95949/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(95949/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(8691/10000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(8691/10000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((33649/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(33649/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((81227/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(81227/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(68223/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(68223/100000 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76771/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76771/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base7 : ((1 : ℝ)*T) ≤ (93447/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base44 : ((-1 : ℝ)*N 1+(1 : ℝ)*P 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base60 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s1_pow0 : (84353/100000 : ℝ) ^ (133/32 : ℝ) ≤ (49300955849865661441/100000000000000000000 : ℝ) := by
    have hpowers : (84353/100000 : ℝ)^133 ≤ (49300955849865661441/100000000000000000000 : ℝ)^32 := by
      have hnat : (84353 : ℕ)^133*100000000000000000000^32 ≤ 49300955849865661441^32*100000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        84353 100000 49300955849865661441 100000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (84353/100000 : ℝ)) (X := (49300955849865661441/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s1_corner0a : (149300955849865661441/100000000000000000000 : ℝ) ≤ (11012342762013953/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (149300955849865661441/100000000000000000000 : ℝ)^32 ≤ (11012342762013953/10000000000000000 : ℝ)^133 := by
      have hnat : (149300955849865661441 : ℕ)^32*10000000000000000^133 ≤ 11012342762013953^133*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        149300955849865661441 100000000000000000000 11012342762013953 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11012342762013953/10000000000000000 : ℝ)) (X := (149300955849865661441/100000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s1_corner0b : (99300955849865661441/50000000000000000000 : ℝ) ≤ (11794927073823029/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (99300955849865661441/50000000000000000000 : ℝ)^32 ≤ (11794927073823029/10000000000000000 : ℝ)^133 := by
      have hnat : (99300955849865661441 : ℕ)^32*10000000000000000^133 ≤ 11794927073823029^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        99300955849865661441 50000000000000000000 11794927073823029 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11794927073823029/10000000000000000 : ℝ)) (X := (99300955849865661441/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1012342762013953/8435300000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(195646077952269/2108825000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (84353/100000 : ℝ)) (alpha := (1012342762013953/8435300000000000 : ℝ)) (beta := (195646077952269/2108825000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (84353/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1012342762013953/8435300000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(195646077952269/2108825000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (95949/100000 : ℝ) ^ (133/32 : ℝ) ≤ (84208441935646949027/100000000000000000000 : ℝ) := by
    have hpowers : (95949/100000 : ℝ)^133 ≤ (84208441935646949027/100000000000000000000 : ℝ)^32 := by
      have hnat : (95949 : ℕ)^133*100000000000000000000^32 ≤ 84208441935646949027^32*100000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        95949 100000 84208441935646949027 100000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (95949/100000 : ℝ)) (X := (84208441935646949027/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s1_corner1a : (184208441935646949027/100000000000000000000 : ℝ) ≤ (11583341801302571/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (184208441935646949027/100000000000000000000 : ℝ)^32 ≤ (11583341801302571/10000000000000000 : ℝ)^133 := by
      have hnat : (184208441935646949027 : ℕ)^32*10000000000000000^133 ≤ 11583341801302571^133*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        184208441935646949027 100000000000000000000 11583341801302571 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11583341801302571/10000000000000000 : ℝ)) (X := (184208441935646949027/100000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s1_corner1b : (134208441935646949027/50000000000000000000 : ℝ) ≤ (3170387146860303/2500000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (134208441935646949027/50000000000000000000 : ℝ)^32 ≤ (3170387146860303/2500000000000000 : ℝ)^133 := by
      have hnat : (134208441935646949027 : ℕ)^32*2500000000000000^133 ≤ 3170387146860303^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        134208441935646949027 50000000000000000000 3170387146860303 2500000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3170387146860303/2500000000000000 : ℝ)) (X := (134208441935646949027/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1583341801302571/9594900000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(1098206786138641/9594900000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (95949/100000 : ℝ)) (alpha := (1583341801302571/9594900000000000 : ℝ)) (beta := (1098206786138641/9594900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (95949/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1583341801302571/9594900000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(1098206786138641/9594900000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (8691/10000 : ℝ) ^ (133/32 : ℝ) ≤ (13953998012683181923/25000000000000000000 : ℝ) := by
    have hpowers : (8691/10000 : ℝ)^133 ≤ (13953998012683181923/25000000000000000000 : ℝ)^32 := by
      have hnat : (8691 : ℕ)^133*25000000000000000000^32 ≤ 13953998012683181923^32*10000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8691 10000 13953998012683181923 25000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8691/10000 : ℝ)) (X := (13953998012683181923/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s1_corner2a : (38953998012683181923/25000000000000000000 : ℝ) ≤ (2781523621933953/2500000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (38953998012683181923/25000000000000000000 : ℝ)^32 ≤ (2781523621933953/2500000000000000 : ℝ)^133 := by
      have hnat : (38953998012683181923 : ℕ)^32*2500000000000000^133 ≤ 2781523621933953^133*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        38953998012683181923 25000000000000000000 2781523621933953 2500000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2781523621933953/2500000000000000 : ℝ)) (X := (38953998012683181923/25000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s1_corner2b : (26453998012683181923/12500000000000000000 : ℝ) ≤ (11976649810095819/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (26453998012683181923/12500000000000000000 : ℝ)^32 ≤ (11976649810095819/10000000000000000 : ℝ)^133 := by
      have hnat : (26453998012683181923 : ℕ)^32*10000000000000000^133 ≤ 11976649810095819^133*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26453998012683181923 12500000000000000000 11976649810095819 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11976649810095819/10000000000000000 : ℝ)) (X := (26453998012683181923/12500000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(281523621933953/2172750000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(283518440786669/2897000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (8691/10000 : ℝ)) (alpha := (281523621933953/2172750000000000 : ℝ)) (beta := (283518440786669/2897000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (8691/10000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(281523621933953/2172750000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(283518440786669/2897000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-3780297471/10000000000 : ℝ)*X 0 0+(3194903779/10000000000 : ℝ)*X 0 1+(5882496499/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305082_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((629504197/1000000000 : ℝ)*X 2 0+(2599784677/5000000000 : ℝ)*X 2 1+(-72917003/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305082_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-182194323/625000000 : ℝ)*X 0 0+(2344672987/10000000000 : ℝ)*X 0 1+(3615763719/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305082_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((1025883891/2500000000 : ℝ)*X 1 0+(-1708213433/10000000000 : ℝ)*X 1 1+(3352900129/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305082_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((641043571/1250000000 : ℝ)*X 2 0+(6604951851/10000000000 : ℝ)*X 2 1+(-154956497/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305082_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((13259499/10000000000 : ℝ)*X 0 0+(8163135093/10000000000 : ℝ)*X 0 1+(827213349/2500000000 : ℝ)*X 0 2+(13259499/10000000000 : ℝ)*X 1 0+(8163135093/10000000000 : ℝ)*X 1 1+(827213349/2500000000 : ℝ)*X 1 2+(13259499/10000000000 : ℝ)*X 2 0+(8163135093/10000000000 : ℝ)*X 2 1+(827213349/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305082_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-3039780311/10000000000 : ℝ)*X 0 0+(2400919931/10000000000 : ℝ)*X 0 1+(1774276933/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305082_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((6523595647/10000000000 : ℝ)*X 1 0+(-523748131/2000000000 : ℝ)*X 1 1+(444981563/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305082_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((1536923139/2000000000 : ℝ)*X 2 0+(3692270877/10000000000 : ℝ)*X 2 1+(-554311769/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305082_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((-4905151/2500000000 : ℝ)*X 0 0+(4325943893/10000000000 : ℝ)*X 0 1+(1469673573/2000000000 : ℝ)*X 0 2+(-4905151/2500000000 : ℝ)*X 1 0+(4325943893/10000000000 : ℝ)*X 1 1+(1469673573/2000000000 : ℝ)*X 1 2+(-4905151/2500000000 : ℝ)*X 2 0+(4325943893/10000000000 : ℝ)*X 2 1+(1469673573/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305082_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-4706339613/10000000000 : ℝ)*X 0 0+(3765265167/10000000000 : ℝ)*X 0 1+(4510162101/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305082_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((4647581991/10000000000 : ℝ)*X 1 0+(-3620692091/10000000000 : ℝ)*X 1 1+(4704080613/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305082_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((1882849901/2500000000 : ℝ)*X 2 0+(1975571453/5000000000 : ℝ)*X 2 1+(-423251517/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305082_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((-130498513/10000000000 : ℝ)*X 0 0+(3598334801/5000000000 : ℝ)*X 0 1+(4473339039/10000000000 : ℝ)*X 0 2+(-130498513/10000000000 : ℝ)*X 1 0+(3598334801/5000000000 : ℝ)*X 1 1+(4473339039/10000000000 : ℝ)*X 1 2+(-130498513/10000000000 : ℝ)*X 2 0+(3598334801/5000000000 : ℝ)*X 2 1+(4473339039/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305082_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((33649/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(33649/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (85008937741317899686823154481/9304412156075000000000000000000000 : ℝ) := by norm_num
    linear_combination (535675233081/1000000000000 : ℝ)*(base7) + (3296623/125000000000 : ℝ)*(base23) + (21364675479/1000000000000 : ℝ)*(base39) + (1978267/100000000000 : ℝ)*(base53) + (283419427259/1000000000000 : ℝ)*(base60) + (1292860336593/500000000000 : ℝ)*(major_s1_0) + (1292860336593/500000000000 : ℝ)*(major_s1_1) + (646425222629/250000000000 : ℝ)*(major_s1_2) + (629346219447/200000000000 : ℝ)*(sp_s1_7) + (3146894374721/1000000000000 : ℝ)*(sp_s1_8) + (393360973051/125000000000 : ℝ)*(sp_s1_9) + (222648408371/100000000000 : ℝ)*(sp_s1_13) + (163277487/1000000000000 : ℝ)*(sp_s1_14) + (336169/1000000000000 : ℝ)*(sp_s1_27) + (845404593399/500000000000 : ℝ)*(f.failure) + (196682134837/62500000000 : ℝ)*(f.sum) + (215335953917679703/1103032750000000000000000000000 : ℝ)*base62 + (895259388583949/724250000000000000000000000 : ℝ)*base64 + (94406288991841/114225000000000000000000000 : ℝ)*base66 + (1235665795133923/2172750000000000000000000000 : ℝ)*base68 + (53210086278769613057/61092660250000000000000000000000 : ℝ)*base70 + (223791171610783/4217650000000000000000000000 : ℝ)*base73 + (39577487723909/114225000000000000000000000 : ℝ)*base74 + (4502662932280511/4217650000000000000000000000 : ℝ)*base76 + (254879010391211363/2408805356250000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (87/195312500000000 : ℝ)*base87 + (87/195312500000000 : ℝ)*base89 + (87/195312500000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((81227/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(81227/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (45733033354835555406696937421/2605235403701000000000000000000000 : ℝ) := by norm_num
    linear_combination (23191591689/250000000000 : ℝ)*(base1) + (853508073927/1000000000000 : ℝ)*(base7) + (1687733/250000000000 : ℝ)*(base15) + (165259523763/500000000000 : ℝ)*(base60) + (86829105593/31250000000 : ℝ)*(major_s1_0) + (86829105593/31250000000 : ℝ)*(major_s1_1) + (86829105593/31250000000 : ℝ)*(major_s1_2) + (34126321/1000000000000 : ℝ)*(sp_s1_0) + (17615859/500000000000 : ℝ)*(sp_s1_2) + (8537471/200000000000 : ℝ)*(sp_s1_8) + (660236419927/200000000000 : ℝ)*(sp_s1_14) + (3208400420913/1000000000000 : ℝ)*(sp_s1_15) + (1604207313741/500000000000 : ℝ)*(sp_s1_16) + (515526058919/200000000000 : ℝ)*(sp_s1_20) + (56777768357/31250000000 : ℝ)*(f.failure) + (1002640581/312500000 : ℝ)*(f.sum) + (537077543958118063/8686382906250000000000000000000 : ℝ)*base62 + (599330458766339/724250000000000000000000000 : ℝ)*base64 + (1551820940219741/2398725000000000000000000000 : ℝ)*base66 + (1542953334315653/2172750000000000000000000000 : ℝ)*base68 + (20611732609872623277/61092660250000000000000000000000 : ℝ)*base70 + (3402247188077917/4217650000000000000000000000 : ℝ)*base72 + (1338510704321479/2398725000000000000000000000 : ℝ)*base74 + (3021937896834001/4217650000000000000000000000 : ℝ)*base76 + (118649059380612442589/404679299850000000000000000000000 : ℝ)*base78 + (11/48828125000000 : ℝ)*base86 + (11/48828125000000 : ℝ)*base88 + (11/48828125000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(68223/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(68223/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2868504218368351374876675998209/260523540370100000000000000000000000 : ℝ) := by norm_num
    linear_combination (184523598/244140625 : ℝ)*(base7) + (145135342533/500000000000 : ℝ)*(base39) + (3413883/1000000000000 : ℝ)*(base44) + (608876091219/200000000000 : ℝ)*(major_s1_0) + (761094260553/250000000000 : ℝ)*(major_s1_1) + (608876091219/200000000000 : ℝ)*(major_s1_2) + (12951771/1000000000000 : ℝ)*(sp_s1_0) + (2550631/1000000000000 : ℝ)*(sp_s1_2) + (1805599/62500000000 : ℝ)*(sp_s1_13) + (488663/31250000000 : ℝ)*(sp_s1_15) + (3627162651907/1000000000000 : ℝ)*(sp_s1_21) + (1813578276289/500000000000 : ℝ)*(sp_s1_22) + (3627173053047/1000000000000 : ℝ)*(sp_s1_23) + (1373252157437/500000000000 : ℝ)*(sp_s1_27) + (497681990233/250000000000 : ℝ)*(f.failure) + (1813587801839/500000000000 : ℝ)*(f.sum) + (196181559278071709/4632737550000000000000000000000 : ℝ)*base63 + (105091652192209/579400000000000000000000000 : ℝ)*base64 + (847498549991/12493359375000000000000000 : ℝ)*base66 + (94733328286491/144850000000000000000000000 : ℝ)*base69 + (25484423145396604067/48874128200000000000000000000000 : ℝ)*base70 + (222319451928719/421765000000000000000000000 : ℝ)*base73 + (14842677912269/799575000000000000000000000 : ℝ)*base75 + (315204794170989/1687060000000000000000000000 : ℝ)*base76 + (4477106044594448039/134893099950000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (2847/3125000000000000 : ℝ)*base86 + (2847/3125000000000000 : ℝ)*base88 + (2847/3125000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((84353/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(84353/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((95949/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(95949/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(8691/10000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(8691/10000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((33649/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(33649/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((81227/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(81227/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(68223/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(68223/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c305082_s1 p hpa hpb X hX hprev0

#print axioms solution
