-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c308055_s6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:37:09.470662+00:00
-- url     : https://prove2.me/submissions/07319e23-ba59-49d9-bdff-47770c5a181a

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
theorem collision_support_c308055_s6_s6_0 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-258215791/1000000000 : ℝ)*x 0 + (272017671/500000000 : ℝ)*x 1 + (294659533/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (258215791/1000000000 : ℝ)^69 ≤ (8579029771321/50000000000000 : ℝ)^53 := by
    have hnat : (258215791 : ℕ)^69*50000000000000^53 ≤ 8579029771321^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258215791 1000000000 8579029771321 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (272017671/500000000 : ℝ)^69 ≤ (22635309399173/50000000000000 : ℝ)^53 := by
    have hnat : (272017671 : ℕ)^69*50000000000000^53 ≤ 22635309399173^53*500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272017671 500000000 22635309399173 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (294659533/625000000 : ℝ)^69 ≤ (75142643289/200000000000 : ℝ)^53 := by
    have hnat : (294659533 : ℕ)^69*200000000000^53 ≤ 75142643289^53*625000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      294659533 625000000 75142643289 200000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-258215791/1000000000 : ℝ), (272017671/500000000 : ℝ), (294659533/625000000 : ℝ)] ![(8579029771321/50000000000000 : ℝ), (22635309399173/50000000000000 : ℝ), (75142643289/200000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-258215791/1000000000 : ℝ)|^69 ≤ (8579029771321/50000000000000 : ℝ)^53
        have hw : |(-258215791/1000000000 : ℝ)|=(258215791/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(272017671/500000000 : ℝ)|^69 ≤ (22635309399173/50000000000000 : ℝ)^53
        have hw : |(272017671/500000000 : ℝ)|=(272017671/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(294659533/625000000 : ℝ)|^69 ≤ (75142643289/200000000000 : ℝ)^53
        have hw : |(294659533/625000000 : ℝ)|=(294659533/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308055_s6_s6_2 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2357257889/5000000000 : ℝ)*x 0 + (5439194889/10000000000 : ℝ)*x 1 + (-129182631/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2357257889/5000000000 : ℝ)^69 ≤ (1502837614509/4000000000000 : ℝ)^53 := by
    have hnat : (2357257889 : ℕ)^69*4000000000000^53 ≤ 1502837614509^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2357257889 5000000000 1502837614509 4000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5439194889/10000000000 : ℝ)^69 ≤ (11314517109201/25000000000000 : ℝ)^53 := by
    have hnat : (5439194889 : ℕ)^69*25000000000000^53 ≤ 11314517109201^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439194889 10000000000 11314517109201 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (129182631/500000000 : ℝ)^69 ≤ (2146373897339/12500000000000 : ℝ)^53 := by
    have hnat : (129182631 : ℕ)^69*12500000000000^53 ≤ 2146373897339^53*500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129182631 500000000 2146373897339 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2357257889/5000000000 : ℝ), (5439194889/10000000000 : ℝ), (-129182631/500000000 : ℝ)] ![(1502837614509/4000000000000 : ℝ), (11314517109201/25000000000000 : ℝ), (2146373897339/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2357257889/5000000000 : ℝ)|^69 ≤ (1502837614509/4000000000000 : ℝ)^53
        have hw : |(2357257889/5000000000 : ℝ)|=(2357257889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5439194889/10000000000 : ℝ)|^69 ≤ (11314517109201/25000000000000 : ℝ)^53
        have hw : |(5439194889/10000000000 : ℝ)|=(5439194889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-129182631/500000000 : ℝ)|^69 ≤ (2146373897339/12500000000000 : ℝ)^53
        have hw : |(-129182631/500000000 : ℝ)|=(129182631/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308055_s6_s6_6 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5683565871/10000000000 : ℝ)*x 0 + (1031921953/2500000000 : ℝ)*x 1 + (2957769773/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5683565871/10000000000 : ℝ)^69 ≤ (47923021003719/100000000000000 : ℝ)^53 := by
    have hnat : (5683565871 : ℕ)^69*100000000000000^53 ≤ 47923021003719^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5683565871 10000000000 47923021003719 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1031921953/2500000000 : ℝ)^69 ≤ (1580024491313/5000000000000 : ℝ)^53 := by
    have hnat : (1031921953 : ℕ)^69*5000000000000^53 ≤ 1580024491313^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031921953 2500000000 1580024491313 5000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2957769773/10000000000 : ℝ)^69 ≤ (20476489160269/100000000000000 : ℝ)^53 := by
    have hnat : (2957769773 : ℕ)^69*100000000000000^53 ≤ 20476489160269^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2957769773 10000000000 20476489160269 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5683565871/10000000000 : ℝ), (1031921953/2500000000 : ℝ), (2957769773/10000000000 : ℝ)] ![(47923021003719/100000000000000 : ℝ), (1580024491313/5000000000000 : ℝ), (20476489160269/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5683565871/10000000000 : ℝ)|^69 ≤ (47923021003719/100000000000000 : ℝ)^53
        have hw : |(5683565871/10000000000 : ℝ)|=(5683565871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1031921953/2500000000 : ℝ)|^69 ≤ (1580024491313/5000000000000 : ℝ)^53
        have hw : |(1031921953/2500000000 : ℝ)|=(1031921953/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2957769773/10000000000 : ℝ)|^69 ≤ (20476489160269/100000000000000 : ℝ)^53
        have hw : |(2957769773/10000000000 : ℝ)|=(2957769773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308055_s6_s6_7 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2495255921/10000000000 : ℝ)*x 0 + (64331627/125000000 : ℝ)*x 1 + (5086559287/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2495255921/10000000000 : ℝ)^69 ≤ (1641013313741/10000000000000 : ℝ)^53 := by
    have hnat : (2495255921 : ℕ)^69*10000000000000^53 ≤ 1641013313741^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2495255921 10000000000 1641013313741 10000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (64331627/125000000 : ℝ)^69 ≤ (21056906609243/50000000000000 : ℝ)^53 := by
    have hnat : (64331627 : ℕ)^69*50000000000000^53 ≤ 21056906609243^53*125000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64331627 125000000 21056906609243 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5086559287/10000000000 : ℝ)^69 ≤ (10369013406283/25000000000000 : ℝ)^53 := by
    have hnat : (5086559287 : ℕ)^69*25000000000000^53 ≤ 10369013406283^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5086559287 10000000000 10369013406283 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2495255921/10000000000 : ℝ), (64331627/125000000 : ℝ), (5086559287/10000000000 : ℝ)] ![(1641013313741/10000000000000 : ℝ), (21056906609243/50000000000000 : ℝ), (10369013406283/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2495255921/10000000000 : ℝ)|^69 ≤ (1641013313741/10000000000000 : ℝ)^53
        have hw : |(-2495255921/10000000000 : ℝ)|=(2495255921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(64331627/125000000 : ℝ)|^69 ≤ (21056906609243/50000000000000 : ℝ)^53
        have hw : |(64331627/125000000 : ℝ)|=(64331627/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5086559287/10000000000 : ℝ)|^69 ≤ (10369013406283/25000000000000 : ℝ)^53
        have hw : |(5086559287/10000000000 : ℝ)|=(5086559287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308055_s6_s6_8 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (58446697/125000000 : ℝ)*x 0 + (-1549368793/10000000000 : ℝ)*x 1 + (3115007153/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (58446697/125000000 : ℝ)^69 ≤ (23230686317/62500000000 : ℝ)^53 := by
    have hnat : (58446697 : ℕ)^69*62500000000^53 ≤ 23230686317^53*125000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58446697 125000000 23230686317 62500000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1549368793/10000000000 : ℝ)^69 ≤ (4412078593941/50000000000000 : ℝ)^53 := by
    have hnat : (1549368793 : ℕ)^69*50000000000000^53 ≤ 4412078593941^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1549368793 10000000000 4412078593941 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3115007153/5000000000 : ℝ)^69 ≤ (54006744696273/100000000000000 : ℝ)^53 := by
    have hnat : (3115007153 : ℕ)^69*100000000000000^53 ≤ 54006744696273^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3115007153 5000000000 54006744696273 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(58446697/125000000 : ℝ), (-1549368793/10000000000 : ℝ), (3115007153/5000000000 : ℝ)] ![(23230686317/62500000000 : ℝ), (4412078593941/50000000000000 : ℝ), (54006744696273/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(58446697/125000000 : ℝ)|^69 ≤ (23230686317/62500000000 : ℝ)^53
        have hw : |(58446697/125000000 : ℝ)|=(58446697/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1549368793/10000000000 : ℝ)|^69 ≤ (4412078593941/50000000000000 : ℝ)^53
        have hw : |(-1549368793/10000000000 : ℝ)|=(1549368793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3115007153/5000000000 : ℝ)|^69 ≤ (54006744696273/100000000000000 : ℝ)^53
        have hw : |(3115007153/5000000000 : ℝ)|=(3115007153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308055_s6_s6_9 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (467790369/1000000000 : ℝ)*x 0 + (5755680427/10000000000 : ℝ)*x 1 + (-2219829241/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (467790369/1000000000 : ℝ)^69 ≤ (37191535941153/100000000000000 : ℝ)^53 := by
    have hnat : (467790369 : ℕ)^69*100000000000000^53 ≤ 37191535941153^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      467790369 1000000000 37191535941153 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5755680427/10000000000 : ℝ)^69 ≤ (12179039394001/25000000000000 : ℝ)^53 := by
    have hnat : (5755680427 : ℕ)^69*25000000000000^53 ≤ 12179039394001^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5755680427 10000000000 12179039394001 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2219829241/10000000000 : ℝ)^69 ≤ (14092306457257/100000000000000 : ℝ)^53 := by
    have hnat : (2219829241 : ℕ)^69*100000000000000^53 ≤ 14092306457257^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2219829241 10000000000 14092306457257 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(467790369/1000000000 : ℝ), (5755680427/10000000000 : ℝ), (-2219829241/10000000000 : ℝ)] ![(37191535941153/100000000000000 : ℝ), (12179039394001/25000000000000 : ℝ), (14092306457257/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(467790369/1000000000 : ℝ)|^69 ≤ (37191535941153/100000000000000 : ℝ)^53
        have hw : |(467790369/1000000000 : ℝ)|=(467790369/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5755680427/10000000000 : ℝ)|^69 ≤ (12179039394001/25000000000000 : ℝ)^53
        have hw : |(5755680427/10000000000 : ℝ)|=(5755680427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2219829241/10000000000 : ℝ)|^69 ≤ (14092306457257/100000000000000 : ℝ)^53
        have hw : |(-2219829241/10000000000 : ℝ)|=(2219829241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308055_s6_s6_13 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2745959813/5000000000 : ℝ)*x 0 + (4767789663/10000000000 : ℝ)*x 1 + (122626997/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2745959813/5000000000 : ℝ)^69 ≤ (45830050741717/100000000000000 : ℝ)^53 := by
    have hnat : (2745959813 : ℕ)^69*100000000000000^53 ≤ 45830050741717^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2745959813 5000000000 45830050741717 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4767789663/10000000000 : ℝ)^69 ≤ (19062298654009/50000000000000 : ℝ)^53 := by
    have hnat : (4767789663 : ℕ)^69*50000000000000^53 ≤ 19062298654009^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4767789663 10000000000 19062298654009 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (122626997/500000000 : ℝ)^69 ≤ (8022675972229/50000000000000 : ℝ)^53 := by
    have hnat : (122626997 : ℕ)^69*50000000000000^53 ≤ 8022675972229^53*500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      122626997 500000000 8022675972229 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2745959813/5000000000 : ℝ), (4767789663/10000000000 : ℝ), (122626997/500000000 : ℝ)] ![(45830050741717/100000000000000 : ℝ), (19062298654009/50000000000000 : ℝ), (8022675972229/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2745959813/5000000000 : ℝ)|^69 ≤ (45830050741717/100000000000000 : ℝ)^53
        have hw : |(2745959813/5000000000 : ℝ)|=(2745959813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4767789663/10000000000 : ℝ)|^69 ≤ (19062298654009/50000000000000 : ℝ)^53
        have hw : |(4767789663/10000000000 : ℝ)|=(4767789663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(122626997/500000000 : ℝ)|^69 ≤ (8022675972229/50000000000000 : ℝ)^53
        have hw : |(122626997/500000000 : ℝ)|=(122626997/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308055_s6_s6_14 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-218365811/1000000000 : ℝ)*x 0 + (669532091/1250000000 : ℝ)*x 1 + (204848137/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (218365811/1000000000 : ℝ)^69 ≤ (3448523763753/25000000000000 : ℝ)^53 := by
    have hnat : (218365811 : ℕ)^69*25000000000000^53 ≤ 3448523763753^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218365811 1000000000 3448523763753 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (669532091/1250000000 : ℝ)^69 ≤ (8872340763721/20000000000000 : ℝ)^53 := by
    have hnat : (669532091 : ℕ)^69*20000000000000^53 ≤ 8872340763721^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669532091 1250000000 8872340763721 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (204848137/400000000 : ℝ)^69 ≤ (41844201116451/100000000000000 : ℝ)^53 := by
    have hnat : (204848137 : ℕ)^69*100000000000000^53 ≤ 41844201116451^53*400000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      204848137 400000000 41844201116451 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-218365811/1000000000 : ℝ), (669532091/1250000000 : ℝ), (204848137/400000000 : ℝ)] ![(3448523763753/25000000000000 : ℝ), (8872340763721/20000000000000 : ℝ), (41844201116451/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-218365811/1000000000 : ℝ)|^69 ≤ (3448523763753/25000000000000 : ℝ)^53
        have hw : |(-218365811/1000000000 : ℝ)|=(218365811/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(669532091/1250000000 : ℝ)|^69 ≤ (8872340763721/20000000000000 : ℝ)^53
        have hw : |(669532091/1250000000 : ℝ)|=(669532091/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(204848137/400000000 : ℝ)|^69 ≤ (41844201116451/100000000000000 : ℝ)^53
        have hw : |(204848137/400000000 : ℝ)|=(204848137/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308055_s6_s6_15 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4489369219/10000000000 : ℝ)*x 0 + (-1809066531/10000000000 : ℝ)*x 1 + (389068561/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4489369219/10000000000 : ℝ)^69 ≤ (176260367841/500000000000 : ℝ)^53 := by
    have hnat : (4489369219 : ℕ)^69*500000000000^53 ≤ 176260367841^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4489369219 10000000000 176260367841 500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1809066531/10000000000 : ℝ)^69 ≤ (10796671096151/100000000000000 : ℝ)^53 := by
    have hnat : (1809066531 : ℕ)^69*100000000000000^53 ≤ 10796671096151^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1809066531 10000000000 10796671096151 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (389068561/625000000 : ℝ)^69 ≤ (13487813832071/25000000000000 : ℝ)^53 := by
    have hnat : (389068561 : ℕ)^69*25000000000000^53 ≤ 13487813832071^53*625000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      389068561 625000000 13487813832071 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4489369219/10000000000 : ℝ), (-1809066531/10000000000 : ℝ), (389068561/625000000 : ℝ)] ![(176260367841/500000000000 : ℝ), (10796671096151/100000000000000 : ℝ), (13487813832071/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4489369219/10000000000 : ℝ)|^69 ≤ (176260367841/500000000000 : ℝ)^53
        have hw : |(4489369219/10000000000 : ℝ)|=(4489369219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1809066531/10000000000 : ℝ)|^69 ≤ (10796671096151/100000000000000 : ℝ)^53
        have hw : |(-1809066531/10000000000 : ℝ)|=(1809066531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(389068561/625000000 : ℝ)|^69 ≤ (13487813832071/25000000000000 : ℝ)^53
        have hw : |(389068561/625000000 : ℝ)|=(389068561/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308055_s6_s6_16 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5121199843/10000000000 : ℝ)*x 0 + (5355096713/10000000000 : ℝ)*x 1 + (-2185183437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5121199843/10000000000 : ℝ)^69 ≤ (20922081506601/50000000000000 : ℝ)^53 := by
    have hnat : (5121199843 : ℕ)^69*50000000000000^53 ≤ 20922081506601^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5121199843 10000000000 20922081506601 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5355096713/10000000000 : ℝ)^69 ≤ (44349196348853/100000000000000 : ℝ)^53 := by
    have hnat : (5355096713 : ℕ)^69*100000000000000^53 ≤ 44349196348853^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355096713 10000000000 44349196348853 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2185183437/10000000000 : ℝ)^69 ≤ (690332031443/5000000000000 : ℝ)^53 := by
    have hnat : (2185183437 : ℕ)^69*5000000000000^53 ≤ 690332031443^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185183437 10000000000 690332031443 5000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5121199843/10000000000 : ℝ), (5355096713/10000000000 : ℝ), (-2185183437/10000000000 : ℝ)] ![(20922081506601/50000000000000 : ℝ), (44349196348853/100000000000000 : ℝ), (690332031443/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5121199843/10000000000 : ℝ)|^69 ≤ (20922081506601/50000000000000 : ℝ)^53
        have hw : |(5121199843/10000000000 : ℝ)|=(5121199843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5355096713/10000000000 : ℝ)|^69 ≤ (44349196348853/100000000000000 : ℝ)^53
        have hw : |(5355096713/10000000000 : ℝ)|=(5355096713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2185183437/10000000000 : ℝ)|^69 ≤ (690332031443/5000000000000 : ℝ)^53
        have hw : |(-2185183437/10000000000 : ℝ)|=(2185183437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308055_s6_s6_20 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (192835421/312500000 : ℝ)*x 0 + (4019506779/10000000000 : ℝ)*x 1 + (307878959/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (192835421/312500000 : ℝ)^69 ≤ (53338676378071/100000000000000 : ℝ)^53 := by
    have hnat : (192835421 : ℕ)^69*100000000000000^53 ≤ 53338676378071^53*312500000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      192835421 312500000 53338676378071 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4019506779/10000000000 : ℝ)^69 ≤ (15263275933409/50000000000000 : ℝ)^53 := by
    have hnat : (4019506779 : ℕ)^69*50000000000000^53 ≤ 15263275933409^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4019506779 10000000000 15263275933409 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (307878959/1250000000 : ℝ)^69 ≤ (504211616619/3125000000000 : ℝ)^53 := by
    have hnat : (307878959 : ℕ)^69*3125000000000^53 ≤ 504211616619^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      307878959 1250000000 504211616619 3125000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(192835421/312500000 : ℝ), (4019506779/10000000000 : ℝ), (307878959/1250000000 : ℝ)] ![(53338676378071/100000000000000 : ℝ), (15263275933409/50000000000000 : ℝ), (504211616619/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(192835421/312500000 : ℝ)|^69 ≤ (53338676378071/100000000000000 : ℝ)^53
        have hw : |(192835421/312500000 : ℝ)|=(192835421/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4019506779/10000000000 : ℝ)|^69 ≤ (15263275933409/50000000000000 : ℝ)^53
        have hw : |(4019506779/10000000000 : ℝ)|=(4019506779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(307878959/1250000000 : ℝ)|^69 ≤ (504211616619/3125000000000 : ℝ)^53
        have hw : |(307878959/1250000000 : ℝ)|=(307878959/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308055_s6_s6_21 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-442183631/2000000000 : ℝ)*x 0 + (719200253/1250000000 : ℝ)*x 1 + (4687224521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (442183631/2000000000 : ℝ)^69 ≤ (14018702208003/100000000000000 : ℝ)^53 := by
    have hnat : (442183631 : ℕ)^69*100000000000000^53 ≤ 14018702208003^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442183631 2000000000 14018702208003 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (719200253/1250000000 : ℝ)^69 ≤ (1217331412799/2500000000000 : ℝ)^53 := by
    have hnat : (719200253 : ℕ)^69*2500000000000^53 ≤ 1217331412799^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      719200253 1250000000 1217331412799 2500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4687224521/10000000000 : ℝ)^69 ≤ (18644020627827/50000000000000 : ℝ)^53 := by
    have hnat : (4687224521 : ℕ)^69*50000000000000^53 ≤ 18644020627827^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4687224521 10000000000 18644020627827 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-442183631/2000000000 : ℝ), (719200253/1250000000 : ℝ), (4687224521/10000000000 : ℝ)] ![(14018702208003/100000000000000 : ℝ), (1217331412799/2500000000000 : ℝ), (18644020627827/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-442183631/2000000000 : ℝ)|^69 ≤ (14018702208003/100000000000000 : ℝ)^53
        have hw : |(-442183631/2000000000 : ℝ)|=(442183631/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(719200253/1250000000 : ℝ)|^69 ≤ (1217331412799/2500000000000 : ℝ)^53
        have hw : |(719200253/1250000000 : ℝ)|=(719200253/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4687224521/10000000000 : ℝ)|^69 ≤ (18644020627827/50000000000000 : ℝ)^53
        have hw : |(4687224521/10000000000 : ℝ)|=(4687224521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308055_s6_s6_22 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5091768691/10000000000 : ℝ)*x 0 + (-774963807/5000000000 : ℝ)*x 1 + (5839367277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5091768691/10000000000 : ℝ)^69 ≤ (41531363374777/100000000000000 : ℝ)^53 := by
    have hnat : (5091768691 : ℕ)^69*100000000000000^53 ≤ 41531363374777^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5091768691 10000000000 41531363374777 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (774963807/5000000000 : ℝ)^69 ≤ (4414150442541/50000000000000 : ℝ)^53 := by
    have hnat : (774963807 : ℕ)^69*50000000000000^53 ≤ 4414150442541^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      774963807 5000000000 4414150442541 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5839367277/10000000000 : ℝ)^69 ≤ (49640335730823/100000000000000 : ℝ)^53 := by
    have hnat : (5839367277 : ℕ)^69*100000000000000^53 ≤ 49640335730823^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5839367277 10000000000 49640335730823 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5091768691/10000000000 : ℝ), (-774963807/5000000000 : ℝ), (5839367277/10000000000 : ℝ)] ![(41531363374777/100000000000000 : ℝ), (4414150442541/50000000000000 : ℝ), (49640335730823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5091768691/10000000000 : ℝ)|^69 ≤ (41531363374777/100000000000000 : ℝ)^53
        have hw : |(5091768691/10000000000 : ℝ)|=(5091768691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-774963807/5000000000 : ℝ)|^69 ≤ (4414150442541/50000000000000 : ℝ)^53
        have hw : |(-774963807/5000000000 : ℝ)|=(774963807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5839367277/10000000000 : ℝ)|^69 ≤ (49640335730823/100000000000000 : ℝ)^53
        have hw : |(5839367277/10000000000 : ℝ)|=(5839367277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308055_s6_s6_23 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1115615483/2500000000 : ℝ)*x 0 + (1151024201/2000000000 : ℝ)*x 1 + (-310484309/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1115615483/2500000000 : ℝ)^69 ≤ (34977253244489/100000000000000 : ℝ)^53 := by
    have hnat : (1115615483 : ℕ)^69*100000000000000^53 ≤ 34977253244489^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1115615483 2500000000 34977253244489 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1151024201/2000000000 : ℝ)^69 ≤ (48709993290503/100000000000000 : ℝ)^53 := by
    have hnat : (1151024201 : ℕ)^69*100000000000000^53 ≤ 48709993290503^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1151024201 2000000000 48709993290503 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (310484309/1250000000 : ℝ)^69 ≤ (3262550690737/20000000000000 : ℝ)^53 := by
    have hnat : (310484309 : ℕ)^69*20000000000000^53 ≤ 3262550690737^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      310484309 1250000000 3262550690737 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1115615483/2500000000 : ℝ), (1151024201/2000000000 : ℝ), (-310484309/1250000000 : ℝ)] ![(34977253244489/100000000000000 : ℝ), (48709993290503/100000000000000 : ℝ), (3262550690737/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1115615483/2500000000 : ℝ)|^69 ≤ (34977253244489/100000000000000 : ℝ)^53
        have hw : |(1115615483/2500000000 : ℝ)|=(1115615483/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1151024201/2000000000 : ℝ)|^69 ≤ (48709993290503/100000000000000 : ℝ)^53
        have hw : |(1151024201/2000000000 : ℝ)|=(1151024201/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-310484309/1250000000 : ℝ)|^69 ≤ (3262550690737/20000000000000 : ℝ)^53
        have hw : |(-310484309/1250000000 : ℝ)|=(310484309/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308055_s6_s6_27 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6232785829/10000000000 : ℝ)*x 0 + (1736083259/5000000000 : ℝ)*x 1 + (1493048513/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6232785829/10000000000 : ℝ)^69 ≤ (5403802563831/10000000000000 : ℝ)^53 := by
    have hnat : (6232785829 : ℕ)^69*10000000000000^53 ≤ 5403802563831^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6232785829 10000000000 5403802563831 10000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1736083259/5000000000 : ℝ)^69 ≤ (25229806337823/100000000000000 : ℝ)^53 := by
    have hnat : (1736083259 : ℕ)^69*100000000000000^53 ≤ 25229806337823^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1736083259 5000000000 25229806337823 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1493048513/5000000000 : ℝ)^69 ≤ (20732168003039/100000000000000 : ℝ)^53 := by
    have hnat : (1493048513 : ℕ)^69*100000000000000^53 ≤ 20732168003039^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1493048513 5000000000 20732168003039 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6232785829/10000000000 : ℝ), (1736083259/5000000000 : ℝ), (1493048513/5000000000 : ℝ)] ![(5403802563831/10000000000000 : ℝ), (25229806337823/100000000000000 : ℝ), (20732168003039/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6232785829/10000000000 : ℝ)|^69 ≤ (5403802563831/10000000000000 : ℝ)^53
        have hw : |(6232785829/10000000000 : ℝ)|=(6232785829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1736083259/5000000000 : ℝ)|^69 ≤ (25229806337823/100000000000000 : ℝ)^53
        have hw : |(1736083259/5000000000 : ℝ)|=(1736083259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1493048513/5000000000 : ℝ)|^69 ≤ (20732168003039/100000000000000 : ℝ)^53
        have hw : |(1493048513/5000000000 : ℝ)|=(1493048513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c308055_s6 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev5 : (0 : ℝ) ≤ ((30559/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(30559/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(31439/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(31439/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3863/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(3863/12500 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((21579/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(21579/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(179/800 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(179/800 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(21849/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(21849/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (3861/5000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (3861/5000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (3861/5000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (3861/5000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (3861/5000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (3861/5000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
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
  rcases hprev5 with ⟨ratio_s5_0,ratio_s5_1,ratio_s5_2⟩
  have s6_pow0 : (30559/100000 : ℝ) ^ (17/4 : ℝ) ≤ (32419875506503031/5000000000000000000 : ℝ) := by
    have hpowers : (30559/100000 : ℝ)^17 ≤ (32419875506503031/5000000000000000000 : ℝ)^4 := by
      have hnat : (30559 : ℕ)^17*5000000000000000000^4 ≤ 32419875506503031^4*100000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        30559 100000 32419875506503031 5000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (30559/100000 : ℝ)) (X := (32419875506503031/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s6_corner0a : (5032419875506503031/5000000000000000000 : ℝ) ≤ (10015218732428813/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (5032419875506503031/5000000000000000000 : ℝ)^4 ≤ (10015218732428813/10000000000000000 : ℝ)^17 := by
      have hnat : (5032419875506503031 : ℕ)^4*10000000000000000^17 ≤ 10015218732428813^17*5000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5032419875506503031 5000000000000000000 10015218732428813 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10015218732428813/10000000000000000 : ℝ)) (X := (5032419875506503031/5000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s6_corner0b : (2532419875506503031/2500000000000000000 : ℝ) ≤ (10030362675084529/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (2532419875506503031/2500000000000000000 : ℝ)^4 ≤ (10030362675084529/10000000000000000 : ℝ)^17 := by
      have hnat : (2532419875506503031 : ℕ)^4*10000000000000000^17 ≤ 10030362675084529^17*2500000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2532419875506503031 2500000000000000000 10030362675084529 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10030362675084529/10000000000000000 : ℝ)) (X := (2532419875506503031/2500000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s6_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(15218732428813/3055900000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(3785985663929/763975000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (30559/100000 : ℝ)) (alpha := (15218732428813/3055900000000000 : ℝ)) (beta := (3785985663929/763975000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s6_pow0,s6_corner0a]) (by linarith only [s6_pow0,s6_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (30559/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s5_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(15218732428813/3055900000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(3785985663929/763975000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s6_pow1 : (31439/100000 : ℝ) ^ (17/4 : ℝ) ≤ (731546734049185943/100000000000000000000 : ℝ) := by
    have hpowers : (31439/100000 : ℝ)^17 ≤ (731546734049185943/100000000000000000000 : ℝ)^4 := by
      have hnat : (31439 : ℕ)^17*100000000000000000000^4 ≤ 731546734049185943^4*100000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31439 100000 731546734049185943 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (31439/100000 : ℝ)) (X := (731546734049185943/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s6_corner1a : (100731546734049185943/100000000000000000000 : ℝ) ≤ (10017164924532611/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (100731546734049185943/100000000000000000000 : ℝ)^4 ≤ (10017164924532611/10000000000000000 : ℝ)^17 := by
      have hnat : (100731546734049185943 : ℕ)^4*10000000000000000^17 ≤ 10017164924532611^17*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100731546734049185943 100000000000000000000 10017164924532611 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10017164924532611/10000000000000000 : ℝ)) (X := (100731546734049185943/100000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s6_corner1b : (50731546734049185943/50000000000000000000 : ℝ) ≤ (1254279348223441/1250000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (50731546734049185943/50000000000000000000 : ℝ)^4 ≤ (1254279348223441/1250000000000000 : ℝ)^17 := by
      have hnat : (50731546734049185943 : ℕ)^4*1250000000000000^17 ≤ 1254279348223441^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50731546734049185943 50000000000000000000 1254279348223441 1250000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1254279348223441/1250000000000000 : ℝ)) (X := (50731546734049185943/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s6_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(17164924532611/3143900000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(17069861254917/3143900000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (31439/100000 : ℝ)) (alpha := (17164924532611/3143900000000000 : ℝ)) (beta := (17069861254917/3143900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s6_pow1,s6_corner1a]) (by linarith only [s6_pow1,s6_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (31439/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s5_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(17164924532611/3143900000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(17069861254917/3143900000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s6_pow2 : (3863/12500 : ℝ) ^ (17/4 : ℝ) ≤ (42505239899264769/6250000000000000000 : ℝ) := by
    have hpowers : (3863/12500 : ℝ)^17 ≤ (42505239899264769/6250000000000000000 : ℝ)^4 := by
      have hnat : (3863 : ℕ)^17*6250000000000000000^4 ≤ 42505239899264769^4*12500^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3863 12500 42505239899264769 6250000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3863/12500 : ℝ)) (X := (42505239899264769/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s6_corner2a : (6292505239899264769/6250000000000000000 : ℝ) ≤ (625997533005783/625000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (6292505239899264769/6250000000000000000 : ℝ)^4 ≤ (625997533005783/625000000000000 : ℝ)^17 := by
      have hnat : (6292505239899264769 : ℕ)^4*625000000000000^17 ≤ 625997533005783^17*6250000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6292505239899264769 6250000000000000000 625997533005783 625000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625997533005783/625000000000000 : ℝ)) (X := (6292505239899264769/6250000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s6_corner2b : (3167505239899264769/3125000000000000000 : ℝ) ≤ (5015919411800863/5000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (3167505239899264769/3125000000000000000 : ℝ)^4 ≤ (5015919411800863/5000000000000000 : ℝ)^17 := by
      have hnat : (3167505239899264769 : ℕ)^4*5000000000000000^17 ≤ 5015919411800863^17*3125000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3167505239899264769 3125000000000000000 5015919411800863 5000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5015919411800863/5000000000000000 : ℝ)) (X := (3167505239899264769/3125000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s6_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(997533005783/193150000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(7939147754599/1545200000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (3863/12500 : ℝ)) (alpha := (997533005783/193150000000000 : ℝ)) (beta := (7939147754599/1545200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s6_pow2,s6_corner2a]) (by linarith only [s6_pow2,s6_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (3863/12500 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s5_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(997533005783/193150000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(7939147754599/1545200000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s6_0 : ((-258215791/1000000000 : ℝ)*X 0 0+(272017671/500000000 : ℝ)*X 0 1+(294659533/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308055_s6_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_2 : ((2357257889/5000000000 : ℝ)*X 2 0+(5439194889/10000000000 : ℝ)*X 2 1+(-129182631/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308055_s6_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_6 : ((5683565871/10000000000 : ℝ)*X 0 0+(1031921953/2500000000 : ℝ)*X 0 1+(2957769773/10000000000 : ℝ)*X 0 2+(5683565871/10000000000 : ℝ)*X 1 0+(1031921953/2500000000 : ℝ)*X 1 1+(2957769773/10000000000 : ℝ)*X 1 2+(5683565871/10000000000 : ℝ)*X 2 0+(1031921953/2500000000 : ℝ)*X 2 1+(2957769773/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308055_s6_s6_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_7 : ((-2495255921/10000000000 : ℝ)*X 0 0+(64331627/125000000 : ℝ)*X 0 1+(5086559287/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308055_s6_s6_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_8 : ((58446697/125000000 : ℝ)*X 1 0+(-1549368793/10000000000 : ℝ)*X 1 1+(3115007153/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308055_s6_s6_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_9 : ((467790369/1000000000 : ℝ)*X 2 0+(5755680427/10000000000 : ℝ)*X 2 1+(-2219829241/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308055_s6_s6_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_13 : ((2745959813/5000000000 : ℝ)*X 0 0+(4767789663/10000000000 : ℝ)*X 0 1+(122626997/500000000 : ℝ)*X 0 2+(2745959813/5000000000 : ℝ)*X 1 0+(4767789663/10000000000 : ℝ)*X 1 1+(122626997/500000000 : ℝ)*X 1 2+(2745959813/5000000000 : ℝ)*X 2 0+(4767789663/10000000000 : ℝ)*X 2 1+(122626997/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308055_s6_s6_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_14 : ((-218365811/1000000000 : ℝ)*X 0 0+(669532091/1250000000 : ℝ)*X 0 1+(204848137/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308055_s6_s6_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_15 : ((4489369219/10000000000 : ℝ)*X 1 0+(-1809066531/10000000000 : ℝ)*X 1 1+(389068561/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308055_s6_s6_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_16 : ((5121199843/10000000000 : ℝ)*X 2 0+(5355096713/10000000000 : ℝ)*X 2 1+(-2185183437/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308055_s6_s6_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_20 : ((192835421/312500000 : ℝ)*X 0 0+(4019506779/10000000000 : ℝ)*X 0 1+(307878959/1250000000 : ℝ)*X 0 2+(192835421/312500000 : ℝ)*X 1 0+(4019506779/10000000000 : ℝ)*X 1 1+(307878959/1250000000 : ℝ)*X 1 2+(192835421/312500000 : ℝ)*X 2 0+(4019506779/10000000000 : ℝ)*X 2 1+(307878959/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308055_s6_s6_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_21 : ((-442183631/2000000000 : ℝ)*X 0 0+(719200253/1250000000 : ℝ)*X 0 1+(4687224521/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308055_s6_s6_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_22 : ((5091768691/10000000000 : ℝ)*X 1 0+(-774963807/5000000000 : ℝ)*X 1 1+(5839367277/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308055_s6_s6_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_23 : ((1115615483/2500000000 : ℝ)*X 2 0+(1151024201/2000000000 : ℝ)*X 2 1+(-310484309/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308055_s6_s6_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_27 : ((6232785829/10000000000 : ℝ)*X 0 0+(1736083259/5000000000 : ℝ)*X 0 1+(1493048513/5000000000 : ℝ)*X 0 2+(6232785829/10000000000 : ℝ)*X 1 0+(1736083259/5000000000 : ℝ)*X 1 1+(1493048513/5000000000 : ℝ)*X 1 2+(6232785829/10000000000 : ℝ)*X 2 0+(1736083259/5000000000 : ℝ)*X 2 1+(1493048513/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308055_s6_s6_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s6_0 : (0 : ℝ) ≤ ((21579/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(21579/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (67951986262403396609856213/6072442850000000000000000000000 : ℝ) := by norm_num
    linear_combination (1748634281571/1000000000000 : ℝ)*(base49) + (257283/500000000000 : ℝ)*(base60) + (12031306428807/1000000000000 : ℝ)*(major_s6_0) + (12031306428807/1000000000000 : ℝ)*(major_s6_1) + (12031306428807/1000000000000 : ℝ)*(major_s6_2) + (126172249/1000000000000 : ℝ)*(sp_s6_0) + (4002873/125000000000 : ℝ)*(sp_s6_2) + (4586239/125000000000 : ℝ)*(sp_s6_6) + (16385098196841/1000000000000 : ℝ)*(sp_s6_7) + (2048130105397/125000000000 : ℝ)*(sp_s6_8) + (16384980686693/1000000000000 : ℝ)*(sp_s6_9) + (7677348068533/1000000000000 : ℝ)*(sp_s6_13) + (91762957/500000000000 : ℝ)*(sp_s6_15) + (211659413/1000000000000 : ℝ)*(sp_s6_23) + (1535476951689/200000000000 : ℝ)*(f.failure) + (1638522436909/100000000000 : ℝ)*(f.sum) + (2995594211786586339/12144885700000000000000000000000 : ℝ)*base63 + (194948308238633/1545200000000000000000000000 : ℝ)*base65 + (409335693740331/3143900000000000000000000000 : ℝ)*base67 + (151905577872041/193150000000000000000000000 : ℝ)*base69 + (19410404931941195461/47219766800000000000000000000000 : ℝ)*base70 + (378762654945093/763975000000000000000000000 : ℝ)*base73 + (1441031164460357/3143900000000000000000000000 : ℝ)*base75 + (1477365326772841/3055900000000000000000000000 : ℝ)*base77 + (41699582041199305823/96074440100000000000000000000000 : ℝ)*base78 + (5121/20000000000000000 : ℝ)*base86 + (5121/20000000000000000 : ℝ)*base88 + (5121/20000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s6_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(179/800 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(179/800 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (607024449638633811840713891691/148454224842520000000000000000000000 : ℝ) := by norm_num
    linear_combination (163205406609/100000000000 : ℝ)*(base49) + (11661508603023/1000000000000 : ℝ)*(major_s6_0) + (11661508603023/1000000000000 : ℝ)*(major_s6_1) + (11661508603023/1000000000000 : ℝ)*(major_s6_2) + (163719/1953125000 : ℝ)*(sp_s6_2) + (1339431/62500000000 : ℝ)*(sp_s6_6) + (9171001/200000000000 : ℝ)*(sp_s6_8) + (37852957/1000000000000 : ℝ)*(sp_s6_9) + (15881594545233/1000000000000 : ℝ)*(sp_s6_14) + (7940779809633/500000000000 : ℝ)*(sp_s6_15) + (7940741898593/500000000000 : ℝ)*(sp_s6_16) + (1488272417983/200000000000 : ℝ)*(sp_s6_20) + (5464519/500000000000 : ℝ)*(sp_s6_21) + (6711993/250000000000 : ℝ)*(sp_s6_27) + (7441410368783/1000000000000 : ℝ)*(f.failure) + (15881605474271/1000000000000 : ℝ)*(f.sum) + (1009813365209187839/12144885700000000000000000000000 : ℝ)*base62 + (602565062465103/1545200000000000000000000000 : ℝ)*base64 + (482422216813461/3143900000000000000000000000 : ℝ)*base66 + (76050168073461/193150000000000000000000000 : ℝ)*base68 + (3139847570058449669/47219766800000000000000000000000 : ℝ)*base70 + (36412917249221/95496875000000000000000000 : ℝ)*base72 + (1302220477591387/3143900000000000000000000000 : ℝ)*base74 + (1126137474448681/3055900000000000000000000000 : ℝ)*base76 + (16320200740454408773/96074440100000000000000000000000 : ℝ)*base79 + (52713/100000000000000000 : ℝ)*base87 + (52713/100000000000000000 : ℝ)*base89 + (52713/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s6_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(21849/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(21849/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (668152578967114262780714002707/74227112421260000000000000000000000 : ℝ) := by norm_num
    linear_combination (780763/1000000000000 : ℝ)*(base39) + (4245714987/1000000000000 : ℝ)*(base40) + (854008430741/500000000000 : ℝ)*(base49) + (21239/3906250000 : ℝ)*(base59) + (1162800664163/100000000000 : ℝ)*(major_s6_0) + (1162800664163/100000000000 : ℝ)*(major_s6_1) + (1162800664163/100000000000 : ℝ)*(major_s6_2) + (22606137/500000000000 : ℝ)*(sp_s6_0) + (447339/7812500000 : ℝ)*(sp_s6_2) + (131959113/1000000000000 : ℝ)*(sp_s6_20) + (7917966441407/500000000000 : ℝ)*(sp_s6_21) + (15835978095087/1000000000000 : ℝ)*(sp_s6_22) + (3167184167139/200000000000 : ℝ)*(sp_s6_23) + (1854975057141/250000000000 : ℝ)*(sp_s6_27) + (1855008046919/250000000000 : ℝ)*(f.failure) + (15835978095087/1000000000000 : ℝ)*(f.sum) + (169389687151131353/1214488570000000000000000000000 : ℝ)*base62 + (68961485976703/154520000000000000000000000 : ℝ)*base64 + (9673340675629/62878000000000000000000000 : ℝ)*base66 + (4461396801491/38630000000000000000000000 : ℝ)*base69 + (953868678289770677/4721976680000000000000000000000 : ℝ)*base70 + (11380621310033/305590000000000000000000000 : ℝ)*base72 + (33729588543681/314390000000000000000000000 : ℝ)*base75 + (129340767577141/305590000000000000000000000 : ℝ)*base77 + (4918053715060920997/9607444010000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (26591/25000000000000000 : ℝ)*base86 + (26591/25000000000000000 : ℝ)*base88 + (26591/25000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s6_0,ratio_s6_1,ratio_s6_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev5 : (0 : ℝ) ≤ ((30559/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(30559/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(31439/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(31439/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3863/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(3863/12500 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((21579/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(21579/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(179/800 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(179/800 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(21849/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(21849/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c308055_s6 p hpa hpb X hX hprev5

#print axioms solution
