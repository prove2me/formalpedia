-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c301055_s3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:32:38.423012+00:00
-- url     : https://prove2.me/submissions/9e705ff9-81a7-497b-a194-42d4dbce5dff

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
theorem collision_support_c301055_s3_s3_0 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-141884759/1250000000 : ℝ)*x 0 + (6053546879/10000000000 : ℝ)*x 1 + (1059280389/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (141884759/1250000000 : ℝ)^65 ≤ (174306157767/3125000000000 : ℝ)^49 := by
    have hnat : (141884759 : ℕ)^65*3125000000000^49 ≤ 174306157767^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141884759 1250000000 174306157767 3125000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6053546879/10000000000 : ℝ)^65 ≤ (25692092487317/50000000000000 : ℝ)^49 := by
    have hnat : (6053546879 : ℕ)^65*50000000000000^49 ≤ 25692092487317^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6053546879 10000000000 25692092487317 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1059280389/2000000000 : ℝ)^65 ≤ (43038017968779/100000000000000 : ℝ)^49 := by
    have hnat : (1059280389 : ℕ)^65*100000000000000^49 ≤ 43038017968779^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059280389 2000000000 43038017968779 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-141884759/1250000000 : ℝ), (6053546879/10000000000 : ℝ), (1059280389/2000000000 : ℝ)] ![(174306157767/3125000000000 : ℝ), (25692092487317/50000000000000 : ℝ), (43038017968779/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-141884759/1250000000 : ℝ)|^65 ≤ (174306157767/3125000000000 : ℝ)^49
        have hw : |(-141884759/1250000000 : ℝ)|=(141884759/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6053546879/10000000000 : ℝ)|^65 ≤ (25692092487317/50000000000000 : ℝ)^49
        have hw : |(6053546879/10000000000 : ℝ)|=(6053546879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1059280389/2000000000 : ℝ)|^65 ≤ (43038017968779/100000000000000 : ℝ)^49
        have hw : |(1059280389/2000000000 : ℝ)|=(1059280389/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301055_s3_s3_6 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1667667269/2500000000 : ℝ)*x 0 + (1916271473/5000000000 : ℝ)*x 1 + (553534077/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1667667269/2500000000 : ℝ)^65 ≤ (5844607105147/10000000000000 : ℝ)^49 := by
    have hnat : (1667667269 : ℕ)^65*10000000000000^49 ≤ 5844607105147^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1667667269 2500000000 5844607105147 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1916271473/5000000000 : ℝ)^65 ≤ (14010473059343/50000000000000 : ℝ)^49 := by
    have hnat : (1916271473 : ℕ)^65*50000000000000^49 ≤ 14010473059343^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1916271473 5000000000 14010473059343 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (553534077/2500000000 : ℝ)^65 ≤ (3383245704127/25000000000000 : ℝ)^49 := by
    have hnat : (553534077 : ℕ)^65*25000000000000^49 ≤ 3383245704127^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553534077 2500000000 3383245704127 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1667667269/2500000000 : ℝ), (1916271473/5000000000 : ℝ), (553534077/2500000000 : ℝ)] ![(5844607105147/10000000000000 : ℝ), (14010473059343/50000000000000 : ℝ), (3383245704127/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1667667269/2500000000 : ℝ)|^65 ≤ (5844607105147/10000000000000 : ℝ)^49
        have hw : |(1667667269/2500000000 : ℝ)|=(1667667269/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1916271473/5000000000 : ℝ)|^65 ≤ (14010473059343/50000000000000 : ℝ)^49
        have hw : |(1916271473/5000000000 : ℝ)|=(1916271473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(553534077/2500000000 : ℝ)|^65 ≤ (3383245704127/25000000000000 : ℝ)^49
        have hw : |(553534077/2500000000 : ℝ)|=(553534077/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301055_s3_s3_7 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-327422517/1000000000 : ℝ)*x 0 + (2202518669/5000000000 : ℝ)*x 1 + (534440293/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (327422517/1000000000 : ℝ)^65 ≤ (22739276279401/100000000000000 : ℝ)^49 := by
    have hnat : (327422517 : ℕ)^65*100000000000000^49 ≤ 22739276279401^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327422517 1000000000 22739276279401 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2202518669/5000000000 : ℝ)^65 ≤ (33704527007803/100000000000000 : ℝ)^49 := by
    have hnat : (2202518669 : ℕ)^65*100000000000000^49 ≤ 33704527007803^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2202518669 5000000000 33704527007803 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (534440293/1000000000 : ℝ)^65 ≤ (43556196703907/100000000000000 : ℝ)^49 := by
    have hnat : (534440293 : ℕ)^65*100000000000000^49 ≤ 43556196703907^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534440293 1000000000 43556196703907 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-327422517/1000000000 : ℝ), (2202518669/5000000000 : ℝ), (534440293/1000000000 : ℝ)] ![(22739276279401/100000000000000 : ℝ), (33704527007803/100000000000000 : ℝ), (43556196703907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-327422517/1000000000 : ℝ)|^65 ≤ (22739276279401/100000000000000 : ℝ)^49
        have hw : |(-327422517/1000000000 : ℝ)|=(327422517/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2202518669/5000000000 : ℝ)|^65 ≤ (33704527007803/100000000000000 : ℝ)^49
        have hw : |(2202518669/5000000000 : ℝ)|=(2202518669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(534440293/1000000000 : ℝ)|^65 ≤ (43556196703907/100000000000000 : ℝ)^49
        have hw : |(534440293/1000000000 : ℝ)|=(534440293/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301055_s3_s3_8 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2364001771/10000000000 : ℝ)*x 0 + (176629/1250000000 : ℝ)*x 1 + (8865593739/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2364001771/10000000000 : ℝ)^65 ≤ (3690325193297/25000000000000 : ℝ)^49 := by
    have hnat : (2364001771 : ℕ)^65*25000000000000^49 ≤ 3690325193297^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2364001771 10000000000 3690325193297 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (176629/1250000000 : ℝ)^65 ≤ (781733587/100000000000000 : ℝ)^49 := by
    have hnat : (176629 : ℕ)^65*100000000000000^49 ≤ 781733587^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      176629 1250000000 781733587 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8865593739/10000000000 : ℝ)^65 ≤ (85237917480341/100000000000000 : ℝ)^49 := by
    have hnat : (8865593739 : ℕ)^65*100000000000000^49 ≤ 85237917480341^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8865593739 10000000000 85237917480341 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2364001771/10000000000 : ℝ), (176629/1250000000 : ℝ), (8865593739/10000000000 : ℝ)] ![(3690325193297/25000000000000 : ℝ), (781733587/100000000000000 : ℝ), (85237917480341/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2364001771/10000000000 : ℝ)|^65 ≤ (3690325193297/25000000000000 : ℝ)^49
        have hw : |(2364001771/10000000000 : ℝ)|=(2364001771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(176629/1250000000 : ℝ)|^65 ≤ (781733587/100000000000000 : ℝ)^49
        have hw : |(176629/1250000000 : ℝ)|=(176629/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8865593739/10000000000 : ℝ)|^65 ≤ (85237917480341/100000000000000 : ℝ)^49
        have hw : |(8865593739/10000000000 : ℝ)|=(8865593739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301055_s3_s3_9 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1018277453/5000000000 : ℝ)*x 0 + (4367194399/5000000000 : ℝ)*x 1 + (-936030671/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1018277453/5000000000 : ℝ)^65 ≤ (6056190890179/50000000000000 : ℝ)^49 := by
    have hnat : (1018277453 : ℕ)^65*50000000000000^49 ≤ 6056190890179^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1018277453 5000000000 6056190890179 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4367194399/5000000000 : ℝ)^65 ≤ (16713720466337/20000000000000 : ℝ)^49 := by
    have hnat : (4367194399 : ℕ)^65*20000000000000^49 ≤ 16713720466337^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4367194399 5000000000 16713720466337 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (936030671/10000000000 : ℝ)^65 ≤ (863803173091/20000000000000 : ℝ)^49 := by
    have hnat : (936030671 : ℕ)^65*20000000000000^49 ≤ 863803173091^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      936030671 10000000000 863803173091 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1018277453/5000000000 : ℝ), (4367194399/5000000000 : ℝ), (-936030671/10000000000 : ℝ)] ![(6056190890179/50000000000000 : ℝ), (16713720466337/20000000000000 : ℝ), (863803173091/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1018277453/5000000000 : ℝ)|^65 ≤ (6056190890179/50000000000000 : ℝ)^49
        have hw : |(1018277453/5000000000 : ℝ)|=(1018277453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4367194399/5000000000 : ℝ)|^65 ≤ (16713720466337/20000000000000 : ℝ)^49
        have hw : |(4367194399/5000000000 : ℝ)|=(4367194399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-936030671/10000000000 : ℝ)|^65 ≤ (863803173091/20000000000000 : ℝ)^49
        have hw : |(-936030671/10000000000 : ℝ)|=(936030671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301055_s3_s3_13 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2008217529/5000000000 : ℝ)*x 0 + (729544799/1000000000 : ℝ)*x 1 + (943582409/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2008217529/5000000000 : ℝ)^65 ≤ (2981828260711/10000000000000 : ℝ)^49 := by
    have hnat : (2008217529 : ℕ)^65*10000000000000^49 ≤ 2981828260711^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2008217529 5000000000 2981828260711 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (729544799/1000000000 : ℝ)^65 ≤ (65816417647127/100000000000000 : ℝ)^49 := by
    have hnat : (729544799 : ℕ)^65*100000000000000^49 ≤ 65816417647127^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      729544799 1000000000 65816417647127 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (943582409/10000000000 : ℝ)^65 ≤ (4365299723653/100000000000000 : ℝ)^49 := by
    have hnat : (943582409 : ℕ)^65*100000000000000^49 ≤ 4365299723653^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      943582409 10000000000 4365299723653 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2008217529/5000000000 : ℝ), (729544799/1000000000 : ℝ), (943582409/10000000000 : ℝ)] ![(2981828260711/10000000000000 : ℝ), (65816417647127/100000000000000 : ℝ), (4365299723653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2008217529/5000000000 : ℝ)|^65 ≤ (2981828260711/10000000000000 : ℝ)^49
        have hw : |(2008217529/5000000000 : ℝ)|=(2008217529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(729544799/1000000000 : ℝ)|^65 ≤ (65816417647127/100000000000000 : ℝ)^49
        have hw : |(729544799/1000000000 : ℝ)|=(729544799/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(943582409/10000000000 : ℝ)|^65 ≤ (4365299723653/100000000000000 : ℝ)^49
        have hw : |(943582409/10000000000 : ℝ)|=(943582409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301055_s3_s3_14 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-98600163/500000000 : ℝ)*x 0 + (470718723/1000000000 : ℝ)*x 1 + (1214347997/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (98600163/500000000 : ℝ)^65 ≤ (11605754640421/100000000000000 : ℝ)^49 := by
    have hnat : (98600163 : ℕ)^65*100000000000000^49 ≤ 11605754640421^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      98600163 500000000 11605754640421 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (470718723/1000000000 : ℝ)^65 ≤ (4600638285959/12500000000000 : ℝ)^49 := by
    have hnat : (470718723 : ℕ)^65*12500000000000^49 ≤ 4600638285959^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      470718723 1000000000 4600638285959 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1214347997/2000000000 : ℝ)^65 ≤ (10317827812899/20000000000000 : ℝ)^49 := by
    have hnat : (1214347997 : ℕ)^65*20000000000000^49 ≤ 10317827812899^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1214347997 2000000000 10317827812899 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-98600163/500000000 : ℝ), (470718723/1000000000 : ℝ), (1214347997/2000000000 : ℝ)] ![(11605754640421/100000000000000 : ℝ), (4600638285959/12500000000000 : ℝ), (10317827812899/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-98600163/500000000 : ℝ)|^65 ≤ (11605754640421/100000000000000 : ℝ)^49
        have hw : |(-98600163/500000000 : ℝ)|=(98600163/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(470718723/1000000000 : ℝ)|^65 ≤ (4600638285959/12500000000000 : ℝ)^49
        have hw : |(470718723/1000000000 : ℝ)|=(470718723/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1214347997/2000000000 : ℝ)|^65 ≤ (10317827812899/20000000000000 : ℝ)^49
        have hw : |(1214347997/2000000000 : ℝ)|=(1214347997/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301055_s3_s3_15 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (289064631/2000000000 : ℝ)*x 0 + (-782677/200000000 : ℝ)*x 1 + (9410050247/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (289064631/2000000000 : ℝ)^65 ≤ (240169484723/3125000000000 : ℝ)^49 := by
    have hnat : (289064631 : ℕ)^65*3125000000000^49 ≤ 240169484723^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      289064631 2000000000 240169484723 3125000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (782677/200000000 : ℝ)^65 ≤ (4002462873/6250000000000 : ℝ)^49 := by
    have hnat : (782677 : ℕ)^65*6250000000000^49 ≤ 4002462873^49*200000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      782677 200000000 4002462873 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9410050247/10000000000 : ℝ)^65 ≤ (92250537069789/100000000000000 : ℝ)^49 := by
    have hnat : (9410050247 : ℕ)^65*100000000000000^49 ≤ 92250537069789^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9410050247 10000000000 92250537069789 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(289064631/2000000000 : ℝ), (-782677/200000000 : ℝ), (9410050247/10000000000 : ℝ)] ![(240169484723/3125000000000 : ℝ), (4002462873/6250000000000 : ℝ), (92250537069789/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(289064631/2000000000 : ℝ)|^65 ≤ (240169484723/3125000000000 : ℝ)^49
        have hw : |(289064631/2000000000 : ℝ)|=(289064631/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-782677/200000000 : ℝ)|^65 ≤ (4002462873/6250000000000 : ℝ)^49
        have hw : |(-782677/200000000 : ℝ)|=(782677/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(9410050247/10000000000 : ℝ)|^65 ≤ (92250537069789/100000000000000 : ℝ)^49
        have hw : |(9410050247/10000000000 : ℝ)|=(9410050247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301055_s3_s3_16 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1870662933/2500000000 : ℝ)*x 0 + (235839427/625000000 : ℝ)*x 1 + (-60187113/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1870662933/2500000000 : ℝ)^65 ≤ (850826133473/1250000000000 : ℝ)^49 := by
    have hnat : (1870662933 : ℕ)^65*1250000000000^49 ≤ 850826133473^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1870662933 2500000000 850826133473 1250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (235839427/625000000 : ℝ)^65 ≤ (27449084815863/100000000000000 : ℝ)^49 := by
    have hnat : (235839427 : ℕ)^65*100000000000000^49 ≤ 27449084815863^49*625000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      235839427 625000000 27449084815863 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (60187113/625000000 : ℝ)^65 ≤ (4484824491339/100000000000000 : ℝ)^49 := by
    have hnat : (60187113 : ℕ)^65*100000000000000^49 ≤ 4484824491339^49*625000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      60187113 625000000 4484824491339 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1870662933/2500000000 : ℝ), (235839427/625000000 : ℝ), (-60187113/625000000 : ℝ)] ![(850826133473/1250000000000 : ℝ), (27449084815863/100000000000000 : ℝ), (4484824491339/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1870662933/2500000000 : ℝ)|^65 ≤ (850826133473/1250000000000 : ℝ)^49
        have hw : |(1870662933/2500000000 : ℝ)|=(1870662933/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(235839427/625000000 : ℝ)|^65 ≤ (27449084815863/100000000000000 : ℝ)^49
        have hw : |(235839427/625000000 : ℝ)|=(235839427/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-60187113/625000000 : ℝ)|^65 ≤ (4484824491339/100000000000000 : ℝ)^49
        have hw : |(-60187113/625000000 : ℝ)|=(60187113/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301055_s3_s3_20 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2203841793/2500000000 : ℝ)*x 0 + (38674797/200000000 : ℝ)*x 1 + (449521153/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2203841793/2500000000 : ℝ)^65 ≤ (16523032657/19531250000 : ℝ)^49 := by
    have hnat : (2203841793 : ℕ)^65*19531250000^49 ≤ 16523032657^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2203841793 2500000000 16523032657 19531250000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (38674797/200000000 : ℝ)^65 ≤ (5653991729997/50000000000000 : ℝ)^49 := by
    have hnat : (38674797 : ℕ)^65*50000000000000^49 ≤ 5653991729997^49*200000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38674797 200000000 5653991729997 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (449521153/5000000000 : ℝ)^65 ≤ (409408932211/10000000000000 : ℝ)^49 := by
    have hnat : (449521153 : ℕ)^65*10000000000000^49 ≤ 409408932211^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449521153 5000000000 409408932211 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2203841793/2500000000 : ℝ), (38674797/200000000 : ℝ), (449521153/5000000000 : ℝ)] ![(16523032657/19531250000 : ℝ), (5653991729997/50000000000000 : ℝ), (409408932211/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2203841793/2500000000 : ℝ)|^65 ≤ (16523032657/19531250000 : ℝ)^49
        have hw : |(2203841793/2500000000 : ℝ)|=(2203841793/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(38674797/200000000 : ℝ)|^65 ≤ (5653991729997/50000000000000 : ℝ)^49
        have hw : |(38674797/200000000 : ℝ)|=(38674797/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(449521153/5000000000 : ℝ)|^65 ≤ (409408932211/10000000000000 : ℝ)^49
        have hw : |(449521153/5000000000 : ℝ)|=(449521153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301055_s3_s3_21 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1386325063/10000000000 : ℝ)*x 0 + (4103205747/5000000000 : ℝ)*x 1 + (2487554197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1386325063/10000000000 : ℝ)^65 ≤ (7272065003319/100000000000000 : ℝ)^49 := by
    have hnat : (1386325063 : ℕ)^65*100000000000000^49 ≤ 7272065003319^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1386325063 10000000000 7272065003319 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4103205747/5000000000 : ℝ)^65 ≤ (76934601964679/100000000000000 : ℝ)^49 := by
    have hnat : (4103205747 : ℕ)^65*100000000000000^49 ≤ 76934601964679^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4103205747 5000000000 76934601964679 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2487554197/10000000000 : ℝ)^65 ≤ (15793333016377/100000000000000 : ℝ)^49 := by
    have hnat : (2487554197 : ℕ)^65*100000000000000^49 ≤ 15793333016377^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2487554197 10000000000 15793333016377 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1386325063/10000000000 : ℝ), (4103205747/5000000000 : ℝ), (2487554197/10000000000 : ℝ)] ![(7272065003319/100000000000000 : ℝ), (76934601964679/100000000000000 : ℝ), (15793333016377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1386325063/10000000000 : ℝ)|^65 ≤ (7272065003319/100000000000000 : ℝ)^49
        have hw : |(-1386325063/10000000000 : ℝ)|=(1386325063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4103205747/5000000000 : ℝ)|^65 ≤ (76934601964679/100000000000000 : ℝ)^49
        have hw : |(4103205747/5000000000 : ℝ)|=(4103205747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2487554197/10000000000 : ℝ)|^65 ≤ (15793333016377/100000000000000 : ℝ)^49
        have hw : |(2487554197/10000000000 : ℝ)|=(2487554197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301055_s3_s3_22 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7570764113/10000000000 : ℝ)*x 0 + (-12645019/10000000000 : ℝ)*x 1 + (41211923/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7570764113/10000000000 : ℝ)^65 ≤ (69131364964099/100000000000000 : ℝ)^49 := by
    have hnat : (7570764113 : ℕ)^65*100000000000000^49 ≤ 69131364964099^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7570764113 10000000000 69131364964099 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (12645019/10000000000 : ℝ)^65 ≤ (14308940631/100000000000000 : ℝ)^49 := by
    have hnat : (12645019 : ℕ)^65*100000000000000^49 ≤ 14308940631^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12645019 10000000000 14308940631 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41211923/100000000 : ℝ)^65 ≤ (30854326075833/100000000000000 : ℝ)^49 := by
    have hnat : (41211923 : ℕ)^65*100000000000000^49 ≤ 30854326075833^49*100000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41211923 100000000 30854326075833 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7570764113/10000000000 : ℝ), (-12645019/10000000000 : ℝ), (41211923/100000000 : ℝ)] ![(69131364964099/100000000000000 : ℝ), (14308940631/100000000000000 : ℝ), (30854326075833/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7570764113/10000000000 : ℝ)|^65 ≤ (69131364964099/100000000000000 : ℝ)^49
        have hw : |(7570764113/10000000000 : ℝ)|=(7570764113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-12645019/10000000000 : ℝ)|^65 ≤ (14308940631/100000000000000 : ℝ)^49
        have hw : |(-12645019/10000000000 : ℝ)|=(12645019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(41211923/100000000 : ℝ)|^65 ≤ (30854326075833/100000000000000 : ℝ)^49
        have hw : |(41211923/100000000 : ℝ)|=(41211923/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301055_s3_s3_23 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (130134131/1000000000 : ℝ)*x 0 + (873652923/1000000000 : ℝ)*x 1 + (-431233413/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (130134131/1000000000 : ℝ)^65 ≤ (6686715381973/100000000000000 : ℝ)^49 := by
    have hnat : (130134131 : ℕ)^65*100000000000000^49 ≤ 6686715381973^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130134131 1000000000 6686715381973 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (873652923/1000000000 : ℝ)^65 ≤ (41797884822929/50000000000000 : ℝ)^49 := by
    have hnat : (873652923 : ℕ)^65*50000000000000^49 ≤ 41797884822929^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873652923 1000000000 41797884822929 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (431233413/2500000000 : ℝ)^65 ≤ (1943502991767/20000000000000 : ℝ)^49 := by
    have hnat : (431233413 : ℕ)^65*20000000000000^49 ≤ 1943502991767^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431233413 2500000000 1943502991767 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(130134131/1000000000 : ℝ), (873652923/1000000000 : ℝ), (-431233413/2500000000 : ℝ)] ![(6686715381973/100000000000000 : ℝ), (41797884822929/50000000000000 : ℝ), (1943502991767/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(130134131/1000000000 : ℝ)|^65 ≤ (6686715381973/100000000000000 : ℝ)^49
        have hw : |(130134131/1000000000 : ℝ)|=(130134131/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(873652923/1000000000 : ℝ)|^65 ≤ (41797884822929/50000000000000 : ℝ)^49
        have hw : |(873652923/1000000000 : ℝ)|=(873652923/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-431233413/2500000000 : ℝ)|^65 ≤ (1943502991767/20000000000000 : ℝ)^49
        have hw : |(-431233413/2500000000 : ℝ)|=(431233413/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301055_s3_s3_27 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8452459517/10000000000 : ℝ)*x 0 + (428241521/2000000000 : ℝ)*x 1 + (42302297/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8452459517/10000000000 : ℝ)^65 ≤ (40004684574249/50000000000000 : ℝ)^49 := by
    have hnat : (8452459517 : ℕ)^65*50000000000000^49 ≤ 40004684574249^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8452459517 10000000000 40004684574249 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (428241521/2000000000 : ℝ)^65 ≤ (12944890405153/100000000000000 : ℝ)^49 := by
    have hnat : (428241521 : ℕ)^65*100000000000000^49 ≤ 12944890405153^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428241521 2000000000 12944890405153 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42302297/312500000 : ℝ)^65 ≤ (7045740434097/100000000000000 : ℝ)^49 := by
    have hnat : (42302297 : ℕ)^65*100000000000000^49 ≤ 7045740434097^49*312500000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42302297 312500000 7045740434097 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8452459517/10000000000 : ℝ), (428241521/2000000000 : ℝ), (42302297/312500000 : ℝ)] ![(40004684574249/50000000000000 : ℝ), (12944890405153/100000000000000 : ℝ), (7045740434097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8452459517/10000000000 : ℝ)|^65 ≤ (40004684574249/50000000000000 : ℝ)^49
        have hw : |(8452459517/10000000000 : ℝ)|=(8452459517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(428241521/2000000000 : ℝ)|^65 ≤ (12944890405153/100000000000000 : ℝ)^49
        have hw : |(428241521/2000000000 : ℝ)|=(428241521/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(42302297/312500000 : ℝ)|^65 ≤ (7045740434097/100000000000000 : ℝ)^49
        have hw : |(42302297/312500000 : ℝ)|=(42302297/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c301055_s3 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev2 : (0 : ℝ) ≤ ((18143/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(18143/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(45281/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(45281/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(88599/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(88599/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((43369/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(43369/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1719/2000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1719/2000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(84781/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(84781/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4759/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4759/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4759/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4759/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (92391/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base34 : ((-1 : ℝ)*N 0+(1 : ℝ)*P 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 0]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
  rcases hprev2 with ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩
  have s3_pow0 : (18143/20000 : ℝ) ^ (129/32 : ℝ) ≤ (1350280162508363581/2000000000000000000 : ℝ) := by
    have hpowers : (18143/20000 : ℝ)^129 ≤ (1350280162508363581/2000000000000000000 : ℝ)^32 := by
      have hnat : (18143 : ℕ)^129*2000000000000000000^32 ≤ 1350280162508363581^32*20000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18143 20000 1350280162508363581 2000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18143/20000 : ℝ)) (X := (1350280162508363581/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s3_corner0a : (3350280162508363581/2000000000000000000 : ℝ) ≤ (11365239051642341/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (3350280162508363581/2000000000000000000 : ℝ)^32 ≤ (11365239051642341/10000000000000000 : ℝ)^129 := by
      have hnat : (3350280162508363581 : ℕ)^32*10000000000000000^129 ≤ 11365239051642341^129*2000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3350280162508363581 2000000000000000000 11365239051642341 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11365239051642341/10000000000000000 : ℝ)) (X := (3350280162508363581/2000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s3_corner0b : (2350280162508363581/1000000000000000000 : ℝ) ≤ (2472240292700839/2000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (2350280162508363581/1000000000000000000 : ℝ)^32 ≤ (2472240292700839/2000000000000000 : ℝ)^129 := by
      have hnat : (2350280162508363581 : ℕ)^32*2000000000000000^129 ≤ 2472240292700839^129*1000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2350280162508363581 1000000000000000000 2472240292700839 2000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2472240292700839/2000000000000000 : ℝ)) (X := (2350280162508363581/1000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s3_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1365239051642341/9071500000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(497981205930927/4535750000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (18143/20000 : ℝ)) (alpha := (1365239051642341/9071500000000000 : ℝ)) (beta := (497981205930927/4535750000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow0,s3_corner0a]) (by linarith only [s3_pow0,s3_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (18143/20000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1365239051642341/9071500000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(497981205930927/4535750000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow1 : (45281/50000 : ℝ) ^ (129/32 : ℝ) ≤ (67056145039052497623/100000000000000000000 : ℝ) := by
    have hpowers : (45281/50000 : ℝ)^129 ≤ (67056145039052497623/100000000000000000000 : ℝ)^32 := by
      have hnat : (45281 : ℕ)^129*100000000000000000000^32 ≤ 67056145039052497623^32*50000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        45281 50000 67056145039052497623 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (45281/50000 : ℝ)) (X := (67056145039052497623/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s3_corner1a : (167056145039052497623/100000000000000000000 : ℝ) ≤ (5678762610303199/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (167056145039052497623/100000000000000000000 : ℝ)^32 ≤ (5678762610303199/5000000000000000 : ℝ)^129 := by
      have hnat : (167056145039052497623 : ℕ)^32*5000000000000000^129 ≤ 5678762610303199^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        167056145039052497623 100000000000000000000 5678762610303199 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5678762610303199/5000000000000000 : ℝ)) (X := (167056145039052497623/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s3_corner1b : (117056145039052497623/50000000000000000000 : ℝ) ≤ (12349236700186163/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (117056145039052497623/50000000000000000000 : ℝ)^32 ≤ (12349236700186163/10000000000000000 : ℝ)^129 := by
      have hnat : (117056145039052497623 : ℕ)^32*10000000000000000^129 ≤ 12349236700186163^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        117056145039052497623 50000000000000000000 12349236700186163 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12349236700186163/10000000000000000 : ℝ)) (X := (117056145039052497623/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s3_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(678762610303199/4528100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(198342295915953/1811240000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (45281/50000 : ℝ)) (alpha := (678762610303199/4528100000000000 : ℝ)) (beta := (198342295915953/1811240000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow1,s3_corner1a]) (by linarith only [s3_pow1,s3_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (45281/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(678762610303199/4528100000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(198342295915953/1811240000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow2 : (88599/100000 : ℝ) ^ (129/32 : ℝ) ≤ (7673304702032964439/12500000000000000000 : ℝ) := by
    have hpowers : (88599/100000 : ℝ)^129 ≤ (7673304702032964439/12500000000000000000 : ℝ)^32 := by
      have hnat : (88599 : ℕ)^129*12500000000000000000^32 ≤ 7673304702032964439^32*100000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        88599 100000 7673304702032964439 12500000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (88599/100000 : ℝ)) (X := (7673304702032964439/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s3_corner2a : (20173304702032964439/12500000000000000000 : ℝ) ≤ (2815165453544269/2500000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (20173304702032964439/12500000000000000000 : ℝ)^32 ≤ (2815165453544269/2500000000000000 : ℝ)^129 := by
      have hnat : (20173304702032964439 : ℕ)^32*2500000000000000^129 ≤ 2815165453544269^129*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20173304702032964439 12500000000000000000 2815165453544269 2500000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2815165453544269/2500000000000000 : ℝ)) (X := (20173304702032964439/12500000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s3_corner2b : (13923304702032964439/6250000000000000000 : ℝ) ≤ (2439615710469897/2000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (13923304702032964439/6250000000000000000 : ℝ)^32 ≤ (2439615710469897/2000000000000000 : ℝ)^129 := by
      have hnat : (13923304702032964439 : ℕ)^32*2000000000000000^129 ≤ 2439615710469897^129*6250000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13923304702032964439 6250000000000000000 2439615710469897 2000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2439615710469897/2000000000000000 : ℝ)) (X := (13923304702032964439/6250000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s3_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(105055151181423/738325000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(937416738172409/8859900000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (88599/100000 : ℝ)) (alpha := (105055151181423/738325000000000 : ℝ)) (beta := (937416738172409/8859900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow2,s3_corner2a]) (by linarith only [s3_pow2,s3_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (88599/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(105055151181423/738325000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(937416738172409/8859900000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s3_0 : ((-141884759/1250000000 : ℝ)*X 0 0+(6053546879/10000000000 : ℝ)*X 0 1+(1059280389/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301055_s3_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_6 : ((1667667269/2500000000 : ℝ)*X 0 0+(1916271473/5000000000 : ℝ)*X 0 1+(553534077/2500000000 : ℝ)*X 0 2+(1667667269/2500000000 : ℝ)*X 1 0+(1916271473/5000000000 : ℝ)*X 1 1+(553534077/2500000000 : ℝ)*X 1 2+(1667667269/2500000000 : ℝ)*X 2 0+(1916271473/5000000000 : ℝ)*X 2 1+(553534077/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301055_s3_s3_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_7 : ((-327422517/1000000000 : ℝ)*X 0 0+(2202518669/5000000000 : ℝ)*X 0 1+(534440293/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301055_s3_s3_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_8 : ((2364001771/10000000000 : ℝ)*X 1 0+(176629/1250000000 : ℝ)*X 1 1+(8865593739/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301055_s3_s3_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_9 : ((1018277453/5000000000 : ℝ)*X 2 0+(4367194399/5000000000 : ℝ)*X 2 1+(-936030671/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301055_s3_s3_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_13 : ((2008217529/5000000000 : ℝ)*X 0 0+(729544799/1000000000 : ℝ)*X 0 1+(943582409/10000000000 : ℝ)*X 0 2+(2008217529/5000000000 : ℝ)*X 1 0+(729544799/1000000000 : ℝ)*X 1 1+(943582409/10000000000 : ℝ)*X 1 2+(2008217529/5000000000 : ℝ)*X 2 0+(729544799/1000000000 : ℝ)*X 2 1+(943582409/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301055_s3_s3_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_14 : ((-98600163/500000000 : ℝ)*X 0 0+(470718723/1000000000 : ℝ)*X 0 1+(1214347997/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301055_s3_s3_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_15 : ((289064631/2000000000 : ℝ)*X 1 0+(-782677/200000000 : ℝ)*X 1 1+(9410050247/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301055_s3_s3_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_16 : ((1870662933/2500000000 : ℝ)*X 2 0+(235839427/625000000 : ℝ)*X 2 1+(-60187113/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301055_s3_s3_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_20 : ((2203841793/2500000000 : ℝ)*X 0 0+(38674797/200000000 : ℝ)*X 0 1+(449521153/5000000000 : ℝ)*X 0 2+(2203841793/2500000000 : ℝ)*X 1 0+(38674797/200000000 : ℝ)*X 1 1+(449521153/5000000000 : ℝ)*X 1 2+(2203841793/2500000000 : ℝ)*X 2 0+(38674797/200000000 : ℝ)*X 2 1+(449521153/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301055_s3_s3_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_21 : ((-1386325063/10000000000 : ℝ)*X 0 0+(4103205747/5000000000 : ℝ)*X 0 1+(2487554197/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301055_s3_s3_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_22 : ((7570764113/10000000000 : ℝ)*X 1 0+(-12645019/10000000000 : ℝ)*X 1 1+(41211923/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301055_s3_s3_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_23 : ((130134131/1000000000 : ℝ)*X 2 0+(873652923/1000000000 : ℝ)*X 2 1+(-431233413/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301055_s3_s3_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_27 : ((8452459517/10000000000 : ℝ)*X 0 0+(428241521/2000000000 : ℝ)*X 0 1+(42302297/312500000 : ℝ)*X 0 2+(8452459517/10000000000 : ℝ)*X 1 0+(428241521/2000000000 : ℝ)*X 1 1+(42302297/312500000 : ℝ)*X 1 2+(8452459517/10000000000 : ℝ)*X 2 0+(428241521/2000000000 : ℝ)*X 2 1+(42302297/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301055_s3_s3_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s3_0 : (0 : ℝ) ≤ ((43369/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(43369/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4590406096308188062666694742489/606558487338475000000000000000000000 : ℝ) := by norm_num
    linear_combination (172747951431/250000000000 : ℝ)*(base7) + (611031/500000000000 : ℝ)*(base49) + (793315950603/1000000000000 : ℝ)*(base53) + (159679/1000000000000 : ℝ)*(base60) + (434596691107/250000000000 : ℝ)*(major_s3_0) + (434596691107/250000000000 : ℝ)*(major_s3_1) + (7383365733/7812500000 : ℝ)*(major_s3_2) + (1739869/125000000000 : ℝ)*(sp_s3_0) + (541317941793/500000000000 : ℝ)*(sp_s3_7) + (541328217819/500000000000 : ℝ)*(sp_s3_8) + (23449582191/12500000000 : ℝ)*(sp_s3_9) + (933090466431/500000000000 : ℝ)*(sp_s3_13) + (66331/10000000000 : ℝ)*(sp_s3_14) + (2905481/500000000000 : ℝ)*(sp_s3_23) + (587594563569/500000000000 : ℝ)*(f.failure) + (937986193121/500000000000 : ℝ)*(f.sum) + (8920889291270661941/33432094325000000000000000000000 : ℝ)*base63 + (105024709087887/184581250000000000000000000 : ℝ)*base65 + (64904570306489/452810000000000000000000000 : ℝ)*base66 + (605150103210297/738325000000000000000000000 : ℝ)*base69 + (9733393614883694141/66977152375000000000000000000000 : ℝ)*base71 + (168440500224189/1133937500000000000000000000 : ℝ)*base73 + (646653828624353/1132025000000000000000000000 : ℝ)*base75 + (1246108161968487/2267875000000000000000000000 : ℝ)*base77 + (1360621853025743061/205383295750000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (4811/12500000000000000 : ℝ)*base86 + (4811/12500000000000000 : ℝ)*base88 + (7689/12500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s3_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1719/2000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1719/2000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (8192695470855011481409689452833/2426233949353900000000000000000000000 : ℝ) := by norm_num
    linear_combination (717753345661/1000000000000 : ℝ)*(base7) + (2004427/1000000000000 : ℝ)*(base34) + (312088975987/500000000000 : ℝ)*(base53) + (159843665673/100000000000 : ℝ)*(major_s3_0) + (1598438661157/1000000000000 : ℝ)*(major_s3_1) + (974260709183/1000000000000 : ℝ)*(major_s3_2) + (5889273/200000000000 : ℝ)*(sp_s3_0) + (8595147/1000000000000 : ℝ)*(sp_s3_7) + (10315847/200000000000 : ℝ)*(sp_s3_8) + (524992093871/500000000000 : ℝ)*(sp_s3_14) + (524986327223/500000000000 : ℝ)*(sp_s3_15) + (334840437131/200000000000 : ℝ)*(sp_s3_16) + (1798320505661/1000000000000 : ℝ)*(sp_s3_20) + (1185093/100000000000 : ℝ)*(sp_s3_27) + (1080581015357/1000000000000 : ℝ)*(f.failure) + (334840437131/200000000000 : ℝ)*(f.sum) + (2198842050346223419/5349135092000000000000000000000 : ℝ)*base63 + (659493612082657/8859900000000000000000000000 : ℝ)*base65 + (101558885996499/362248000000000000000000000 : ℝ)*base67 + (806948219377513/1476650000000000000000000000 : ℝ)*base69 + (4133551723162174867/32149033140000000000000000000000 : ℝ)*base71 + (441904688036447/907150000000000000000000000 : ℝ)*base73 + (3872450099888023/4528100000000000000000000000 : ℝ)*base75 + (213767697811593/907150000000000000000000000 : ℝ)*base77 + (3630928087601722633/164306636600000000000000000000000 : ℝ)*base79 + (7783/25000000000000000 : ℝ)*base86 + (7783/25000000000000000 : ℝ)*base88 + (7783/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s3_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(84781/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(84781/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (77968258352258562105415901531289/6065584873384750000000000000000000000 : ℝ) := by norm_num
    linear_combination (834826573273/1000000000000 : ℝ)*(base7) + (123885613177/500000000000 : ℝ)*(base43) + (1971/500000000000 : ℝ)*(base49) + (1584493632511/1000000000000 : ℝ)*(major_s3_0) + (1336722406157/1000000000000 : ℝ)*(major_s3_1) + (1584493632511/1000000000000 : ℝ)*(major_s3_2) + (15013/125000000000 : ℝ)*(sp_s3_0) + (3467211/125000000000 : ℝ)*(sp_s3_6) + (14195283/200000000000 : ℝ)*(sp_s3_9) + (154866627/1000000000000 : ℝ)*(sp_s3_20) + (166981837069/125000000000 : ℝ)*(sp_s3_21) + (158362604301/100000000000 : ℝ)*(sp_s3_22) + (667891920121/500000000000 : ℝ)*(sp_s3_23) + (190579782669/100000000000 : ℝ)*(sp_s3_27) + (267788464433/250000000000 : ℝ)*(f.failure) + (158362604301/100000000000 : ℝ)*(f.sum) + (77497815665772504049/133728377300000000000000000000000 : ℝ)*base62 + (118128168080519/8859900000000000000000000000 : ℝ)*base65 + (315809376459179/1811240000000000000000000000 : ℝ)*base67 + (112628976771187/738325000000000000000000000 : ℝ)*base68 + (59065541618444360333/401862914250000000000000000000000 : ℝ)*base70 + (425302516337247/4535750000000000000000000000 : ℝ)*base73 + (2219853587574077/4528100000000000000000000000 : ℝ)*base74 + (6711003781759449/9071500000000000000000000000 : ℝ)*base76 + (58830161835694737747/821533183000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + (3023/6250000000000000 : ℝ)*base87 + (3023/6250000000000000 : ℝ)*base89 + (3023/6250000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev2 : (0 : ℝ) ≤ ((18143/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(18143/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(45281/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(45281/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(88599/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(88599/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((43369/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(43369/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1719/2000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1719/2000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(84781/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(84781/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c301055_s3 p hpa hpb X hX hprev2

#print axioms solution
