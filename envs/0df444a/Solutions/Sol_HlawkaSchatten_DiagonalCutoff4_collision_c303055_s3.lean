-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c303055_s3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:55:46.437761+00:00
-- url     : https://prove2.me/submissions/0fb41b25-8314-4cb7-8d32-df615d417cbf

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
theorem collision_support_c303055_s3_s3_0 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-751100509/5000000000 : ℝ)*x 0 + (1194630627/2000000000 : ℝ)*x 1 + (5104198833/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (751100509/5000000000 : ℝ)^33 ≤ (8189945817227/100000000000000 : ℝ)^25 := by
    have hnat : (751100509 : ℕ)^33*100000000000000^25 ≤ 8189945817227^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      751100509 5000000000 8189945817227 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1194630627/2000000000 : ℝ)^33 ≤ (50651092443473/100000000000000 : ℝ)^25 := by
    have hnat : (1194630627 : ℕ)^33*100000000000000^25 ≤ 50651092443473^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1194630627 2000000000 50651092443473 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5104198833/10000000000 : ℝ)^33 ≤ (8231792345251/20000000000000 : ℝ)^25 := by
    have hnat : (5104198833 : ℕ)^33*20000000000000^25 ≤ 8231792345251^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5104198833 10000000000 8231792345251 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-751100509/5000000000 : ℝ), (1194630627/2000000000 : ℝ), (5104198833/10000000000 : ℝ)] ![(8189945817227/100000000000000 : ℝ), (50651092443473/100000000000000 : ℝ), (8231792345251/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-751100509/5000000000 : ℝ)|^33 ≤ (8189945817227/100000000000000 : ℝ)^25
        have hw : |(-751100509/5000000000 : ℝ)|=(751100509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1194630627/2000000000 : ℝ)|^33 ≤ (50651092443473/100000000000000 : ℝ)^25
        have hw : |(1194630627/2000000000 : ℝ)|=(1194630627/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5104198833/10000000000 : ℝ)|^33 ≤ (8231792345251/20000000000000 : ℝ)^25
        have hw : |(5104198833/10000000000 : ℝ)|=(5104198833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303055_s3_s3_2 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (614500969/1250000000 : ℝ)*x 0 + (386550203/625000000 : ℝ)*x 1 + (-289504803/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (614500969/1250000000 : ℝ)^33 ≤ (9791936458847/25000000000000 : ℝ)^25 := by
    have hnat : (614500969 : ℕ)^33*25000000000000^25 ≤ 9791936458847^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      614500969 1250000000 9791936458847 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (386550203/625000000 : ℝ)^33 ≤ (3314592855751/6250000000000 : ℝ)^25 := by
    have hnat : (386550203 : ℕ)^33*6250000000000^25 ≤ 3314592855751^25*625000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      386550203 625000000 3314592855751 6250000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (289504803/2000000000 : ℝ)^33 ≤ (1949692113969/25000000000000 : ℝ)^25 := by
    have hnat : (289504803 : ℕ)^33*25000000000000^25 ≤ 1949692113969^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      289504803 2000000000 1949692113969 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(614500969/1250000000 : ℝ), (386550203/625000000 : ℝ), (-289504803/2000000000 : ℝ)] ![(9791936458847/25000000000000 : ℝ), (3314592855751/6250000000000 : ℝ), (1949692113969/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(614500969/1250000000 : ℝ)|^33 ≤ (9791936458847/25000000000000 : ℝ)^25
        have hw : |(614500969/1250000000 : ℝ)|=(614500969/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(386550203/625000000 : ℝ)|^33 ≤ (3314592855751/6250000000000 : ℝ)^25
        have hw : |(386550203/625000000 : ℝ)|=(386550203/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-289504803/2000000000 : ℝ)|^33 ≤ (1949692113969/25000000000000 : ℝ)^25
        have hw : |(-289504803/2000000000 : ℝ)|=(289504803/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303055_s3_s3_7 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1936431223/10000000000 : ℝ)*x 0 + (941408563/2500000000 : ℝ)*x 1 + (6876556439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1936431223/10000000000 : ℝ)^33 ≤ (1431372779989/12500000000000 : ℝ)^25 := by
    have hnat : (1936431223 : ℕ)^33*12500000000000^25 ≤ 1431372779989^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1936431223 10000000000 1431372779989 12500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (941408563/2500000000 : ℝ)^33 ≤ (13774515858537/50000000000000 : ℝ)^25 := by
    have hnat : (941408563 : ℕ)^33*50000000000000^25 ≤ 13774515858537^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      941408563 2500000000 13774515858537 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6876556439/10000000000 : ℝ)^33 ≤ (60999986032117/100000000000000 : ℝ)^25 := by
    have hnat : (6876556439 : ℕ)^33*100000000000000^25 ≤ 60999986032117^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6876556439 10000000000 60999986032117 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1936431223/10000000000 : ℝ), (941408563/2500000000 : ℝ), (6876556439/10000000000 : ℝ)] ![(1431372779989/12500000000000 : ℝ), (13774515858537/50000000000000 : ℝ), (60999986032117/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1936431223/10000000000 : ℝ)|^33 ≤ (1431372779989/12500000000000 : ℝ)^25
        have hw : |(-1936431223/10000000000 : ℝ)|=(1936431223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(941408563/2500000000 : ℝ)|^33 ≤ (13774515858537/50000000000000 : ℝ)^25
        have hw : |(941408563/2500000000 : ℝ)|=(941408563/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6876556439/10000000000 : ℝ)|^33 ≤ (60999986032117/100000000000000 : ℝ)^25
        have hw : |(6876556439/10000000000 : ℝ)|=(6876556439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303055_s3_s3_8 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (293083147/1000000000 : ℝ)*x 0 + (404531/10000000000 : ℝ)*x 1 + (8461522921/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (293083147/1000000000 : ℝ)^33 ≤ (19789185382141/100000000000000 : ℝ)^25 := by
    have hnat : (293083147 : ℕ)^33*100000000000000^25 ≤ 19789185382141^25*1000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      293083147 1000000000 19789185382141 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (404531/10000000000 : ℝ)^33 ≤ (158919207/100000000000000 : ℝ)^25 := by
    have hnat : (404531 : ℕ)^33*100000000000000^25 ≤ 158919207^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      404531 10000000000 158919207 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8461522921/10000000000 : ℝ)^33 ≤ (80210655681543/100000000000000 : ℝ)^25 := by
    have hnat : (8461522921 : ℕ)^33*100000000000000^25 ≤ 80210655681543^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8461522921 10000000000 80210655681543 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(293083147/1000000000 : ℝ), (404531/10000000000 : ℝ), (8461522921/10000000000 : ℝ)] ![(19789185382141/100000000000000 : ℝ), (158919207/100000000000000 : ℝ), (80210655681543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(293083147/1000000000 : ℝ)|^33 ≤ (19789185382141/100000000000000 : ℝ)^25
        have hw : |(293083147/1000000000 : ℝ)|=(293083147/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(404531/10000000000 : ℝ)|^33 ≤ (158919207/100000000000000 : ℝ)^25
        have hw : |(404531/10000000000 : ℝ)|=(404531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8461522921/10000000000 : ℝ)|^33 ≤ (80210655681543/100000000000000 : ℝ)^25
        have hw : |(8461522921/10000000000 : ℝ)|=(8461522921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303055_s3_s3_9 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (735453881/2500000000 : ℝ)*x 0 + (250456127/312500000 : ℝ)*x 1 + (-220574739/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (735453881/2500000000 : ℝ)^33 ≤ (3977428400077/20000000000000 : ℝ)^25 := by
    have hnat : (735453881 : ℕ)^33*20000000000000^25 ≤ 3977428400077^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      735453881 2500000000 3977428400077 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (250456127/312500000 : ℝ)^33 ≤ (37333075408217/50000000000000 : ℝ)^25 := by
    have hnat : (250456127 : ℕ)^33*50000000000000^25 ≤ 37333075408217^25*312500000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      250456127 312500000 37333075408217 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (220574739/2000000000 : ℝ)^33 ≤ (2723353587419/50000000000000 : ℝ)^25 := by
    have hnat : (220574739 : ℕ)^33*50000000000000^25 ≤ 2723353587419^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220574739 2000000000 2723353587419 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(735453881/2500000000 : ℝ), (250456127/312500000 : ℝ), (-220574739/2000000000 : ℝ)] ![(3977428400077/20000000000000 : ℝ), (37333075408217/50000000000000 : ℝ), (2723353587419/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(735453881/2500000000 : ℝ)|^33 ≤ (3977428400077/20000000000000 : ℝ)^25
        have hw : |(735453881/2500000000 : ℝ)|=(735453881/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(250456127/312500000 : ℝ)|^33 ≤ (37333075408217/50000000000000 : ℝ)^25
        have hw : |(250456127/312500000 : ℝ)|=(250456127/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-220574739/2000000000 : ℝ)|^33 ≤ (2723353587419/50000000000000 : ℝ)^25
        have hw : |(-220574739/2000000000 : ℝ)|=(220574739/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303055_s3_s3_13 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2237824259/5000000000 : ℝ)*x 0 + (416959757/625000000 : ℝ)*x 1 + (651440187/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2237824259/5000000000 : ℝ)^33 ≤ (34604285346879/100000000000000 : ℝ)^25 := by
    have hnat : (2237824259 : ℕ)^33*100000000000000^25 ≤ 34604285346879^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2237824259 5000000000 34604285346879 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (416959757/625000000 : ℝ)^33 ≤ (29304387431129/50000000000000 : ℝ)^25 := by
    have hnat : (416959757 : ℕ)^33*50000000000000^25 ≤ 29304387431129^25*625000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416959757 625000000 29304387431129 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (651440187/5000000000 : ℝ)^33 ≤ (1357387955519/20000000000000 : ℝ)^25 := by
    have hnat : (651440187 : ℕ)^33*20000000000000^25 ≤ 1357387955519^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      651440187 5000000000 1357387955519 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2237824259/5000000000 : ℝ), (416959757/625000000 : ℝ), (651440187/5000000000 : ℝ)] ![(34604285346879/100000000000000 : ℝ), (29304387431129/50000000000000 : ℝ), (1357387955519/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2237824259/5000000000 : ℝ)|^33 ≤ (34604285346879/100000000000000 : ℝ)^25
        have hw : |(2237824259/5000000000 : ℝ)|=(2237824259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(416959757/625000000 : ℝ)|^33 ≤ (29304387431129/50000000000000 : ℝ)^25
        have hw : |(416959757/625000000 : ℝ)|=(416959757/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(651440187/5000000000 : ℝ)|^33 ≤ (1357387955519/20000000000000 : ℝ)^25
        have hw : |(651440187/5000000000 : ℝ)|=(651440187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303055_s3_s3_14 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-399378547/5000000000 : ℝ)*x 0 + (165514709/400000000 : ℝ)*x 1 + (7235933231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (399378547/5000000000 : ℝ)^33 ≤ (711569684077/20000000000000 : ℝ)^25 := by
    have hnat : (399378547 : ℕ)^33*20000000000000^25 ≤ 711569684077^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      399378547 5000000000 711569684077 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (165514709/400000000 : ℝ)^33 ≤ (15599659571641/50000000000000 : ℝ)^25 := by
    have hnat : (165514709 : ℕ)^33*50000000000000^25 ≤ 15599659571641^25*400000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165514709 400000000 15599659571641 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7235933231/10000000000 : ℝ)^33 ≤ (32621416211329/50000000000000 : ℝ)^25 := by
    have hnat : (7235933231 : ℕ)^33*50000000000000^25 ≤ 32621416211329^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7235933231 10000000000 32621416211329 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-399378547/5000000000 : ℝ), (165514709/400000000 : ℝ), (7235933231/10000000000 : ℝ)] ![(711569684077/20000000000000 : ℝ), (15599659571641/50000000000000 : ℝ), (32621416211329/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-399378547/5000000000 : ℝ)|^33 ≤ (711569684077/20000000000000 : ℝ)^25
        have hw : |(-399378547/5000000000 : ℝ)|=(399378547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(165514709/400000000 : ℝ)|^33 ≤ (15599659571641/50000000000000 : ℝ)^25
        have hw : |(165514709/400000000 : ℝ)|=(165514709/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7235933231/10000000000 : ℝ)|^33 ≤ (32621416211329/50000000000000 : ℝ)^25
        have hw : |(7235933231/10000000000 : ℝ)|=(7235933231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303055_s3_s3_15 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2317269553/10000000000 : ℝ)*x 0 + (-234197453/10000000000 : ℝ)*x 1 + (551525013/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2317269553/10000000000 : ℝ)^33 ≤ (7256698132349/50000000000000 : ℝ)^25 := by
    have hnat : (2317269553 : ℕ)^33*50000000000000^25 ≤ 7256698132349^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2317269553 10000000000 7256698132349 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (234197453/10000000000 : ℝ)^33 ≤ (70444722271/10000000000000 : ℝ)^25 := by
    have hnat : (234197453 : ℕ)^33*10000000000000^25 ≤ 70444722271^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      234197453 10000000000 70444722271 10000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (551525013/625000000 : ℝ)^33 ≤ (3391286259841/4000000000000 : ℝ)^25 := by
    have hnat : (551525013 : ℕ)^33*4000000000000^25 ≤ 3391286259841^25*625000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551525013 625000000 3391286259841 4000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2317269553/10000000000 : ℝ), (-234197453/10000000000 : ℝ), (551525013/625000000 : ℝ)] ![(7256698132349/50000000000000 : ℝ), (70444722271/10000000000000 : ℝ), (3391286259841/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2317269553/10000000000 : ℝ)|^33 ≤ (7256698132349/50000000000000 : ℝ)^25
        have hw : |(2317269553/10000000000 : ℝ)|=(2317269553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-234197453/10000000000 : ℝ)|^33 ≤ (70444722271/10000000000000 : ℝ)^25
        have hw : |(-234197453/10000000000 : ℝ)|=(234197453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(551525013/625000000 : ℝ)|^33 ≤ (3391286259841/4000000000000 : ℝ)^25
        have hw : |(551525013/625000000 : ℝ)|=(551525013/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303055_s3_s3_16 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (7035327291/10000000000 : ℝ)*x 0 + (4396208237/10000000000 : ℝ)*x 1 + (-152223663/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7035327291/10000000000 : ℝ)^33 ≤ (7858240153713/12500000000000 : ℝ)^25 := by
    have hnat : (7035327291 : ℕ)^33*12500000000000^25 ≤ 7858240153713^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7035327291 10000000000 7858240153713 12500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4396208237/10000000000 : ℝ)^33 ≤ (33795844053539/100000000000000 : ℝ)^25 := by
    have hnat : (4396208237 : ℕ)^33*100000000000000^25 ≤ 33795844053539^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4396208237 10000000000 33795844053539 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (152223663/2000000000 : ℝ)^33 ≤ (1669117352529/50000000000000 : ℝ)^25 := by
    have hnat : (152223663 : ℕ)^33*50000000000000^25 ≤ 1669117352529^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      152223663 2000000000 1669117352529 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7035327291/10000000000 : ℝ), (4396208237/10000000000 : ℝ), (-152223663/2000000000 : ℝ)] ![(7858240153713/12500000000000 : ℝ), (33795844053539/100000000000000 : ℝ), (1669117352529/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7035327291/10000000000 : ℝ)|^33 ≤ (7858240153713/12500000000000 : ℝ)^25
        have hw : |(7035327291/10000000000 : ℝ)|=(7035327291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4396208237/10000000000 : ℝ)|^33 ≤ (33795844053539/100000000000000 : ℝ)^25
        have hw : |(4396208237/10000000000 : ℝ)|=(4396208237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-152223663/2000000000 : ℝ)|^33 ≤ (1669117352529/50000000000000 : ℝ)^25
        have hw : |(-152223663/2000000000 : ℝ)|=(152223663/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303055_s3_s3_20 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (8537158611/10000000000 : ℝ)*x 0 + (2334367451/10000000000 : ℝ)*x 1 + (903566297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8537158611/10000000000 : ℝ)^33 ≤ (20289606808949/25000000000000 : ℝ)^25 := by
    have hnat : (8537158611 : ℕ)^33*25000000000000^25 ≤ 20289606808949^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8537158611 10000000000 20289606808949 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2334367451/10000000000 : ℝ)^33 ≤ (14654917204207/100000000000000 : ℝ)^25 := by
    have hnat : (2334367451 : ℕ)^33*100000000000000^25 ≤ 14654917204207^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2334367451 10000000000 14654917204207 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (903566297/10000000000 : ℝ)^33 ≤ (4186655543643/100000000000000 : ℝ)^25 := by
    have hnat : (903566297 : ℕ)^33*100000000000000^25 ≤ 4186655543643^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903566297 10000000000 4186655543643 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8537158611/10000000000 : ℝ), (2334367451/10000000000 : ℝ), (903566297/10000000000 : ℝ)] ![(20289606808949/25000000000000 : ℝ), (14654917204207/100000000000000 : ℝ), (4186655543643/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8537158611/10000000000 : ℝ)|^33 ≤ (20289606808949/25000000000000 : ℝ)^25
        have hw : |(8537158611/10000000000 : ℝ)|=(8537158611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2334367451/10000000000 : ℝ)|^33 ≤ (14654917204207/100000000000000 : ℝ)^25
        have hw : |(2334367451/10000000000 : ℝ)|=(2334367451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(903566297/10000000000 : ℝ)|^33 ≤ (4186655543643/100000000000000 : ℝ)^25
        have hw : |(903566297/10000000000 : ℝ)|=(903566297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303055_s3_s3_21 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1044040279/10000000000 : ℝ)*x 0 + (7849072581/10000000000 : ℝ)*x 1 + (160400023/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1044040279/10000000000 : ℝ)^33 ≤ (1266621291209/25000000000000 : ℝ)^25 := by
    have hnat : (1044040279 : ℕ)^33*25000000000000^25 ≤ 1266621291209^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044040279 10000000000 1266621291209 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7849072581/10000000000 : ℝ)^33 ≤ (72637387443007/100000000000000 : ℝ)^25 := by
    have hnat : (7849072581 : ℕ)^33*100000000000000^25 ≤ 72637387443007^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7849072581 10000000000 72637387443007 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (160400023/500000000 : ℝ)^33 ≤ (11148063690253/50000000000000 : ℝ)^25 := by
    have hnat : (160400023 : ℕ)^33*50000000000000^25 ≤ 11148063690253^25*500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      160400023 500000000 11148063690253 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1044040279/10000000000 : ℝ), (7849072581/10000000000 : ℝ), (160400023/500000000 : ℝ)] ![(1266621291209/25000000000000 : ℝ), (72637387443007/100000000000000 : ℝ), (11148063690253/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1044040279/10000000000 : ℝ)|^33 ≤ (1266621291209/25000000000000 : ℝ)^25
        have hw : |(-1044040279/10000000000 : ℝ)|=(1044040279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7849072581/10000000000 : ℝ)|^33 ≤ (72637387443007/100000000000000 : ℝ)^25
        have hw : |(7849072581/10000000000 : ℝ)|=(7849072581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(160400023/500000000 : ℝ)|^33 ≤ (11148063690253/50000000000000 : ℝ)^25
        have hw : |(160400023/500000000 : ℝ)|=(160400023/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303055_s3_s3_22 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (7062505791/10000000000 : ℝ)*x 0 + (-36699817/10000000000 : ℝ)*x 1 + (292785877/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7062505791/10000000000 : ℝ)^33 ≤ (15796673688307/25000000000000 : ℝ)^25 := by
    have hnat : (7062505791 : ℕ)^33*25000000000000^25 ≤ 15796673688307^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7062505791 10000000000 15796673688307 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (36699817/10000000000 : ℝ)^33 ≤ (2440148953/4000000000000 : ℝ)^25 := by
    have hnat : (36699817 : ℕ)^33*4000000000000^25 ≤ 2440148953^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36699817 10000000000 2440148953 4000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (292785877/625000000 : ℝ)^33 ≤ (18376150756339/50000000000000 : ℝ)^25 := by
    have hnat : (292785877 : ℕ)^33*50000000000000^25 ≤ 18376150756339^25*625000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      292785877 625000000 18376150756339 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7062505791/10000000000 : ℝ), (-36699817/10000000000 : ℝ), (292785877/625000000 : ℝ)] ![(15796673688307/25000000000000 : ℝ), (2440148953/4000000000000 : ℝ), (18376150756339/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7062505791/10000000000 : ℝ)|^33 ≤ (15796673688307/25000000000000 : ℝ)^25
        have hw : |(7062505791/10000000000 : ℝ)|=(7062505791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-36699817/10000000000 : ℝ)|^33 ≤ (2440148953/4000000000000 : ℝ)^25
        have hw : |(-36699817/10000000000 : ℝ)|=(36699817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(292785877/625000000 : ℝ)|^33 ≤ (18376150756339/50000000000000 : ℝ)^25
        have hw : |(292785877/625000000 : ℝ)|=(292785877/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303055_s3_s3_23 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (264890431/1250000000 : ℝ)*x 0 + (2071556513/2500000000 : ℝ)*x 1 + (-405991219/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264890431/1250000000 : ℝ)^33 ≤ (12898115427147/100000000000000 : ℝ)^25 := by
    have hnat : (264890431 : ℕ)^33*100000000000000^25 ≤ 12898115427147^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264890431 1250000000 12898115427147 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2071556513/2500000000 : ℝ)^33 ≤ (15604898246261/20000000000000 : ℝ)^25 := by
    have hnat : (2071556513 : ℕ)^33*20000000000000^25 ≤ 15604898246261^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2071556513 2500000000 15604898246261 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (405991219/2500000000 : ℝ)^33 ≤ (4538696663887/50000000000000 : ℝ)^25 := by
    have hnat : (405991219 : ℕ)^33*50000000000000^25 ≤ 4538696663887^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      405991219 2500000000 4538696663887 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(264890431/1250000000 : ℝ), (2071556513/2500000000 : ℝ), (-405991219/2500000000 : ℝ)] ![(12898115427147/100000000000000 : ℝ), (15604898246261/20000000000000 : ℝ), (4538696663887/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(264890431/1250000000 : ℝ)|^33 ≤ (12898115427147/100000000000000 : ℝ)^25
        have hw : |(264890431/1250000000 : ℝ)|=(264890431/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2071556513/2500000000 : ℝ)|^33 ≤ (15604898246261/20000000000000 : ℝ)^25
        have hw : |(2071556513/2500000000 : ℝ)|=(2071556513/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-405991219/2500000000 : ℝ)|^33 ≤ (4538696663887/50000000000000 : ℝ)^25
        have hw : |(-405991219/2500000000 : ℝ)|=(405991219/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303055_s3_s3_27 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (8315152571/10000000000 : ℝ)*x 0 + (2152625973/10000000000 : ℝ)*x 1 + (1537897433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8315152571/10000000000 : ℝ)^33 ≤ (39192114728491/50000000000000 : ℝ)^25 := by
    have hnat : (8315152571 : ℕ)^33*50000000000000^25 ≤ 39192114728491^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8315152571 10000000000 39192114728491 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2152625973/10000000000 : ℝ)^33 ≤ (13167960659843/100000000000000 : ℝ)^25 := by
    have hnat : (2152625973 : ℕ)^33*100000000000000^25 ≤ 13167960659843^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2152625973 10000000000 13167960659843 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1537897433/10000000000 : ℝ)^33 ≤ (8447809873751/100000000000000 : ℝ)^25 := by
    have hnat : (1537897433 : ℕ)^33*100000000000000^25 ≤ 8447809873751^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1537897433 10000000000 8447809873751 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8315152571/10000000000 : ℝ), (2152625973/10000000000 : ℝ), (1537897433/10000000000 : ℝ)] ![(39192114728491/50000000000000 : ℝ), (13167960659843/100000000000000 : ℝ), (8447809873751/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8315152571/10000000000 : ℝ)|^33 ≤ (39192114728491/50000000000000 : ℝ)^25
        have hw : |(8315152571/10000000000 : ℝ)|=(8315152571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2152625973/10000000000 : ℝ)|^33 ≤ (13167960659843/100000000000000 : ℝ)^25
        have hw : |(2152625973/10000000000 : ℝ)|=(2152625973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1537897433/10000000000 : ℝ)|^33 ≤ (8447809873751/100000000000000 : ℝ)^25
        have hw : |(1537897433/10000000000 : ℝ)|=(1537897433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c303055_s3 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev2 : (0 : ℝ) ≤ ((82753/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(82753/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10149/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(10149/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(80841/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(80841/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((73627/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(73627/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9033/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(9033/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18287/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(18287/25000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76461/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76461/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76461/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76461/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76461/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76461/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (91389/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
  rcases hprev2 with ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩
  have s3_pow0 : (82753/100000 : ℝ) ^ (131/32 : ℝ) ≤ (46070954936135925627/100000000000000000000 : ℝ) := by
    have hpowers : (82753/100000 : ℝ)^131 ≤ (46070954936135925627/100000000000000000000 : ℝ)^32 := by
      have hnat : (82753 : ℕ)^131*100000000000000000000^32 ≤ 46070954936135925627^32*100000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        82753 100000 46070954936135925627 100000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (82753/100000 : ℝ)) (X := (46070954936135925627/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s3_corner0a : (146070954936135925627/100000000000000000000 : ℝ) ≤ (10969802473335461/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (146070954936135925627/100000000000000000000 : ℝ)^32 ≤ (10969802473335461/10000000000000000 : ℝ)^131 := by
      have hnat : (146070954936135925627 : ℕ)^32*10000000000000000^131 ≤ 10969802473335461^131*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        146070954936135925627 100000000000000000000 10969802473335461 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10969802473335461/10000000000000000 : ℝ)) (X := (146070954936135925627/100000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s3_corner0b : (96070954936135925627/50000000000000000000 : ℝ) ≤ (2932390094542381/2500000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (96070954936135925627/50000000000000000000 : ℝ)^32 ≤ (2932390094542381/2500000000000000 : ℝ)^131 := by
      have hnat : (96070954936135925627 : ℕ)^32*2500000000000000^131 ≤ 2932390094542381^131*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        96070954936135925627 50000000000000000000 2932390094542381 2500000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2932390094542381/2500000000000000 : ℝ)) (X := (96070954936135925627/50000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s3_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(969802473335461/8275300000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(759757904834063/8275300000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (82753/100000 : ℝ)) (alpha := (969802473335461/8275300000000000 : ℝ)) (beta := (759757904834063/8275300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow0,s3_corner0a]) (by linarith only [s3_pow0,s3_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (82753/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(969802473335461/8275300000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(759757904834063/8275300000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow1 : (10149/12500 : ℝ) ^ (131/32 : ℝ) ≤ (21307859699735325879/50000000000000000000 : ℝ) := by
    have hpowers : (10149/12500 : ℝ)^131 ≤ (21307859699735325879/50000000000000000000 : ℝ)^32 := by
      have hnat : (10149 : ℕ)^131*50000000000000000000^32 ≤ 21307859699735325879^32*12500^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10149 12500 21307859699735325879 50000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10149/12500 : ℝ)) (X := (21307859699735325879/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s3_corner1a : (71307859699735325879/50000000000000000000 : ℝ) ≤ (1363230281350773/1250000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (71307859699735325879/50000000000000000000 : ℝ)^32 ≤ (1363230281350773/1250000000000000 : ℝ)^131 := by
      have hnat : (71307859699735325879 : ℕ)^32*1250000000000000^131 ≤ 1363230281350773^131*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        71307859699735325879 50000000000000000000 1363230281350773 1250000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1363230281350773/1250000000000000 : ℝ)) (X := (71307859699735325879/50000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s3_corner1b : (46307859699735325879/25000000000000000000 : ℝ) ≤ (5812540094285433/5000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (46307859699735325879/25000000000000000000 : ℝ)^32 ≤ (5812540094285433/5000000000000000 : ℝ)^131 := by
      have hnat : (46307859699735325879 : ℕ)^32*5000000000000000^131 ≤ 5812540094285433^131*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        46307859699735325879 25000000000000000000 5812540094285433 5000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5812540094285433/5000000000000000 : ℝ)) (X := (46307859699735325879/25000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s3_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(113230281350773/1014900000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(119872989627447/1353200000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (10149/12500 : ℝ)) (alpha := (113230281350773/1014900000000000 : ℝ)) (beta := (119872989627447/1353200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow1,s3_corner1a]) (by linarith only [s3_pow1,s3_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (10149/12500 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(113230281350773/1014900000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(119872989627447/1353200000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow2 : (80841/100000 : ℝ) ^ (131/32 : ℝ) ≤ (4186655034617342959/10000000000000000000 : ℝ) := by
    have hpowers : (80841/100000 : ℝ)^131 ≤ (4186655034617342959/10000000000000000000 : ℝ)^32 := by
      have hnat : (80841 : ℕ)^131*10000000000000000000^32 ≤ 4186655034617342959^32*100000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        80841 100000 4186655034617342959 10000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (80841/100000 : ℝ)) (X := (4186655034617342959/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s3_corner2a : (14186655034617342959/10000000000000000000 : ℝ) ≤ (10891820114873567/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (14186655034617342959/10000000000000000000 : ℝ)^32 ≤ (10891820114873567/10000000000000000 : ℝ)^131 := by
      have hnat : (14186655034617342959 : ℕ)^32*10000000000000000^131 ≤ 10891820114873567^131*10000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14186655034617342959 10000000000000000000 10891820114873567 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10891820114873567/10000000000000000 : ℝ)) (X := (14186655034617342959/10000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s3_corner2b : (9186655034617342959/5000000000000000000 : ℝ) ≤ (1160203918053447/1000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (9186655034617342959/5000000000000000000 : ℝ)^32 ≤ (1160203918053447/1000000000000000 : ℝ)^131 := by
      have hnat : (9186655034617342959 : ℕ)^32*1000000000000000^131 ≤ 1160203918053447^131*5000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9186655034617342959 5000000000000000000 1160203918053447 1000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1160203918053447/1000000000000000 : ℝ)) (X := (9186655034617342959/5000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s3_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(891820114873567/8084100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(710219065660903/8084100000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (80841/100000 : ℝ)) (alpha := (891820114873567/8084100000000000 : ℝ)) (beta := (710219065660903/8084100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow2,s3_corner2a]) (by linarith only [s3_pow2,s3_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (80841/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(891820114873567/8084100000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(710219065660903/8084100000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s3_0 : ((-751100509/5000000000 : ℝ)*X 0 0+(1194630627/2000000000 : ℝ)*X 0 1+(5104198833/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303055_s3_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_2 : ((614500969/1250000000 : ℝ)*X 2 0+(386550203/625000000 : ℝ)*X 2 1+(-289504803/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303055_s3_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_7 : ((-1936431223/10000000000 : ℝ)*X 0 0+(941408563/2500000000 : ℝ)*X 0 1+(6876556439/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303055_s3_s3_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_8 : ((293083147/1000000000 : ℝ)*X 1 0+(404531/10000000000 : ℝ)*X 1 1+(8461522921/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303055_s3_s3_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_9 : ((735453881/2500000000 : ℝ)*X 2 0+(250456127/312500000 : ℝ)*X 2 1+(-220574739/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303055_s3_s3_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_13 : ((2237824259/5000000000 : ℝ)*X 0 0+(416959757/625000000 : ℝ)*X 0 1+(651440187/5000000000 : ℝ)*X 0 2+(2237824259/5000000000 : ℝ)*X 1 0+(416959757/625000000 : ℝ)*X 1 1+(651440187/5000000000 : ℝ)*X 1 2+(2237824259/5000000000 : ℝ)*X 2 0+(416959757/625000000 : ℝ)*X 2 1+(651440187/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303055_s3_s3_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_14 : ((-399378547/5000000000 : ℝ)*X 0 0+(165514709/400000000 : ℝ)*X 0 1+(7235933231/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303055_s3_s3_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_15 : ((2317269553/10000000000 : ℝ)*X 1 0+(-234197453/10000000000 : ℝ)*X 1 1+(551525013/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303055_s3_s3_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_16 : ((7035327291/10000000000 : ℝ)*X 2 0+(4396208237/10000000000 : ℝ)*X 2 1+(-152223663/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303055_s3_s3_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_20 : ((8537158611/10000000000 : ℝ)*X 0 0+(2334367451/10000000000 : ℝ)*X 0 1+(903566297/10000000000 : ℝ)*X 0 2+(8537158611/10000000000 : ℝ)*X 1 0+(2334367451/10000000000 : ℝ)*X 1 1+(903566297/10000000000 : ℝ)*X 1 2+(8537158611/10000000000 : ℝ)*X 2 0+(2334367451/10000000000 : ℝ)*X 2 1+(903566297/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303055_s3_s3_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_21 : ((-1044040279/10000000000 : ℝ)*X 0 0+(7849072581/10000000000 : ℝ)*X 0 1+(160400023/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303055_s3_s3_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_22 : ((7062505791/10000000000 : ℝ)*X 1 0+(-36699817/10000000000 : ℝ)*X 1 1+(292785877/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303055_s3_s3_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_23 : ((264890431/1250000000 : ℝ)*X 2 0+(2071556513/2500000000 : ℝ)*X 2 1+(-405991219/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303055_s3_s3_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_27 : ((8315152571/10000000000 : ℝ)*X 0 0+(2152625973/10000000000 : ℝ)*X 0 1+(1537897433/10000000000 : ℝ)*X 0 2+(8315152571/10000000000 : ℝ)*X 1 0+(2152625973/10000000000 : ℝ)*X 1 1+(1537897433/10000000000 : ℝ)*X 1 2+(8315152571/10000000000 : ℝ)*X 2 0+(2152625973/10000000000 : ℝ)*X 2 1+(1537897433/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303055_s3_s3_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s3_0 : (0 : ℝ) ≤ ((73627/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(73627/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (139229569402598611871906091/18232340200000000000000000000000 : ℝ) := by norm_num
    linear_combination (711906870657/1000000000000 : ℝ)*(base7) + (15061/12500000000 : ℝ)*(base49) + (1216337/1000000000000 : ℝ)*(base53) + (93471/200000000000 : ℝ)*(base60) + (440274982109/200000000000 : ℝ)*(major_s3_0) + (440274982109/200000000000 : ℝ)*(major_s3_1) + (8599115993/3906250000 : ℝ)*(major_s3_2) + (11022957/1000000000000 : ℝ)*(sp_s3_0) + (313187100471/125000000000 : ℝ)*(sp_s3_7) + (156595260313/62500000000 : ℝ)*(sp_s3_8) + (2505515807977/1000000000000 : ℝ)*(sp_s3_9) + (1087696192457/500000000000 : ℝ)*(sp_s3_13) + (16338283/1000000000000 : ℝ)*(sp_s3_14) + (1196671/125000000000 : ℝ)*(sp_s3_23) + (1463485514257/1000000000000 : ℝ)*(f.failure) + (501105076269/200000000000 : ℝ)*(f.sum) + (11707407127412569583/27348510300000000000000000000000 : ℝ)*base63 + (735239520518629/2021025000000000000000000000 : ℝ)*base64 + (117897664401589/270640000000000000000000000 : ℝ)*base67 + (235442295578377/1010512500000000000000000000 : ℝ)*base69 + (103017498105776364163/668983527300000000000000000000000 : ℝ)*base70 + (19078092540357/1655060000000000000000000000 : ℝ)*base72 + (1139870337683/40596000000000000000000000 : ℝ)*base74 + (145449336091057/1655060000000000000000000000 : ℝ)*base77 + (9221777426989214849/22396271920000000000000000000000 : ℝ)*base79 + (1897/5000000000000000 : ℝ)*base87 + (1897/5000000000000000 : ℝ)*base89 + (1897/5000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s3_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9033/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(9033/12500 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (397688177539420815921667829749/88751814621800000000000000000000000 : ℝ) := by norm_num
    linear_combination (306336361597/500000000000 : ℝ)*(base7) + (217/250000000000 : ℝ)*(base40) + (657/125000000000 : ℝ)*(base59) + (1870715166863/1000000000000 : ℝ)*(major_s3_0) + (1870715166863/1000000000000 : ℝ)*(major_s3_1) + (1870715166863/1000000000000 : ℝ)*(major_s3_2) + (6671163/500000000000 : ℝ)*(sp_s3_0) + (6756519/500000000000 : ℝ)*(sp_s3_2) + (89274673/1000000000000 : ℝ)*(sp_s3_8) + (1062238660597/500000000000 : ℝ)*(sp_s3_14) + (2124401388847/1000000000000 : ℝ)*(sp_s3_15) + (1062238575241/500000000000 : ℝ)*(sp_s3_16) + (371261442609/200000000000 : ℝ)*(sp_s3_20) + (26703383/1000000000000 : ℝ)*(sp_s3_27) + (621830596617/500000000000 : ℝ)*(f.failure) + (13278066647/6250000000 : ℝ)*(f.sum) + (4876571844996043/16757665625000000000000000000 : ℝ)*base63 + (2806167860693549/8084100000000000000000000000 : ℝ)*base65 + (24238189600407/79600000000000000000000000 : ℝ)*base67 + (4026054499913831/8084100000000000000000000000 : ℝ)*base69 + (498761430000492973/3344917636500000000000000000000 : ℝ)*base71 + (2684062480390479/8275300000000000000000000000 : ℝ)*base73 + (32281371642727/59700000000000000000000000 : ℝ)*base75 + (1757203712620483/8275300000000000000000000000 : ℝ)*base77 + (122925248797102711/1317427760000000000000000000000 : ℝ)*base79 + (1043/2500000000000000 : ℝ)*base86 + (1043/2500000000000000 : ℝ)*base88 + (1043/2500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s3_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18287/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(18287/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (24976155257519101412023933/4558085050000000000000000000000 : ℝ) := by norm_num
    linear_combination (90395272339/125000000000 : ℝ)*(base7) + (17099434119/500000000000 : ℝ)*(base40) + (14189/6250000000 : ℝ)*(base43) + (254681/1000000000000 : ℝ)*(base49) + (25333/125000000000 : ℝ)*(base59) + (920783350079/500000000000 : ℝ)*(major_s3_0) + (1841564429917/1000000000000 : ℝ)*(major_s3_1) + (920783350079/500000000000 : ℝ)*(major_s3_2) + (17296217/500000000000 : ℝ)*(sp_s3_9) + (12508571/1000000000000 : ℝ)*(sp_s3_20) + (2018252373911/1000000000000 : ℝ)*(sp_s3_21) + (252281830519/125000000000 : ℝ)*(sp_s3_22) + (2018217781477/1000000000000 : ℝ)*(sp_s3_23) + (1947432810787/1000000000000 : ℝ)*(sp_s3_27) + (244856628129/200000000000 : ℝ)*(f.failure) + (252281830519/125000000000 : ℝ)*(f.sum) + (1540028800467098187/1823234020000000000000000000000 : ℝ)*base62 + (194434351829461/2021025000000000000000000000 : ℝ)*base65 + (227224175504341/1353200000000000000000000000 : ℝ)*base67 + (3124772305108657/4042050000000000000000000000 : ℝ)*base68 + (2892139065043765951/16724588182500000000000000000000 : ℝ)*base71 + (686011572055147/4137650000000000000000000000 : ℝ)*base73 + (509634784715459/1014900000000000000000000000 : ℝ)*base74 + (2165584251591361/4137650000000000000000000000 : ℝ)*base76 + (10590497414561937379/111981359600000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base84 + (209/1000000000000000 : ℝ)*base87 + (1209/1000000000000000 : ℝ)*base89 + (209/1000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev2 : (0 : ℝ) ≤ ((82753/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(82753/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10149/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(10149/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(80841/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(80841/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((73627/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(73627/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9033/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(9033/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18287/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(18287/25000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c303055_s3 p hpa hpb X hX hprev2

#print axioms solution
