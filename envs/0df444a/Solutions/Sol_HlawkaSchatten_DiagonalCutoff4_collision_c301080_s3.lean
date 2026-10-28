-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c301080_s3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:42:40.286775+00:00
-- url     : https://prove2.me/submissions/0e3e614c-7bea-4d0b-96a6-f1a82bdffc2f

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
theorem collision_support_c301080_s3_s3_1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (46808873/80000000 : ℝ)*x 0 + (-132773733/1000000000 : ℝ)*x 1 + (84169243/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (46808873/80000000 : ℝ)^65 ≤ (49117284024347/100000000000000 : ℝ)^49 := by
    have hnat : (46808873 : ℕ)^65*100000000000000^49 ≤ 49117284024347^49*80000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46808873 80000000 49117284024347 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (132773733/1000000000 : ℝ)^65 ≤ (6867227648263/100000000000000 : ℝ)^49 := by
    have hnat : (132773733 : ℕ)^65*100000000000000^49 ≤ 6867227648263^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132773733 1000000000 6867227648263 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84169243/156250000 : ℝ)^65 ≤ (8803097661527/20000000000000 : ℝ)^49 := by
    have hnat : (84169243 : ℕ)^65*20000000000000^49 ≤ 8803097661527^49*156250000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84169243 156250000 8803097661527 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(46808873/80000000 : ℝ), (-132773733/1000000000 : ℝ), (84169243/156250000 : ℝ)] ![(49117284024347/100000000000000 : ℝ), (6867227648263/100000000000000 : ℝ), (8803097661527/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(46808873/80000000 : ℝ)|^65 ≤ (49117284024347/100000000000000 : ℝ)^49
        have hw : |(46808873/80000000 : ℝ)|=(46808873/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-132773733/1000000000 : ℝ)|^65 ≤ (6867227648263/100000000000000 : ℝ)^49
        have hw : |(-132773733/1000000000 : ℝ)|=(132773733/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84169243/156250000 : ℝ)|^65 ≤ (8803097661527/20000000000000 : ℝ)^49
        have hw : |(84169243/156250000 : ℝ)|=(84169243/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301080_s3_s3_2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3438546109/10000000000 : ℝ)*x 0 + (5799008743/10000000000 : ℝ)*x 1 + (-1873621107/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3438546109/10000000000 : ℝ)^65 ≤ (12132688665363/50000000000000 : ℝ)^49 := by
    have hnat : (3438546109 : ℕ)^65*50000000000000^49 ≤ 12132688665363^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3438546109 10000000000 12132688665363 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5799008743/10000000000 : ℝ)^65 ≤ (48537960402977/100000000000000 : ℝ)^49 := by
    have hnat : (5799008743 : ℕ)^65*100000000000000^49 ≤ 48537960402977^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5799008743 10000000000 48537960402977 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1873621107/5000000000 : ℝ)^65 ≤ (27196662246537/100000000000000 : ℝ)^49 := by
    have hnat : (1873621107 : ℕ)^65*100000000000000^49 ≤ 27196662246537^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1873621107 5000000000 27196662246537 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3438546109/10000000000 : ℝ), (5799008743/10000000000 : ℝ), (-1873621107/5000000000 : ℝ)] ![(12132688665363/50000000000000 : ℝ), (48537960402977/100000000000000 : ℝ), (27196662246537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3438546109/10000000000 : ℝ)|^65 ≤ (12132688665363/50000000000000 : ℝ)^49
        have hw : |(3438546109/10000000000 : ℝ)|=(3438546109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5799008743/10000000000 : ℝ)|^65 ≤ (48537960402977/100000000000000 : ℝ)^49
        have hw : |(5799008743/10000000000 : ℝ)|=(5799008743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1873621107/5000000000 : ℝ)|^65 ≤ (27196662246537/100000000000000 : ℝ)^49
        have hw : |(-1873621107/5000000000 : ℝ)|=(1873621107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301080_s3_s3_7 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3712322043/10000000000 : ℝ)*x 0 + (5405044151/10000000000 : ℝ)*x 1 + (392549619/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3712322043/10000000000 : ℝ)^65 ≤ (26860975010143/100000000000000 : ℝ)^49 := by
    have hnat : (3712322043 : ℕ)^65*100000000000000^49 ≤ 26860975010143^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3712322043 10000000000 26860975010143 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5405044151/10000000000 : ℝ)^65 ≤ (44213003638383/100000000000000 : ℝ)^49 := by
    have hnat : (5405044151 : ℕ)^65*100000000000000^49 ≤ 44213003638383^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405044151 10000000000 44213003638383 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (392549619/1000000000 : ℝ)^65 ≤ (28926021340899/100000000000000 : ℝ)^49 := by
    have hnat : (392549619 : ℕ)^65*100000000000000^49 ≤ 28926021340899^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      392549619 1000000000 28926021340899 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3712322043/10000000000 : ℝ), (5405044151/10000000000 : ℝ), (392549619/1000000000 : ℝ)] ![(26860975010143/100000000000000 : ℝ), (44213003638383/100000000000000 : ℝ), (28926021340899/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3712322043/10000000000 : ℝ)|^65 ≤ (26860975010143/100000000000000 : ℝ)^49
        have hw : |(-3712322043/10000000000 : ℝ)|=(3712322043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5405044151/10000000000 : ℝ)|^65 ≤ (44213003638383/100000000000000 : ℝ)^49
        have hw : |(5405044151/10000000000 : ℝ)|=(5405044151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(392549619/1000000000 : ℝ)|^65 ≤ (28926021340899/100000000000000 : ℝ)^49
        have hw : |(392549619/1000000000 : ℝ)|=(392549619/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301080_s3_s3_8 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2890520979/5000000000 : ℝ)*x 0 + (-836096907/10000000000 : ℝ)*x 1 + (5745357001/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2890520979/5000000000 : ℝ)^65 ≤ (48338574010293/100000000000000 : ℝ)^49 := by
    have hnat : (2890520979 : ℕ)^65*100000000000000^49 ≤ 48338574010293^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2890520979 5000000000 48338574010293 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (836096907/10000000000 : ℝ)^65 ≤ (1859132805949/50000000000000 : ℝ)^49 := by
    have hnat : (836096907 : ℕ)^65*50000000000000^49 ≤ 1859132805949^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      836096907 10000000000 1859132805949 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5745357001/10000000000 : ℝ)^65 ≤ (47943160360189/100000000000000 : ℝ)^49 := by
    have hnat : (5745357001 : ℕ)^65*100000000000000^49 ≤ 47943160360189^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5745357001 10000000000 47943160360189 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2890520979/5000000000 : ℝ), (-836096907/10000000000 : ℝ), (5745357001/10000000000 : ℝ)] ![(48338574010293/100000000000000 : ℝ), (1859132805949/50000000000000 : ℝ), (47943160360189/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2890520979/5000000000 : ℝ)|^65 ≤ (48338574010293/100000000000000 : ℝ)^49
        have hw : |(2890520979/5000000000 : ℝ)|=(2890520979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-836096907/10000000000 : ℝ)|^65 ≤ (1859132805949/50000000000000 : ℝ)^49
        have hw : |(-836096907/10000000000 : ℝ)|=(836096907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5745357001/10000000000 : ℝ)|^65 ≤ (47943160360189/100000000000000 : ℝ)^49
        have hw : |(5745357001/10000000000 : ℝ)|=(5745357001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301080_s3_s3_9 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (200047029/625000000 : ℝ)*x 0 + (6299682403/10000000000 : ℝ)*x 1 + (-846137637/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (200047029/625000000 : ℝ)^65 ≤ (22064889153407/100000000000000 : ℝ)^49 := by
    have hnat : (200047029 : ℕ)^65*100000000000000^49 ≤ 22064889153407^49*625000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200047029 625000000 22064889153407 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6299682403/10000000000 : ℝ)^65 ≤ (54173893889249/100000000000000 : ℝ)^49 := by
    have hnat : (6299682403 : ℕ)^65*100000000000000^49 ≤ 54173893889249^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6299682403 10000000000 54173893889249 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (846137637/2500000000 : ℝ)^65 ≤ (5940304237451/25000000000000 : ℝ)^49 := by
    have hnat : (846137637 : ℕ)^65*25000000000000^49 ≤ 5940304237451^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      846137637 2500000000 5940304237451 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(200047029/625000000 : ℝ), (6299682403/10000000000 : ℝ), (-846137637/2500000000 : ℝ)] ![(22064889153407/100000000000000 : ℝ), (54173893889249/100000000000000 : ℝ), (5940304237451/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(200047029/625000000 : ℝ)|^65 ≤ (22064889153407/100000000000000 : ℝ)^49
        have hw : |(200047029/625000000 : ℝ)|=(200047029/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6299682403/10000000000 : ℝ)|^65 ≤ (54173893889249/100000000000000 : ℝ)^49
        have hw : |(6299682403/10000000000 : ℝ)|=(6299682403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-846137637/2500000000 : ℝ)|^65 ≤ (5940304237451/25000000000000 : ℝ)^49
        have hw : |(-846137637/2500000000 : ℝ)|=(846137637/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301080_s3_s3_12 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (252562307/625000000 : ℝ)*x 0 + (2511924051/5000000000 : ℝ)*x 1 + (1004013207/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (252562307/625000000 : ℝ)^65 ≤ (30060415114447/100000000000000 : ℝ)^49 := by
    have hnat : (252562307 : ℕ)^65*100000000000000^49 ≤ 30060415114447^49*625000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      252562307 625000000 30060415114447 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2511924051/5000000000 : ℝ)^65 ≤ (10031266623837/25000000000000 : ℝ)^49 := by
    have hnat : (2511924051 : ℕ)^65*25000000000000^49 ≤ 10031266623837^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2511924051 5000000000 10031266623837 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1004013207/2500000000 : ℝ)^65 ≤ (7453629592057/25000000000000 : ℝ)^49 := by
    have hnat : (1004013207 : ℕ)^65*25000000000000^49 ≤ 7453629592057^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004013207 2500000000 7453629592057 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(252562307/625000000 : ℝ), (2511924051/5000000000 : ℝ), (1004013207/2500000000 : ℝ)] ![(30060415114447/100000000000000 : ℝ), (10031266623837/25000000000000 : ℝ), (7453629592057/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(252562307/625000000 : ℝ)|^65 ≤ (30060415114447/100000000000000 : ℝ)^49
        have hw : |(252562307/625000000 : ℝ)|=(252562307/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2511924051/5000000000 : ℝ)|^65 ≤ (10031266623837/25000000000000 : ℝ)^49
        have hw : |(2511924051/5000000000 : ℝ)|=(2511924051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1004013207/2500000000 : ℝ)|^65 ≤ (7453629592057/25000000000000 : ℝ)^49
        have hw : |(1004013207/2500000000 : ℝ)|=(1004013207/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301080_s3_s3_13 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-74739677/200000000 : ℝ)*x 0 + (339481139/625000000 : ℝ)*x 1 + (483940007/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (74739677/200000000 : ℝ)^65 ≤ (27097942290713/100000000000000 : ℝ)^49 := by
    have hnat : (74739677 : ℕ)^65*100000000000000^49 ≤ 27097942290713^49*200000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      74739677 200000000 27097942290713 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (339481139/625000000 : ℝ)^65 ≤ (11125614610991/25000000000000 : ℝ)^49 := by
    have hnat : (339481139 : ℕ)^65*25000000000000^49 ≤ 11125614610991^49*625000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339481139 625000000 11125614610991 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (483940007/1250000000 : ℝ)^65 ≤ (5679919849623/20000000000000 : ℝ)^49 := by
    have hnat : (483940007 : ℕ)^65*20000000000000^49 ≤ 5679919849623^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      483940007 1250000000 5679919849623 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-74739677/200000000 : ℝ), (339481139/625000000 : ℝ), (483940007/1250000000 : ℝ)] ![(27097942290713/100000000000000 : ℝ), (11125614610991/25000000000000 : ℝ), (5679919849623/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-74739677/200000000 : ℝ)|^65 ≤ (27097942290713/100000000000000 : ℝ)^49
        have hw : |(-74739677/200000000 : ℝ)|=(74739677/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(339481139/625000000 : ℝ)|^65 ≤ (11125614610991/25000000000000 : ℝ)^49
        have hw : |(339481139/625000000 : ℝ)|=(339481139/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(483940007/1250000000 : ℝ)|^65 ≤ (5679919849623/20000000000000 : ℝ)^49
        have hw : |(483940007/1250000000 : ℝ)|=(483940007/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301080_s3_s3_14 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1448072051/2500000000 : ℝ)*x 0 + (-330092389/2500000000 : ℝ)*x 1 + (2725847461/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1448072051/2500000000 : ℝ)^65 ≤ (12115838893473/25000000000000 : ℝ)^49 := by
    have hnat : (1448072051 : ℕ)^65*25000000000000^49 ≤ 12115838893473^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1448072051 2500000000 12115838893473 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (330092389/2500000000 : ℝ)^65 ≤ (3408361653007/50000000000000 : ℝ)^49 := by
    have hnat : (330092389 : ℕ)^65*50000000000000^49 ≤ 3408361653007^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330092389 2500000000 3408361653007 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2725847461/5000000000 : ℝ)^65 ≤ (44719921094433/100000000000000 : ℝ)^49 := by
    have hnat : (2725847461 : ℕ)^65*100000000000000^49 ≤ 44719921094433^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2725847461 5000000000 44719921094433 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1448072051/2500000000 : ℝ), (-330092389/2500000000 : ℝ), (2725847461/5000000000 : ℝ)] ![(12115838893473/25000000000000 : ℝ), (3408361653007/50000000000000 : ℝ), (44719921094433/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1448072051/2500000000 : ℝ)|^65 ≤ (12115838893473/25000000000000 : ℝ)^49
        have hw : |(1448072051/2500000000 : ℝ)|=(1448072051/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-330092389/2500000000 : ℝ)|^65 ≤ (3408361653007/50000000000000 : ℝ)^49
        have hw : |(-330092389/2500000000 : ℝ)|=(330092389/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2725847461/5000000000 : ℝ)|^65 ≤ (44719921094433/100000000000000 : ℝ)^49
        have hw : |(2725847461/5000000000 : ℝ)|=(2725847461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301080_s3_s3_15 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1675183157/5000000000 : ℝ)*x 0 + (1447481469/2500000000 : ℝ)*x 1 + (-48033717/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1675183157/5000000000 : ℝ)^65 ≤ (23443388747589/100000000000000 : ℝ)^49 := by
    have hnat : (1675183157 : ℕ)^65*100000000000000^49 ≤ 23443388747589^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1675183157 5000000000 23443388747589 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1447481469/2500000000 : ℝ)^65 ≤ (24218569019007/50000000000000 : ℝ)^49 := by
    have hnat : (1447481469 : ℕ)^65*50000000000000^49 ≤ 24218569019007^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1447481469 2500000000 24218569019007 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (48033717/125000000 : ℝ)^65 ≤ (14059736600277/50000000000000 : ℝ)^49 := by
    have hnat : (48033717 : ℕ)^65*50000000000000^49 ≤ 14059736600277^49*125000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48033717 125000000 14059736600277 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1675183157/5000000000 : ℝ), (1447481469/2500000000 : ℝ), (-48033717/125000000 : ℝ)] ![(23443388747589/100000000000000 : ℝ), (24218569019007/50000000000000 : ℝ), (14059736600277/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1675183157/5000000000 : ℝ)|^65 ≤ (23443388747589/100000000000000 : ℝ)^49
        have hw : |(1675183157/5000000000 : ℝ)|=(1675183157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1447481469/2500000000 : ℝ)|^65 ≤ (24218569019007/50000000000000 : ℝ)^49
        have hw : |(1447481469/2500000000 : ℝ)|=(1447481469/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-48033717/125000000 : ℝ)|^65 ≤ (14059736600277/50000000000000 : ℝ)^49
        have hw : |(-48033717/125000000 : ℝ)|=(48033717/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301080_s3_s3_19 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4360286127/10000000000 : ℝ)*x 0 + (4921735907/10000000000 : ℝ)*x 1 + (759924853/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4360286127/10000000000 : ℝ)^65 ≤ (33251067901379/100000000000000 : ℝ)^49 := by
    have hnat : (4360286127 : ℕ)^65*100000000000000^49 ≤ 33251067901379^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4360286127 10000000000 33251067901379 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4921735907/10000000000 : ℝ)^65 ≤ (39046805441733/100000000000000 : ℝ)^49 := by
    have hnat : (4921735907 : ℕ)^65*100000000000000^49 ≤ 39046805441733^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4921735907 10000000000 39046805441733 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (759924853/2000000000 : ℝ)^65 ≤ (3462765831001/12500000000000 : ℝ)^49 := by
    have hnat : (759924853 : ℕ)^65*12500000000000^49 ≤ 3462765831001^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      759924853 2000000000 3462765831001 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4360286127/10000000000 : ℝ), (4921735907/10000000000 : ℝ), (759924853/2000000000 : ℝ)] ![(33251067901379/100000000000000 : ℝ), (39046805441733/100000000000000 : ℝ), (3462765831001/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4360286127/10000000000 : ℝ)|^65 ≤ (33251067901379/100000000000000 : ℝ)^49
        have hw : |(4360286127/10000000000 : ℝ)|=(4360286127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4921735907/10000000000 : ℝ)|^65 ≤ (39046805441733/100000000000000 : ℝ)^49
        have hw : |(4921735907/10000000000 : ℝ)|=(4921735907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(759924853/2000000000 : ℝ)|^65 ≤ (3462765831001/12500000000000 : ℝ)^49
        have hw : |(759924853/2000000000 : ℝ)|=(759924853/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301080_s3_s3_20 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-418151581/1250000000 : ℝ)*x 0 + (2788231939/5000000000 : ℝ)*x 1 + (4087665451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (418151581/1250000000 : ℝ)^65 ≤ (1462222751139/6250000000000 : ℝ)^49 := by
    have hnat : (418151581 : ℕ)^65*6250000000000^49 ≤ 1462222751139^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      418151581 1250000000 1462222751139 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2788231939/5000000000 : ℝ)^65 ≤ (46082635370599/100000000000000 : ℝ)^49 := by
    have hnat : (2788231939 : ℕ)^65*100000000000000^49 ≤ 46082635370599^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2788231939 5000000000 46082635370599 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4087665451/10000000000 : ℝ)^65 ≤ (7630450149139/25000000000000 : ℝ)^49 := by
    have hnat : (4087665451 : ℕ)^65*25000000000000^49 ≤ 7630450149139^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4087665451 10000000000 7630450149139 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-418151581/1250000000 : ℝ), (2788231939/5000000000 : ℝ), (4087665451/10000000000 : ℝ)] ![(1462222751139/6250000000000 : ℝ), (46082635370599/100000000000000 : ℝ), (7630450149139/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-418151581/1250000000 : ℝ)|^65 ≤ (1462222751139/6250000000000 : ℝ)^49
        have hw : |(-418151581/1250000000 : ℝ)|=(418151581/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2788231939/5000000000 : ℝ)|^65 ≤ (46082635370599/100000000000000 : ℝ)^49
        have hw : |(2788231939/5000000000 : ℝ)|=(2788231939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4087665451/10000000000 : ℝ)|^65 ≤ (7630450149139/25000000000000 : ℝ)^49
        have hw : |(4087665451/10000000000 : ℝ)|=(4087665451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301080_s3_s3_21 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6351142933/10000000000 : ℝ)*x 0 + (-240587559/2500000000 : ℝ)*x 1 + (508341991/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6351142933/10000000000 : ℝ)^65 ≤ (27380854464029/50000000000000 : ℝ)^49 := by
    have hnat : (6351142933 : ℕ)^65*50000000000000^49 ≤ 27380854464029^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6351142933 10000000000 27380854464029 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (240587559/2500000000 : ℝ)^65 ≤ (179233960671/4000000000000 : ℝ)^49 := by
    have hnat : (240587559 : ℕ)^65*4000000000000^49 ≤ 179233960671^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      240587559 2500000000 179233960671 4000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (508341991/1000000000 : ℝ)^65 ≤ (5094680255211/12500000000000 : ℝ)^49 := by
    have hnat : (508341991 : ℕ)^65*12500000000000^49 ≤ 5094680255211^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508341991 1000000000 5094680255211 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6351142933/10000000000 : ℝ), (-240587559/2500000000 : ℝ), (508341991/1000000000 : ℝ)] ![(27380854464029/50000000000000 : ℝ), (179233960671/4000000000000 : ℝ), (5094680255211/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6351142933/10000000000 : ℝ)|^65 ≤ (27380854464029/50000000000000 : ℝ)^49
        have hw : |(6351142933/10000000000 : ℝ)|=(6351142933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-240587559/2500000000 : ℝ)|^65 ≤ (179233960671/4000000000000 : ℝ)^49
        have hw : |(-240587559/2500000000 : ℝ)|=(240587559/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(508341991/1000000000 : ℝ)|^65 ≤ (5094680255211/12500000000000 : ℝ)^49
        have hw : |(508341991/1000000000 : ℝ)|=(508341991/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301080_s3_s3_22 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3028924839/10000000000 : ℝ)*x 0 + (192919653/312500000 : ℝ)*x 1 + (-231323699/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3028924839/10000000000 : ℝ)^65 ≤ (20507527941649/100000000000000 : ℝ)^49 := by
    have hnat : (3028924839 : ℕ)^65*100000000000000^49 ≤ 20507527941649^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3028924839 10000000000 20507527941649 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (192919653/312500000 : ℝ)^65 ≤ (26369198431891/50000000000000 : ℝ)^49 := by
    have hnat : (192919653 : ℕ)^65*50000000000000^49 ≤ 26369198431891^49*312500000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      192919653 312500000 26369198431891 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (231323699/625000000 : ℝ)^65 ≤ (26754075179711/100000000000000 : ℝ)^49 := by
    have hnat : (231323699 : ℕ)^65*100000000000000^49 ≤ 26754075179711^49*625000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      231323699 625000000 26754075179711 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3028924839/10000000000 : ℝ), (192919653/312500000 : ℝ), (-231323699/625000000 : ℝ)] ![(20507527941649/100000000000000 : ℝ), (26369198431891/50000000000000 : ℝ), (26754075179711/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3028924839/10000000000 : ℝ)|^65 ≤ (20507527941649/100000000000000 : ℝ)^49
        have hw : |(3028924839/10000000000 : ℝ)|=(3028924839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(192919653/312500000 : ℝ)|^65 ≤ (26369198431891/50000000000000 : ℝ)^49
        have hw : |(192919653/312500000 : ℝ)|=(192919653/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-231323699/625000000 : ℝ)|^65 ≤ (26754075179711/100000000000000 : ℝ)^49
        have hw : |(-231323699/625000000 : ℝ)|=(231323699/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301080_s3_s3_25 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4662592627/10000000000 : ℝ)*x 0 + (4688125873/10000000000 : ℝ)*x 1 + (1865956761/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4662592627/10000000000 : ℝ)^65 ≤ (9085821637891/25000000000000 : ℝ)^49 := by
    have hnat : (4662592627 : ℕ)^65*25000000000000^49 ≤ 9085821637891^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4662592627 10000000000 9085821637891 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4688125873/10000000000 : ℝ)^65 ≤ (9151883023973/25000000000000 : ℝ)^49 := by
    have hnat : (4688125873 : ℕ)^65*25000000000000^49 ≤ 9151883023973^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4688125873 10000000000 9151883023973 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1865956761/5000000000 : ℝ)^65 ≤ (6762295334569/25000000000000 : ℝ)^49 := by
    have hnat : (1865956761 : ℕ)^65*25000000000000^49 ≤ 6762295334569^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1865956761 5000000000 6762295334569 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4662592627/10000000000 : ℝ), (4688125873/10000000000 : ℝ), (1865956761/5000000000 : ℝ)] ![(9085821637891/25000000000000 : ℝ), (9151883023973/25000000000000 : ℝ), (6762295334569/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4662592627/10000000000 : ℝ)|^65 ≤ (9085821637891/25000000000000 : ℝ)^49
        have hw : |(4662592627/10000000000 : ℝ)|=(4662592627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4688125873/10000000000 : ℝ)|^65 ≤ (9151883023973/25000000000000 : ℝ)^49
        have hw : |(4688125873/10000000000 : ℝ)|=(4688125873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1865956761/5000000000 : ℝ)|^65 ≤ (6762295334569/25000000000000 : ℝ)^49
        have hw : |(1865956761/5000000000 : ℝ)|=(1865956761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c301080_s3 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]])
    (hprev2 : (0 : ℝ) ≤ ((2817/5000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2817/5000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((15881/100000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(15881/100000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(64437/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(64437/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((18529/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(18529/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((147/10000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(147/10000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(23011/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(23011/100000 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  rcases hprev2 with ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩
  have s3_pow0 : (2817/5000 : ℝ) ^ (129/32 : ℝ) ≤ (7917177539444999/80000000000000000 : ℝ) := by
    have hpowers : (2817/5000 : ℝ)^129 ≤ (7917177539444999/80000000000000000 : ℝ)^32 := by
      have hnat : (2817 : ℕ)^129*80000000000000000^32 ≤ 7917177539444999^32*5000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2817 5000 7917177539444999 80000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2817/5000 : ℝ)) (X := (7917177539444999/80000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s3_corner0a : (87917177539444999/80000000000000000 : ℝ) ≤ (7997542230651/7812500000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (87917177539444999/80000000000000000 : ℝ)^32 ≤ (7997542230651/7812500000000 : ℝ)^129 := by
      have hnat : (87917177539444999 : ℕ)^32*7812500000000^129 ≤ 7997542230651^129*80000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        87917177539444999 80000000000000000 7997542230651 7812500000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (7997542230651/7812500000000 : ℝ)) (X := (87917177539444999/80000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s3_corner0b : (47917177539444999/40000000000000000 : ℝ) ≤ (5229086369826143/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (47917177539444999/40000000000000000 : ℝ)^32 ≤ (5229086369826143/5000000000000000 : ℝ)^129 := by
      have hnat : (47917177539444999 : ℕ)^32*5000000000000000^129 ≤ 5229086369826143^129*40000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        47917177539444999 40000000000000000 5229086369826143 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5229086369826143/5000000000000000 : ℝ)) (X := (47917177539444999/40000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s3_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(185042230651/4401562500000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(110659342209503/2817000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (2817/5000 : ℝ)) (alpha := (185042230651/4401562500000 : ℝ)) (beta := (110659342209503/2817000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow0,s3_corner0a]) (by linarith only [s3_pow0,s3_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (2817/5000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(185042230651/4401562500000 : ℝ)*((1 : ℝ)*pair X 0 1)+(110659342209503/2817000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow1 : (15881/100000 : ℝ) ^ (129/32 : ℝ) ≤ (30026784011201573/50000000000000000000 : ℝ) := by
    have hpowers : (15881/100000 : ℝ)^129 ≤ (30026784011201573/50000000000000000000 : ℝ)^32 := by
      have hnat : (15881 : ℕ)^129*50000000000000000000^32 ≤ 30026784011201573^32*100000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15881 100000 30026784011201573 50000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15881/100000 : ℝ)) (X := (30026784011201573/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s3_corner1a : (50030026784011201573/50000000000000000000 : ℝ) ≤ (5000744682340629/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (50030026784011201573/50000000000000000000 : ℝ)^32 ≤ (5000744682340629/5000000000000000 : ℝ)^129 := by
      have hnat : (50030026784011201573 : ℕ)^32*5000000000000000^129 ≤ 5000744682340629^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030026784011201573 50000000000000000000 5000744682340629 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000744682340629/5000000000000000 : ℝ)) (X := (50030026784011201573/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s3_corner1b : (25030026784011201573/25000000000000000000 : ℝ) ≤ (1000297805737191/1000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (25030026784011201573/25000000000000000000 : ℝ)^32 ≤ (1000297805737191/1000000000000000 : ℝ)^129 := by
      have hnat : (25030026784011201573 : ℕ)^32*1000000000000000^129 ≤ 1000297805737191^129*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25030026784011201573 25000000000000000000 1000297805737191 1000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000297805737191/1000000000000000 : ℝ)) (X := (25030026784011201573/25000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s3_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(744682340629/794050000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(372173172663/397025000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (15881/100000 : ℝ)) (alpha := (744682340629/794050000000000 : ℝ)) (beta := (372173172663/397025000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow1,s3_corner1a]) (by linarith only [s3_pow1,s3_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (15881/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(744682340629/794050000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(372173172663/397025000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow2 : (64437/100000 : ℝ) ^ (129/32 : ℝ) ≤ (2125625455940134271/12500000000000000000 : ℝ) := by
    have hpowers : (64437/100000 : ℝ)^129 ≤ (2125625455940134271/12500000000000000000 : ℝ)^32 := by
      have hnat : (64437 : ℕ)^129*12500000000000000000^32 ≤ 2125625455940134271^32*100000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        64437 100000 2125625455940134271 12500000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (64437/100000 : ℝ)) (X := (2125625455940134271/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s3_corner2a : (14625625455940134271/12500000000000000000 : ℝ) ≤ (10397260602168587/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (14625625455940134271/12500000000000000000 : ℝ)^32 ≤ (10397260602168587/10000000000000000 : ℝ)^129 := by
      have hnat : (14625625455940134271 : ℕ)^32*10000000000000000^129 ≤ 10397260602168587^129*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14625625455940134271 12500000000000000000 10397260602168587 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10397260602168587/10000000000000000 : ℝ)) (X := (14625625455940134271/12500000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s3_corner2b : (8375625455940134271/6250000000000000000 : ℝ) ≤ (10753204812251647/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (8375625455940134271/6250000000000000000 : ℝ)^32 ≤ (10753204812251647/10000000000000000 : ℝ)^129 := by
      have hnat : (8375625455940134271 : ℕ)^32*10000000000000000^129 ≤ 10753204812251647^129*6250000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8375625455940134271 6250000000000000000 10753204812251647 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10753204812251647/10000000000000000 : ℝ)) (X := (8375625455940134271/6250000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s3_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(397260602168587/6443700000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(17797210504153/322185000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (64437/100000 : ℝ)) (alpha := (397260602168587/6443700000000000 : ℝ)) (beta := (17797210504153/322185000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow2,s3_corner2a]) (by linarith only [s3_pow2,s3_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (64437/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(397260602168587/6443700000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(17797210504153/322185000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s3_1 : ((46808873/80000000 : ℝ)*X 1 0+(-132773733/1000000000 : ℝ)*X 1 1+(84169243/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301080_s3_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_2 : ((3438546109/10000000000 : ℝ)*X 2 0+(5799008743/10000000000 : ℝ)*X 2 1+(-1873621107/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301080_s3_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_7 : ((-3712322043/10000000000 : ℝ)*X 0 0+(5405044151/10000000000 : ℝ)*X 0 1+(392549619/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301080_s3_s3_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_8 : ((2890520979/5000000000 : ℝ)*X 1 0+(-836096907/10000000000 : ℝ)*X 1 1+(5745357001/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301080_s3_s3_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_9 : ((200047029/625000000 : ℝ)*X 2 0+(6299682403/10000000000 : ℝ)*X 2 1+(-846137637/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301080_s3_s3_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_12 : ((252562307/625000000 : ℝ)*X 0 0+(2511924051/5000000000 : ℝ)*X 0 1+(1004013207/2500000000 : ℝ)*X 0 2+(252562307/625000000 : ℝ)*X 1 0+(2511924051/5000000000 : ℝ)*X 1 1+(1004013207/2500000000 : ℝ)*X 1 2+(252562307/625000000 : ℝ)*X 2 0+(2511924051/5000000000 : ℝ)*X 2 1+(1004013207/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301080_s3_s3_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_13 : ((-74739677/200000000 : ℝ)*X 0 0+(339481139/625000000 : ℝ)*X 0 1+(483940007/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301080_s3_s3_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_14 : ((1448072051/2500000000 : ℝ)*X 1 0+(-330092389/2500000000 : ℝ)*X 1 1+(2725847461/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301080_s3_s3_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_15 : ((1675183157/5000000000 : ℝ)*X 2 0+(1447481469/2500000000 : ℝ)*X 2 1+(-48033717/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301080_s3_s3_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_19 : ((4360286127/10000000000 : ℝ)*X 0 0+(4921735907/10000000000 : ℝ)*X 0 1+(759924853/2000000000 : ℝ)*X 0 2+(4360286127/10000000000 : ℝ)*X 1 0+(4921735907/10000000000 : ℝ)*X 1 1+(759924853/2000000000 : ℝ)*X 1 2+(4360286127/10000000000 : ℝ)*X 2 0+(4921735907/10000000000 : ℝ)*X 2 1+(759924853/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301080_s3_s3_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_20 : ((-418151581/1250000000 : ℝ)*X 0 0+(2788231939/5000000000 : ℝ)*X 0 1+(4087665451/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301080_s3_s3_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_21 : ((6351142933/10000000000 : ℝ)*X 1 0+(-240587559/2500000000 : ℝ)*X 1 1+(508341991/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301080_s3_s3_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_22 : ((3028924839/10000000000 : ℝ)*X 2 0+(192919653/312500000 : ℝ)*X 2 1+(-231323699/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301080_s3_s3_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_25 : ((4662592627/10000000000 : ℝ)*X 0 0+(4688125873/10000000000 : ℝ)*X 0 1+(1865956761/5000000000 : ℝ)*X 0 2+(4662592627/10000000000 : ℝ)*X 1 0+(4688125873/10000000000 : ℝ)*X 1 1+(1865956761/5000000000 : ℝ)*X 1 2+(4662592627/10000000000 : ℝ)*X 2 0+(4688125873/10000000000 : ℝ)*X 2 1+(1865956761/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301080_s3_s3_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s3_0 : (0 : ℝ) ≤ ((18529/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(18529/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1244861716252158439902504927317/160150205530500000000000000000000000 : ℝ) := by norm_num
    linear_combination (28576182071/500000000000 : ℝ)*(base40) + (1954876302447/500000000000 : ℝ)*(base49) + (8345099331/5000000000 : ℝ)*(base50) + (684259/500000000000 : ℝ)*(base60) + (8030263795379/1000000000000 : ℝ)*(major_s3_0) + (8030263795379/1000000000000 : ℝ)*(major_s3_1) + (8030263795379/1000000000000 : ℝ)*(major_s3_2) + (39294721/500000000000 : ℝ)*(sp_s3_2) + (332246356347/31250000000 : ℝ)*(sp_s3_7) + (10631682127037/1000000000000 : ℝ)*(sp_s3_8) + (10631600343191/1000000000000 : ℝ)*(sp_s3_9) + (678580199577/125000000000 : ℝ)*(sp_s3_12) + (201276067/1000000000000 : ℝ)*(sp_s3_14) + (20447047/100000000000 : ℝ)*(sp_s3_22) + (678580199577/125000000000 : ℝ)*(f.failure) + (332246356347/31250000000 : ℝ)*(f.sum) + (25191477276236692117/102332399700000000000000000000000 : ℝ)*base63 + (60818518799629/322185000000000000000000000 : ℝ)*base64 + (284922242472369/794050000000000000000000000 : ℝ)*base67 + (4367708703790253/6443700000000000000000000000 : ℝ)*base69 + (2061640212750387973/3025317150000000000000000000000 : ℝ)*base70 + (1842145964406337/2817000000000000000000000000 : ℝ)*base73 + (54301379123113/397025000000000000000000000 : ℝ)*base75 + (56349090558193/140850000000000000000000000 : ℝ)*base77 + (19013559844936590857/44736777000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (1169/1562500000000000 : ℝ)*base86 + (1169/1562500000000000 : ℝ)*base88 + (1169/1562500000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s3_1 : (0 : ℝ) ≤ ((147/10000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(147/10000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (5515510478462483349471557/621344125000000000000000000000 : ℝ) := by norm_num
    linear_combination (264038229943/1000000000000 : ℝ)*(base40) + (567716332329/500000000000 : ℝ)*(base49) + (289709/125000000000 : ℝ)*(base60) + (544383809619/125000000000 : ℝ)*(major_s3_0) + (544383809619/125000000000 : ℝ)*(major_s3_1) + (544383809619/125000000000 : ℝ)*(major_s3_2) + (162319439/500000000000 : ℝ)*(sp_s3_2) + (310294093/250000000000 : ℝ)*(sp_s3_7) + (7543043/200000000000 : ℝ)*(sp_s3_8) + (90074527851/15625000000 : ℝ)*(sp_s3_13) + (5765973243621/1000000000000 : ℝ)*(sp_s3_14) + (2882843159979/500000000000 : ℝ)*(sp_s3_15) + (1471997858439/500000000000 : ℝ)*(sp_s3_19) + (13131927/100000000000 : ℝ)*(sp_s3_25) + (736031759037/250000000000 : ℝ)*(f.failure) + (1441502739709/250000000000 : ℝ)*(f.sum) + (2902646688502018071/4263849987500000000000000000000 : ℝ)*base62 + (48116603438387/53697500000000000000000000 : ℝ)*base65 + (230098020145111/397025000000000000000000000 : ℝ)*base67 + (242712682072527/536975000000000000000000000 : ℝ)*base69 + (62768158946279543/1008439050000000000000000000000 : ℝ)*base70 + (219694933221413/234750000000000000000000000 : ℝ)*base73 + (96239722194049/397025000000000000000000000 : ℝ)*base75 + (8938462131589/23475000000000000000000000 : ℝ)*base77 + (140784341483376517/932016187500000000000000000000 : ℝ)*base79 + (2703/6250000000000000 : ℝ)*base86 + (2703/6250000000000000 : ℝ)*base88 + (2703/6250000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s3_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(23011/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(23011/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (42862723747325828164342251343/3203004110610000000000000000000000 : ℝ) := by norm_num
    linear_combination (488401627553/500000000000 : ℝ)*(base40) + (4942422847621/1000000000000 : ℝ)*(base49) + (1947067377271/1000000000000 : ℝ)*(base50) + (1323809344561/125000000000 : ℝ)*(major_s3_0) + (1323809344561/125000000000 : ℝ)*(major_s3_1) + (1323809344561/125000000000 : ℝ)*(major_s3_2) + (283139761/500000000000 : ℝ)*(sp_s3_1) + (662097733/1000000000000 : ℝ)*(sp_s3_2) + (119595001/200000000000 : ℝ)*(sp_s3_9) + (108417371/1000000000000 : ℝ)*(sp_s3_19) + (560861696619/40000000000 : ℝ)*(sp_s3_20) + (14020976135953/1000000000000 : ℝ)*(sp_s3_21) + (14020282342737/1000000000000 : ℝ)*(sp_s3_22) + (894911777431/125000000000 : ℝ)*(sp_s3_25) + (7159402636819/1000000000000 : ℝ)*(f.failure) + (560861696619/40000000000 : ℝ)*(f.sum) + (19013307380772229607/51166199850000000000000000000000 : ℝ)*base63 + (47079022830841/644370000000000000000000000 : ℝ)*base65 + (68066606920083/198512500000000000000000000 : ℝ)*base66 + (10316668569719/100682812500000000000000000 : ℝ)*base69 + (894712837842896971/3025317150000000000000000000000 : ℝ)*base70 + (213609104119741/704250000000000000000000000 : ℝ)*base73 + (405829719430847/794050000000000000000000000 : ℝ)*base75 + (21106458284879/140850000000000000000000000 : ℝ)*base76 + (3046920315163757899/11184194250000000000000000000000 : ℝ)*base78 + (3439/25000000000000000 : ℝ)*base87 + (3439/25000000000000000 : ℝ)*base89 + (3439/25000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]])
    (hprev2 : (0 : ℝ) ≤ ((2817/5000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2817/5000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((15881/100000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(15881/100000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(64437/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(64437/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((18529/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(18529/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((147/10000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(147/10000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(23011/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(23011/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c301080_s3 p hpa hpb X hX hprev2

#print axioms solution
