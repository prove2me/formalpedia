-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c310054_s3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:27:00.776489+00:00
-- url     : https://prove2.me/submissions/d2348103-9e91-42ad-970c-2ae476250372

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
theorem collision_support_c310054_s3_s3_0 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-78510311/500000000 : ℝ)*x 0 + (564889947/1250000000 : ℝ)*x 1 + (-1572611681/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (78510311/500000000 : ℝ)^71 ≤ (4581663511027/50000000000000 : ℝ)^55 := by
    have hnat : (78510311 : ℕ)^71*50000000000000^55 ≤ 4581663511027^55*500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      78510311 500000000 4581663511027 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (564889947/1250000000 : ℝ)^71 ≤ (4483486537591/12500000000000 : ℝ)^55 := by
    have hnat : (564889947 : ℕ)^71*12500000000000^55 ≤ 4483486537591^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      564889947 1250000000 4483486537591 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1572611681/2500000000 : ℝ)^71 ≤ (1099375613137/2000000000000 : ℝ)^55 := by
    have hnat : (1572611681 : ℕ)^71*2000000000000^55 ≤ 1099375613137^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1572611681 2500000000 1099375613137 2000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-78510311/500000000 : ℝ), (564889947/1250000000 : ℝ), (-1572611681/2500000000 : ℝ)] ![(4581663511027/50000000000000 : ℝ), (4483486537591/12500000000000 : ℝ), (1099375613137/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-78510311/500000000 : ℝ)|^71 ≤ (4581663511027/50000000000000 : ℝ)^55
        have hw : |(-78510311/500000000 : ℝ)|=(78510311/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(564889947/1250000000 : ℝ)|^71 ≤ (4483486537591/12500000000000 : ℝ)^55
        have hw : |(564889947/1250000000 : ℝ)|=(564889947/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1572611681/2500000000 : ℝ)|^71 ≤ (1099375613137/2000000000000 : ℝ)^55
        have hw : |(-1572611681/2500000000 : ℝ)|=(1572611681/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310054_s3_s3_2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2554047609/5000000000 : ℝ)*x 0 + (1272141993/2500000000 : ℝ)*x 1 + (2439165977/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2554047609/5000000000 : ℝ)^71 ≤ (21006750380387/50000000000000 : ℝ)^55 := by
    have hnat : (2554047609 : ℕ)^71*50000000000000^55 ≤ 21006750380387^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2554047609 5000000000 21006750380387 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1272141993/2500000000 : ℝ)^71 ≤ (2612892753289/6250000000000 : ℝ)^55 := by
    have hnat : (1272141993 : ℕ)^71*6250000000000^55 ≤ 2612892753289^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1272141993 2500000000 2612892753289 6250000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2439165977/10000000000 : ℝ)^71 ≤ (16180215173983/100000000000000 : ℝ)^55 := by
    have hnat : (2439165977 : ℕ)^71*100000000000000^55 ≤ 16180215173983^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2439165977 10000000000 16180215173983 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2554047609/5000000000 : ℝ), (1272141993/2500000000 : ℝ), (2439165977/10000000000 : ℝ)] ![(21006750380387/50000000000000 : ℝ), (2612892753289/6250000000000 : ℝ), (16180215173983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2554047609/5000000000 : ℝ)|^71 ≤ (21006750380387/50000000000000 : ℝ)^55
        have hw : |(2554047609/5000000000 : ℝ)|=(2554047609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1272141993/2500000000 : ℝ)|^71 ≤ (2612892753289/6250000000000 : ℝ)^55
        have hw : |(1272141993/2500000000 : ℝ)|=(1272141993/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2439165977/10000000000 : ℝ)|^71 ≤ (16180215173983/100000000000000 : ℝ)^55
        have hw : |(2439165977/10000000000 : ℝ)|=(2439165977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310054_s3_s3_7 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-370477491/2500000000 : ℝ)*x 0 + (4183527443/10000000000 : ℝ)*x 1 + (-6647473217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (370477491/2500000000 : ℝ)^71 ≤ (8503668996903/100000000000000 : ℝ)^55 := by
    have hnat : (370477491 : ℕ)^71*100000000000000^55 ≤ 8503668996903^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      370477491 2500000000 8503668996903 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4183527443/10000000000 : ℝ)^71 ≤ (32467281799491/100000000000000 : ℝ)^55 := by
    have hnat : (4183527443 : ℕ)^71*100000000000000^55 ≤ 32467281799491^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4183527443 10000000000 32467281799491 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6647473217/10000000000 : ℝ)^71 ≤ (5902904918409/10000000000000 : ℝ)^55 := by
    have hnat : (6647473217 : ℕ)^71*10000000000000^55 ≤ 5902904918409^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6647473217 10000000000 5902904918409 10000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-370477491/2500000000 : ℝ), (4183527443/10000000000 : ℝ), (-6647473217/10000000000 : ℝ)] ![(8503668996903/100000000000000 : ℝ), (32467281799491/100000000000000 : ℝ), (5902904918409/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-370477491/2500000000 : ℝ)|^71 ≤ (8503668996903/100000000000000 : ℝ)^55
        have hw : |(-370477491/2500000000 : ℝ)|=(370477491/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4183527443/10000000000 : ℝ)|^71 ≤ (32467281799491/100000000000000 : ℝ)^55
        have hw : |(4183527443/10000000000 : ℝ)|=(4183527443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6647473217/10000000000 : ℝ)|^71 ≤ (5902904918409/10000000000000 : ℝ)^55
        have hw : |(-6647473217/10000000000 : ℝ)|=(6647473217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310054_s3_s3_8 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5325485193/10000000000 : ℝ)*x 0 + (-196710833/1000000000 : ℝ)*x 1 + (-5238841681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5325485193/10000000000 : ℝ)^71 ≤ (44335803107249/100000000000000 : ℝ)^55 := by
    have hnat : (5325485193 : ℕ)^71*100000000000000^55 ≤ 44335803107249^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5325485193 10000000000 44335803107249 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (196710833/1000000000 : ℝ)^71 ≤ (6128673820219/50000000000000 : ℝ)^55 := by
    have hnat : (196710833 : ℕ)^71*50000000000000^55 ≤ 6128673820219^55*1000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      196710833 1000000000 6128673820219 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5238841681/10000000000 : ℝ)^71 ≤ (21703424621843/50000000000000 : ℝ)^55 := by
    have hnat : (5238841681 : ℕ)^71*50000000000000^55 ≤ 21703424621843^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238841681 10000000000 21703424621843 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5325485193/10000000000 : ℝ), (-196710833/1000000000 : ℝ), (-5238841681/10000000000 : ℝ)] ![(44335803107249/100000000000000 : ℝ), (6128673820219/50000000000000 : ℝ), (21703424621843/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5325485193/10000000000 : ℝ)|^71 ≤ (44335803107249/100000000000000 : ℝ)^55
        have hw : |(5325485193/10000000000 : ℝ)|=(5325485193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-196710833/1000000000 : ℝ)|^71 ≤ (6128673820219/50000000000000 : ℝ)^55
        have hw : |(-196710833/1000000000 : ℝ)|=(196710833/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5238841681/10000000000 : ℝ)|^71 ≤ (21703424621843/50000000000000 : ℝ)^55
        have hw : |(-5238841681/10000000000 : ℝ)|=(5238841681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310054_s3_s3_9 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4900692003/10000000000 : ℝ)*x 0 + (1438065563/2500000000 : ℝ)*x 1 + (1834409771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4900692003/10000000000 : ℝ)^71 ≤ (39824512976203/100000000000000 : ℝ)^55 := by
    have hnat : (4900692003 : ℕ)^71*100000000000000^55 ≤ 39824512976203^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4900692003 10000000000 39824512976203 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1438065563/2500000000 : ℝ)^71 ≤ (12243725224943/25000000000000 : ℝ)^55 := by
    have hnat : (1438065563 : ℕ)^71*25000000000000^55 ≤ 12243725224943^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1438065563 2500000000 12243725224943 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1834409771/10000000000 : ℝ)^71 ≤ (5600293054163/50000000000000 : ℝ)^55 := by
    have hnat : (1834409771 : ℕ)^71*50000000000000^55 ≤ 5600293054163^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1834409771 10000000000 5600293054163 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4900692003/10000000000 : ℝ), (1438065563/2500000000 : ℝ), (1834409771/10000000000 : ℝ)] ![(39824512976203/100000000000000 : ℝ), (12243725224943/25000000000000 : ℝ), (5600293054163/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4900692003/10000000000 : ℝ)|^71 ≤ (39824512976203/100000000000000 : ℝ)^55
        have hw : |(4900692003/10000000000 : ℝ)|=(4900692003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1438065563/2500000000 : ℝ)|^71 ≤ (12243725224943/25000000000000 : ℝ)^55
        have hw : |(1438065563/2500000000 : ℝ)|=(1438065563/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1834409771/10000000000 : ℝ)|^71 ≤ (5600293054163/50000000000000 : ℝ)^55
        have hw : |(1834409771/10000000000 : ℝ)|=(1834409771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310054_s3_s3_13 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5021312987/10000000000 : ℝ)*x 0 + (5745390111/10000000000 : ℝ)*x 1 + (-840489343/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5021312987/10000000000 : ℝ)^71 ≤ (41094369643747/100000000000000 : ℝ)^55 := by
    have hnat : (5021312987 : ℕ)^71*100000000000000^55 ≤ 41094369643747^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5021312987 10000000000 41094369643747 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5745390111/10000000000 : ℝ)^71 ≤ (48899383485253/100000000000000 : ℝ)^55 := by
    have hnat : (5745390111 : ℕ)^71*100000000000000^55 ≤ 48899383485253^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5745390111 10000000000 48899383485253 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (840489343/5000000000 : ℝ)^71 ≤ (200124936957/2000000000000 : ℝ)^55 := by
    have hnat : (840489343 : ℕ)^71*2000000000000^55 ≤ 200124936957^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      840489343 5000000000 200124936957 2000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5021312987/10000000000 : ℝ), (5745390111/10000000000 : ℝ), (-840489343/5000000000 : ℝ)] ![(41094369643747/100000000000000 : ℝ), (48899383485253/100000000000000 : ℝ), (200124936957/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5021312987/10000000000 : ℝ)|^71 ≤ (41094369643747/100000000000000 : ℝ)^55
        have hw : |(5021312987/10000000000 : ℝ)|=(5021312987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5745390111/10000000000 : ℝ)|^71 ≤ (48899383485253/100000000000000 : ℝ)^55
        have hw : |(5745390111/10000000000 : ℝ)|=(5745390111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-840489343/5000000000 : ℝ)|^71 ≤ (200124936957/2000000000000 : ℝ)^55
        have hw : |(-840489343/5000000000 : ℝ)|=(840489343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310054_s3_s3_14 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1098193501/10000000000 : ℝ)*x 0 + (4497499431/10000000000 : ℝ)*x 1 + (-826009077/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1098193501/10000000000 : ℝ)^71 ≤ (721960844453/12500000000000 : ℝ)^55 := by
    have hnat : (1098193501 : ℕ)^71*12500000000000^55 ≤ 721960844453^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098193501 10000000000 721960844453 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4497499431/10000000000 : ℝ)^71 ≤ (17823265009549/50000000000000 : ℝ)^55 := by
    have hnat : (4497499431 : ℕ)^71*50000000000000^55 ≤ 17823265009549^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4497499431 10000000000 17823265009549 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (826009077/1250000000 : ℝ)^71 ≤ (7322222900997/12500000000000 : ℝ)^55 := by
    have hnat : (826009077 : ℕ)^71*12500000000000^55 ≤ 7322222900997^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      826009077 1250000000 7322222900997 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1098193501/10000000000 : ℝ), (4497499431/10000000000 : ℝ), (-826009077/1250000000 : ℝ)] ![(721960844453/12500000000000 : ℝ), (17823265009549/50000000000000 : ℝ), (7322222900997/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1098193501/10000000000 : ℝ)|^71 ≤ (721960844453/12500000000000 : ℝ)^55
        have hw : |(-1098193501/10000000000 : ℝ)|=(1098193501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4497499431/10000000000 : ℝ)|^71 ≤ (17823265009549/50000000000000 : ℝ)^55
        have hw : |(4497499431/10000000000 : ℝ)|=(4497499431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-826009077/1250000000 : ℝ)|^71 ≤ (7322222900997/12500000000000 : ℝ)^55
        have hw : |(-826009077/1250000000 : ℝ)|=(826009077/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310054_s3_s3_15 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (251395579/500000000 : ℝ)*x 0 + (-145284939/625000000 : ℝ)*x 1 + (-5259722063/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (251395579/500000000 : ℝ)^71 ≤ (8232819137079/20000000000000 : ℝ)^55 := by
    have hnat : (251395579 : ℕ)^71*20000000000000^55 ≤ 8232819137079^55*500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      251395579 500000000 8232819137079 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (145284939/625000000 : ℝ)^71 ≤ (7602795272369/50000000000000 : ℝ)^55 := by
    have hnat : (145284939 : ℕ)^71*50000000000000^55 ≤ 7602795272369^55*625000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      145284939 625000000 7602795272369 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5259722063/10000000000 : ℝ)^71 ≤ (21815156875527/50000000000000 : ℝ)^55 := by
    have hnat : (5259722063 : ℕ)^71*50000000000000^55 ≤ 21815156875527^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5259722063 10000000000 21815156875527 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(251395579/500000000 : ℝ), (-145284939/625000000 : ℝ), (-5259722063/10000000000 : ℝ)] ![(8232819137079/20000000000000 : ℝ), (7602795272369/50000000000000 : ℝ), (21815156875527/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(251395579/500000000 : ℝ)|^71 ≤ (8232819137079/20000000000000 : ℝ)^55
        have hw : |(251395579/500000000 : ℝ)|=(251395579/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-145284939/625000000 : ℝ)|^71 ≤ (7602795272369/50000000000000 : ℝ)^55
        have hw : |(-145284939/625000000 : ℝ)|=(145284939/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5259722063/10000000000 : ℝ)|^71 ≤ (21815156875527/50000000000000 : ℝ)^55
        have hw : |(-5259722063/10000000000 : ℝ)|=(5259722063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310054_s3_s3_16 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5784704437/10000000000 : ℝ)*x 0 + (976465493/2000000000 : ℝ)*x 1 + (906764273/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5784704437/10000000000 : ℝ)^71 ≤ (4933175960667/10000000000000 : ℝ)^55 := by
    have hnat : (5784704437 : ℕ)^71*10000000000000^55 ≤ 4933175960667^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5784704437 10000000000 4933175960667 10000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (976465493/2000000000 : ℝ)^71 ≤ (19815984100883/50000000000000 : ℝ)^55 := by
    have hnat : (976465493 : ℕ)^71*50000000000000^55 ≤ 19815984100883^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      976465493 2000000000 19815984100883 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (906764273/5000000000 : ℝ)^71 ≤ (11036272167/100000000000 : ℝ)^55 := by
    have hnat : (906764273 : ℕ)^71*100000000000^55 ≤ 11036272167^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      906764273 5000000000 11036272167 100000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5784704437/10000000000 : ℝ), (976465493/2000000000 : ℝ), (906764273/5000000000 : ℝ)] ![(4933175960667/10000000000000 : ℝ), (19815984100883/50000000000000 : ℝ), (11036272167/100000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5784704437/10000000000 : ℝ)|^71 ≤ (4933175960667/10000000000000 : ℝ)^55
        have hw : |(5784704437/10000000000 : ℝ)|=(5784704437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(976465493/2000000000 : ℝ)|^71 ≤ (19815984100883/50000000000000 : ℝ)^55
        have hw : |(976465493/2000000000 : ℝ)|=(976465493/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(906764273/5000000000 : ℝ)|^71 ≤ (11036272167/100000000000 : ℝ)^55
        have hw : |(906764273/5000000000 : ℝ)|=(906764273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310054_s3_s3_20 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (89495281/156250000 : ℝ)*x 0 + (124377033/250000000 : ℝ)*x 1 + (-176907649/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (89495281/156250000 : ℝ)^71 ≤ (48705087037957/100000000000000 : ℝ)^55 := by
    have hnat : (89495281 : ℕ)^71*100000000000000^55 ≤ 48705087037957^55*156250000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89495281 156250000 48705087037957 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (124377033/250000000 : ℝ)^71 ≤ (1015164938239/2500000000000 : ℝ)^55 := by
    have hnat : (124377033 : ℕ)^71*2500000000000^55 ≤ 1015164938239^55*250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      124377033 250000000 1015164938239 2500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (176907649/1000000000 : ℝ)^71 ≤ (10688315415641/100000000000000 : ℝ)^55 := by
    have hnat : (176907649 : ℕ)^71*100000000000000^55 ≤ 10688315415641^55*1000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      176907649 1000000000 10688315415641 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(89495281/156250000 : ℝ), (124377033/250000000 : ℝ), (-176907649/1000000000 : ℝ)] ![(48705087037957/100000000000000 : ℝ), (1015164938239/2500000000000 : ℝ), (10688315415641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(89495281/156250000 : ℝ)|^71 ≤ (48705087037957/100000000000000 : ℝ)^55
        have hw : |(89495281/156250000 : ℝ)|=(89495281/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(124377033/250000000 : ℝ)|^71 ≤ (1015164938239/2500000000000 : ℝ)^55
        have hw : |(124377033/250000000 : ℝ)|=(124377033/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-176907649/1000000000 : ℝ)|^71 ≤ (10688315415641/100000000000000 : ℝ)^55
        have hw : |(-176907649/1000000000 : ℝ)|=(176907649/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310054_s3_s3_21 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-225877289/2500000000 : ℝ)*x 0 + (5051662001/10000000000 : ℝ)*x 1 + (-621286203/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (225877289/2500000000 : ℝ)^71 ≤ (4489560698649/100000000000000 : ℝ)^55 := by
    have hnat : (225877289 : ℕ)^71*100000000000000^55 ≤ 4489560698649^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225877289 2500000000 4489560698649 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5051662001/10000000000 : ℝ)^71 ≤ (20707640973327/50000000000000 : ℝ)^55 := by
    have hnat : (5051662001 : ℕ)^71*50000000000000^55 ≤ 20707640973327^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5051662001 10000000000 20707640973327 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (621286203/1000000000 : ℝ)^71 ≤ (54095157343181/100000000000000 : ℝ)^55 := by
    have hnat : (621286203 : ℕ)^71*100000000000000^55 ≤ 54095157343181^55*1000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      621286203 1000000000 54095157343181 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-225877289/2500000000 : ℝ), (5051662001/10000000000 : ℝ), (-621286203/1000000000 : ℝ)] ![(4489560698649/100000000000000 : ℝ), (20707640973327/50000000000000 : ℝ), (54095157343181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-225877289/2500000000 : ℝ)|^71 ≤ (4489560698649/100000000000000 : ℝ)^55
        have hw : |(-225877289/2500000000 : ℝ)|=(225877289/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5051662001/10000000000 : ℝ)|^71 ≤ (20707640973327/50000000000000 : ℝ)^55
        have hw : |(5051662001/10000000000 : ℝ)|=(5051662001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-621286203/1000000000 : ℝ)|^71 ≤ (54095157343181/100000000000000 : ℝ)^55
        have hw : |(-621286203/1000000000 : ℝ)|=(621286203/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310054_s3_s3_22 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3081607813/5000000000 : ℝ)*x 0 + (-102095671/500000000 : ℝ)*x 1 + (-134254299/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3081607813/5000000000 : ℝ)^71 ≤ (5353778669117/10000000000000 : ℝ)^55 := by
    have hnat : (3081607813 : ℕ)^71*10000000000000^55 ≤ 5353778669117^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3081607813 5000000000 5353778669117 10000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (102095671/500000000 : ℝ)^71 ≤ (3215591834137/25000000000000 : ℝ)^55 := by
    have hnat : (102095671 : ℕ)^71*25000000000000^55 ≤ 3215591834137^55*500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      102095671 500000000 3215591834137 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (134254299/312500000 : ℝ)^71 ≤ (8399961490719/25000000000000 : ℝ)^55 := by
    have hnat : (134254299 : ℕ)^71*25000000000000^55 ≤ 8399961490719^55*312500000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134254299 312500000 8399961490719 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3081607813/5000000000 : ℝ), (-102095671/500000000 : ℝ), (-134254299/312500000 : ℝ)] ![(5353778669117/10000000000000 : ℝ), (3215591834137/25000000000000 : ℝ), (8399961490719/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3081607813/5000000000 : ℝ)|^71 ≤ (5353778669117/10000000000000 : ℝ)^55
        have hw : |(3081607813/5000000000 : ℝ)|=(3081607813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-102095671/500000000 : ℝ)|^71 ≤ (3215591834137/25000000000000 : ℝ)^55
        have hw : |(-102095671/500000000 : ℝ)|=(102095671/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-134254299/312500000 : ℝ)|^71 ≤ (8399961490719/25000000000000 : ℝ)^55
        have hw : |(-134254299/312500000 : ℝ)|=(134254299/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310054_s3_s3_23 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4975045673/10000000000 : ℝ)*x 0 + (642375199/1250000000 : ℝ)*x 1 + (79385869/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4975045673/10000000000 : ℝ)^71 ≤ (812124438781/2000000000000 : ℝ)^55 := by
    have hnat : (4975045673 : ℕ)^71*2000000000000^55 ≤ 812124438781^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4975045673 10000000000 812124438781 2000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (642375199/1250000000 : ℝ)^71 ≤ (10585485011299/25000000000000 : ℝ)^55 := by
    have hnat : (642375199 : ℕ)^71*25000000000000^55 ≤ 10585485011299^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      642375199 1250000000 10585485011299 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (79385869/312500000 : ℝ)^71 ≤ (17051837996481/100000000000000 : ℝ)^55 := by
    have hnat : (79385869 : ℕ)^71*100000000000000^55 ≤ 17051837996481^55*312500000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79385869 312500000 17051837996481 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4975045673/10000000000 : ℝ), (642375199/1250000000 : ℝ), (79385869/312500000 : ℝ)] ![(812124438781/2000000000000 : ℝ), (10585485011299/25000000000000 : ℝ), (17051837996481/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4975045673/10000000000 : ℝ)|^71 ≤ (812124438781/2000000000000 : ℝ)^55
        have hw : |(4975045673/10000000000 : ℝ)|=(4975045673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(642375199/1250000000 : ℝ)|^71 ≤ (10585485011299/25000000000000 : ℝ)^55
        have hw : |(642375199/1250000000 : ℝ)|=(642375199/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(79385869/312500000 : ℝ)|^71 ≤ (17051837996481/100000000000000 : ℝ)^55
        have hw : |(79385869/312500000 : ℝ)|=(79385869/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310054_s3_s3_27 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2717444169/5000000000 : ℝ)*x 0 + (5008271543/10000000000 : ℝ)*x 1 + (-424667689/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2717444169/5000000000 : ℝ)^71 ≤ (2844691589671/6250000000000 : ℝ)^55 := by
    have hnat : (2717444169 : ℕ)^71*6250000000000^55 ≤ 2844691589671^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717444169 5000000000 2844691589671 6250000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5008271543/10000000000 : ℝ)^71 ≤ (40956641665547/100000000000000 : ℝ)^55 := by
    have hnat : (5008271543 : ℕ)^71*100000000000000^55 ≤ 40956641665547^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5008271543 10000000000 40956641665547 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (424667689/2000000000 : ℝ)^71 ≤ (845518305391/6250000000000 : ℝ)^55 := by
    have hnat : (424667689 : ℕ)^71*6250000000000^55 ≤ 845518305391^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424667689 2000000000 845518305391 6250000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2717444169/5000000000 : ℝ), (5008271543/10000000000 : ℝ), (-424667689/2000000000 : ℝ)] ![(2844691589671/6250000000000 : ℝ), (40956641665547/100000000000000 : ℝ), (845518305391/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2717444169/5000000000 : ℝ)|^71 ≤ (2844691589671/6250000000000 : ℝ)^55
        have hw : |(2717444169/5000000000 : ℝ)|=(2717444169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5008271543/10000000000 : ℝ)|^71 ≤ (40956641665547/100000000000000 : ℝ)^55
        have hw : |(5008271543/10000000000 : ℝ)|=(5008271543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-424667689/2000000000 : ℝ)|^71 ≤ (845518305391/6250000000000 : ℝ)^55
        have hw : |(-424667689/2000000000 : ℝ)|=(424667689/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c310054_s3 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev2 : (0 : ℝ) ≤ ((48617/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(48617/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(51227/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(51227/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-36703/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-36703/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((27503/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(27503/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(28867/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(28867/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-4547/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-4547/25000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (2431/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (2431/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2431/3125 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2431/3125 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  have s3_pow0 : (48617/100000 : ℝ) ^ (35/8 : ℝ) ≤ (426283167631994363/10000000000000000000 : ℝ) := by
    have hpowers : (48617/100000 : ℝ)^35 ≤ (426283167631994363/10000000000000000000 : ℝ)^8 := by
      have hnat : (48617 : ℕ)^35*10000000000000000000^8 ≤ 426283167631994363^8*100000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        48617 100000 426283167631994363 10000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (48617/100000 : ℝ)) (X := (426283167631994363/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s3_corner0a : (10426283167631994363/10000000000000000000 : ℝ) ≤ (10095873245156929/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (10426283167631994363/10000000000000000000 : ℝ)^8 ≤ (10095873245156929/10000000000000000 : ℝ)^35 := by
      have hnat : (10426283167631994363 : ℕ)^8*10000000000000000^35 ≤ 10095873245156929^35*10000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10426283167631994363 10000000000000000000 10095873245156929 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10095873245156929/10000000000000000 : ℝ)) (X := (10426283167631994363/10000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s3_corner0b : (5426283167631994363/5000000000000000000 : ℝ) ≤ (10188768686423541/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (5426283167631994363/5000000000000000000 : ℝ)^8 ≤ (10188768686423541/10000000000000000 : ℝ)^35 := by
      have hnat : (5426283167631994363 : ℕ)^8*10000000000000000^35 ≤ 10188768686423541^35*5000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5426283167631994363 5000000000000000000 10188768686423541 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10188768686423541/10000000000000000 : ℝ)) (X := (5426283167631994363/5000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s3_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(95873245156929/4861700000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(23223860316653/1215425000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (48617/100000 : ℝ)) (alpha := (95873245156929/4861700000000000 : ℝ)) (beta := (23223860316653/1215425000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow0,s3_corner0a]) (by linarith only [s3_pow0,s3_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (48617/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(95873245156929/4861700000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(23223860316653/1215425000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow1 : (51227/100000 : ℝ) ^ (35/8 : ℝ) ≤ (2679339784814776471/50000000000000000000 : ℝ) := by
    have hpowers : (51227/100000 : ℝ)^35 ≤ (2679339784814776471/50000000000000000000 : ℝ)^8 := by
      have hnat : (51227 : ℕ)^35*50000000000000000000^8 ≤ 2679339784814776471^8*100000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51227 100000 2679339784814776471 50000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (51227/100000 : ℝ)) (X := (2679339784814776471/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s3_corner1a : (52679339784814776471/50000000000000000000 : ℝ) ≤ (10120029703745431/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (52679339784814776471/50000000000000000000 : ℝ)^8 ≤ (10120029703745431/10000000000000000 : ℝ)^35 := by
      have hnat : (52679339784814776471 : ℕ)^8*10000000000000000^35 ≤ 10120029703745431^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52679339784814776471 50000000000000000000 10120029703745431 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10120029703745431/10000000000000000 : ℝ)) (X := (52679339784814776471/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s3_corner1b : (27679339784814776471/25000000000000000000 : ℝ) ≤ (10235438423265119/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (27679339784814776471/25000000000000000000 : ℝ)^8 ≤ (10235438423265119/10000000000000000 : ℝ)^35 := by
      have hnat : (27679339784814776471 : ℕ)^8*10000000000000000^35 ≤ 10235438423265119^35*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27679339784814776471 25000000000000000000 10235438423265119 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10235438423265119/10000000000000000 : ℝ)) (X := (27679339784814776471/25000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s3_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(120029703745431/5122700000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(14426089939961/640337500000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (51227/100000 : ℝ)) (alpha := (120029703745431/5122700000000000 : ℝ)) (beta := (14426089939961/640337500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow1,s3_corner1a]) (by linarith only [s3_pow1,s3_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (51227/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(120029703745431/5122700000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(14426089939961/640337500000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow2 : (36703/100000 : ℝ) ^ (35/8 : ℝ) ≤ (623073593185022567/50000000000000000000 : ℝ) := by
    have hpowers : (36703/100000 : ℝ)^35 ≤ (623073593185022567/50000000000000000000 : ℝ)^8 := by
      have hnat : (36703 : ℕ)^35*50000000000000000000^8 ≤ 623073593185022567^8*100000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        36703 100000 623073593185022567 50000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (36703/100000 : ℝ)) (X := (623073593185022567/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s3_corner2a : (50623073593185022567/50000000000000000000 : ℝ) ≤ (626771715988429/625000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (50623073593185022567/50000000000000000000 : ℝ)^8 ≤ (626771715988429/625000000000000 : ℝ)^35 := by
      have hnat : (50623073593185022567 : ℕ)^8*625000000000000^35 ≤ 626771715988429^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50623073593185022567 50000000000000000000 626771715988429 625000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (626771715988429/625000000000000 : ℝ)) (X := (50623073593185022567/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s3_corner2b : (25623073593185022567/25000000000000000000 : ℝ) ≤ (2011285404434271/2000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (25623073593185022567/25000000000000000000 : ℝ)^8 ≤ (2011285404434271/2000000000000000 : ℝ)^35 := by
      have hnat : (25623073593185022567 : ℕ)^8*2000000000000000^35 ≤ 2011285404434271^35*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25623073593185022567 25000000000000000000 2011285404434271 2000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2011285404434271/2000000000000000 : ℝ)) (X := (25623073593185022567/25000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s3_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1771715988429/229393750000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(28079566356491/3670300000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (36703/100000 : ℝ)) (alpha := (1771715988429/229393750000000 : ℝ)) (beta := (28079566356491/3670300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow2,s3_corner2a]) (by linarith only [s3_pow2,s3_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (36703/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1771715988429/229393750000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(28079566356491/3670300000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s3_0 : ((-78510311/500000000 : ℝ)*X 0 0+(564889947/1250000000 : ℝ)*X 0 1+(-1572611681/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310054_s3_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_2 : ((2554047609/5000000000 : ℝ)*X 2 0+(1272141993/2500000000 : ℝ)*X 2 1+(2439165977/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310054_s3_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_7 : ((-370477491/2500000000 : ℝ)*X 0 0+(4183527443/10000000000 : ℝ)*X 0 1+(-6647473217/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310054_s3_s3_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_8 : ((5325485193/10000000000 : ℝ)*X 1 0+(-196710833/1000000000 : ℝ)*X 1 1+(-5238841681/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310054_s3_s3_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_9 : ((4900692003/10000000000 : ℝ)*X 2 0+(1438065563/2500000000 : ℝ)*X 2 1+(1834409771/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310054_s3_s3_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_13 : ((5021312987/10000000000 : ℝ)*X 0 0+(5745390111/10000000000 : ℝ)*X 0 1+(-840489343/5000000000 : ℝ)*X 0 2+(5021312987/10000000000 : ℝ)*X 1 0+(5745390111/10000000000 : ℝ)*X 1 1+(-840489343/5000000000 : ℝ)*X 1 2+(5021312987/10000000000 : ℝ)*X 2 0+(5745390111/10000000000 : ℝ)*X 2 1+(-840489343/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310054_s3_s3_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_14 : ((-1098193501/10000000000 : ℝ)*X 0 0+(4497499431/10000000000 : ℝ)*X 0 1+(-826009077/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310054_s3_s3_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_15 : ((251395579/500000000 : ℝ)*X 1 0+(-145284939/625000000 : ℝ)*X 1 1+(-5259722063/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310054_s3_s3_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_16 : ((5784704437/10000000000 : ℝ)*X 2 0+(976465493/2000000000 : ℝ)*X 2 1+(906764273/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310054_s3_s3_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_20 : ((89495281/156250000 : ℝ)*X 0 0+(124377033/250000000 : ℝ)*X 0 1+(-176907649/1000000000 : ℝ)*X 0 2+(89495281/156250000 : ℝ)*X 1 0+(124377033/250000000 : ℝ)*X 1 1+(-176907649/1000000000 : ℝ)*X 1 2+(89495281/156250000 : ℝ)*X 2 0+(124377033/250000000 : ℝ)*X 2 1+(-176907649/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310054_s3_s3_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_21 : ((-225877289/2500000000 : ℝ)*X 0 0+(5051662001/10000000000 : ℝ)*X 0 1+(-621286203/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310054_s3_s3_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_22 : ((3081607813/5000000000 : ℝ)*X 1 0+(-102095671/500000000 : ℝ)*X 1 1+(-134254299/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310054_s3_s3_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_23 : ((4975045673/10000000000 : ℝ)*X 2 0+(642375199/1250000000 : ℝ)*X 2 1+(79385869/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310054_s3_s3_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_27 : ((2717444169/5000000000 : ℝ)*X 0 0+(5008271543/10000000000 : ℝ)*X 0 1+(-424667689/2000000000 : ℝ)*X 0 2+(2717444169/5000000000 : ℝ)*X 1 0+(5008271543/10000000000 : ℝ)*X 1 1+(-424667689/2000000000 : ℝ)*X 1 2+(2717444169/5000000000 : ℝ)*X 2 0+(5008271543/10000000000 : ℝ)*X 2 1+(-424667689/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310054_s3_s3_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s3_0 : (0 : ℝ) ≤ ((27503/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(27503/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3901613727831824376338021917227/268849805219050000000000000000000000 : ℝ) := by norm_num
    linear_combination (1174358973081/1000000000000 : ℝ)*(base39) + (326801/62500000000 : ℝ)*(base50) + (285520858437/500000000000 : ℝ)*(base60) + (7674220504559/1000000000000 : ℝ)*(major_s3_0) + (7674220504559/1000000000000 : ℝ)*(major_s3_1) + (7674220504559/1000000000000 : ℝ)*(major_s3_2) + (465717/100000000000 : ℝ)*(sp_s3_0) + (5302571301469/500000000000 : ℝ)*(sp_s3_7) + (10604962885337/1000000000000 : ℝ)*(sp_s3_8) + (10605097389393/1000000000000 : ℝ)*(sp_s3_9) + (4743233949899/1000000000000 : ℝ)*(sp_s3_13) + (54961689/1000000000000 : ℝ)*(sp_s3_14) + (239336459/1000000000000 : ℝ)*(sp_s3_15) + (104832403/1000000000000 : ℝ)*(sp_s3_23) + (4743233949899/1000000000000 : ℝ)*(f.failure) + (10605202221797/1000000000000 : ℝ)*(f.sum) + (131722944066553388881/188018458100000000000000000000000 : ℝ)*base62 + (2707062520447591/3670300000000000000000000000 : ℝ)*base64 + (73795723703959/160084375000000000000000000 : ℝ)*base67 + (518094578537561/917575000000000000000000000 : ℝ)*base68 + (7723288000960750281/44609743775000000000000000000000 : ℝ)*base70 + (143148472714033/1215425000000000000000000000 : ℝ)*base72 + (4128320247384041/5122700000000000000000000000 : ℝ)*base74 + (1960596467604859/4861700000000000000000000000 : ℝ)*base76 + (72725861955863199209/124525152950000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (108907/100000000000000000 : ℝ)*base87 + (108907/100000000000000000 : ℝ)*base89 + (108907/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s3_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(28867/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(28867/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1083417358825588352183112124959/67212451304762500000000000000000000 : ℝ) := by norm_num
    linear_combination (278294399181/250000000000 : ℝ)*(base39) + (7457231/1000000000000 : ℝ)*(base40) + (158136476723/500000000000 : ℝ)*(base60) + (7693181792009/1000000000000 : ℝ)*(major_s3_0) + (7693181792009/1000000000000 : ℝ)*(major_s3_1) + (7693181792009/1000000000000 : ℝ)*(major_s3_2) + (13726169/200000000000 : ℝ)*(sp_s3_2) + (208647791/1000000000000 : ℝ)*(sp_s3_7) + (33436423/200000000000 : ℝ)*(sp_s3_8) + (2657799034979/250000000000 : ℝ)*(sp_s3_14) + (1328904700699/125000000000 : ℝ)*(sp_s3_15) + (5315668078431/500000000000 : ℝ)*(sp_s3_16) + (2377439135357/500000000000 : ℝ)*(sp_s3_20) + (75152493/1000000000000 : ℝ)*(sp_s3_27) + (4754953423207/1000000000000 : ℝ)*(f.failure) + (10631404787707/1000000000000 : ℝ)*(f.sum) + (51909311954518822611/188018458100000000000000000000000 : ℝ)*base62 + (431090370877221/3670300000000000000000000000 : ℝ)*base64 + (18199540482131/40021093750000000000000000 : ℝ)*base67 + (1338145536253087/1835150000000000000000000000 : ℝ)*base68 + (3536472569276679351/44609743775000000000000000000000 : ℝ)*base70 + (1641487664081257/1215425000000000000000000000 : ℝ)*base73 + (2287556780347901/5122700000000000000000000000 : ℝ)*base74 + (4242026473092969/4861700000000000000000000000 : ℝ)*base76 + (55854720424671036343/62262576475000000000000000000000 : ℝ)*base79 + (30151/100000000000000000 : ℝ)*base87 + (30151/100000000000000000 : ℝ)*base89 + (30151/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s3_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-4547/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-4547/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (15325111178953602515900094978873/1142611672180962500000000000000000000 : ℝ) := by norm_num
    linear_combination (1240892487067/1000000000000 : ℝ)*(base39) + (3490497/1000000000000 : ℝ)*(base40) + (241817/125000000000 : ℝ)*(base50) + (5558520040923/1000000000000 : ℝ)*(major_s3_0) + (5558520040923/1000000000000 : ℝ)*(major_s3_1) + (5558520040923/1000000000000 : ℝ)*(major_s3_2) + (54092037/1000000000000 : ℝ)*(sp_s3_2) + (56282361/1000000000000 : ℝ)*(sp_s3_9) + (34943263/1000000000000 : ℝ)*(sp_s3_13) + (208526369/1000000000000 : ℝ)*(sp_s3_20) + (192036512477/25000000000 : ℝ)*(sp_s3_21) + (192036512477/25000000000 : ℝ)*(sp_s3_22) + (3840675062341/500000000000 : ℝ)*(sp_s3_23) + (1717665821173/500000000000 : ℝ)*(sp_s3_27) + (1717787555989/500000000000 : ℝ)*(f.failure) + (192036512477/25000000000 : ℝ)*(f.sum) + (4895193593887884767/188018458100000000000000000000000 : ℝ)*base62 + (224214042642737/3670300000000000000000000000 : ℝ)*base64 + (27130659753859/1280675000000000000000000000 : ℝ)*base67 + (210890834753339/1835150000000000000000000000 : ℝ)*base68 + (5567753416882784343/44609743775000000000000000000000 : ℝ)*base71 + (347341320294917/607712500000000000000000000 : ℝ)*base73 + (1705233863972387/5122700000000000000000000000 : ℝ)*base74 + (983012145761803/4861700000000000000000000000 : ℝ)*base76 + (26307751800121083/1945705514843750000000000000000 : ℝ)*base79 + (21723/50000000000000000 : ℝ)*base86 + (21723/50000000000000000 : ℝ)*base88 + (21723/50000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev2 : (0 : ℝ) ≤ ((48617/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(48617/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(51227/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(51227/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-36703/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-36703/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((27503/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(27503/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(28867/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(28867/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-4547/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-4547/25000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c310054_s3 p hpa hpb X hX hprev2

#print axioms solution
