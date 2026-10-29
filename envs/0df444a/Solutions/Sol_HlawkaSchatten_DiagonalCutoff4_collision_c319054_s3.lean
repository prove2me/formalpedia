-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c319054_s3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:29:43.611029+00:00
-- url     : https://prove2.me/submissions/e8ef6d83-7d28-4f79-aebd-22e66cd046d2

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
theorem collision_support_c319054_s3_s3_0 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-285369423/2000000000 : ℝ)*x 0 + (181472629/400000000 : ℝ)*x 1 + (-6082378671/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (285369423/2000000000 : ℝ)^81 ≤ (2208839728359/25000000000000 : ℝ)^65 := by
    have hnat : (285369423 : ℕ)^81*25000000000000^65 ≤ 2208839728359^65*2000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      285369423 2000000000 2208839728359 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (181472629/400000000 : ℝ)^81 ≤ (18673645793491/50000000000000 : ℝ)^65 := by
    have hnat : (181472629 : ℕ)^81*50000000000000^65 ≤ 18673645793491^65*400000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      181472629 400000000 18673645793491 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6082378671/10000000000 : ℝ)^81 ≤ (26908674744369/50000000000000 : ℝ)^65 := by
    have hnat : (6082378671 : ℕ)^81*50000000000000^65 ≤ 26908674744369^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6082378671 10000000000 26908674744369 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-285369423/2000000000 : ℝ), (181472629/400000000 : ℝ), (-6082378671/10000000000 : ℝ)] ![(2208839728359/25000000000000 : ℝ), (18673645793491/50000000000000 : ℝ), (26908674744369/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-285369423/2000000000 : ℝ)|^81 ≤ (2208839728359/25000000000000 : ℝ)^65
        have hw : |(-285369423/2000000000 : ℝ)|=(285369423/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(181472629/400000000 : ℝ)|^81 ≤ (18673645793491/50000000000000 : ℝ)^65
        have hw : |(181472629/400000000 : ℝ)|=(181472629/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6082378671/10000000000 : ℝ)|^81 ≤ (26908674744369/50000000000000 : ℝ)^65
        have hw : |(-6082378671/10000000000 : ℝ)|=(6082378671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319054_s3_s3_1 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2707792313/5000000000 : ℝ)*x 0 + (-2307052301/10000000000 : ℝ)*x 1 + (-283587153/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2707792313/5000000000 : ℝ)^81 ≤ (2328365355507/5000000000000 : ℝ)^65 := by
    have hnat : (2707792313 : ℕ)^81*5000000000000^65 ≤ 2328365355507^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707792313 5000000000 2328365355507 5000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2307052301/10000000000 : ℝ)^81 ≤ (803973221341/5000000000000 : ℝ)^65 := by
    have hnat : (2307052301 : ℕ)^81*5000000000000^65 ≤ 803973221341^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2307052301 10000000000 803973221341 5000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (283587153/625000000 : ℝ)^81 ≤ (583644194567/1562500000000 : ℝ)^65 := by
    have hnat : (283587153 : ℕ)^81*1562500000000^65 ≤ 583644194567^65*625000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283587153 625000000 583644194567 1562500000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2707792313/5000000000 : ℝ), (-2307052301/10000000000 : ℝ), (-283587153/625000000 : ℝ)] ![(2328365355507/5000000000000 : ℝ), (803973221341/5000000000000 : ℝ), (583644194567/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2707792313/5000000000 : ℝ)|^81 ≤ (2328365355507/5000000000000 : ℝ)^65
        have hw : |(2707792313/5000000000 : ℝ)|=(2707792313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2307052301/10000000000 : ℝ)|^81 ≤ (803973221341/5000000000000 : ℝ)^65
        have hw : |(-2307052301/10000000000 : ℝ)|=(2307052301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-283587153/625000000 : ℝ)|^81 ≤ (583644194567/1562500000000 : ℝ)^65
        have hw : |(-283587153/625000000 : ℝ)|=(283587153/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319054_s3_s3_2 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (77853711/156250000 : ℝ)*x 0 + (2490772367/5000000000 : ℝ)*x 1 + (2305046549/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (77853711/156250000 : ℝ)^81 ≤ (41974712855419/100000000000000 : ℝ)^65 := by
    have hnat : (77853711 : ℕ)^81*100000000000000^65 ≤ 41974712855419^65*156250000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      77853711 156250000 41974712855419 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2490772367/5000000000 : ℝ)^81 ≤ (41963241436399/100000000000000 : ℝ)^65 := by
    have hnat : (2490772367 : ℕ)^81*100000000000000^65 ≤ 41963241436399^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2490772367 5000000000 41963241436399 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2305046549/10000000000 : ℝ)^81 ≤ (16062045694239/100000000000000 : ℝ)^65 := by
    have hnat : (2305046549 : ℕ)^81*100000000000000^65 ≤ 16062045694239^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2305046549 10000000000 16062045694239 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(77853711/156250000 : ℝ), (2490772367/5000000000 : ℝ), (2305046549/10000000000 : ℝ)] ![(41974712855419/100000000000000 : ℝ), (41963241436399/100000000000000 : ℝ), (16062045694239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(77853711/156250000 : ℝ)|^81 ≤ (41974712855419/100000000000000 : ℝ)^65
        have hw : |(77853711/156250000 : ℝ)|=(77853711/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2490772367/5000000000 : ℝ)|^81 ≤ (41963241436399/100000000000000 : ℝ)^65
        have hw : |(2490772367/5000000000 : ℝ)|=(2490772367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2305046549/10000000000 : ℝ)|^81 ≤ (16062045694239/100000000000000 : ℝ)^65
        have hw : |(2305046549/10000000000 : ℝ)|=(2305046549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319054_s3_s3_6 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (126693759/250000000 : ℝ)*x 0 + (2533409143/5000000000 : ℝ)*x 1 + (-2096249299/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (126693759/250000000 : ℝ)^81 ≤ (4287008479871/10000000000000 : ℝ)^65 := by
    have hnat : (126693759 : ℕ)^81*10000000000000^65 ≤ 4287008479871^65*250000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126693759 250000000 4287008479871 10000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2533409143/5000000000 : ℝ)^81 ≤ (42860259373511/100000000000000 : ℝ)^65 := by
    have hnat : (2533409143 : ℕ)^81*100000000000000^65 ≤ 42860259373511^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2533409143 5000000000 42860259373511 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2096249299/10000000000 : ℝ)^81 ≤ (7134827904731/50000000000000 : ℝ)^65 := by
    have hnat : (2096249299 : ℕ)^81*50000000000000^65 ≤ 7134827904731^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2096249299 10000000000 7134827904731 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(126693759/250000000 : ℝ), (2533409143/5000000000 : ℝ), (-2096249299/10000000000 : ℝ)] ![(4287008479871/10000000000000 : ℝ), (42860259373511/100000000000000 : ℝ), (7134827904731/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(126693759/250000000 : ℝ)|^81 ≤ (4287008479871/10000000000000 : ℝ)^65
        have hw : |(126693759/250000000 : ℝ)|=(126693759/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2533409143/5000000000 : ℝ)|^81 ≤ (42860259373511/100000000000000 : ℝ)^65
        have hw : |(2533409143/5000000000 : ℝ)|=(2533409143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2096249299/10000000000 : ℝ)|^81 ≤ (7134827904731/50000000000000 : ℝ)^65
        have hw : |(-2096249299/10000000000 : ℝ)|=(2096249299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319054_s3_s3_7 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-710320819/5000000000 : ℝ)*x 0 + (4500537329/10000000000 : ℝ)*x 1 + (-6120409267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (710320819/5000000000 : ℝ)^81 ≤ (4393750111827/50000000000000 : ℝ)^65 := by
    have hnat : (710320819 : ℕ)^81*50000000000000^65 ≤ 4393750111827^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      710320819 5000000000 4393750111827 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4500537329/10000000000 : ℝ)^81 ≤ (288871096039/781250000000 : ℝ)^65 := by
    have hnat : (4500537329 : ℕ)^81*781250000000^65 ≤ 288871096039^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4500537329 10000000000 288871096039 781250000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6120409267/10000000000 : ℝ)^81 ≤ (13559249866339/25000000000000 : ℝ)^65 := by
    have hnat : (6120409267 : ℕ)^81*25000000000000^65 ≤ 13559249866339^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6120409267 10000000000 13559249866339 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-710320819/5000000000 : ℝ), (4500537329/10000000000 : ℝ), (-6120409267/10000000000 : ℝ)] ![(4393750111827/50000000000000 : ℝ), (288871096039/781250000000 : ℝ), (13559249866339/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-710320819/5000000000 : ℝ)|^81 ≤ (4393750111827/50000000000000 : ℝ)^65
        have hw : |(-710320819/5000000000 : ℝ)|=(710320819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4500537329/10000000000 : ℝ)|^81 ≤ (288871096039/781250000000 : ℝ)^65
        have hw : |(4500537329/10000000000 : ℝ)|=(4500537329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6120409267/10000000000 : ℝ)|^81 ≤ (13559249866339/25000000000000 : ℝ)^65
        have hw : |(-6120409267/10000000000 : ℝ)|=(6120409267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319054_s3_s3_8 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5402680399/10000000000 : ℝ)*x 0 + (-1115458779/5000000000 : ℝ)*x 1 + (-4614900667/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5402680399/10000000000 : ℝ)^81 ≤ (46429074033317/100000000000000 : ℝ)^65 := by
    have hnat : (5402680399 : ℕ)^81*100000000000000^65 ≤ 46429074033317^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402680399 10000000000 46429074033317 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1115458779/5000000000 : ℝ)^81 ≤ (15420918237641/100000000000000 : ℝ)^65 := by
    have hnat : (1115458779 : ℕ)^81*100000000000000^65 ≤ 15420918237641^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1115458779 5000000000 15420918237641 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4614900667/10000000000 : ℝ)^81 ≤ (2384375482391/6250000000000 : ℝ)^65 := by
    have hnat : (4614900667 : ℕ)^81*6250000000000^65 ≤ 2384375482391^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4614900667 10000000000 2384375482391 6250000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5402680399/10000000000 : ℝ), (-1115458779/5000000000 : ℝ), (-4614900667/10000000000 : ℝ)] ![(46429074033317/100000000000000 : ℝ), (15420918237641/100000000000000 : ℝ), (2384375482391/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5402680399/10000000000 : ℝ)|^81 ≤ (46429074033317/100000000000000 : ℝ)^65
        have hw : |(5402680399/10000000000 : ℝ)|=(5402680399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1115458779/5000000000 : ℝ)|^81 ≤ (15420918237641/100000000000000 : ℝ)^65
        have hw : |(-1115458779/5000000000 : ℝ)|=(1115458779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4614900667/10000000000 : ℝ)|^81 ≤ (2384375482391/6250000000000 : ℝ)^65
        have hw : |(-4614900667/10000000000 : ℝ)|=(4614900667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319054_s3_s3_9 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4964236783/10000000000 : ℝ)*x 0 + (2531710367/5000000000 : ℝ)*x 1 + (1113891323/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4964236783/10000000000 : ℝ)^81 ≤ (20890816421003/50000000000000 : ℝ)^65 := by
    have hnat : (4964236783 : ℕ)^81*50000000000000^65 ≤ 20890816421003^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4964236783 10000000000 20890816421003 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2531710367/5000000000 : ℝ)^81 ≤ (1338263998937/3125000000000 : ℝ)^65 := by
    have hnat : (2531710367 : ℕ)^81*3125000000000^65 ≤ 1338263998937^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2531710367 5000000000 1338263998937 3125000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1113891323/5000000000 : ℝ)^81 ≤ (1924239897659/12500000000000 : ℝ)^65 := by
    have hnat : (1113891323 : ℕ)^81*12500000000000^65 ≤ 1924239897659^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1113891323 5000000000 1924239897659 12500000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4964236783/10000000000 : ℝ), (2531710367/5000000000 : ℝ), (1113891323/5000000000 : ℝ)] ![(20890816421003/50000000000000 : ℝ), (1338263998937/3125000000000 : ℝ), (1924239897659/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4964236783/10000000000 : ℝ)|^81 ≤ (20890816421003/50000000000000 : ℝ)^65
        have hw : |(4964236783/10000000000 : ℝ)|=(4964236783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2531710367/5000000000 : ℝ)|^81 ≤ (1338263998937/3125000000000 : ℝ)^65
        have hw : |(2531710367/5000000000 : ℝ)|=(2531710367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1113891323/5000000000 : ℝ)|^81 ≤ (1924239897659/12500000000000 : ℝ)^65
        have hw : |(1113891323/5000000000 : ℝ)|=(1113891323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319054_s3_s3_13 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (31660363/62500000 : ℝ)*x 0 + (5150461229/10000000000 : ℝ)*x 1 + (-1994079473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (31660363/62500000 : ℝ)^81 ≤ (21424014862227/50000000000000 : ℝ)^65 := by
    have hnat : (31660363 : ℕ)^81*50000000000000^65 ≤ 21424014862227^65*62500000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31660363 62500000 21424014862227 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5150461229/10000000000 : ℝ)^81 ≤ (2187187128089/5000000000000 : ℝ)^65 := by
    have hnat : (5150461229 : ℕ)^81*5000000000000^65 ≤ 2187187128089^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5150461229 10000000000 2187187128089 5000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1994079473/10000000000 : ℝ)^81 ≤ (3352056927011/25000000000000 : ℝ)^65 := by
    have hnat : (1994079473 : ℕ)^81*25000000000000^65 ≤ 3352056927011^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1994079473 10000000000 3352056927011 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(31660363/62500000 : ℝ), (5150461229/10000000000 : ℝ), (-1994079473/10000000000 : ℝ)] ![(21424014862227/50000000000000 : ℝ), (2187187128089/5000000000000 : ℝ), (3352056927011/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(31660363/62500000 : ℝ)|^81 ≤ (21424014862227/50000000000000 : ℝ)^65
        have hw : |(31660363/62500000 : ℝ)|=(31660363/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5150461229/10000000000 : ℝ)|^81 ≤ (2187187128089/5000000000000 : ℝ)^65
        have hw : |(5150461229/10000000000 : ℝ)|=(5150461229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1994079473/10000000000 : ℝ)|^81 ≤ (3352056927011/25000000000000 : ℝ)^65
        have hw : |(-1994079473/10000000000 : ℝ)|=(1994079473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319054_s3_s3_14 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1368813679/10000000000 : ℝ)*x 0 + (908829453/2000000000 : ℝ)*x 1 + (-6115942069/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1368813679/10000000000 : ℝ)^81 ≤ (4194905459977/50000000000000 : ℝ)^65 := by
    have hnat : (1368813679 : ℕ)^81*50000000000000^65 ≤ 4194905459977^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1368813679 10000000000 4194905459977 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (908829453/2000000000 : ℝ)^81 ≤ (3742251641061/10000000000000 : ℝ)^65 := by
    have hnat : (908829453 : ℕ)^81*10000000000000^65 ≤ 3742251641061^65*2000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      908829453 2000000000 3742251641061 10000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6115942069/10000000000 : ℝ)^81 ≤ (54187672655033/100000000000000 : ℝ)^65 := by
    have hnat : (6115942069 : ℕ)^81*100000000000000^65 ≤ 54187672655033^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6115942069 10000000000 54187672655033 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1368813679/10000000000 : ℝ), (908829453/2000000000 : ℝ), (-6115942069/10000000000 : ℝ)] ![(4194905459977/50000000000000 : ℝ), (3742251641061/10000000000000 : ℝ), (54187672655033/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1368813679/10000000000 : ℝ)|^81 ≤ (4194905459977/50000000000000 : ℝ)^65
        have hw : |(-1368813679/10000000000 : ℝ)|=(1368813679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(908829453/2000000000 : ℝ)|^81 ≤ (3742251641061/10000000000000 : ℝ)^65
        have hw : |(908829453/2000000000 : ℝ)|=(908829453/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6115942069/10000000000 : ℝ)|^81 ≤ (54187672655033/100000000000000 : ℝ)^65
        have hw : |(-6115942069/10000000000 : ℝ)|=(6115942069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319054_s3_s3_15 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2680597797/5000000000 : ℝ)*x 0 + (-2279188321/10000000000 : ℝ)*x 1 + (-4617516027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2680597797/5000000000 : ℝ)^81 ≤ (22992615177051/50000000000000 : ℝ)^65 := by
    have hnat : (2680597797 : ℕ)^81*50000000000000^65 ≤ 22992615177051^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2680597797 5000000000 22992615177051 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2279188321/10000000000 : ℝ)^81 ≤ (7918908848237/50000000000000 : ℝ)^65 := by
    have hnat : (2279188321 : ℕ)^81*50000000000000^65 ≤ 7918908848237^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2279188321 10000000000 7918908848237 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4617516027/10000000000 : ℝ)^81 ≤ (38176951943407/100000000000000 : ℝ)^65 := by
    have hnat : (4617516027 : ℕ)^81*100000000000000^65 ≤ 38176951943407^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4617516027 10000000000 38176951943407 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2680597797/5000000000 : ℝ), (-2279188321/10000000000 : ℝ), (-4617516027/10000000000 : ℝ)] ![(22992615177051/50000000000000 : ℝ), (7918908848237/50000000000000 : ℝ), (38176951943407/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2680597797/5000000000 : ℝ)|^81 ≤ (22992615177051/50000000000000 : ℝ)^65
        have hw : |(2680597797/5000000000 : ℝ)|=(2680597797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2279188321/10000000000 : ℝ)|^81 ≤ (7918908848237/50000000000000 : ℝ)^65
        have hw : |(-2279188321/10000000000 : ℝ)|=(2279188321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4617516027/10000000000 : ℝ)|^81 ≤ (38176951943407/100000000000000 : ℝ)^65
        have hw : |(-4617516027/10000000000 : ℝ)|=(4617516027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319054_s3_s3_16 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5066155553/10000000000 : ℝ)*x 0 + (2481817501/5000000000 : ℝ)*x 1 + (1112583839/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5066155553/10000000000 : ℝ)^81 ≤ (21426636733797/50000000000000 : ℝ)^65 := by
    have hnat : (5066155553 : ℕ)^81*50000000000000^65 ≤ 21426636733797^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5066155553 10000000000 21426636733797 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2481817501/5000000000 : ℝ)^81 ≤ (20887660642027/50000000000000 : ℝ)^65 := by
    have hnat : (2481817501 : ℕ)^81*50000000000000^65 ≤ 20887660642027^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2481817501 5000000000 20887660642027 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1112583839/5000000000 : ℝ)^81 ≤ (15371405233099/100000000000000 : ℝ)^65 := by
    have hnat : (1112583839 : ℕ)^81*100000000000000^65 ≤ 15371405233099^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1112583839 5000000000 15371405233099 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5066155553/10000000000 : ℝ), (2481817501/5000000000 : ℝ), (1112583839/5000000000 : ℝ)] ![(21426636733797/50000000000000 : ℝ), (20887660642027/50000000000000 : ℝ), (15371405233099/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5066155553/10000000000 : ℝ)|^81 ≤ (21426636733797/50000000000000 : ℝ)^65
        have hw : |(5066155553/10000000000 : ℝ)|=(5066155553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2481817501/5000000000 : ℝ)|^81 ≤ (20887660642027/50000000000000 : ℝ)^65
        have hw : |(2481817501/5000000000 : ℝ)|=(2481817501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1112583839/5000000000 : ℝ)|^81 ≤ (15371405233099/100000000000000 : ℝ)^65
        have hw : |(1112583839/5000000000 : ℝ)|=(1112583839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319054_s3_s3_20 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5146978239/10000000000 : ℝ)*x 0 + (5059553079/10000000000 : ℝ)*x 1 + (-100307411/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5146978239/10000000000 : ℝ)^81 ≤ (4370688237341/10000000000000 : ℝ)^65 := by
    have hnat : (5146978239 : ℕ)^81*10000000000000^65 ≤ 4370688237341^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5146978239 10000000000 4370688237341 10000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5059553079/10000000000 : ℝ)^81 ≤ (8556737740851/20000000000000 : ℝ)^65 := by
    have hnat : (5059553079 : ℕ)^81*20000000000000^65 ≤ 8556737740851^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5059553079 10000000000 8556737740851 20000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (100307411/500000000 : ℝ)^81 ≤ (13509428905977/100000000000000 : ℝ)^65 := by
    have hnat : (100307411 : ℕ)^81*100000000000000^65 ≤ 13509428905977^65*500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100307411 500000000 13509428905977 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5146978239/10000000000 : ℝ), (5059553079/10000000000 : ℝ), (-100307411/500000000 : ℝ)] ![(4370688237341/10000000000000 : ℝ), (8556737740851/20000000000000 : ℝ), (13509428905977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5146978239/10000000000 : ℝ)|^81 ≤ (4370688237341/10000000000000 : ℝ)^65
        have hw : |(5146978239/10000000000 : ℝ)|=(5146978239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5059553079/10000000000 : ℝ)|^81 ≤ (8556737740851/20000000000000 : ℝ)^65
        have hw : |(5059553079/10000000000 : ℝ)|=(5059553079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-100307411/500000000 : ℝ)|^81 ≤ (13509428905977/100000000000000 : ℝ)^65
        have hw : |(-100307411/500000000 : ℝ)|=(100307411/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319054_s3_s3_21 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-333060307/2500000000 : ℝ)*x 0 + (1153922603/2500000000 : ℝ)*x 1 + (-1518624283/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (333060307/2500000000 : ℝ)^81 ≤ (8111395465771/100000000000000 : ℝ)^65 := by
    have hnat : (333060307 : ℕ)^81*100000000000000^65 ≤ 8111395465771^65*2500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      333060307 2500000000 8111395465771 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1153922603/2500000000 : ℝ)^81 ≤ (7631628702537/20000000000000 : ℝ)^65 := by
    have hnat : (1153922603 : ℕ)^81*20000000000000^65 ≤ 7631628702537^65*2500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1153922603 2500000000 7631628702537 20000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1518624283/2500000000 : ℝ)^81 ≤ (26865230499271/50000000000000 : ℝ)^65 := by
    have hnat : (1518624283 : ℕ)^81*50000000000000^65 ≤ 26865230499271^65*2500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1518624283 2500000000 26865230499271 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-333060307/2500000000 : ℝ), (1153922603/2500000000 : ℝ), (-1518624283/2500000000 : ℝ)] ![(8111395465771/100000000000000 : ℝ), (7631628702537/20000000000000 : ℝ), (26865230499271/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-333060307/2500000000 : ℝ)|^81 ≤ (8111395465771/100000000000000 : ℝ)^65
        have hw : |(-333060307/2500000000 : ℝ)|=(333060307/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1153922603/2500000000 : ℝ)|^81 ≤ (7631628702537/20000000000000 : ℝ)^65
        have hw : |(1153922603/2500000000 : ℝ)|=(1153922603/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1518624283/2500000000 : ℝ)|^81 ≤ (26865230499271/50000000000000 : ℝ)^65
        have hw : |(-1518624283/2500000000 : ℝ)|=(1518624283/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319054_s3_s3_22 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5510432981/10000000000 : ℝ)*x 0 + (-445684193/2000000000 : ℝ)*x 1 + (-1126092893/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5510432981/10000000000 : ℝ)^81 ≤ (47585824164951/100000000000000 : ℝ)^65 := by
    have hnat : (5510432981 : ℕ)^81*100000000000000^65 ≤ 47585824164951^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5510432981 10000000000 47585824164951 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (445684193/2000000000 : ℝ)^81 ≤ (15399415869867/100000000000000 : ℝ)^65 := by
    have hnat : (445684193 : ℕ)^81*100000000000000^65 ≤ 15399415869867^65*2000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      445684193 2000000000 15399415869867 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1126092893/2500000000 : ℝ)^81 ≤ (37014759951021/100000000000000 : ℝ)^65 := by
    have hnat : (1126092893 : ℕ)^81*100000000000000^65 ≤ 37014759951021^65*2500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126092893 2500000000 37014759951021 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5510432981/10000000000 : ℝ), (-445684193/2000000000 : ℝ), (-1126092893/2500000000 : ℝ)] ![(47585824164951/100000000000000 : ℝ), (15399415869867/100000000000000 : ℝ), (37014759951021/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5510432981/10000000000 : ℝ)|^81 ≤ (47585824164951/100000000000000 : ℝ)^65
        have hw : |(5510432981/10000000000 : ℝ)|=(5510432981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-445684193/2000000000 : ℝ)|^81 ≤ (15399415869867/100000000000000 : ℝ)^65
        have hw : |(-445684193/2000000000 : ℝ)|=(445684193/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1126092893/2500000000 : ℝ)|^81 ≤ (37014759951021/100000000000000 : ℝ)^65
        have hw : |(-1126092893/2500000000 : ℝ)|=(1126092893/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319054_s3_s3_23 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (995519897/2000000000 : ℝ)*x 0 + (199060193/400000000 : ℝ)*x 1 + (1158610241/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (995519897/2000000000 : ℝ)^81 ≤ (2096091555131/5000000000000 : ℝ)^65 := by
    have hnat : (995519897 : ℕ)^81*5000000000000^65 ≤ 2096091555131^65*2000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      995519897 2000000000 2096091555131 5000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (199060193/400000000 : ℝ)^81 ≤ (4191034270521/10000000000000 : ℝ)^65 := by
    have hnat : (199060193 : ℕ)^81*10000000000000^65 ≤ 4191034270521^65*400000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      199060193 400000000 4191034270521 10000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1158610241/5000000000 : ℝ)^81 ≤ (16167826181213/100000000000000 : ℝ)^65 := by
    have hnat : (1158610241 : ℕ)^81*100000000000000^65 ≤ 16167826181213^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1158610241 5000000000 16167826181213 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(995519897/2000000000 : ℝ), (199060193/400000000 : ℝ), (1158610241/5000000000 : ℝ)] ![(2096091555131/5000000000000 : ℝ), (4191034270521/10000000000000 : ℝ), (16167826181213/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(995519897/2000000000 : ℝ)|^81 ≤ (2096091555131/5000000000000 : ℝ)^65
        have hw : |(995519897/2000000000 : ℝ)|=(995519897/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(199060193/400000000 : ℝ)|^81 ≤ (4191034270521/10000000000000 : ℝ)^65
        have hw : |(199060193/400000000 : ℝ)|=(199060193/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1158610241/5000000000 : ℝ)|^81 ≤ (16167826181213/100000000000000 : ℝ)^65
        have hw : |(1158610241/5000000000 : ℝ)|=(1158610241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319054_s3_s3_27 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5081839371/10000000000 : ℝ)*x 0 + (2540456289/5000000000 : ℝ)*x 1 + (-2061141869/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5081839371/10000000000 : ℝ)^81 ≤ (8603731551569/20000000000000 : ℝ)^65 := by
    have hnat : (5081839371 : ℕ)^81*20000000000000^65 ≤ 8603731551569^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5081839371 10000000000 8603731551569 20000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2540456289/5000000000 : ℝ)^81 ≤ (21504440660709/50000000000000 : ℝ)^65 := by
    have hnat : (2540456289 : ℕ)^81*50000000000000^65 ≤ 21504440660709^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2540456289 5000000000 21504440660709 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2061141869/10000000000 : ℝ)^81 ≤ (218319701763/1562500000000 : ℝ)^65 := by
    have hnat : (2061141869 : ℕ)^81*1562500000000^65 ≤ 218319701763^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2061141869 10000000000 218319701763 1562500000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5081839371/10000000000 : ℝ), (2540456289/5000000000 : ℝ), (-2061141869/10000000000 : ℝ)] ![(8603731551569/20000000000000 : ℝ), (21504440660709/50000000000000 : ℝ), (218319701763/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5081839371/10000000000 : ℝ)|^81 ≤ (8603731551569/20000000000000 : ℝ)^65
        have hw : |(5081839371/10000000000 : ℝ)|=(5081839371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2540456289/5000000000 : ℝ)|^81 ≤ (21504440660709/50000000000000 : ℝ)^65
        have hw : |(2540456289/5000000000 : ℝ)|=(2540456289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2061141869/10000000000 : ℝ)|^81 ≤ (218319701763/1562500000000 : ℝ)^65
        have hw : |(-2061141869/10000000000 : ℝ)|=(2061141869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c319054_s3 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (92547/50000 : ℝ) (17037/10000 : ℝ) (1601/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev2 : (0 : ℝ) ≤ ((12783/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(12783/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(26907/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(26907/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-16949/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-16949/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((8589/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(8589/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18441/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(18441/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-2869/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-2869/25000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (1601/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (1601/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (1601/2000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (1601/2000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (1601/2000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (1601/2000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
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
  have s3_pow0 : (12783/50000 : ℝ) ^ (79/16 : ℝ) ≤ (118941934827062963/100000000000000000000 : ℝ) := by
    have hpowers : (12783/50000 : ℝ)^79 ≤ (118941934827062963/100000000000000000000 : ℝ)^16 := by
      have hnat : (12783 : ℕ)^79*100000000000000000000^16 ≤ 118941934827062963^16*50000^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12783 50000 118941934827062963 100000000000000000000 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (12783/50000 : ℝ)) (X := (118941934827062963/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s3_corner0a : (100118941934827062963/100000000000000000000 : ℝ) ≤ (2500601952229553/2500000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (100118941934827062963/100000000000000000000 : ℝ)^16 ≤ (2500601952229553/2500000000000000 : ℝ)^79 := by
      have hnat : (100118941934827062963 : ℕ)^16*2500000000000000^79 ≤ 2500601952229553^79*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100118941934827062963 100000000000000000000 2500601952229553 2500000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500601952229553/2500000000000000 : ℝ)) (X := (100118941934827062963/100000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s3_corner0b : (50118941934827062963/50000000000000000000 : ℝ) ≤ (10004813337763913/10000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (50118941934827062963/50000000000000000000 : ℝ)^16 ≤ (10004813337763913/10000000000000000 : ℝ)^79 := by
      have hnat : (50118941934827062963 : ℕ)^16*10000000000000000^79 ≤ 10004813337763913^79*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50118941934827062963 50000000000000000000 10004813337763913 10000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004813337763913/10000000000000000 : ℝ)) (X := (50118941934827062963/50000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s3_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(601952229553/639150000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(801842948567/852200000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (12783/50000 : ℝ)) (alpha := (601952229553/639150000000000 : ℝ)) (beta := (801842948567/852200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow0,s3_corner0a]) (by linarith only [s3_pow0,s3_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (12783/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(601952229553/639150000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(801842948567/852200000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow1 : (26907/100000 : ℝ) ^ (79/16 : ℝ) ≤ (153094579325987449/100000000000000000000 : ℝ) := by
    have hpowers : (26907/100000 : ℝ)^79 ≤ (153094579325987449/100000000000000000000 : ℝ)^16 := by
      have hnat : (26907 : ℕ)^79*100000000000000000000^16 ≤ 153094579325987449^16*100000^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26907 100000 153094579325987449 100000000000000000000 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26907/100000 : ℝ)) (X := (153094579325987449/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s3_corner1a : (100153094579325987449/100000000000000000000 : ℝ) ≤ (10003098758680313/10000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (100153094579325987449/100000000000000000000 : ℝ)^16 ≤ (10003098758680313/10000000000000000 : ℝ)^79 := by
      have hnat : (100153094579325987449 : ℕ)^16*10000000000000000^79 ≤ 10003098758680313^79*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100153094579325987449 100000000000000000000 10003098758680313 10000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003098758680313/10000000000000000 : ℝ)) (X := (100153094579325987449/100000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s3_corner1b : (50153094579325987449/50000000000000000000 : ℝ) ≤ (2001238748445601/2000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (50153094579325987449/50000000000000000000 : ℝ)^16 ≤ (2001238748445601/2000000000000000 : ℝ)^79 := by
      have hnat : (50153094579325987449 : ℕ)^16*2000000000000000^79 ≤ 2001238748445601^79*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50153094579325987449 50000000000000000000 2001238748445601 2000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2001238748445601/2000000000000000 : ℝ)) (X := (50153094579325987449/50000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s3_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(3098758680313/2690700000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(257915295641/224225000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (26907/100000 : ℝ)) (alpha := (3098758680313/2690700000000000 : ℝ)) (beta := (257915295641/224225000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow1,s3_corner1a]) (by linarith only [s3_pow1,s3_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (26907/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(3098758680313/2690700000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(257915295641/224225000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow2 : (16949/100000 : ℝ) ^ (79/16 : ℝ) ≤ (15627837742367259/100000000000000000000 : ℝ) := by
    have hpowers : (16949/100000 : ℝ)^79 ≤ (15627837742367259/100000000000000000000 : ℝ)^16 := by
      have hnat : (16949 : ℕ)^79*100000000000000000000^16 ≤ 15627837742367259^16*100000^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16949 100000 15627837742367259 100000000000000000000 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16949/100000 : ℝ)) (X := (15627837742367259/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s3_corner2a : (100015627837742367259/100000000000000000000 : ℝ) ≤ (500015824672413/500000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (100015627837742367259/100000000000000000000 : ℝ)^16 ≤ (500015824672413/500000000000000 : ℝ)^79 := by
      have hnat : (100015627837742367259 : ℕ)^16*500000000000000^79 ≤ 500015824672413^79*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100015627837742367259 100000000000000000000 500015824672413 500000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500015824672413/500000000000000 : ℝ)) (X := (100015627837742367259/100000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s3_corner2b : (50015627837742367259/50000000000000000000 : ℝ) ≤ (10000632947461491/10000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (50015627837742367259/50000000000000000000 : ℝ)^16 ≤ (10000632947461491/10000000000000000 : ℝ)^79 := by
      have hnat : (50015627837742367259 : ℕ)^16*10000000000000000^79 ≤ 10000632947461491^79*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015627837742367259 50000000000000000000 10000632947461491 10000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000632947461491/10000000000000000 : ℝ)) (X := (50015627837742367259/50000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s3_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(15824672413/84745000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(316454013231/1694900000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (16949/100000 : ℝ)) (alpha := (15824672413/84745000000000 : ℝ)) (beta := (316454013231/1694900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow2,s3_corner2a]) (by linarith only [s3_pow2,s3_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (16949/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(15824672413/84745000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(316454013231/1694900000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s3_0 : ((-285369423/2000000000 : ℝ)*X 0 0+(181472629/400000000 : ℝ)*X 0 1+(-6082378671/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319054_s3_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_1 : ((2707792313/5000000000 : ℝ)*X 1 0+(-2307052301/10000000000 : ℝ)*X 1 1+(-283587153/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319054_s3_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_2 : ((77853711/156250000 : ℝ)*X 2 0+(2490772367/5000000000 : ℝ)*X 2 1+(2305046549/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319054_s3_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_6 : ((126693759/250000000 : ℝ)*X 0 0+(2533409143/5000000000 : ℝ)*X 0 1+(-2096249299/10000000000 : ℝ)*X 0 2+(126693759/250000000 : ℝ)*X 1 0+(2533409143/5000000000 : ℝ)*X 1 1+(-2096249299/10000000000 : ℝ)*X 1 2+(126693759/250000000 : ℝ)*X 2 0+(2533409143/5000000000 : ℝ)*X 2 1+(-2096249299/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c319054_s3_s3_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_7 : ((-710320819/5000000000 : ℝ)*X 0 0+(4500537329/10000000000 : ℝ)*X 0 1+(-6120409267/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319054_s3_s3_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_8 : ((5402680399/10000000000 : ℝ)*X 1 0+(-1115458779/5000000000 : ℝ)*X 1 1+(-4614900667/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319054_s3_s3_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_9 : ((4964236783/10000000000 : ℝ)*X 2 0+(2531710367/5000000000 : ℝ)*X 2 1+(1113891323/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319054_s3_s3_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_13 : ((31660363/62500000 : ℝ)*X 0 0+(5150461229/10000000000 : ℝ)*X 0 1+(-1994079473/10000000000 : ℝ)*X 0 2+(31660363/62500000 : ℝ)*X 1 0+(5150461229/10000000000 : ℝ)*X 1 1+(-1994079473/10000000000 : ℝ)*X 1 2+(31660363/62500000 : ℝ)*X 2 0+(5150461229/10000000000 : ℝ)*X 2 1+(-1994079473/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c319054_s3_s3_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_14 : ((-1368813679/10000000000 : ℝ)*X 0 0+(908829453/2000000000 : ℝ)*X 0 1+(-6115942069/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319054_s3_s3_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_15 : ((2680597797/5000000000 : ℝ)*X 1 0+(-2279188321/10000000000 : ℝ)*X 1 1+(-4617516027/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319054_s3_s3_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_16 : ((5066155553/10000000000 : ℝ)*X 2 0+(2481817501/5000000000 : ℝ)*X 2 1+(1112583839/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319054_s3_s3_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_20 : ((5146978239/10000000000 : ℝ)*X 0 0+(5059553079/10000000000 : ℝ)*X 0 1+(-100307411/500000000 : ℝ)*X 0 2+(5146978239/10000000000 : ℝ)*X 1 0+(5059553079/10000000000 : ℝ)*X 1 1+(-100307411/500000000 : ℝ)*X 1 2+(5146978239/10000000000 : ℝ)*X 2 0+(5059553079/10000000000 : ℝ)*X 2 1+(-100307411/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c319054_s3_s3_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_21 : ((-333060307/2500000000 : ℝ)*X 0 0+(1153922603/2500000000 : ℝ)*X 0 1+(-1518624283/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319054_s3_s3_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_22 : ((5510432981/10000000000 : ℝ)*X 1 0+(-445684193/2000000000 : ℝ)*X 1 1+(-1126092893/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319054_s3_s3_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_23 : ((995519897/2000000000 : ℝ)*X 2 0+(199060193/400000000 : ℝ)*X 2 1+(1158610241/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319054_s3_s3_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_27 : ((5081839371/10000000000 : ℝ)*X 0 0+(2540456289/5000000000 : ℝ)*X 0 1+(-2061141869/10000000000 : ℝ)*X 0 2+(5081839371/10000000000 : ℝ)*X 1 0+(2540456289/5000000000 : ℝ)*X 1 1+(-2061141869/10000000000 : ℝ)*X 1 2+(5081839371/10000000000 : ℝ)*X 2 0+(2540456289/5000000000 : ℝ)*X 2 1+(-2061141869/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c319054_s3_s3_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s3_0 : (0 : ℝ) ≤ ((8589/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(8589/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (41393382815385921/10000000000000000000000 : ℝ) := by norm_num
    linear_combination (3309185376857/250000000000 : ℝ)*(base39) + (1975300618491/500000000000 : ℝ)*(base60) + (60810277557347/1000000000000 : ℝ)*(major_s3_0) + (60810277557347/1000000000000 : ℝ)*(major_s3_1) + (60810277557347/1000000000000 : ℝ)*(major_s3_2) + (4288966947/1000000000000 : ℝ)*(sp_s3_0) + (196008187/125000000000 : ℝ)*(sp_s3_6) + (44381121144203/500000000000 : ℝ)*(sp_s3_7) + (8876670390397/100000000000 : ℝ)*(sp_s3_8) + (44383301278703/500000000000 : ℝ)*(sp_s3_9) + (16426079495337/500000000000 : ℝ)*(sp_s3_13) + (29542339/100000000000 : ℝ)*(sp_s3_14) + (122774773/1000000000000 : ℝ)*(sp_s3_15) + (224121337/1000000000000 : ℝ)*(sp_s3_23) + (3285372705617/100000000000 : ℝ)*(f.failure) + (88766826678743/1000000000000 : ℝ)*(f.sum) + (2625159641003567531/45604674300000000000000000000000 : ℝ)*base62 + (58388041095667/1694900000000000000000000000 : ℝ)*base65 + (92878550861379/448450000000000000000000000 : ℝ)*base66 + (18101991402447/84745000000000000000000000 : ℝ)*base69 + (5366810244464497981/21665906700000000000000000000000 : ℝ)*base70 + (36937639300511/852200000000000000000000000 : ℝ)*base72 + (312570044965001/2690700000000000000000000000 : ℝ)*base75 + (40828170368263/319575000000000000000000000 : ℝ)*base77 + (344435603724969697/1528676360000000000000000000000 : ℝ)*base79 + (1499/5000000000000000 : ℝ)*base87 + (1499/5000000000000000 : ℝ)*base89 + (1499/5000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s3_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18441/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(18441/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (150971074853948290311438958389/12954767812820000000000000000000000 : ℝ) := by norm_num
    linear_combination (13173584850821/1000000000000 : ℝ)*(base39) + (3677635306037/1000000000000 : ℝ)*(base60) + (60809195327949/1000000000000 : ℝ)*(major_s3_0) + (60809195327949/1000000000000 : ℝ)*(major_s3_1) + (60809195327949/1000000000000 : ℝ)*(major_s3_2) + (12242719121/1000000000000 : ℝ)*(sp_s3_0) + (8331679687/1000000000000 : ℝ)*(sp_s3_6) + (3267658607/500000000000 : ℝ)*(sp_s3_8) + (22186482900519/250000000000 : ℝ)*(sp_s3_14) + (22189677272429/250000000000 : ℝ)*(sp_s3_15) + (88765029295873/1000000000000 : ℝ)*(sp_s3_16) + (6568962136941/200000000000 : ℝ)*(sp_s3_20) + (3535042867/500000000000 : ℝ)*(sp_s3_21) + (107555529/500000000000 : ℝ)*(sp_s3_23) + (32853142364393/1000000000000 : ℝ)*(f.failure) + (88765244406931/1000000000000 : ℝ)*(f.sum) + (3648245986641420791/15201558100000000000000000000000 : ℝ)*base63 + (609588339272719/1694900000000000000000000000 : ℝ)*base65 + (17028392969901/224225000000000000000000000 : ℝ)*base67 + (93323813403629/169490000000000000000000000 : ℝ)*base69 + (2599618490296470251/7221968900000000000000000000000 : ℝ)*base71 + (43605945562343/852200000000000000000000000 : ℝ)*base73 + (159641653074019/896900000000000000000000000 : ℝ)*base75 + (18255691493417/106525000000000000000000000 : ℝ)*base77 + (81435472586499023/305735272000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (28971/50000000000000000 : ℝ)*base87 + (28971/50000000000000000 : ℝ)*base89 + (28971/50000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s3_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-2869/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-2869/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (10463380602268413822684445157/809672988301250000000000000000000 : ℝ) := by norm_num
    linear_combination (4232276488317/500000000000 : ℝ)*(base39) + (1210979/250000000000 : ℝ)*(base50) + (1934919695197/1000000000000 : ℝ)*(base60) + (1863573075191/50000000000 : ℝ)*(major_s3_0) + (1863573075191/50000000000 : ℝ)*(major_s3_1) + (1863573075191/50000000000 : ℝ)*(major_s3_2) + (52559029/125000000000 : ℝ)*(sp_s3_1) + (302896361/125000000000 : ℝ)*(sp_s3_2) + (364788621/500000000000 : ℝ)*(sp_s3_13) + (1245750453/1000000000000 : ℝ)*(sp_s3_20) + (10881282854627/200000000000 : ℝ)*(sp_s3_21) + (6800749225113/125000000000 : ℝ)*(sp_s3_22) + (54403991102247/1000000000000 : ℝ)*(sp_s3_23) + (20134529099147/1000000000000 : ℝ)*(sp_s3_27) + (20136504426843/1000000000000 : ℝ)*(f.failure) + (10881282854627/200000000000 : ℝ)*(f.sum) + (1466163745910709031/2280233715000000000000000000000 : ℝ)*base63 + (40214545255417/169490000000000000000000000 : ℝ)*base64 + (11043951420807/89690000000000000000000000 : ℝ)*base66 + (839775447527/8474500000000000000000000 : ℝ)*base69 + (254322542222740801/2166590670000000000000000000000 : ℝ)*base71 + (2771129841737/4261000000000000000000000 : ℝ)*base73 + (15809459330089/269070000000000000000000000 : ℝ)*base75 + (12391939240819/63915000000000000000000000 : ℝ)*base77 + (6888247275771427/95542272500000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (39121/50000000000000000 : ℝ)*base87 + (39121/50000000000000000 : ℝ)*base89 + (39121/50000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  exact ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (92547/50000 : ℝ) (17037/10000 : ℝ) (1601/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev2 : (0 : ℝ) ≤ ((12783/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(12783/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(26907/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(26907/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-16949/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-16949/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((8589/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(8589/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18441/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(18441/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-2869/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-2869/25000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c319054_s3 p hpa hpb X hX hprev2

#print axioms solution
