-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c302059_s3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:22:58.270509+00:00
-- url     : https://prove2.me/submissions/6f7fac49-7fe2-4cb5-a1bb-8b354add1905

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
theorem collision_support_c302059_s3_s3_1 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3194845479/10000000000 : ℝ)*x 0 + (-1596173967/5000000000 : ℝ)*x 1 + (6437709779/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3194845479/10000000000 : ℝ)^131 ≤ (4418776442667/20000000000000 : ℝ)^99 := by
    have hnat : (3194845479 : ℕ)^131*20000000000000^99 ≤ 4418776442667^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3194845479 10000000000 4418776442667 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1596173967/5000000000 : ℝ)^131 ≤ (22071030607913/100000000000000 : ℝ)^99 := by
    have hnat : (1596173967 : ℕ)^131*100000000000000^99 ≤ 22071030607913^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1596173967 5000000000 22071030607913 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6437709779/10000000000 : ℝ)^131 ≤ (27917543576617/50000000000000 : ℝ)^99 := by
    have hnat : (6437709779 : ℕ)^131*50000000000000^99 ≤ 27917543576617^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6437709779 10000000000 27917543576617 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3194845479/10000000000 : ℝ), (-1596173967/5000000000 : ℝ), (6437709779/10000000000 : ℝ)] ![(4418776442667/20000000000000 : ℝ), (22071030607913/100000000000000 : ℝ), (27917543576617/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3194845479/10000000000 : ℝ)|^131 ≤ (4418776442667/20000000000000 : ℝ)^99
        have hw : |(3194845479/10000000000 : ℝ)|=(3194845479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1596173967/5000000000 : ℝ)|^131 ≤ (22071030607913/100000000000000 : ℝ)^99
        have hw : |(-1596173967/5000000000 : ℝ)|=(1596173967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6437709779/10000000000 : ℝ)|^131 ≤ (27917543576617/50000000000000 : ℝ)^99
        have hw : |(6437709779/10000000000 : ℝ)|=(6437709779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302059_s3_s3_2 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (6418921339/10000000000 : ℝ)*x 0 + (268476049/500000000 : ℝ)*x 1 + (-17197411/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6418921339/10000000000 : ℝ)^131 ≤ (13904890545277/25000000000000 : ℝ)^99 := by
    have hnat : (6418921339 : ℕ)^131*25000000000000^99 ≤ 13904890545277^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6418921339 10000000000 13904890545277 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (268476049/500000000 : ℝ)^131 ≤ (4391794211333/10000000000000 : ℝ)^99 := by
    have hnat : (268476049 : ℕ)^131*10000000000000^99 ≤ 4391794211333^99*500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268476049 500000000 4391794211333 10000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (17197411/1000000000 : ℝ)^131 ≤ (462495700157/100000000000000 : ℝ)^99 := by
    have hnat : (17197411 : ℕ)^131*100000000000000^99 ≤ 462495700157^99*1000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17197411 1000000000 462495700157 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6418921339/10000000000 : ℝ), (268476049/500000000 : ℝ), (-17197411/1000000000 : ℝ)] ![(13904890545277/25000000000000 : ℝ), (4391794211333/10000000000000 : ℝ), (462495700157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6418921339/10000000000 : ℝ)|^131 ≤ (13904890545277/25000000000000 : ℝ)^99
        have hw : |(6418921339/10000000000 : ℝ)|=(6418921339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(268476049/500000000 : ℝ)|^131 ≤ (4391794211333/10000000000000 : ℝ)^99
        have hw : |(268476049/500000000 : ℝ)|=(268476049/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-17197411/1000000000 : ℝ)|^131 ≤ (462495700157/100000000000000 : ℝ)^99
        have hw : |(-17197411/1000000000 : ℝ)|=(17197411/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302059_s3_s3_6 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3756408673/10000000000 : ℝ)*x 0 + (2950959109/5000000000 : ℝ)*x 1 + (655566189/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3756408673/10000000000 : ℝ)^131 ≤ (6843301567297/25000000000000 : ℝ)^99 := by
    have hnat : (3756408673 : ℕ)^131*25000000000000^99 ≤ 6843301567297^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3756408673 10000000000 6843301567297 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2950959109/5000000000 : ℝ)^131 ≤ (12442590029451/25000000000000 : ℝ)^99 := by
    have hnat : (2950959109 : ℕ)^131*25000000000000^99 ≤ 12442590029451^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2950959109 5000000000 12442590029451 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655566189/2000000000 : ℝ)^131 ≤ (2285643360767/10000000000000 : ℝ)^99 := by
    have hnat : (655566189 : ℕ)^131*10000000000000^99 ≤ 2285643360767^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655566189 2000000000 2285643360767 10000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3756408673/10000000000 : ℝ), (2950959109/5000000000 : ℝ), (655566189/2000000000 : ℝ)] ![(6843301567297/25000000000000 : ℝ), (12442590029451/25000000000000 : ℝ), (2285643360767/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3756408673/10000000000 : ℝ)|^131 ≤ (6843301567297/25000000000000 : ℝ)^99
        have hw : |(3756408673/10000000000 : ℝ)|=(3756408673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2950959109/5000000000 : ℝ)|^131 ≤ (12442590029451/25000000000000 : ℝ)^99
        have hw : |(2950959109/5000000000 : ℝ)|=(2950959109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655566189/2000000000 : ℝ)|^131 ≤ (2285643360767/10000000000000 : ℝ)^99
        have hw : |(655566189/2000000000 : ℝ)|=(655566189/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302059_s3_s3_7 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-219249767/1000000000 : ℝ)*x 0 + (1783835049/10000000000 : ℝ)*x 1 + (4077897853/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (219249767/1000000000 : ℝ)^131 ≤ (419526490871/3125000000000 : ℝ)^99 := by
    have hnat : (219249767 : ℕ)^131*3125000000000^99 ≤ 419526490871^99*1000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219249767 1000000000 419526490871 3125000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1783835049/10000000000 : ℝ)^131 ≤ (10218057230459/100000000000000 : ℝ)^99 := by
    have hnat : (1783835049 : ℕ)^131*100000000000000^99 ≤ 10218057230459^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1783835049 10000000000 10218057230459 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4077897853/5000000000 : ℝ)^131 ≤ (38178547521423/50000000000000 : ℝ)^99 := by
    have hnat : (4077897853 : ℕ)^131*50000000000000^99 ≤ 38178547521423^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4077897853 5000000000 38178547521423 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-219249767/1000000000 : ℝ), (1783835049/10000000000 : ℝ), (4077897853/5000000000 : ℝ)] ![(419526490871/3125000000000 : ℝ), (10218057230459/100000000000000 : ℝ), (38178547521423/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-219249767/1000000000 : ℝ)|^131 ≤ (419526490871/3125000000000 : ℝ)^99
        have hw : |(-219249767/1000000000 : ℝ)|=(219249767/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1783835049/10000000000 : ℝ)|^131 ≤ (10218057230459/100000000000000 : ℝ)^99
        have hw : |(1783835049/10000000000 : ℝ)|=(1783835049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4077897853/5000000000 : ℝ)|^131 ≤ (38178547521423/50000000000000 : ℝ)^99
        have hw : |(4077897853/5000000000 : ℝ)|=(4077897853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302059_s3_s3_8 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (574770559/2500000000 : ℝ)*x 0 + (-1662791079/10000000000 : ℝ)*x 1 + (1019847407/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (574770559/2500000000 : ℝ)^131 ≤ (714756790203/5000000000000 : ℝ)^99 := by
    have hnat : (574770559 : ℕ)^131*5000000000000^99 ≤ 714756790203^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      574770559 2500000000 714756790203 5000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1662791079/10000000000 : ℝ)^131 ≤ (9310805207807/100000000000000 : ℝ)^99 := by
    have hnat : (1662791079 : ℕ)^131*100000000000000^99 ≤ 9310805207807^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1662791079 10000000000 9310805207807 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1019847407/1250000000 : ℝ)^131 ≤ (38197029487057/50000000000000 : ℝ)^99 := by
    have hnat : (1019847407 : ℕ)^131*50000000000000^99 ≤ 38197029487057^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1019847407 1250000000 38197029487057 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(574770559/2500000000 : ℝ), (-1662791079/10000000000 : ℝ), (1019847407/1250000000 : ℝ)] ![(714756790203/5000000000000 : ℝ), (9310805207807/100000000000000 : ℝ), (38197029487057/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(574770559/2500000000 : ℝ)|^131 ≤ (714756790203/5000000000000 : ℝ)^99
        have hw : |(574770559/2500000000 : ℝ)|=(574770559/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1662791079/10000000000 : ℝ)|^131 ≤ (9310805207807/100000000000000 : ℝ)^99
        have hw : |(-1662791079/10000000000 : ℝ)|=(1662791079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1019847407/1250000000 : ℝ)|^131 ≤ (38197029487057/50000000000000 : ℝ)^99
        have hw : |(1019847407/1250000000 : ℝ)|=(1019847407/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302059_s3_s3_9 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2279812411/5000000000 : ℝ)*x 0 + (7189605281/10000000000 : ℝ)*x 1 + (-151249/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2279812411/5000000000 : ℝ)^131 ≤ (35373983819069/100000000000000 : ℝ)^99 := by
    have hnat : (2279812411 : ℕ)^131*100000000000000^99 ≤ 35373983819069^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2279812411 5000000000 35373983819069 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7189605281/10000000000 : ℝ)^131 ≤ (32311527669103/50000000000000 : ℝ)^99 := by
    have hnat : (7189605281 : ℕ)^131*50000000000000^99 ≤ 32311527669103^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7189605281 10000000000 32311527669103 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (151249/400000000 : ℝ)^131 ≤ (1480412467/50000000000000 : ℝ)^99 := by
    have hnat : (151249 : ℕ)^131*50000000000000^99 ≤ 1480412467^99*400000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      151249 400000000 1480412467 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2279812411/5000000000 : ℝ), (7189605281/10000000000 : ℝ), (-151249/400000000 : ℝ)] ![(35373983819069/100000000000000 : ℝ), (32311527669103/50000000000000 : ℝ), (1480412467/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2279812411/5000000000 : ℝ)|^131 ≤ (35373983819069/100000000000000 : ℝ)^99
        have hw : |(2279812411/5000000000 : ℝ)|=(2279812411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7189605281/10000000000 : ℝ)|^131 ≤ (32311527669103/50000000000000 : ℝ)^99
        have hw : |(7189605281/10000000000 : ℝ)|=(7189605281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-151249/400000000 : ℝ)|^131 ≤ (1480412467/50000000000000 : ℝ)^99
        have hw : |(-151249/400000000 : ℝ)|=(151249/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302059_s3_s3_13 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2392759011/10000000000 : ℝ)*x 0 + (3976147823/5000000000 : ℝ)*x 1 + (1896788979/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2392759011/10000000000 : ℝ)^131 ≤ (3767723614363/25000000000000 : ℝ)^99 := by
    have hnat : (2392759011 : ℕ)^131*25000000000000^99 ≤ 3767723614363^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2392759011 10000000000 3767723614363 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3976147823/5000000000 : ℝ)^131 ≤ (73846256244917/100000000000000 : ℝ)^99 := by
    have hnat : (3976147823 : ℕ)^131*100000000000000^99 ≤ 73846256244917^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3976147823 5000000000 73846256244917 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1896788979/10000000000 : ℝ)^131 ≤ (11082849284169/100000000000000 : ℝ)^99 := by
    have hnat : (1896788979 : ℕ)^131*100000000000000^99 ≤ 11082849284169^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1896788979 10000000000 11082849284169 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2392759011/10000000000 : ℝ), (3976147823/5000000000 : ℝ), (1896788979/10000000000 : ℝ)] ![(3767723614363/25000000000000 : ℝ), (73846256244917/100000000000000 : ℝ), (11082849284169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2392759011/10000000000 : ℝ)|^131 ≤ (3767723614363/25000000000000 : ℝ)^99
        have hw : |(2392759011/10000000000 : ℝ)|=(2392759011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3976147823/5000000000 : ℝ)|^131 ≤ (73846256244917/100000000000000 : ℝ)^99
        have hw : |(3976147823/5000000000 : ℝ)|=(3976147823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1896788979/10000000000 : ℝ)|^131 ≤ (11082849284169/100000000000000 : ℝ)^99
        have hw : |(1896788979/10000000000 : ℝ)|=(1896788979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302059_s3_s3_14 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1004877009/5000000000 : ℝ)*x 0 + (2407915499/10000000000 : ℝ)*x 1 + (3074263/3906250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1004877009/5000000000 : ℝ)^131 ≤ (5982272232039/50000000000000 : ℝ)^99 := by
    have hnat : (1004877009 : ℕ)^131*50000000000000^99 ≤ 5982272232039^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004877009 5000000000 5982272232039 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2407915499/10000000000 : ℝ)^131 ≤ (7598672178389/50000000000000 : ℝ)^99 := by
    have hnat : (2407915499 : ℕ)^131*50000000000000^99 ≤ 7598672178389^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2407915499 10000000000 7598672178389 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3074263/3906250 : ℝ)^131 ≤ (36419055581021/50000000000000 : ℝ)^99 := by
    have hnat : (3074263 : ℕ)^131*50000000000000^99 ≤ 36419055581021^99*3906250^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3074263 3906250 36419055581021 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1004877009/5000000000 : ℝ), (2407915499/10000000000 : ℝ), (3074263/3906250 : ℝ)] ![(5982272232039/50000000000000 : ℝ), (7598672178389/50000000000000 : ℝ), (36419055581021/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1004877009/5000000000 : ℝ)|^131 ≤ (5982272232039/50000000000000 : ℝ)^99
        have hw : |(-1004877009/5000000000 : ℝ)|=(1004877009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2407915499/10000000000 : ℝ)|^131 ≤ (7598672178389/50000000000000 : ℝ)^99
        have hw : |(2407915499/10000000000 : ℝ)|=(2407915499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3074263/3906250 : ℝ)|^131 ≤ (36419055581021/50000000000000 : ℝ)^99
        have hw : |(3074263/3906250 : ℝ)|=(3074263/3906250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302059_s3_s3_15 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (487778777/2500000000 : ℝ)*x 0 + (-2458568293/10000000000 : ℝ)*x 1 + (1574598783/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (487778777/2500000000 : ℝ)^131 ≤ (11504808180151/100000000000000 : ℝ)^99 := by
    have hnat : (487778777 : ℕ)^131*100000000000000^99 ≤ 11504808180151^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      487778777 2500000000 11504808180151 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2458568293/10000000000 : ℝ)^131 ≤ (312436014141/2000000000000 : ℝ)^99 := by
    have hnat : (2458568293 : ℕ)^131*2000000000000^99 ≤ 312436014141^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2458568293 10000000000 312436014141 2000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1574598783/2000000000 : ℝ)^131 ≤ (72873391091951/100000000000000 : ℝ)^99 := by
    have hnat : (1574598783 : ℕ)^131*100000000000000^99 ≤ 72873391091951^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1574598783 2000000000 72873391091951 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(487778777/2500000000 : ℝ), (-2458568293/10000000000 : ℝ), (1574598783/2000000000 : ℝ)] ![(11504808180151/100000000000000 : ℝ), (312436014141/2000000000000 : ℝ), (72873391091951/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(487778777/2500000000 : ℝ)|^131 ≤ (11504808180151/100000000000000 : ℝ)^99
        have hw : |(487778777/2500000000 : ℝ)|=(487778777/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2458568293/10000000000 : ℝ)|^131 ≤ (312436014141/2000000000000 : ℝ)^99
        have hw : |(-2458568293/10000000000 : ℝ)|=(2458568293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1574598783/2000000000 : ℝ)|^131 ≤ (72873391091951/100000000000000 : ℝ)^99
        have hw : |(1574598783/2000000000 : ℝ)|=(1574598783/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302059_s3_s3_16 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (8004971181/10000000000 : ℝ)*x 0 + (1780540939/5000000000 : ℝ)*x 1 + (-1/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8004971181/10000000000 : ℝ)^131 ≤ (74494211488349/100000000000000 : ℝ)^99 := by
    have hnat : (8004971181 : ℕ)^131*100000000000000^99 ≤ 74494211488349^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8004971181 10000000000 74494211488349 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1780540939/5000000000 : ℝ)^131 ≤ (6376447126613/25000000000000 : ℝ)^99 := by
    have hnat : (1780540939 : ℕ)^131*25000000000000^99 ≤ 6376447126613^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1780540939 5000000000 6376447126613 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1/312500000 : ℝ)^131 ≤ (23/4000000000000 : ℝ)^99 := by
    have hnat : (1 : ℕ)^131*4000000000000^99 ≤ 23^99*312500000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1 312500000 23 4000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8004971181/10000000000 : ℝ), (1780540939/5000000000 : ℝ), (-1/312500000 : ℝ)] ![(74494211488349/100000000000000 : ℝ), (6376447126613/25000000000000 : ℝ), (23/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8004971181/10000000000 : ℝ)|^131 ≤ (74494211488349/100000000000000 : ℝ)^99
        have hw : |(8004971181/10000000000 : ℝ)|=(8004971181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1780540939/5000000000 : ℝ)|^131 ≤ (6376447126613/25000000000000 : ℝ)^99
        have hw : |(1780540939/5000000000 : ℝ)|=(1780540939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1/312500000 : ℝ)|^131 ≤ (23/4000000000000 : ℝ)^99
        have hw : |(-1/312500000 : ℝ)|=(1/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302059_s3_s3_20 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3240506771/5000000000 : ℝ)*x 0 + (167499499/400000000 : ℝ)*x 1 + (1011077491/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3240506771/5000000000 : ℝ)^131 ≤ (28166302522941/50000000000000 : ℝ)^99 := by
    have hnat : (3240506771 : ℕ)^131*50000000000000^99 ≤ 28166302522941^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3240506771 5000000000 28166302522941 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (167499499/400000000 : ℝ)^131 ≤ (7901266095697/25000000000000 : ℝ)^99 := by
    have hnat : (167499499 : ℕ)^131*25000000000000^99 ≤ 7901266095697^99*400000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167499499 400000000 7901266095697 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1011077491/5000000000 : ℝ)^131 ≤ (12062330555447/100000000000000 : ℝ)^99 := by
    have hnat : (1011077491 : ℕ)^131*100000000000000^99 ≤ 12062330555447^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1011077491 5000000000 12062330555447 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3240506771/5000000000 : ℝ), (167499499/400000000 : ℝ), (1011077491/5000000000 : ℝ)] ![(28166302522941/50000000000000 : ℝ), (7901266095697/25000000000000 : ℝ), (12062330555447/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3240506771/5000000000 : ℝ)|^131 ≤ (28166302522941/50000000000000 : ℝ)^99
        have hw : |(3240506771/5000000000 : ℝ)|=(3240506771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(167499499/400000000 : ℝ)|^131 ≤ (7901266095697/25000000000000 : ℝ)^99
        have hw : |(167499499/400000000 : ℝ)|=(167499499/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1011077491/5000000000 : ℝ)|^131 ≤ (12062330555447/100000000000000 : ℝ)^99
        have hw : |(1011077491/5000000000 : ℝ)|=(1011077491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302059_s3_s3_21 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1060229733/2500000000 : ℝ)*x 0 + (3061240093/10000000000 : ℝ)*x 1 + (2825078191/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060229733/2500000000 : ℝ)^131 ≤ (2008736675049/6250000000000 : ℝ)^99 := by
    have hnat : (1060229733 : ℕ)^131*6250000000000^99 ≤ 2008736675049^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060229733 2500000000 2008736675049 6250000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3061240093/10000000000 : ℝ)^131 ≤ (4175926135131/20000000000000 : ℝ)^99 := by
    have hnat : (3061240093 : ℕ)^131*20000000000000^99 ≤ 4175926135131^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3061240093 10000000000 4175926135131 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2825078191/5000000000 : ℝ)^131 ≤ (46980582508377/100000000000000 : ℝ)^99 := by
    have hnat : (2825078191 : ℕ)^131*100000000000000^99 ≤ 46980582508377^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2825078191 5000000000 46980582508377 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1060229733/2500000000 : ℝ), (3061240093/10000000000 : ℝ), (2825078191/5000000000 : ℝ)] ![(2008736675049/6250000000000 : ℝ), (4175926135131/20000000000000 : ℝ), (46980582508377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1060229733/2500000000 : ℝ)|^131 ≤ (2008736675049/6250000000000 : ℝ)^99
        have hw : |(-1060229733/2500000000 : ℝ)|=(1060229733/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3061240093/10000000000 : ℝ)|^131 ≤ (4175926135131/20000000000000 : ℝ)^99
        have hw : |(3061240093/10000000000 : ℝ)|=(3061240093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2825078191/5000000000 : ℝ)|^131 ≤ (46980582508377/100000000000000 : ℝ)^99
        have hw : |(2825078191/5000000000 : ℝ)|=(2825078191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302059_s3_s3_22 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3025094387/10000000000 : ℝ)*x 0 + (-960664017/2500000000 : ℝ)*x 1 + (301648969/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3025094387/10000000000 : ℝ)^131 ≤ (1027701456461/5000000000000 : ℝ)^99 := by
    have hnat : (3025094387 : ℕ)^131*5000000000000^99 ≤ 1027701456461^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3025094387 10000000000 1027701456461 5000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (960664017/2500000000 : ℝ)^131 ≤ (5641583112029/20000000000000 : ℝ)^99 := by
    have hnat : (960664017 : ℕ)^131*20000000000000^99 ≤ 5641583112029^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      960664017 2500000000 5641583112029 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (301648969/500000000 : ℝ)^131 ≤ (10247611058757/20000000000000 : ℝ)^99 := by
    have hnat : (301648969 : ℕ)^131*20000000000000^99 ≤ 10247611058757^99*500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      301648969 500000000 10247611058757 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3025094387/10000000000 : ℝ), (-960664017/2500000000 : ℝ), (301648969/500000000 : ℝ)] ![(1027701456461/5000000000000 : ℝ), (5641583112029/20000000000000 : ℝ), (10247611058757/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3025094387/10000000000 : ℝ)|^131 ≤ (1027701456461/5000000000000 : ℝ)^99
        have hw : |(3025094387/10000000000 : ℝ)|=(3025094387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-960664017/2500000000 : ℝ)|^131 ≤ (5641583112029/20000000000000 : ℝ)^99
        have hw : |(-960664017/2500000000 : ℝ)|=(960664017/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(301648969/500000000 : ℝ)|^131 ≤ (10247611058757/20000000000000 : ℝ)^99
        have hw : |(301648969/500000000 : ℝ)|=(301648969/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302059_s3_s3_23 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3999215791/5000000000 : ℝ)*x 0 + (713902683/2000000000 : ℝ)*x 1 + (68727/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3999215791/5000000000 : ℝ)^131 ≤ (37206846777447/50000000000000 : ℝ)^99 := by
    have hnat : (3999215791 : ℕ)^131*50000000000000^99 ≤ 37206846777447^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3999215791 5000000000 37206846777447 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (713902683/2000000000 : ℝ)^131 ≤ (5117145758999/20000000000000 : ℝ)^99 := by
    have hnat : (713902683 : ℕ)^131*20000000000000^99 ≤ 5117145758999^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      713902683 2000000000 5117145758999 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (68727/625000000 : ℝ)^131 ≤ (57763109/10000000000000 : ℝ)^99 := by
    have hnat : (68727 : ℕ)^131*10000000000000^99 ≤ 57763109^99*625000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68727 625000000 57763109 10000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3999215791/5000000000 : ℝ), (713902683/2000000000 : ℝ), (68727/625000000 : ℝ)] ![(37206846777447/50000000000000 : ℝ), (5117145758999/20000000000000 : ℝ), (57763109/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3999215791/5000000000 : ℝ)|^131 ≤ (37206846777447/50000000000000 : ℝ)^99
        have hw : |(3999215791/5000000000 : ℝ)|=(3999215791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(713902683/2000000000 : ℝ)|^131 ≤ (5117145758999/20000000000000 : ℝ)^99
        have hw : |(713902683/2000000000 : ℝ)|=(713902683/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(68727/625000000 : ℝ)|^131 ≤ (57763109/10000000000000 : ℝ)^99
        have hw : |(68727/625000000 : ℝ)|=(68727/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302059_s3_s3_27 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1971181563/10000000000 : ℝ)*x 0 + (2000111507/2500000000 : ℝ)*x 1 + (562719079/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1971181563/10000000000 : ℝ)^131 ≤ (2915408976893/25000000000000 : ℝ)^99 := by
    have hnat : (1971181563 : ℕ)^131*25000000000000^99 ≤ 2915408976893^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1971181563 10000000000 2915408976893 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2000111507/2500000000 : ℝ)^131 ≤ (74438493883449/100000000000000 : ℝ)^99 := by
    have hnat : (2000111507 : ℕ)^131*100000000000000^99 ≤ 74438493883449^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2000111507 2500000000 74438493883449 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (562719079/2500000000 : ℝ)^131 ≤ (3474967549731/25000000000000 : ℝ)^99 := by
    have hnat : (562719079 : ℕ)^131*25000000000000^99 ≤ 3474967549731^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562719079 2500000000 3474967549731 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1971181563/10000000000 : ℝ), (2000111507/2500000000 : ℝ), (562719079/2500000000 : ℝ)] ![(2915408976893/25000000000000 : ℝ), (74438493883449/100000000000000 : ℝ), (3474967549731/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1971181563/10000000000 : ℝ)|^131 ≤ (2915408976893/25000000000000 : ℝ)^99
        have hw : |(1971181563/10000000000 : ℝ)|=(1971181563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2000111507/2500000000 : ℝ)|^131 ≤ (74438493883449/100000000000000 : ℝ)^99
        have hw : |(2000111507/2500000000 : ℝ)|=(2000111507/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(562719079/2500000000 : ℝ)|^131 ≤ (3474967549731/25000000000000 : ℝ)^99
        have hw : |(562719079/2500000000 : ℝ)|=(562719079/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c302059_s3 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]])
    (hprev2 : (0 : ℝ) ≤ ((683/800 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(683/800 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8521/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8521/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(35167/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(35167/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((76593/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(76593/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(75053/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(75053/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(26023/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(26023/50000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4769/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4769/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4769/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4769/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4769/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4769/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (36753/20000 : ℝ) := by
    linarith only [f.Tcap]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base44 : ((-1 : ℝ)*N 1+(1 : ℝ)*P 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  rcases hprev2 with ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩
  have s3_pow0 : (683/800 : ℝ) ^ (65/16 : ℝ) ≤ (52605485919007034511/100000000000000000000 : ℝ) := by
    have hpowers : (683/800 : ℝ)^65 ≤ (52605485919007034511/100000000000000000000 : ℝ)^16 := by
      have hnat : (683 : ℕ)^65*100000000000000000000^16 ≤ 52605485919007034511^16*800^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        683 800 52605485919007034511 100000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (683/800 : ℝ)) (X := (52605485919007034511/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s3_corner0a : (152605485919007034511/100000000000000000000 : ℝ) ≤ (11096512264452979/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (152605485919007034511/100000000000000000000 : ℝ)^16 ≤ (11096512264452979/10000000000000000 : ℝ)^65 := by
      have hnat : (152605485919007034511 : ℕ)^16*10000000000000000^65 ≤ 11096512264452979^65*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        152605485919007034511 100000000000000000000 11096512264452979 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11096512264452979/10000000000000000 : ℝ)) (X := (152605485919007034511/100000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s3_corner0b : (102605485919007034511/50000000000000000000 : ℝ) ≤ (2983935157816461/2500000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (102605485919007034511/50000000000000000000 : ℝ)^16 ≤ (2983935157816461/2500000000000000 : ℝ)^65 := by
      have hnat : (102605485919007034511 : ℕ)^16*2500000000000000^65 ≤ 2983935157816461^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102605485919007034511 50000000000000000000 2983935157816461 2500000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2983935157816461/2500000000000000 : ℝ)) (X := (102605485919007034511/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s3_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1096512264452979/8537500000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(167845673362573/1707500000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (683/800 : ℝ)) (alpha := (1096512264452979/8537500000000000 : ℝ)) (beta := (167845673362573/1707500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow0,s3_corner0a]) (by linarith only [s3_pow0,s3_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (683/800 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1096512264452979/8537500000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(167845673362573/1707500000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow1 : (8521/10000 : ℝ) ^ (65/16 : ℝ) ≤ (26096840179393975903/50000000000000000000 : ℝ) := by
    have hpowers : (8521/10000 : ℝ)^65 ≤ (26096840179393975903/50000000000000000000 : ℝ)^16 := by
      have hnat : (8521 : ℕ)^65*50000000000000000000^16 ≤ 26096840179393975903^16*10000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8521 10000 26096840179393975903 50000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8521/10000 : ℝ)) (X := (26096840179393975903/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s3_corner1a : (76096840179393975903/50000000000000000000 : ℝ) ≤ (693070871632333/625000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (76096840179393975903/50000000000000000000 : ℝ)^16 ≤ (693070871632333/625000000000000 : ℝ)^65 := by
      have hnat : (76096840179393975903 : ℕ)^16*625000000000000^65 ≤ 693070871632333^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        76096840179393975903 50000000000000000000 693070871632333 625000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (693070871632333/625000000000000 : ℝ)) (X := (76096840179393975903/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s3_corner1b : (51096840179393975903/25000000000000000000 : ℝ) ≤ (1192393101841799/1000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (51096840179393975903/25000000000000000000 : ℝ)^16 ≤ (1192393101841799/1000000000000000 : ℝ)^65 := by
      have hnat : (51096840179393975903 : ℕ)^16*1000000000000000^65 ≤ 1192393101841799^65*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51096840179393975903 25000000000000000000 1192393101841799 1000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1192393101841799/1000000000000000 : ℝ)) (X := (51096840179393975903/25000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s3_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(68070871632333/532562500000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(417398536150331/4260500000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (8521/10000 : ℝ)) (alpha := (68070871632333/532562500000000 : ℝ)) (beta := (417398536150331/4260500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow1,s3_corner1a]) (by linarith only [s3_pow1,s3_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (8521/10000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(68070871632333/532562500000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(417398536150331/4260500000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow2 : (35167/50000 : ℝ) ^ (65/16 : ℝ) ≤ (4787834130946534943/20000000000000000000 : ℝ) := by
    have hpowers : (35167/50000 : ℝ)^65 ≤ (4787834130946534943/20000000000000000000 : ℝ)^16 := by
      have hnat : (35167 : ℕ)^65*20000000000000000000^16 ≤ 4787834130946534943^16*50000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        35167 50000 4787834130946534943 20000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (35167/50000 : ℝ)) (X := (4787834130946534943/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s3_corner2a : (24787834130946534943/20000000000000000000 : ℝ) ≤ (2108500204796453/2000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (24787834130946534943/20000000000000000000 : ℝ)^16 ≤ (2108500204796453/2000000000000000 : ℝ)^65 := by
      have hnat : (24787834130946534943 : ℕ)^16*2000000000000000^65 ≤ 2108500204796453^65*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24787834130946534943 20000000000000000000 2108500204796453 2000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2108500204796453/2000000000000000 : ℝ)) (X := (24787834130946534943/20000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s3_corner2b : (14787834130946534943/10000000000000000000 : ℝ) ≤ (11010896072902849/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (14787834130946534943/10000000000000000000 : ℝ)^16 ≤ (11010896072902849/10000000000000000 : ℝ)^65 := by
      have hnat : (14787834130946534943 : ℕ)^16*10000000000000000^65 ≤ 11010896072902849^65*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14787834130946534943 10000000000000000000 11010896072902849 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11010896072902849/10000000000000000 : ℝ)) (X := (14787834130946534943/10000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s3_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(108500204796453/1406680000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(58549381115073/879175000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (35167/50000 : ℝ)) (alpha := (108500204796453/1406680000000000 : ℝ)) (beta := (58549381115073/879175000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow2,s3_corner2a]) (by linarith only [s3_pow2,s3_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (35167/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(108500204796453/1406680000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(58549381115073/879175000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s3_1 : ((3194845479/10000000000 : ℝ)*X 1 0+(-1596173967/5000000000 : ℝ)*X 1 1+(6437709779/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302059_s3_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_2 : ((6418921339/10000000000 : ℝ)*X 2 0+(268476049/500000000 : ℝ)*X 2 1+(-17197411/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302059_s3_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_6 : ((3756408673/10000000000 : ℝ)*X 0 0+(2950959109/5000000000 : ℝ)*X 0 1+(655566189/2000000000 : ℝ)*X 0 2+(3756408673/10000000000 : ℝ)*X 1 0+(2950959109/5000000000 : ℝ)*X 1 1+(655566189/2000000000 : ℝ)*X 1 2+(3756408673/10000000000 : ℝ)*X 2 0+(2950959109/5000000000 : ℝ)*X 2 1+(655566189/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302059_s3_s3_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_7 : ((-219249767/1000000000 : ℝ)*X 0 0+(1783835049/10000000000 : ℝ)*X 0 1+(4077897853/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302059_s3_s3_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_8 : ((574770559/2500000000 : ℝ)*X 1 0+(-1662791079/10000000000 : ℝ)*X 1 1+(1019847407/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302059_s3_s3_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_9 : ((2279812411/5000000000 : ℝ)*X 2 0+(7189605281/10000000000 : ℝ)*X 2 1+(-151249/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302059_s3_s3_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_13 : ((2392759011/10000000000 : ℝ)*X 0 0+(3976147823/5000000000 : ℝ)*X 0 1+(1896788979/10000000000 : ℝ)*X 0 2+(2392759011/10000000000 : ℝ)*X 1 0+(3976147823/5000000000 : ℝ)*X 1 1+(1896788979/10000000000 : ℝ)*X 1 2+(2392759011/10000000000 : ℝ)*X 2 0+(3976147823/5000000000 : ℝ)*X 2 1+(1896788979/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302059_s3_s3_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_14 : ((-1004877009/5000000000 : ℝ)*X 0 0+(2407915499/10000000000 : ℝ)*X 0 1+(3074263/3906250 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302059_s3_s3_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_15 : ((487778777/2500000000 : ℝ)*X 1 0+(-2458568293/10000000000 : ℝ)*X 1 1+(1574598783/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302059_s3_s3_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_16 : ((8004971181/10000000000 : ℝ)*X 2 0+(1780540939/5000000000 : ℝ)*X 2 1+(-1/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302059_s3_s3_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_20 : ((3240506771/5000000000 : ℝ)*X 0 0+(167499499/400000000 : ℝ)*X 0 1+(1011077491/5000000000 : ℝ)*X 0 2+(3240506771/5000000000 : ℝ)*X 1 0+(167499499/400000000 : ℝ)*X 1 1+(1011077491/5000000000 : ℝ)*X 1 2+(3240506771/5000000000 : ℝ)*X 2 0+(167499499/400000000 : ℝ)*X 2 1+(1011077491/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302059_s3_s3_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_21 : ((-1060229733/2500000000 : ℝ)*X 0 0+(3061240093/10000000000 : ℝ)*X 0 1+(2825078191/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302059_s3_s3_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_22 : ((3025094387/10000000000 : ℝ)*X 1 0+(-960664017/2500000000 : ℝ)*X 1 1+(301648969/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302059_s3_s3_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_23 : ((3999215791/5000000000 : ℝ)*X 2 0+(713902683/2000000000 : ℝ)*X 2 1+(68727/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302059_s3_s3_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_27 : ((1971181563/10000000000 : ℝ)*X 0 0+(2000111507/2500000000 : ℝ)*X 0 1+(562719079/2500000000 : ℝ)*X 0 2+(1971181563/10000000000 : ℝ)*X 1 0+(2000111507/2500000000 : ℝ)*X 1 1+(562719079/2500000000 : ℝ)*X 1 2+(1971181563/10000000000 : ℝ)*X 2 0+(2000111507/2500000000 : ℝ)*X 2 1+(562719079/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302059_s3_s3_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s3_0 : (0 : ℝ) ≤ ((76593/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(76593/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (7131695849643054395890148551593/511666046952500000000000000000000000 : ℝ) := by norm_num
    linear_combination (18676240903/25000000000 : ℝ)*(base7) + (118147/125000000000 : ℝ)*(base53) + (22856534061/250000000000 : ℝ)*(base60) + (509496573203/250000000000 : ℝ)*(major_s3_0) + (509496573203/250000000000 : ℝ)*(major_s3_1) + (407597069527/200000000000 : ℝ)*(major_s3_2) + (2141819/250000000000 : ℝ)*(sp_s3_2) + (2252089220957/1000000000000 : ℝ)*(sp_s3_7) + (2252088617263/1000000000000 : ℝ)*(sp_s3_8) + (2252136853607/1000000000000 : ℝ)*(sp_s3_9) + (1056604994001/500000000000 : ℝ)*(sp_s3_13) + (221019/4000000000 : ℝ)*(sp_s3_14) + (55858443/1000000000000 : ℝ)*(sp_s3_15) + (56912187/1000000000000 : ℝ)*(sp_s3_27) + (1366217264069/1000000000000 : ℝ)*(f.failure) + (2252145420883/1000000000000 : ℝ)*(f.sum) + (53377229555940087637/299658007000000000000000000000000 : ℝ)*base63 + (11780117881177/70334000000000000000000000 : ℝ)*base65 + (688502681313957/1065125000000000000000000000 : ℝ)*base66 + (26793276649189/56267200000000000000000000 : ℝ)*base69 + (2507319735000544199/18764891406250000000000000000000 : ℝ)*base70 + (136529082011513/853750000000000000000000000 : ℝ)*base73 + (583708958643059/2130250000000000000000000000 : ℝ)*base75 + (1011853108765349/4268750000000000000000000000 : ℝ)*base77 + (348114940827513463/7274803750000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (2727/10000000000000000 : ℝ)*base86 + (2727/10000000000000000 : ℝ)*base88 + (7273/10000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s3_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(75053/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(75053/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2600640627234725910017301423/150119131250000000000000000000000 : ℝ) := by norm_num
    linear_combination (717566185929/1000000000000 : ℝ)*(base7) + (540843/250000000000 : ℝ)*(base40) + (20999115577/125000000000 : ℝ)*(base60) + (1195107968309/500000000000 : ℝ)*(major_s3_0) + (1195107968309/500000000000 : ℝ)*(major_s3_1) + (1195107968309/500000000000 : ℝ)*(major_s3_2) + (4212093/250000000000 : ℝ)*(sp_s3_1) + (195287/200000000000 : ℝ)*(sp_s3_6) + (75735691/1000000000000 : ℝ)*(sp_s3_7) + (55850099/1000000000000 : ℝ)*(sp_s3_8) + (547692320689/200000000000 : ℝ)*(sp_s3_14) + (547692928133/200000000000 : ℝ)*(sp_s3_15) + (10697411481/3906250000 : ℝ)*(sp_s3_16) + (2319908801783/1000000000000 : ℝ)*(sp_s3_20) + (1602343592289/1000000000000 : ℝ)*(f.failure) + (10697411481/3906250000 : ℝ)*(f.sum) + (34742984784616191991/149829003500000000000000000000000 : ℝ)*base62 + (240265157227387/1758350000000000000000000000 : ℝ)*base64 + (157915786562151/532562500000000000000000000 : ℝ)*base67 + (66087393345319/703340000000000000000000000 : ℝ)*base68 + (92689780109063327/586402856445312500000000000000 : ℝ)*base71 + (180706595626443/853750000000000000000000000 : ℝ)*base72 + (800574313494251/2130250000000000000000000000 : ℝ)*base75 + (1516952174655943/2134375000000000000000000000 : ℝ)*base77 + (2443553383663513393/7274803750000000000000000000000 : ℝ)*base78 + (4987/10000000000000000 : ℝ)*base86 + (4987/10000000000000000 : ℝ)*base88 + (4987/10000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s3_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(26023/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(26023/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4332559591492829329445716379943/1279165117381250000000000000000000000 : ℝ) := by norm_num
    linear_combination (223850008557/500000000000 : ℝ)*(base7) + (672537/250000000000 : ℝ)*(base11) + (15573932193/125000000000 : ℝ)*(base44) + (3110989793/125000000000 : ℝ)*(base50) + (1213699187699/500000000000 : ℝ)*(major_s3_0) + (1151403458927/500000000000 : ℝ)*(major_s3_1) + (1213699187699/500000000000 : ℝ)*(major_s3_2) + (11337281/1000000000000 : ℝ)*(sp_s3_2) + (3923703/500000000000 : ℝ)*(sp_s3_6) + (105845507/1000000000000 : ℝ)*(sp_s3_13) + (2953284476273/1000000000000 : ℝ)*(sp_s3_21) + (1414347854439/500000000000 : ℝ)*(sp_s3_22) + (2953275829141/1000000000000 : ℝ)*(sp_s3_23) + (1950264676537/1000000000000 : ℝ)*(sp_s3_27) + (40681745247/25000000000 : ℝ)*(f.failure) + (1476643583211/500000000000 : ℝ)*(f.sum) + (36126962734312747677/149829003500000000000000000000000 : ℝ)*base63 + (1327437353738183/1758350000000000000000000000 : ℝ)*base65 + (123316094385453/532562500000000000000000000 : ℝ)*base67 + (32386515067413/140668000000000000000000000 : ℝ)*base69 + (166835869447442857/150119131250000000000000000000000 : ℝ)*base71 + (85276473078201/426875000000000000000000000 : ℝ)*base73 + (1356305496435853/2130250000000000000000000000 : ℝ)*base75 + (247387149926723/2134375000000000000000000000 : ℝ)*base77 + (1919283999376375953/7274803750000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/250000000000000 : ℝ)*base86 + (1/250000000000000 : ℝ)*base88 + (1/250000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]])
    (hprev2 : (0 : ℝ) ≤ ((683/800 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(683/800 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8521/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8521/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(35167/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(35167/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((76593/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(76593/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(75053/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(75053/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(26023/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(26023/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c302059_s3 p hpa hpb X hX hprev2

#print axioms solution
