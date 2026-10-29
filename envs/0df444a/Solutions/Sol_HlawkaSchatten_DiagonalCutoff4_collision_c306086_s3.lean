-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c306086_s3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:01:04.604959+00:00
-- url     : https://prove2.me/submissions/1bdf1503-c1f9-407a-93eb-c802f26f7128

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
theorem collision_support_c306086_s3_s3_0 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-11385663/200000000 : ℝ)*x 0 + (-6068965593/10000000000 : ℝ)*x 1 + (5501689967/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (11385663/200000000 : ℝ)^135 ≤ (1168434098643/50000000000000 : ℝ)^103 := by
    have hnat : (11385663 : ℕ)^135*50000000000000^103 ≤ 1168434098643^103*200000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11385663 200000000 1168434098643 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6068965593/10000000000 : ℝ)^135 ≤ (10393523983931/20000000000000 : ℝ)^103 := by
    have hnat : (6068965593 : ℕ)^135*20000000000000^103 ≤ 10393523983931^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6068965593 10000000000 10393523983931 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5501689967/10000000000 : ℝ)^135 ≤ (45695511862639/100000000000000 : ℝ)^103 := by
    have hnat : (5501689967 : ℕ)^135*100000000000000^103 ≤ 45695511862639^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5501689967 10000000000 45695511862639 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-11385663/200000000 : ℝ), (-6068965593/10000000000 : ℝ), (5501689967/10000000000 : ℝ)] ![(1168434098643/50000000000000 : ℝ), (10393523983931/20000000000000 : ℝ), (45695511862639/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-11385663/200000000 : ℝ)|^135 ≤ (1168434098643/50000000000000 : ℝ)^103
        have hw : |(-11385663/200000000 : ℝ)|=(11385663/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6068965593/10000000000 : ℝ)|^135 ≤ (10393523983931/20000000000000 : ℝ)^103
        have hw : |(-6068965593/10000000000 : ℝ)|=(6068965593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5501689967/10000000000 : ℝ)|^135 ≤ (45695511862639/100000000000000 : ℝ)^103
        have hw : |(5501689967/10000000000 : ℝ)|=(5501689967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306086_s3_s3_2 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (727794893/1250000000 : ℝ)*x 0 + (-3633480931/10000000000 : ℝ)*x 1 + (-67862861/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (727794893/1250000000 : ℝ)^135 ≤ (78748088211/160000000000 : ℝ)^103 := by
    have hnat : (727794893 : ℕ)^135*160000000000^103 ≤ 78748088211^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      727794893 1250000000 78748088211 160000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3633480931/10000000000 : ℝ)^135 ≤ (5305840198143/20000000000000 : ℝ)^103 := by
    have hnat : (3633480931 : ℕ)^135*20000000000000^103 ≤ 5305840198143^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3633480931 10000000000 5305840198143 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (67862861/200000000 : ℝ)^135 ≤ (1212662192963/5000000000000 : ℝ)^103 := by
    have hnat : (67862861 : ℕ)^135*5000000000000^103 ≤ 1212662192963^103*200000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67862861 200000000 1212662192963 5000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(727794893/1250000000 : ℝ), (-3633480931/10000000000 : ℝ), (-67862861/200000000 : ℝ)] ![(78748088211/160000000000 : ℝ), (5305840198143/20000000000000 : ℝ), (1212662192963/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(727794893/1250000000 : ℝ)|^135 ≤ (78748088211/160000000000 : ℝ)^103
        have hw : |(727794893/1250000000 : ℝ)|=(727794893/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3633480931/10000000000 : ℝ)|^135 ≤ (5305840198143/20000000000000 : ℝ)^103
        have hw : |(-3633480931/10000000000 : ℝ)|=(3633480931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-67862861/200000000 : ℝ)|^135 ≤ (1212662192963/5000000000000 : ℝ)^103
        have hw : |(-67862861/200000000 : ℝ)|=(67862861/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306086_s3_s3_7 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-47950103/2500000000 : ℝ)*x 0 + (-7187318919/10000000000 : ℝ)*x 1 + (4447188721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (47950103/2500000000 : ℝ)^135 ≤ (561520862319/100000000000000 : ℝ)^103 := by
    have hnat : (47950103 : ℕ)^135*100000000000000^103 ≤ 561520862319^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47950103 2500000000 561520862319 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7187318919/10000000000 : ℝ)^135 ≤ (64864217184601/100000000000000 : ℝ)^103 := by
    have hnat : (7187318919 : ℕ)^135*100000000000000^103 ≤ 64864217184601^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7187318919 10000000000 64864217184601 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4447188721/10000000000 : ℝ)^135 ≤ (34574261934271/100000000000000 : ℝ)^103 := by
    have hnat : (4447188721 : ℕ)^135*100000000000000^103 ≤ 34574261934271^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4447188721 10000000000 34574261934271 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-47950103/2500000000 : ℝ), (-7187318919/10000000000 : ℝ), (4447188721/10000000000 : ℝ)] ![(561520862319/100000000000000 : ℝ), (64864217184601/100000000000000 : ℝ), (34574261934271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-47950103/2500000000 : ℝ)|^135 ≤ (561520862319/100000000000000 : ℝ)^103
        have hw : |(-47950103/2500000000 : ℝ)|=(47950103/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7187318919/10000000000 : ℝ)|^135 ≤ (64864217184601/100000000000000 : ℝ)^103
        have hw : |(-7187318919/10000000000 : ℝ)|=(7187318919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4447188721/10000000000 : ℝ)|^135 ≤ (34574261934271/100000000000000 : ℝ)^103
        have hw : |(4447188721/10000000000 : ℝ)|=(4447188721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306086_s3_s3_8 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (6082416519/10000000000 : ℝ)*x 0 + (3389184859/10000000000 : ℝ)*x 1 + (66603831/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6082416519/10000000000 : ℝ)^135 ≤ (52118633602423/100000000000000 : ℝ)^103 := by
    have hnat : (6082416519 : ℕ)^135*100000000000000^103 ≤ 52118633602423^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6082416519 10000000000 52118633602423 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3389184859/10000000000 : ℝ)^135 ≤ (24216168767963/100000000000000 : ℝ)^103 := by
    have hnat : (3389184859 : ℕ)^135*100000000000000^103 ≤ 24216168767963^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3389184859 10000000000 24216168767963 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (66603831/200000000 : ℝ)^135 ≤ (23665197622611/100000000000000 : ℝ)^103 := by
    have hnat : (66603831 : ℕ)^135*100000000000000^103 ≤ 23665197622611^103*200000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66603831 200000000 23665197622611 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6082416519/10000000000 : ℝ), (3389184859/10000000000 : ℝ), (66603831/200000000 : ℝ)] ![(52118633602423/100000000000000 : ℝ), (24216168767963/100000000000000 : ℝ), (23665197622611/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6082416519/10000000000 : ℝ)|^135 ≤ (52118633602423/100000000000000 : ℝ)^103
        have hw : |(6082416519/10000000000 : ℝ)|=(6082416519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3389184859/10000000000 : ℝ)|^135 ≤ (24216168767963/100000000000000 : ℝ)^103
        have hw : |(3389184859/10000000000 : ℝ)|=(3389184859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(66603831/200000000 : ℝ)|^135 ≤ (23665197622611/100000000000000 : ℝ)^103
        have hw : |(66603831/200000000 : ℝ)|=(66603831/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306086_s3_s3_9 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (6005843063/10000000000 : ℝ)*x 0 + (-865094031/2500000000 : ℝ)*x 1 + (-418813811/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6005843063/10000000000 : ℝ)^135 ≤ (51260333756389/100000000000000 : ℝ)^103 := by
    have hnat : (6005843063 : ℕ)^135*100000000000000^103 ≤ 51260333756389^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6005843063 10000000000 51260333756389 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (865094031/2500000000 : ℝ)^135 ≤ (12442519185599/50000000000000 : ℝ)^103 := by
    have hnat : (865094031 : ℕ)^135*50000000000000^103 ≤ 12442519185599^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      865094031 2500000000 12442519185599 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (418813811/1250000000 : ℝ)^135 ≤ (23854627868163/100000000000000 : ℝ)^103 := by
    have hnat : (418813811 : ℕ)^135*100000000000000^103 ≤ 23854627868163^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      418813811 1250000000 23854627868163 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6005843063/10000000000 : ℝ), (-865094031/2500000000 : ℝ), (-418813811/1250000000 : ℝ)] ![(51260333756389/100000000000000 : ℝ), (12442519185599/50000000000000 : ℝ), (23854627868163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6005843063/10000000000 : ℝ)|^135 ≤ (51260333756389/100000000000000 : ℝ)^103
        have hw : |(6005843063/10000000000 : ℝ)|=(6005843063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-865094031/2500000000 : ℝ)|^135 ≤ (12442519185599/50000000000000 : ℝ)^103
        have hw : |(-865094031/2500000000 : ℝ)|=(865094031/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-418813811/1250000000 : ℝ)|^135 ≤ (23854627868163/100000000000000 : ℝ)^103
        have hw : |(-418813811/1250000000 : ℝ)|=(418813811/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306086_s3_s3_13 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1500318347/5000000000 : ℝ)*x 0 + (-1588272641/10000000000 : ℝ)*x 1 + (478111983/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1500318347/5000000000 : ℝ)^135 ≤ (20644020558499/100000000000000 : ℝ)^103 := by
    have hnat : (1500318347 : ℕ)^135*100000000000000^103 ≤ 20644020558499^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1500318347 5000000000 20644020558499 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1588272641/10000000000 : ℝ)^135 ≤ (2241861454753/25000000000000 : ℝ)^103 := by
    have hnat : (1588272641 : ℕ)^135*25000000000000^103 ≤ 2241861454753^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1588272641 10000000000 2241861454753 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (478111983/625000000 : ℝ)^135 ≤ (35194266802721/50000000000000 : ℝ)^103 := by
    have hnat : (478111983 : ℕ)^135*50000000000000^103 ≤ 35194266802721^103*625000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      478111983 625000000 35194266802721 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1500318347/5000000000 : ℝ), (-1588272641/10000000000 : ℝ), (478111983/625000000 : ℝ)] ![(20644020558499/100000000000000 : ℝ), (2241861454753/25000000000000 : ℝ), (35194266802721/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1500318347/5000000000 : ℝ)|^135 ≤ (20644020558499/100000000000000 : ℝ)^103
        have hw : |(1500318347/5000000000 : ℝ)|=(1500318347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1588272641/10000000000 : ℝ)|^135 ≤ (2241861454753/25000000000000 : ℝ)^103
        have hw : |(-1588272641/10000000000 : ℝ)|=(1588272641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(478111983/625000000 : ℝ)|^135 ≤ (35194266802721/50000000000000 : ℝ)^103
        have hw : |(478111983/625000000 : ℝ)|=(478111983/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306086_s3_s3_14 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-31369/400000000 : ℝ)*x 0 + (-2877026391/5000000000 : ℝ)*x 1 + (1507649583/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (31369/400000000 : ℝ)^135 ≤ (415840811/100000000000000 : ℝ)^103 := by
    have hnat : (31369 : ℕ)^135*100000000000000^103 ≤ 415840811^103*400000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31369 400000000 415840811 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2877026391/5000000000 : ℝ)^135 ≤ (12115535550407/25000000000000 : ℝ)^103 := by
    have hnat : (2877026391 : ℕ)^135*25000000000000^103 ≤ 12115535550407^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2877026391 5000000000 12115535550407 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1507649583/2500000000 : ℝ)^135 ≤ (51537441949267/100000000000000 : ℝ)^103 := by
    have hnat : (1507649583 : ℕ)^135*100000000000000^103 ≤ 51537441949267^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1507649583 2500000000 51537441949267 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-31369/400000000 : ℝ), (-2877026391/5000000000 : ℝ), (1507649583/2500000000 : ℝ)] ![(415840811/100000000000000 : ℝ), (12115535550407/25000000000000 : ℝ), (51537441949267/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-31369/400000000 : ℝ)|^135 ≤ (415840811/100000000000000 : ℝ)^103
        have hw : |(-31369/400000000 : ℝ)|=(31369/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2877026391/5000000000 : ℝ)|^135 ≤ (12115535550407/25000000000000 : ℝ)^103
        have hw : |(-2877026391/5000000000 : ℝ)|=(2877026391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1507649583/2500000000 : ℝ)|^135 ≤ (51537441949267/100000000000000 : ℝ)^103
        have hw : |(1507649583/2500000000 : ℝ)|=(1507649583/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306086_s3_s3_15 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (6812938167/10000000000 : ℝ)*x 0 + (3102777429/10000000000 : ℝ)*x 1 + (2697908093/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6812938167/10000000000 : ℝ)^135 ≤ (12094414644959/20000000000000 : ℝ)^103 := by
    have hnat : (6812938167 : ℕ)^135*20000000000000^103 ≤ 12094414644959^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6812938167 10000000000 12094414644959 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3102777429/10000000000 : ℝ)^135 ≤ (21569888723113/100000000000000 : ℝ)^103 := by
    have hnat : (3102777429 : ℕ)^135*100000000000000^103 ≤ 21569888723113^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3102777429 10000000000 21569888723113 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697908093/10000000000 : ℝ)^135 ≤ (8979019018471/50000000000000 : ℝ)^103 := by
    have hnat : (2697908093 : ℕ)^135*50000000000000^103 ≤ 8979019018471^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697908093 10000000000 8979019018471 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6812938167/10000000000 : ℝ), (3102777429/10000000000 : ℝ), (2697908093/10000000000 : ℝ)] ![(12094414644959/20000000000000 : ℝ), (21569888723113/100000000000000 : ℝ), (8979019018471/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6812938167/10000000000 : ℝ)|^135 ≤ (12094414644959/20000000000000 : ℝ)^103
        have hw : |(6812938167/10000000000 : ℝ)|=(6812938167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3102777429/10000000000 : ℝ)|^135 ≤ (21569888723113/100000000000000 : ℝ)^103
        have hw : |(3102777429/10000000000 : ℝ)|=(3102777429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697908093/10000000000 : ℝ)|^135 ≤ (8979019018471/50000000000000 : ℝ)^103
        have hw : |(2697908093/10000000000 : ℝ)|=(2697908093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306086_s3_s3_16 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (6393894841/10000000000 : ℝ)*x 0 + (-870637351/2500000000 : ℝ)*x 1 + (-569212013/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6393894841/10000000000 : ℝ)^135 ≤ (11128862651637/20000000000000 : ℝ)^103 := by
    have hnat : (6393894841 : ℕ)^135*20000000000000^103 ≤ 11128862651637^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6393894841 10000000000 11128862651637 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (870637351/2500000000 : ℝ)^135 ≤ (5018848758287/20000000000000 : ℝ)^103 := by
    have hnat : (870637351 : ℕ)^135*20000000000000^103 ≤ 5018848758287^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      870637351 2500000000 5018848758287 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (569212013/2000000000 : ℝ)^135 ≤ (4815360734361/25000000000000 : ℝ)^103 := by
    have hnat : (569212013 : ℕ)^135*25000000000000^103 ≤ 4815360734361^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      569212013 2000000000 4815360734361 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6393894841/10000000000 : ℝ), (-870637351/2500000000 : ℝ), (-569212013/2000000000 : ℝ)] ![(11128862651637/20000000000000 : ℝ), (5018848758287/20000000000000 : ℝ), (4815360734361/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6393894841/10000000000 : ℝ)|^135 ≤ (11128862651637/20000000000000 : ℝ)^103
        have hw : |(6393894841/10000000000 : ℝ)|=(6393894841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-870637351/2500000000 : ℝ)|^135 ≤ (5018848758287/20000000000000 : ℝ)^103
        have hw : |(-870637351/2500000000 : ℝ)|=(870637351/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-569212013/2000000000 : ℝ)|^135 ≤ (4815360734361/25000000000000 : ℝ)^103
        have hw : |(-569212013/2000000000 : ℝ)|=(569212013/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306086_s3_s3_20 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3316223777/10000000000 : ℝ)*x 0 + (-2596985527/10000000000 : ℝ)*x 1 + (839880541/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3316223777/10000000000 : ℝ)^135 ≤ (23535186260717/100000000000000 : ℝ)^103 := by
    have hnat : (3316223777 : ℕ)^135*100000000000000^103 ≤ 23535186260717^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3316223777 10000000000 23535186260717 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2596985527/10000000000 : ℝ)^135 ≤ (17082725018023/100000000000000 : ℝ)^103 := by
    have hnat : (2596985527 : ℕ)^135*100000000000000^103 ≤ 17082725018023^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2596985527 10000000000 17082725018023 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (839880541/1250000000 : ℝ)^135 ≤ (59382088708113/100000000000000 : ℝ)^103 := by
    have hnat : (839880541 : ℕ)^135*100000000000000^103 ≤ 59382088708113^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      839880541 1250000000 59382088708113 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3316223777/10000000000 : ℝ), (-2596985527/10000000000 : ℝ), (839880541/1250000000 : ℝ)] ![(23535186260717/100000000000000 : ℝ), (17082725018023/100000000000000 : ℝ), (59382088708113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3316223777/10000000000 : ℝ)|^135 ≤ (23535186260717/100000000000000 : ℝ)^103
        have hw : |(3316223777/10000000000 : ℝ)|=(3316223777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2596985527/10000000000 : ℝ)|^135 ≤ (17082725018023/100000000000000 : ℝ)^103
        have hw : |(-2596985527/10000000000 : ℝ)|=(2596985527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(839880541/1250000000 : ℝ)|^135 ≤ (59382088708113/100000000000000 : ℝ)^103
        have hw : |(839880541/1250000000 : ℝ)|=(839880541/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306086_s3_s3_21 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-3/400000000 : ℝ)*x 0 + (-330560709/500000000 : ℝ)*x 1 + (1286522237/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3/400000000 : ℝ)^135 ≤ (2243/100000000000000 : ℝ)^103 := by
    have hnat : (3 : ℕ)^135*100000000000000^103 ≤ 2243^103*400000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3 400000000 2243 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (330560709/500000000 : ℝ)^135 ≤ (11627230017733/20000000000000 : ℝ)^103 := by
    have hnat : (330560709 : ℕ)^135*20000000000000^103 ≤ 11627230017733^103*500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330560709 500000000 11627230017733 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1286522237/2500000000 : ℝ)^135 ≤ (41863849898827/100000000000000 : ℝ)^103 := by
    have hnat : (1286522237 : ℕ)^135*100000000000000^103 ≤ 41863849898827^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1286522237 2500000000 41863849898827 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3/400000000 : ℝ), (-330560709/500000000 : ℝ), (1286522237/2500000000 : ℝ)] ![(2243/100000000000000 : ℝ), (11627230017733/20000000000000 : ℝ), (41863849898827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3/400000000 : ℝ)|^135 ≤ (2243/100000000000000 : ℝ)^103
        have hw : |(-3/400000000 : ℝ)|=(3/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-330560709/500000000 : ℝ)|^135 ≤ (11627230017733/20000000000000 : ℝ)^103
        have hw : |(-330560709/500000000 : ℝ)|=(330560709/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1286522237/2500000000 : ℝ)|^135 ≤ (41863849898827/100000000000000 : ℝ)^103
        have hw : |(1286522237/2500000000 : ℝ)|=(1286522237/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306086_s3_s3_22 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (6813722247/10000000000 : ℝ)*x 0 + (1511755147/5000000000 : ℝ)*x 1 + (2778942857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6813722247/10000000000 : ℝ)^135 ≤ (60481195120337/100000000000000 : ℝ)^103 := by
    have hnat : (6813722247 : ℕ)^135*100000000000000^103 ≤ 60481195120337^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6813722247 10000000000 60481195120337 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1511755147/5000000000 : ℝ)^135 ≤ (4170104581707/20000000000000 : ℝ)^103 := by
    have hnat : (1511755147 : ℕ)^135*20000000000000^103 ≤ 4170104581707^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1511755147 5000000000 4170104581707 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2778942857/10000000000 : ℝ)^135 ≤ (18668281962383/100000000000000 : ℝ)^103 := by
    have hnat : (2778942857 : ℕ)^135*100000000000000^103 ≤ 18668281962383^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2778942857 10000000000 18668281962383 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6813722247/10000000000 : ℝ), (1511755147/5000000000 : ℝ), (2778942857/10000000000 : ℝ)] ![(60481195120337/100000000000000 : ℝ), (4170104581707/20000000000000 : ℝ), (18668281962383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6813722247/10000000000 : ℝ)|^135 ≤ (60481195120337/100000000000000 : ℝ)^103
        have hw : |(6813722247/10000000000 : ℝ)|=(6813722247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1511755147/5000000000 : ℝ)|^135 ≤ (4170104581707/20000000000000 : ℝ)^103
        have hw : |(1511755147/5000000000 : ℝ)|=(1511755147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2778942857/10000000000 : ℝ)|^135 ≤ (18668281962383/100000000000000 : ℝ)^103
        have hw : |(2778942857/10000000000 : ℝ)|=(2778942857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306086_s3_s3_23 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (704927669/1250000000 : ℝ)*x 0 + (-3826050891/10000000000 : ℝ)*x 1 + (-3410107937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (704927669/1250000000 : ℝ)^135 ≤ (295004205017/625000000000 : ℝ)^103 := by
    have hnat : (704927669 : ℕ)^135*625000000000^103 ≤ 295004205017^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      704927669 1250000000 295004205017 625000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3826050891/10000000000 : ℝ)^135 ≤ (28387026620637/100000000000000 : ℝ)^103 := by
    have hnat : (3826050891 : ℕ)^135*100000000000000^103 ≤ 28387026620637^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3826050891 10000000000 28387026620637 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3410107937/10000000000 : ℝ)^135 ≤ (24412300557003/100000000000000 : ℝ)^103 := by
    have hnat : (3410107937 : ℕ)^135*100000000000000^103 ≤ 24412300557003^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3410107937 10000000000 24412300557003 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(704927669/1250000000 : ℝ), (-3826050891/10000000000 : ℝ), (-3410107937/10000000000 : ℝ)] ![(295004205017/625000000000 : ℝ), (28387026620637/100000000000000 : ℝ), (24412300557003/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(704927669/1250000000 : ℝ)|^135 ≤ (295004205017/625000000000 : ℝ)^103
        have hw : |(704927669/1250000000 : ℝ)|=(704927669/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3826050891/10000000000 : ℝ)|^135 ≤ (28387026620637/100000000000000 : ℝ)^103
        have hw : |(-3826050891/10000000000 : ℝ)|=(3826050891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3410107937/10000000000 : ℝ)|^135 ≤ (24412300557003/100000000000000 : ℝ)^103
        have hw : |(-3410107937/10000000000 : ℝ)|=(3410107937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306086_s3_s3_27 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4888334283/10000000000 : ℝ)*x 0 + (-2788713511/10000000000 : ℝ)*x 1 + (2584507261/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4888334283/10000000000 : ℝ)^135 ≤ (3913717959129/10000000000000 : ℝ)^103 := by
    have hnat : (4888334283 : ℕ)^135*10000000000000^103 ≤ 3913717959129^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4888334283 10000000000 3913717959129 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2788713511/10000000000 : ℝ)^135 ≤ (1875435791847/10000000000000 : ℝ)^103 := by
    have hnat : (2788713511 : ℕ)^135*10000000000000^103 ≤ 1875435791847^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2788713511 10000000000 1875435791847 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2584507261/5000000000 : ℝ)^135 ≤ (42108462469949/100000000000000 : ℝ)^103 := by
    have hnat : (2584507261 : ℕ)^135*100000000000000^103 ≤ 42108462469949^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2584507261 5000000000 42108462469949 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4888334283/10000000000 : ℝ), (-2788713511/10000000000 : ℝ), (2584507261/5000000000 : ℝ)] ![(3913717959129/10000000000000 : ℝ), (1875435791847/10000000000000 : ℝ), (42108462469949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4888334283/10000000000 : ℝ)|^135 ≤ (3913717959129/10000000000000 : ℝ)^103
        have hw : |(4888334283/10000000000 : ℝ)|=(4888334283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2788713511/10000000000 : ℝ)|^135 ≤ (1875435791847/10000000000000 : ℝ)^103
        have hw : |(-2788713511/10000000000 : ℝ)|=(2788713511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2584507261/5000000000 : ℝ)|^135 ≤ (42108462469949/100000000000000 : ℝ)^103
        have hw : |(2584507261/5000000000 : ℝ)|=(2584507261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c306086_s3 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev2 : (0 : ℝ) ≤ ((58261/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(58261/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-39161/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-39161/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19009/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(19009/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((12307/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(12307/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-53373/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-53373/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(44789/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(44789/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (38461/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (38461/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (38461/50000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (38461/50000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (38461/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (38461/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base60 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s3_pow0 : (58261/100000 : ℝ) ^ (67/16 : ℝ) ≤ (5205831484631538553/50000000000000000000 : ℝ) := by
    have hpowers : (58261/100000 : ℝ)^67 ≤ (5205831484631538553/50000000000000000000 : ℝ)^16 := by
      have hnat : (58261 : ℕ)^67*50000000000000000000^16 ≤ 5205831484631538553^16*100000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        58261 100000 5205831484631538553 50000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (58261/100000 : ℝ)) (X := (5205831484631538553/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s3_corner0a : (55205831484631538553/50000000000000000000 : ℝ) ≤ (10239346201219527/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (55205831484631538553/50000000000000000000 : ℝ)^16 ≤ (10239346201219527/10000000000000000 : ℝ)^67 := by
      have hnat : (55205831484631538553 : ℕ)^16*10000000000000000^67 ≤ 10239346201219527^67*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        55205831484631538553 50000000000000000000 10239346201219527 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10239346201219527/10000000000000000 : ℝ)) (X := (55205831484631538553/50000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s3_corner0b : (30205831484631538553/25000000000000000000 : ℝ) ≤ (1046208148544563/1000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (30205831484631538553/25000000000000000000 : ℝ)^16 ≤ (1046208148544563/1000000000000000 : ℝ)^67 := by
      have hnat : (30205831484631538553 : ℕ)^16*1000000000000000^67 ≤ 1046208148544563^67*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        30205831484631538553 25000000000000000000 1046208148544563 1000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1046208148544563/1000000000000000 : ℝ)) (X := (30205831484631538553/25000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s3_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(239346201219527/5826100000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(222735284226103/5826100000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (58261/100000 : ℝ)) (alpha := (239346201219527/5826100000000000 : ℝ)) (beta := (222735284226103/5826100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow0,s3_corner0a]) (by linarith only [s3_pow0,s3_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (58261/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(239346201219527/5826100000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(222735284226103/5826100000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow1 : (39161/50000 : ℝ) ^ (67/16 : ℝ) ≤ (7188996596099160277/20000000000000000000 : ℝ) := by
    have hpowers : (39161/50000 : ℝ)^67 ≤ (7188996596099160277/20000000000000000000 : ℝ)^16 := by
      have hnat : (39161 : ℕ)^67*20000000000000000000^16 ≤ 7188996596099160277^16*50000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        39161 50000 7188996596099160277 20000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (39161/50000 : ℝ)) (X := (7188996596099160277/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s3_corner1a : (27188996596099160277/20000000000000000000 : ℝ) ≤ (1345110422193679/1250000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (27188996596099160277/20000000000000000000 : ℝ)^16 ≤ (1345110422193679/1250000000000000 : ℝ)^67 := by
      have hnat : (27188996596099160277 : ℕ)^16*1250000000000000^67 ≤ 1345110422193679^67*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27188996596099160277 20000000000000000000 1345110422193679 1250000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1345110422193679/1250000000000000 : ℝ)) (X := (27188996596099160277/20000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s3_corner1b : (17188996596099160277/10000000000000000000 : ℝ) ≤ (5690484363691333/5000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (17188996596099160277/10000000000000000000 : ℝ)^16 ≤ (5690484363691333/5000000000000000 : ℝ)^67 := by
      have hnat : (17188996596099160277 : ℕ)^16*5000000000000000^67 ≤ 5690484363691333^67*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17188996596099160277 10000000000000000000 5690484363691333 5000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5690484363691333/5000000000000000 : ℝ)) (X := (17188996596099160277/10000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s3_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(95110422193679/979025000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(310042674916617/3916100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (39161/50000 : ℝ)) (alpha := (95110422193679/979025000000000 : ℝ)) (beta := (310042674916617/3916100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow1,s3_corner1a]) (by linarith only [s3_pow1,s3_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (39161/50000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(95110422193679/979025000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(310042674916617/3916100000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow2 : (19009/25000 : ℝ) ^ (67/16 : ℝ) ≤ (6350357211925638501/20000000000000000000 : ℝ) := by
    have hpowers : (19009/25000 : ℝ)^67 ≤ (6350357211925638501/20000000000000000000 : ℝ)^16 := by
      have hnat : (19009 : ℕ)^67*20000000000000000000^16 ≤ 6350357211925638501^16*25000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19009 25000 6350357211925638501 20000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19009/25000 : ℝ)) (X := (6350357211925638501/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s3_corner2a : (26350357211925638501/20000000000000000000 : ℝ) ≤ (267016794861249/250000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (26350357211925638501/20000000000000000000 : ℝ)^16 ≤ (267016794861249/250000000000000 : ℝ)^67 := by
      have hnat : (26350357211925638501 : ℕ)^16*250000000000000^67 ≤ 267016794861249^67*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26350357211925638501 20000000000000000000 267016794861249 250000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (267016794861249/250000000000000 : ℝ)) (X := (26350357211925638501/20000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s3_corner2b : (16350357211925638501/10000000000000000000 : ℝ) ≤ (5622915865465237/5000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (16350357211925638501/10000000000000000000 : ℝ)^16 ≤ (5622915865465237/5000000000000000 : ℝ)^67 := by
      have hnat : (16350357211925638501 : ℕ)^16*5000000000000000^67 ≤ 5622915865465237^67*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16350357211925638501 10000000000000000000 5622915865465237 5000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5622915865465237/5000000000000000 : ℝ)) (X := (16350357211925638501/10000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s3_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(17016794861249/190090000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(282579968240257/3801800000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (19009/25000 : ℝ)) (alpha := (17016794861249/190090000000000 : ℝ)) (beta := (282579968240257/3801800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow2,s3_corner2a]) (by linarith only [s3_pow2,s3_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (19009/25000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(17016794861249/190090000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(282579968240257/3801800000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s3_0 : ((-11385663/200000000 : ℝ)*X 0 0+(-6068965593/10000000000 : ℝ)*X 0 1+(5501689967/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306086_s3_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_2 : ((727794893/1250000000 : ℝ)*X 2 0+(-3633480931/10000000000 : ℝ)*X 2 1+(-67862861/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306086_s3_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_7 : ((-47950103/2500000000 : ℝ)*X 0 0+(-7187318919/10000000000 : ℝ)*X 0 1+(4447188721/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306086_s3_s3_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_8 : ((6082416519/10000000000 : ℝ)*X 1 0+(3389184859/10000000000 : ℝ)*X 1 1+(66603831/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306086_s3_s3_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_9 : ((6005843063/10000000000 : ℝ)*X 2 0+(-865094031/2500000000 : ℝ)*X 2 1+(-418813811/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306086_s3_s3_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_13 : ((1500318347/5000000000 : ℝ)*X 0 0+(-1588272641/10000000000 : ℝ)*X 0 1+(478111983/625000000 : ℝ)*X 0 2+(1500318347/5000000000 : ℝ)*X 1 0+(-1588272641/10000000000 : ℝ)*X 1 1+(478111983/625000000 : ℝ)*X 1 2+(1500318347/5000000000 : ℝ)*X 2 0+(-1588272641/10000000000 : ℝ)*X 2 1+(478111983/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306086_s3_s3_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_14 : ((-31369/400000000 : ℝ)*X 0 0+(-2877026391/5000000000 : ℝ)*X 0 1+(1507649583/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306086_s3_s3_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_15 : ((6812938167/10000000000 : ℝ)*X 1 0+(3102777429/10000000000 : ℝ)*X 1 1+(2697908093/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306086_s3_s3_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_16 : ((6393894841/10000000000 : ℝ)*X 2 0+(-870637351/2500000000 : ℝ)*X 2 1+(-569212013/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306086_s3_s3_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_20 : ((3316223777/10000000000 : ℝ)*X 0 0+(-2596985527/10000000000 : ℝ)*X 0 1+(839880541/1250000000 : ℝ)*X 0 2+(3316223777/10000000000 : ℝ)*X 1 0+(-2596985527/10000000000 : ℝ)*X 1 1+(839880541/1250000000 : ℝ)*X 1 2+(3316223777/10000000000 : ℝ)*X 2 0+(-2596985527/10000000000 : ℝ)*X 2 1+(839880541/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306086_s3_s3_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_21 : ((-3/400000000 : ℝ)*X 0 0+(-330560709/500000000 : ℝ)*X 0 1+(1286522237/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306086_s3_s3_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_22 : ((6813722247/10000000000 : ℝ)*X 1 0+(1511755147/5000000000 : ℝ)*X 1 1+(2778942857/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306086_s3_s3_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_23 : ((704927669/1250000000 : ℝ)*X 2 0+(-3826050891/10000000000 : ℝ)*X 2 1+(-3410107937/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306086_s3_s3_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_27 : ((4888334283/10000000000 : ℝ)*X 0 0+(-2788713511/10000000000 : ℝ)*X 0 1+(2584507261/5000000000 : ℝ)*X 0 2+(4888334283/10000000000 : ℝ)*X 1 0+(-2788713511/10000000000 : ℝ)*X 1 1+(2584507261/5000000000 : ℝ)*X 1 2+(4888334283/10000000000 : ℝ)*X 2 0+(-2788713511/10000000000 : ℝ)*X 2 1+(2584507261/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306086_s3_s3_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s3_0 : (0 : ℝ) ≤ ((12307/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(12307/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (37311937752256518303074359780023/4337015543018900000000000000000000000 : ℝ) := by norm_num
    linear_combination (310707285493/1000000000000 : ℝ)*(base40) + (368327/250000000000 : ℝ)*(base50) + (740189/200000000000 : ℝ)*(base60) + (3375854351377/1000000000000 : ℝ)*(major_s3_0) + (3375854351377/1000000000000 : ℝ)*(major_s3_1) + (3375854351377/1000000000000 : ℝ)*(major_s3_2) + (16231231/50000000000 : ℝ)*(sp_s3_2) + (2281082098477/500000000000 : ℝ)*(sp_s3_7) + (4562237043201/1000000000000 : ℝ)*(sp_s3_8) + (1140473220021/250000000000 : ℝ)*(sp_s3_9) + (2189443485301/1000000000000 : ℝ)*(sp_s3_13) + (9769249/500000000000 : ℝ)*(sp_s3_16) + (6326633/250000000000 : ℝ)*(sp_s3_20) + (72846247/1000000000000 : ℝ)*(sp_s3_21) + (1094734395917/500000000000 : ℝ)*(f.failure) + (4562237043201/1000000000000 : ℝ)*(f.sum) + (9390788269247184639/74441144900000000000000000000000 : ℝ)*base62 + (2849470556055509/3801800000000000000000000000 : ℝ)*base64 + (64713689246803/61189062500000000000000000 : ℝ)*base67 + (1824116234367/4752250000000000000000000 : ℝ)*base69 + (64034477089260549727/221496669800000000000000000000000 : ℝ)*base70 + (4633594431899691/5826100000000000000000000000 : ℝ)*base73 + (705172176001671/3916100000000000000000000000 : ℝ)*base74 + (374025189944191/5826100000000000000000000000 : ℝ)*base76 + (213761763927118783023/228155902100000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (4281/25000000000000000 : ℝ)*base87 + (4281/25000000000000000 : ℝ)*base89 + (4281/25000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s3_1 : (0 : ℝ) ≤ ((-53373/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-53373/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (25180450656792285292014866779143/4337015543018900000000000000000000000 : ℝ) := by norm_num
    linear_combination (322603/100000000000 : ℝ)*(base13) + (774145058969/500000000000 : ℝ)*(base40) + (301275699531/1000000000000 : ℝ)*(base60) + (6509496601089/1000000000000 : ℝ)*(major_s3_0) + (6509496601089/1000000000000 : ℝ)*(major_s3_1) + (6509496601089/1000000000000 : ℝ)*(major_s3_2) + (22636883/1000000000000 : ℝ)*(sp_s3_0) + (15572349/1000000000000 : ℝ)*(sp_s3_13) + (2199279668167/250000000000 : ℝ)*(sp_s3_14) + (8796844442089/1000000000000 : ℝ)*(sp_s3_15) + (8797144535581/1000000000000 : ℝ)*(sp_s3_16) + (4221819994351/1000000000000 : ℝ)*(sp_s3_20) + (75023373/250000000000 : ℝ)*(sp_s3_22) + (5582289/500000000000 : ℝ)*(sp_s3_27) + (4221846731279/1000000000000 : ℝ)*(f.failure) + (8797144535581/1000000000000 : ℝ)*(f.sum) + (34109319993228800497/74441144900000000000000000000000 : ℝ)*base63 + (488445609707147/3801800000000000000000000000 : ℝ)*base65 + (1038945549332697/1958050000000000000000000000 : ℝ)*base67 + (24114910899623/38018000000000000000000000 : ℝ)*base69 + (47068952770568462101/221496669800000000000000000000000 : ℝ)*base71 + (1547021627641597/5826100000000000000000000000 : ℝ)*base73 + (1493362904239833/3916100000000000000000000000 : ℝ)*base75 + (1137761538310617/5826100000000000000000000000 : ℝ)*base76 + (28836658060378660141/228155902100000000000000000000000 : ℝ)*base79 + (41947/50000000000000000 : ℝ)*base87 + (41947/50000000000000000 : ℝ)*base89 + (41947/50000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s3_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(44789/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(44789/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (13549706863234175905421019132381/1084253885754725000000000000000000000 : ℝ) := by norm_num
    linear_combination (2522707/500000000000 : ℝ)*(base39) + (1759265662017/1000000000000 : ℝ)*(base40) + (14169/31250000000 : ℝ)*(base50) + (6740816708931/1000000000000 : ℝ)*(major_s3_0) + (6740816708931/1000000000000 : ℝ)*(major_s3_1) + (6740816708931/1000000000000 : ℝ)*(major_s3_2) + (4116759/125000000000 : ℝ)*(sp_s3_0) + (128837559/1000000000000 : ℝ)*(sp_s3_2) + (3969563/50000000000 : ℝ)*(sp_s3_7) + (324555853/500000000000 : ℝ)*(sp_s3_15) + (9109643534443/1000000000000 : ℝ)*(sp_s3_21) + (2277276687017/250000000000 : ℝ)*(sp_s3_22) + (1821925404443/200000000000 : ℝ)*(sp_s3_23) + (4371873392481/1000000000000 : ℝ)*(sp_s3_27) + (4371873392481/1000000000000 : ℝ)*(f.failure) + (4554877929887/500000000000 : ℝ)*(f.sum) + (39026244796617828213/74441144900000000000000000000000 : ℝ)*base63 + (960735203954793/3801800000000000000000000000 : ℝ)*base65 + (144276690869419/244756250000000000000000000 : ℝ)*base66 + (7956351721543/19009000000000000000000000 : ℝ)*base69 + (9152349056905486721/221496669800000000000000000000000 : ℝ)*base70 + (3073537142544133/5826100000000000000000000000 : ℝ)*base73 + (3283305903615037/3916100000000000000000000000 : ℝ)*base75 + (2413978292145513/5826100000000000000000000000 : ℝ)*base76 + (62513469190965714841/228155902100000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (12267/50000000000000000 : ℝ)*base86 + (12267/50000000000000000 : ℝ)*base88 + (12267/50000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev2 : (0 : ℝ) ≤ ((58261/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(58261/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-39161/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-39161/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19009/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(19009/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((12307/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(12307/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-53373/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-53373/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(44789/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(44789/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c306086_s3 p hpa hpb X hX hprev2

#print axioms solution
