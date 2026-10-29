-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c325054_s0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:04:06.295153+00:00
-- url     : https://prove2.me/submissions/b0e6035d-31b8-4e8a-8f8d-2499b0084872

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
theorem collision_support_c325054_s0_s0_0 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2526937/10000000000 : ℝ)*x 0 + (4616395849/10000000000 : ℝ)*x 1 + (-3349726577/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2526937/10000000000 : ℝ)^87 ≤ (97690307/2500000000000 : ℝ)^71 := by
    have hnat : (2526937 : ℕ)^87*2500000000000^71 ≤ 97690307^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2526937 10000000000 97690307 2500000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4616395849/10000000000 : ℝ)^87 ≤ (2424002371863/6250000000000 : ℝ)^71 := by
    have hnat : (4616395849 : ℕ)^87*6250000000000^71 ≤ 2424002371863^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4616395849 10000000000 2424002371863 6250000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3349726577/5000000000 : ℝ)^87 ≤ (12242410884627/20000000000000 : ℝ)^71 := by
    have hnat : (3349726577 : ℕ)^87*20000000000000^71 ≤ 12242410884627^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3349726577 5000000000 12242410884627 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2526937/10000000000 : ℝ), (4616395849/10000000000 : ℝ), (-3349726577/5000000000 : ℝ)] ![(97690307/2500000000000 : ℝ), (2424002371863/6250000000000 : ℝ), (12242410884627/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2526937/10000000000 : ℝ)|^87 ≤ (97690307/2500000000000 : ℝ)^71
        have hw : |(-2526937/10000000000 : ℝ)|=(2526937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4616395849/10000000000 : ℝ)|^87 ≤ (2424002371863/6250000000000 : ℝ)^71
        have hw : |(4616395849/10000000000 : ℝ)|=(4616395849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3349726577/5000000000 : ℝ)|^87 ≤ (12242410884627/20000000000000 : ℝ)^71
        have hw : |(-3349726577/5000000000 : ℝ)|=(3349726577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325054_s0_s0_1 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (719693111/1250000000 : ℝ)*x 0 + (-571837921/5000000000 : ℝ)*x 1 + (-4940252193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (719693111/1250000000 : ℝ)^87 ≤ (25420044896577/50000000000000 : ℝ)^71 := by
    have hnat : (719693111 : ℕ)^87*50000000000000^71 ≤ 25420044896577^71*1250000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      719693111 1250000000 25420044896577 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (571837921/5000000000 : ℝ)^87 ≤ (3507999571277/50000000000000 : ℝ)^71 := by
    have hnat : (571837921 : ℕ)^87*50000000000000^71 ≤ 3507999571277^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      571837921 5000000000 3507999571277 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4940252193/10000000000 : ℝ)^87 ≤ (42143911056391/100000000000000 : ℝ)^71 := by
    have hnat : (4940252193 : ℕ)^87*100000000000000^71 ≤ 42143911056391^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4940252193 10000000000 42143911056391 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(719693111/1250000000 : ℝ), (-571837921/5000000000 : ℝ), (-4940252193/10000000000 : ℝ)] ![(25420044896577/50000000000000 : ℝ), (3507999571277/50000000000000 : ℝ), (42143911056391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(719693111/1250000000 : ℝ)|^87 ≤ (25420044896577/50000000000000 : ℝ)^71
        have hw : |(719693111/1250000000 : ℝ)|=(719693111/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-571837921/5000000000 : ℝ)|^87 ≤ (3507999571277/50000000000000 : ℝ)^71
        have hw : |(-571837921/5000000000 : ℝ)|=(571837921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4940252193/10000000000 : ℝ)|^87 ≤ (42143911056391/100000000000000 : ℝ)^71
        have hw : |(-4940252193/10000000000 : ℝ)|=(4940252193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325054_s0_s0_2 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (107019219/200000000 : ℝ)*x 0 + (133774029/250000000 : ℝ)*x 1 + (1147800941/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107019219/200000000 : ℝ)^87 ≤ (23238244360707/50000000000000 : ℝ)^71 := by
    have hnat : (107019219 : ℕ)^87*50000000000000^71 ≤ 23238244360707^71*200000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107019219 200000000 23238244360707 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (133774029/250000000 : ℝ)^87 ≤ (9295298191287/20000000000000 : ℝ)^71 := by
    have hnat : (133774029 : ℕ)^87*20000000000000^71 ≤ 9295298191287^71*250000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133774029 250000000 9295298191287 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1147800941/10000000000 : ℝ)^87 ≤ (7047020311619/100000000000000 : ℝ)^71 := by
    have hnat : (1147800941 : ℕ)^87*100000000000000^71 ≤ 7047020311619^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1147800941 10000000000 7047020311619 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(107019219/200000000 : ℝ), (133774029/250000000 : ℝ), (1147800941/10000000000 : ℝ)] ![(23238244360707/50000000000000 : ℝ), (9295298191287/20000000000000 : ℝ), (7047020311619/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(107019219/200000000 : ℝ)|^87 ≤ (23238244360707/50000000000000 : ℝ)^71
        have hw : |(107019219/200000000 : ℝ)|=(107019219/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(133774029/250000000 : ℝ)|^87 ≤ (9295298191287/20000000000000 : ℝ)^71
        have hw : |(133774029/250000000 : ℝ)|=(133774029/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1147800941/10000000000 : ℝ)|^87 ≤ (7047020311619/100000000000000 : ℝ)^71
        have hw : |(1147800941/10000000000 : ℝ)|=(1147800941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325054_s0_s0_7 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-385062457/10000000000 : ℝ)*x 0 + (1051737737/10000000000 : ℝ)*x 1 + (-9327277871/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (385062457/10000000000 : ℝ)^87 ≤ (57760063483/3125000000000 : ℝ)^71 := by
    have hnat : (385062457 : ℕ)^87*3125000000000^71 ≤ 57760063483^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      385062457 10000000000 57760063483 3125000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1051737737/10000000000 : ℝ)^87 ≤ (3165645214841/50000000000000 : ℝ)^71 := by
    have hnat : (1051737737 : ℕ)^87*50000000000000^71 ≤ 3165645214841^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051737737 10000000000 3165645214841 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9327277871/10000000000 : ℝ)^87 ≤ (18364077504271/20000000000000 : ℝ)^71 := by
    have hnat : (9327277871 : ℕ)^87*20000000000000^71 ≤ 18364077504271^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9327277871 10000000000 18364077504271 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-385062457/10000000000 : ℝ), (1051737737/10000000000 : ℝ), (-9327277871/10000000000 : ℝ)] ![(57760063483/3125000000000 : ℝ), (3165645214841/50000000000000 : ℝ), (18364077504271/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-385062457/10000000000 : ℝ)|^87 ≤ (57760063483/3125000000000 : ℝ)^71
        have hw : |(-385062457/10000000000 : ℝ)|=(385062457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1051737737/10000000000 : ℝ)|^87 ≤ (3165645214841/50000000000000 : ℝ)^71
        have hw : |(1051737737/10000000000 : ℝ)|=(1051737737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-9327277871/10000000000 : ℝ)|^87 ≤ (18364077504271/20000000000000 : ℝ)^71
        have hw : |(-9327277871/10000000000 : ℝ)|=(9327277871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325054_s0_s0_8 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (811931493/2500000000 : ℝ)*x 0 + (-198847943/5000000000 : ℝ)*x 1 + (-965472753/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (811931493/2500000000 : ℝ)^87 ≤ (25206512343383/100000000000000 : ℝ)^71 := by
    have hnat : (811931493 : ℕ)^87*100000000000000^71 ≤ 25206512343383^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      811931493 2500000000 25206512343383 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (198847943/5000000000 : ℝ)^87 ≤ (192290124111/10000000000000 : ℝ)^71 := by
    have hnat : (198847943 : ℕ)^87*10000000000000^71 ≤ 192290124111^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      198847943 5000000000 192290124111 10000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (965472753/1250000000 : ℝ)^87 ≤ (7287058640541/10000000000000 : ℝ)^71 := by
    have hnat : (965472753 : ℕ)^87*10000000000000^71 ≤ 7287058640541^71*1250000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      965472753 1250000000 7287058640541 10000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(811931493/2500000000 : ℝ), (-198847943/5000000000 : ℝ), (-965472753/1250000000 : ℝ)] ![(25206512343383/100000000000000 : ℝ), (192290124111/10000000000000 : ℝ), (7287058640541/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(811931493/2500000000 : ℝ)|^87 ≤ (25206512343383/100000000000000 : ℝ)^71
        have hw : |(811931493/2500000000 : ℝ)|=(811931493/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-198847943/5000000000 : ℝ)|^87 ≤ (192290124111/10000000000000 : ℝ)^71
        have hw : |(-198847943/5000000000 : ℝ)|=(198847943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-965472753/1250000000 : ℝ)|^87 ≤ (7287058640541/10000000000000 : ℝ)^71
        have hw : |(-965472753/1250000000 : ℝ)|=(965472753/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325054_s0_s0_9 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1426003601/5000000000 : ℝ)*x 0 + (8068653607/10000000000 : ℝ)*x 1 + (346848707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1426003601/5000000000 : ℝ)^87 ≤ (1343530951371/6250000000000 : ℝ)^71 := by
    have hnat : (1426003601 : ℕ)^87*6250000000000^71 ≤ 1343530951371^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1426003601 5000000000 1343530951371 6250000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8068653607/10000000000 : ℝ)^87 ≤ (38438683075601/50000000000000 : ℝ)^71 := by
    have hnat : (8068653607 : ℕ)^87*50000000000000^71 ≤ 38438683075601^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8068653607 10000000000 38438683075601 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (346848707/10000000000 : ℝ)^87 ≤ (1626138614079/100000000000000 : ℝ)^71 := by
    have hnat : (346848707 : ℕ)^87*100000000000000^71 ≤ 1626138614079^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      346848707 10000000000 1626138614079 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1426003601/5000000000 : ℝ), (8068653607/10000000000 : ℝ), (346848707/10000000000 : ℝ)] ![(1343530951371/6250000000000 : ℝ), (38438683075601/50000000000000 : ℝ), (1626138614079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1426003601/5000000000 : ℝ)|^87 ≤ (1343530951371/6250000000000 : ℝ)^71
        have hw : |(1426003601/5000000000 : ℝ)|=(1426003601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8068653607/10000000000 : ℝ)|^87 ≤ (38438683075601/50000000000000 : ℝ)^71
        have hw : |(8068653607/10000000000 : ℝ)|=(8068653607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(346848707/10000000000 : ℝ)|^87 ≤ (1626138614079/100000000000000 : ℝ)^71
        have hw : |(346848707/10000000000 : ℝ)|=(346848707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325054_s0_s0_13 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3111919463/10000000000 : ℝ)*x 0 + (1966954973/2500000000 : ℝ)*x 1 + (-165859479/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3111919463/10000000000 : ℝ)^87 ≤ (23921103833679/100000000000000 : ℝ)^71 := by
    have hnat : (3111919463 : ℕ)^87*100000000000000^71 ≤ 23921103833679^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3111919463 10000000000 23921103833679 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1966954973/2500000000 : ℝ)^87 ≤ (74539243501849/100000000000000 : ℝ)^71 := by
    have hnat : (1966954973 : ℕ)^87*100000000000000^71 ≤ 74539243501849^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1966954973 2500000000 74539243501849 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (165859479/5000000000 : ℝ)^87 ≤ (769826323159/50000000000000 : ℝ)^71 := by
    have hnat : (165859479 : ℕ)^87*50000000000000^71 ≤ 769826323159^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165859479 5000000000 769826323159 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3111919463/10000000000 : ℝ), (1966954973/2500000000 : ℝ), (-165859479/5000000000 : ℝ)] ![(23921103833679/100000000000000 : ℝ), (74539243501849/100000000000000 : ℝ), (769826323159/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3111919463/10000000000 : ℝ)|^87 ≤ (23921103833679/100000000000000 : ℝ)^71
        have hw : |(3111919463/10000000000 : ℝ)|=(3111919463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1966954973/2500000000 : ℝ)|^87 ≤ (74539243501849/100000000000000 : ℝ)^71
        have hw : |(1966954973/2500000000 : ℝ)|=(1966954973/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-165859479/5000000000 : ℝ)|^87 ≤ (769826323159/50000000000000 : ℝ)^71
        have hw : |(-165859479/5000000000 : ℝ)|=(165859479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325054_s0_s0_14 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3137/10000000000 : ℝ)*x 0 + (887982539/5000000000 : ℝ)*x 1 + (-2251691409/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3137/10000000000 : ℝ)^87 ≤ (536921/50000000000000 : ℝ)^71 := by
    have hnat : (3137 : ℕ)^87*50000000000000^71 ≤ 536921^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3137 10000000000 536921 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (887982539/5000000000 : ℝ)^87 ≤ (3007688751553/25000000000000 : ℝ)^71 := by
    have hnat : (887982539 : ℕ)^87*25000000000000^71 ≤ 3007688751553^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      887982539 5000000000 3007688751553 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2251691409/2500000000 : ℝ)^87 ≤ (21992310978437/25000000000000 : ℝ)^71 := by
    have hnat : (2251691409 : ℕ)^87*25000000000000^71 ≤ 21992310978437^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251691409 2500000000 21992310978437 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3137/10000000000 : ℝ), (887982539/5000000000 : ℝ), (-2251691409/2500000000 : ℝ)] ![(536921/50000000000000 : ℝ), (3007688751553/25000000000000 : ℝ), (21992310978437/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3137/10000000000 : ℝ)|^87 ≤ (536921/50000000000000 : ℝ)^71
        have hw : |(-3137/10000000000 : ℝ)|=(3137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(887982539/5000000000 : ℝ)|^87 ≤ (3007688751553/25000000000000 : ℝ)^71
        have hw : |(887982539/5000000000 : ℝ)|=(887982539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2251691409/2500000000 : ℝ)|^87 ≤ (21992310978437/25000000000000 : ℝ)^71
        have hw : |(-2251691409/2500000000 : ℝ)|=(2251691409/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325054_s0_s0_15 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (505420071/2500000000 : ℝ)*x 0 + (-703925609/2000000000 : ℝ)*x 1 + (-6418595561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (505420071/2500000000 : ℝ)^87 ≤ (14101110483937/100000000000000 : ℝ)^71 := by
    have hnat : (505420071 : ℕ)^87*100000000000000^71 ≤ 14101110483937^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      505420071 2500000000 14101110483937 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (703925609/2000000000 : ℝ)^87 ≤ (1112650711091/4000000000000 : ℝ)^71 := by
    have hnat : (703925609 : ℕ)^87*4000000000000^71 ≤ 1112650711091^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      703925609 2000000000 1112650711091 4000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6418595561/10000000000 : ℝ)^87 ≤ (58082621715713/100000000000000 : ℝ)^71 := by
    have hnat : (6418595561 : ℕ)^87*100000000000000^71 ≤ 58082621715713^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6418595561 10000000000 58082621715713 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(505420071/2500000000 : ℝ), (-703925609/2000000000 : ℝ), (-6418595561/10000000000 : ℝ)] ![(14101110483937/100000000000000 : ℝ), (1112650711091/4000000000000 : ℝ), (58082621715713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(505420071/2500000000 : ℝ)|^87 ≤ (14101110483937/100000000000000 : ℝ)^71
        have hw : |(505420071/2500000000 : ℝ)|=(505420071/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-703925609/2000000000 : ℝ)|^87 ≤ (1112650711091/4000000000000 : ℝ)^71
        have hw : |(-703925609/2000000000 : ℝ)|=(703925609/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6418595561/10000000000 : ℝ)|^87 ≤ (58082621715713/100000000000000 : ℝ)^71
        have hw : |(-6418595561/10000000000 : ℝ)|=(6418595561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325054_s0_s0_16 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1625691523/2000000000 : ℝ)*x 0 + (2376436373/10000000000 : ℝ)*x 1 + (450165381/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1625691523/2000000000 : ℝ)^87 ≤ (15515232450933/20000000000000 : ℝ)^71 := by
    have hnat : (1625691523 : ℕ)^87*20000000000000^71 ≤ 15515232450933^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1625691523 2000000000 15515232450933 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2376436373/10000000000 : ℝ)^87 ≤ (2148819085099/12500000000000 : ℝ)^71 := by
    have hnat : (2376436373 : ℕ)^87*12500000000000^71 ≤ 2148819085099^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2376436373 10000000000 2148819085099 12500000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (450165381/5000000000 : ℝ)^87 ≤ (5233285051029/100000000000000 : ℝ)^71 := by
    have hnat : (450165381 : ℕ)^87*100000000000000^71 ≤ 5233285051029^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450165381 5000000000 5233285051029 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1625691523/2000000000 : ℝ), (2376436373/10000000000 : ℝ), (450165381/5000000000 : ℝ)] ![(15515232450933/20000000000000 : ℝ), (2148819085099/12500000000000 : ℝ), (5233285051029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1625691523/2000000000 : ℝ)|^87 ≤ (15515232450933/20000000000000 : ℝ)^71
        have hw : |(1625691523/2000000000 : ℝ)|=(1625691523/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2376436373/10000000000 : ℝ)|^87 ≤ (2148819085099/12500000000000 : ℝ)^71
        have hw : |(2376436373/10000000000 : ℝ)|=(2376436373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(450165381/5000000000 : ℝ)|^87 ≤ (5233285051029/100000000000000 : ℝ)^71
        have hw : |(450165381/5000000000 : ℝ)|=(450165381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325054_s0_s0_20 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3843537851/5000000000 : ℝ)*x 0 + (3059991441/10000000000 : ℝ)*x 1 + (-148153811/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3843537851/5000000000 : ℝ)^87 ≤ (18111616022067/25000000000000 : ℝ)^71 := by
    have hnat : (3843537851 : ℕ)^87*25000000000000^71 ≤ 18111616022067^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3843537851 5000000000 18111616022067 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3059991441/10000000000 : ℝ)^87 ≤ (23432907325333/100000000000000 : ℝ)^71 := by
    have hnat : (3059991441 : ℕ)^87*100000000000000^71 ≤ 23432907325333^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3059991441 10000000000 23432907325333 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (148153811/2000000000 : ℝ)^87 ≤ (4120628575359/100000000000000 : ℝ)^71 := by
    have hnat : (148153811 : ℕ)^87*100000000000000^71 ≤ 4120628575359^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      148153811 2000000000 4120628575359 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3843537851/5000000000 : ℝ), (3059991441/10000000000 : ℝ), (-148153811/2000000000 : ℝ)] ![(18111616022067/25000000000000 : ℝ), (23432907325333/100000000000000 : ℝ), (4120628575359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3843537851/5000000000 : ℝ)|^87 ≤ (18111616022067/25000000000000 : ℝ)^71
        have hw : |(3843537851/5000000000 : ℝ)|=(3843537851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3059991441/10000000000 : ℝ)|^87 ≤ (23432907325333/100000000000000 : ℝ)^71
        have hw : |(3059991441/10000000000 : ℝ)|=(3059991441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-148153811/2000000000 : ℝ)|^87 ≤ (4120628575359/100000000000000 : ℝ)^71
        have hw : |(-148153811/2000000000 : ℝ)|=(148153811/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325054_s0_s0_21 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (18011/1000000000 : ℝ)*x 0 + (6617212257/10000000000 : ℝ)*x 1 + (-4705882671/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (18011/1000000000 : ℝ)^87 ≤ (153590111/100000000000000 : ℝ)^71 := by
    have hnat : (18011 : ℕ)^87*100000000000000^71 ≤ 153590111^71*1000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18011 1000000000 153590111 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6617212257/10000000000 : ℝ)^87 ≤ (30146286138311/50000000000000 : ℝ)^71 := by
    have hnat : (6617212257 : ℕ)^87*50000000000000^71 ≤ 30146286138311^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6617212257 10000000000 30146286138311 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4705882671/10000000000 : ℝ)^87 ≤ (19853637063493/50000000000000 : ℝ)^71 := by
    have hnat : (4705882671 : ℕ)^87*50000000000000^71 ≤ 19853637063493^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4705882671 10000000000 19853637063493 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(18011/1000000000 : ℝ), (6617212257/10000000000 : ℝ), (-4705882671/10000000000 : ℝ)] ![(153590111/100000000000000 : ℝ), (30146286138311/50000000000000 : ℝ), (19853637063493/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(18011/1000000000 : ℝ)|^87 ≤ (153590111/100000000000000 : ℝ)^71
        have hw : |(18011/1000000000 : ℝ)|=(18011/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6617212257/10000000000 : ℝ)|^87 ≤ (30146286138311/50000000000000 : ℝ)^71
        have hw : |(6617212257/10000000000 : ℝ)|=(6617212257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4705882671/10000000000 : ℝ)|^87 ≤ (19853637063493/50000000000000 : ℝ)^71
        have hw : |(-4705882671/10000000000 : ℝ)|=(4705882671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325054_s0_s0_22 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8236303597/10000000000 : ℝ)*x 0 + (-809455523/5000000000 : ℝ)*x 1 + (-1579437579/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8236303597/10000000000 : ℝ)^87 ≤ (15767848868071/20000000000000 : ℝ)^71 := by
    have hnat : (8236303597 : ℕ)^87*20000000000000^71 ≤ 15767848868071^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8236303597 10000000000 15767848868071 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (809455523/5000000000 : ℝ)^87 ≤ (10740381692343/100000000000000 : ℝ)^71 := by
    have hnat : (809455523 : ℕ)^87*100000000000000^71 ≤ 10740381692343^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      809455523 5000000000 10740381692343 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1579437579/10000000000 : ℝ)^87 ≤ (5210186973637/50000000000000 : ℝ)^71 := by
    have hnat : (1579437579 : ℕ)^87*50000000000000^71 ≤ 5210186973637^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1579437579 10000000000 5210186973637 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8236303597/10000000000 : ℝ), (-809455523/5000000000 : ℝ), (-1579437579/10000000000 : ℝ)] ![(15767848868071/20000000000000 : ℝ), (10740381692343/100000000000000 : ℝ), (5210186973637/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8236303597/10000000000 : ℝ)|^87 ≤ (15767848868071/20000000000000 : ℝ)^71
        have hw : |(8236303597/10000000000 : ℝ)|=(8236303597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-809455523/5000000000 : ℝ)|^87 ≤ (10740381692343/100000000000000 : ℝ)^71
        have hw : |(-809455523/5000000000 : ℝ)|=(809455523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1579437579/10000000000 : ℝ)|^87 ≤ (5210186973637/50000000000000 : ℝ)^71
        have hw : |(-1579437579/10000000000 : ℝ)|=(1579437579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325054_s0_s0_23 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1580961489/10000000000 : ℝ)*x 0 + (3543090473/5000000000 : ℝ)*x 1 + (1560026481/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1580961489/10000000000 : ℝ)^87 ≤ (10432695012603/100000000000000 : ℝ)^71 := by
    have hnat : (1580961489 : ℕ)^87*100000000000000^71 ≤ 10432695012603^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1580961489 10000000000 10432695012603 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3543090473/5000000000 : ℝ)^87 ≤ (65569567589973/100000000000000 : ℝ)^71 := by
    have hnat : (3543090473 : ℕ)^87*100000000000000^71 ≤ 65569567589973^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3543090473 5000000000 65569567589973 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1560026481/5000000000 : ℝ)^87 ≤ (2999717173793/12500000000000 : ℝ)^71 := by
    have hnat : (1560026481 : ℕ)^87*12500000000000^71 ≤ 2999717173793^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1560026481 5000000000 2999717173793 12500000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1580961489/10000000000 : ℝ), (3543090473/5000000000 : ℝ), (1560026481/5000000000 : ℝ)] ![(10432695012603/100000000000000 : ℝ), (65569567589973/100000000000000 : ℝ), (2999717173793/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1580961489/10000000000 : ℝ)|^87 ≤ (10432695012603/100000000000000 : ℝ)^71
        have hw : |(1580961489/10000000000 : ℝ)|=(1580961489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3543090473/5000000000 : ℝ)|^87 ≤ (65569567589973/100000000000000 : ℝ)^71
        have hw : |(3543090473/5000000000 : ℝ)|=(3543090473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1560026481/5000000000 : ℝ)|^87 ≤ (2999717173793/12500000000000 : ℝ)^71
        have hw : |(1560026481/5000000000 : ℝ)|=(1560026481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325054_s0_s0_27 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3669050943/5000000000 : ℝ)*x 0 + (3004800031/10000000000 : ℝ)*x 1 + (-271268831/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3669050943/5000000000 : ℝ)^87 ≤ (68437281300553/100000000000000 : ℝ)^71 := by
    have hnat : (3669050943 : ℕ)^87*100000000000000^71 ≤ 68437281300553^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3669050943 5000000000 68437281300553 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3004800031/10000000000 : ℝ)^87 ≤ (2291607377357/10000000000000 : ℝ)^71 := by
    have hnat : (3004800031 : ℕ)^87*10000000000000^71 ≤ 2291607377357^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3004800031 10000000000 2291607377357 10000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (271268831/2000000000 : ℝ)^87 ≤ (4323322454177/50000000000000 : ℝ)^71 := by
    have hnat : (271268831 : ℕ)^87*50000000000000^71 ≤ 4323322454177^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271268831 2000000000 4323322454177 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3669050943/5000000000 : ℝ), (3004800031/10000000000 : ℝ), (-271268831/2000000000 : ℝ)] ![(68437281300553/100000000000000 : ℝ), (2291607377357/10000000000000 : ℝ), (4323322454177/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3669050943/5000000000 : ℝ)|^87 ≤ (68437281300553/100000000000000 : ℝ)^71
        have hw : |(3669050943/5000000000 : ℝ)|=(3669050943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3004800031/10000000000 : ℝ)|^87 ≤ (2291607377357/10000000000000 : ℝ)^71
        have hw : |(3004800031/10000000000 : ℝ)|=(3004800031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-271268831/2000000000 : ℝ)|^87 ≤ (4323322454177/50000000000000 : ℝ)^71
        have hw : |(-271268831/2000000000 : ℝ)|=(271268831/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c325054_s0 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (200939/100000 : ℝ) (33069/20000 : ℝ) (81317/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]]) : (0 : ℝ) ≤ ((16177/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16177/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2729/4000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2729/4000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-60187/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-60187/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (81317/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (81317/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (81317/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (81317/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (81317/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (81317/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (33069/20000 : ℝ) := by
    linarith only [f.Tcap]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
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
  have s0_pow0 : (1 : ℝ) ^ (85/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^85 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^85*1^16 ≤ 1^16*1^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11393691857257931/10000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11393691857257931/10000000000000000 : ℝ)^85 := by
      have hnat : (2 : ℕ)^16*10000000000000000^85 ≤ 11393691857257931^85*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11393691857257931 10000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11393691857257931/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (6148668287254881/5000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (6148668287254881/5000000000000000 : ℝ)^85 := by
      have hnat : (3 : ℕ)^16*5000000000000000^85 ≤ 6148668287254881^85*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6148668287254881 5000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6148668287254881/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1393691857257931/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(903644717251831/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1393691857257931/10000000000000000 : ℝ)) (beta := (903644717251831/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1393691857257931/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(903644717251831/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (85/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^85 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^85*1^16 ≤ 1^16*1^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11393691857257931/10000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11393691857257931/10000000000000000 : ℝ)^85 := by
      have hnat : (2 : ℕ)^16*10000000000000000^85 ≤ 11393691857257931^85*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11393691857257931 10000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11393691857257931/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (6148668287254881/5000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (6148668287254881/5000000000000000 : ℝ)^85 := by
      have hnat : (3 : ℕ)^16*5000000000000000^85 ≤ 6148668287254881^85*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6148668287254881 5000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6148668287254881/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1393691857257931/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(903644717251831/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1393691857257931/10000000000000000 : ℝ)) (beta := (903644717251831/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1393691857257931/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(903644717251831/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (85/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^85 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^85*1^16 ≤ 1^16*1^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11393691857257931/10000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11393691857257931/10000000000000000 : ℝ)^85 := by
      have hnat : (2 : ℕ)^16*10000000000000000^85 ≤ 11393691857257931^85*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11393691857257931 10000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11393691857257931/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (6148668287254881/5000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (6148668287254881/5000000000000000 : ℝ)^85 := by
      have hnat : (3 : ℕ)^16*5000000000000000^85 ≤ 6148668287254881^85*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6148668287254881 5000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6148668287254881/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1393691857257931/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(903644717251831/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1393691857257931/10000000000000000 : ℝ)) (beta := (903644717251831/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1393691857257931/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(903644717251831/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-2526937/10000000000 : ℝ)*X 0 0+(4616395849/10000000000 : ℝ)*X 0 1+(-3349726577/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325054_s0_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((719693111/1250000000 : ℝ)*X 1 0+(-571837921/5000000000 : ℝ)*X 1 1+(-4940252193/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325054_s0_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((107019219/200000000 : ℝ)*X 2 0+(133774029/250000000 : ℝ)*X 2 1+(1147800941/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325054_s0_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-385062457/10000000000 : ℝ)*X 0 0+(1051737737/10000000000 : ℝ)*X 0 1+(-9327277871/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325054_s0_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((811931493/2500000000 : ℝ)*X 1 0+(-198847943/5000000000 : ℝ)*X 1 1+(-965472753/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325054_s0_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((1426003601/5000000000 : ℝ)*X 2 0+(8068653607/10000000000 : ℝ)*X 2 1+(346848707/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325054_s0_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((3111919463/10000000000 : ℝ)*X 0 0+(1966954973/2500000000 : ℝ)*X 0 1+(-165859479/5000000000 : ℝ)*X 0 2+(3111919463/10000000000 : ℝ)*X 1 0+(1966954973/2500000000 : ℝ)*X 1 1+(-165859479/5000000000 : ℝ)*X 1 2+(3111919463/10000000000 : ℝ)*X 2 0+(1966954973/2500000000 : ℝ)*X 2 1+(-165859479/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325054_s0_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-3137/10000000000 : ℝ)*X 0 0+(887982539/5000000000 : ℝ)*X 0 1+(-2251691409/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325054_s0_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((505420071/2500000000 : ℝ)*X 1 0+(-703925609/2000000000 : ℝ)*X 1 1+(-6418595561/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325054_s0_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((1625691523/2000000000 : ℝ)*X 2 0+(2376436373/10000000000 : ℝ)*X 2 1+(450165381/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325054_s0_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((3843537851/5000000000 : ℝ)*X 0 0+(3059991441/10000000000 : ℝ)*X 0 1+(-148153811/2000000000 : ℝ)*X 0 2+(3843537851/5000000000 : ℝ)*X 1 0+(3059991441/10000000000 : ℝ)*X 1 1+(-148153811/2000000000 : ℝ)*X 1 2+(3843537851/5000000000 : ℝ)*X 2 0+(3059991441/10000000000 : ℝ)*X 2 1+(-148153811/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325054_s0_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((18011/1000000000 : ℝ)*X 0 0+(6617212257/10000000000 : ℝ)*X 0 1+(-4705882671/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325054_s0_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((8236303597/10000000000 : ℝ)*X 1 0+(-809455523/5000000000 : ℝ)*X 1 1+(-1579437579/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325054_s0_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((1580961489/10000000000 : ℝ)*X 2 0+(3543090473/5000000000 : ℝ)*X 2 1+(1560026481/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325054_s0_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((3669050943/5000000000 : ℝ)*X 0 0+(3004800031/10000000000 : ℝ)*X 0 1+(-271268831/2000000000 : ℝ)*X 0 2+(3669050943/5000000000 : ℝ)*X 1 0+(3004800031/10000000000 : ℝ)*X 1 1+(-271268831/2000000000 : ℝ)*X 1 2+(3669050943/5000000000 : ℝ)*X 2 0+(3004800031/10000000000 : ℝ)*X 2 1+(-271268831/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325054_s0_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((16177/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16177/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (28686493304688272310141/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (244108034953/250000000000 : ℝ)*(base7) + (518637/1000000000000 : ℝ)*(base39) + (1663889/125000000000 : ℝ)*(base53) + (31984292291/500000000000 : ℝ)*(base60) + (717091559737/500000000000 : ℝ)*(major_s0_0) + (717091559737/500000000000 : ℝ)*(major_s0_1) + (717084904181/500000000000 : ℝ)*(major_s0_2) + (18831837/1000000000000 : ℝ)*(sp_s0_1) + (1616348999757/1000000000000 : ℝ)*(sp_s0_7) + (323285697131/200000000000 : ℝ)*(sp_s0_8) + (1616461292357/1000000000000 : ℝ)*(sp_s0_9) + (1690172687677/1000000000000 : ℝ)*(sp_s0_13) + (6186343/62500000000 : ℝ)*(sp_s0_14) + (663753/1000000000000 : ℝ)*(sp_s0_15) + (142748109573/200000000000 : ℝ)*(f.failure) + (1616461292357/1000000000000 : ℝ)*(f.sum) + (82540958916829/2500000000000000000000000000 : ℝ)*base63 + (2254468146694589/5000000000000000000000000000 : ℝ)*base64 + (1505608131371553/5000000000000000000000000000 : ℝ)*base67 + (316363427809511/5000000000000000000000000000 : ℝ)*base69 + (1301217736085221/2500000000000000000000000000 : ℝ)*base70 + (216651639128447/5000000000000000000000000000 : ℝ)*base73 + (887951578975853/5000000000000000000000000000 : ℝ)*base74 + (2350621587975853/5000000000000000000000000000 : ℝ)*base76 + (3300551833/10000000000000000000000 : ℝ)*base78 + (9047/20000000000000000 : ℝ)*base87 + (9047/20000000000000000 : ℝ)*base89 + (9047/20000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2729/4000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2729/4000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (14890683243036785170317/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1105601161273/1000000000000 : ℝ)*(base7) + (508217046649/1000000000000 : ℝ)*(base53) + (16253937589/250000000000 : ℝ)*(base60) + (1389943697081/1000000000000 : ℝ)*(major_s0_0) + (1389943697081/1000000000000 : ℝ)*(major_s0_1) + (881726650431/1000000000000 : ℝ)*(major_s0_2) + (4886131/1000000000000 : ℝ)*(sp_s0_0) + (469057/50000000000 : ℝ)*(sp_s0_1) + (18595637/1000000000000 : ℝ)*(sp_s0_8) + (970585207083/1000000000000 : ℝ)*(sp_s0_14) + (485281058219/500000000000 : ℝ)*(sp_s0_15) + (184850892483/125000000000 : ℝ)*(sp_s0_16) + (898652490923/500000000000 : ℝ)*(sp_s0_20) + (1273927/62500000000 : ℝ)*(sp_s0_27) + (138344840681/200000000000 : ℝ)*(f.failure) + (184850892483/125000000000 : ℝ)*(f.sum) + (578714657764709/1250000000000000000000000000 : ℝ)*base63 + (4806861560689161/10000000000000000000000000000 : ℝ)*base65 + (21247195394689/10000000000000000000000000000 : ℝ)*base67 + (5197645119318261/10000000000000000000000000000 : ℝ)*base69 + (628572343622143/2500000000000000000000000000 : ℝ)*base71 + (6579205772605311/10000000000000000000000000000 : ℝ)*base73 + (4994145744799411/10000000000000000000000000000 : ℝ)*base75 + (4220215998799411/10000000000000000000000000000 : ℝ)*base77 + (448286939/5000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (20541/20000000000000000 : ℝ)*base86 + (20541/20000000000000000 : ℝ)*base88 + (541/20000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-60187/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-60187/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (27922037180465225396439/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (119330384769/100000000000 : ℝ)*(base7) + (3776099/500000000000 : ℝ)*(base15) + (20988965821/100000000000 : ℝ)*(base39) + (5406401/1000000000000 : ℝ)*(base43) + (1437924629049/1000000000000 : ℝ)*(major_s0_0) + (179739902831/125000000000 : ℝ)*(major_s0_1) + (1437924629049/1000000000000 : ℝ)*(major_s0_2) + (3102549/1000000000000 : ℝ)*(sp_s0_2) + (834459/100000000000 : ℝ)*(sp_s0_9) + (1419931/25000000000 : ℝ)*(sp_s0_20) + (375637038149/250000000000 : ℝ)*(sp_s0_21) + (1502546006799/1000000000000 : ℝ)*(sp_s0_22) + (751268352729/500000000000 : ℝ)*(sp_s0_23) + (1908849610953/1000000000000 : ℝ)*(sp_s0_27) + (715602560503/1000000000000 : ℝ)*(f.failure) + (751276779499/500000000000 : ℝ)*(f.sum) + (490473556941093/10000000000000000000000000000 : ℝ)*base62 + (1285249836038719/10000000000000000000000000000 : ℝ)*base65 + (222801932041439/1250000000000000000000000000 : ℝ)*base67 + (1511915647237619/10000000000000000000000000000 : ℝ)*base69 + (721343874861831/5000000000000000000000000000 : ℝ)*base70 + (915381072961281/10000000000000000000000000000 : ℝ)*base72 + (788125647147339/1250000000000000000000000000 : ℝ)*base74 + (5454707132762381/10000000000000000000000000000 : ℝ)*base76 + (3238177403629769/10000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (12317/100000000000000000 : ℝ)*base87 + (12317/100000000000000000 : ℝ)*base89 + (12317/100000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (200939/100000 : ℝ) (33069/20000 : ℝ) (81317/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]]) : (0 : ℝ) ≤ ((16177/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16177/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2729/4000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2729/4000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-60187/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-60187/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c325054_s0 p hpa hpb X hX

#print axioms solution
