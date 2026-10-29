-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c325055_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:04:38.584988+00:00
-- url     : https://prove2.me/submissions/6c6e76c1-9cdf-417d-be2a-8aab85625485

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
theorem collision_support_c325055_s2_s2_0 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-97901487/500000000 : ℝ)*x 0 + (1081730981/2000000000 : ℝ)*x 1 + (4671268193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (97901487/500000000 : ℝ)^87 ≤ (3389762508927/25000000000000 : ℝ)^71 := by
    have hnat : (97901487 : ℕ)^87*25000000000000^71 ≤ 3389762508927^71*500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      97901487 500000000 3389762508927 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081730981/2000000000 : ℝ)^87 ≤ (1177281677139/2500000000000 : ℝ)^71 := by
    have hnat : (1081730981 : ℕ)^87*2500000000000^71 ≤ 1177281677139^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081730981 2000000000 1177281677139 2500000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4671268193/10000000000 : ℝ)^87 ≤ (19674841434979/50000000000000 : ℝ)^71 := by
    have hnat : (4671268193 : ℕ)^87*50000000000000^71 ≤ 19674841434979^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4671268193 10000000000 19674841434979 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-97901487/500000000 : ℝ), (1081730981/2000000000 : ℝ), (4671268193/10000000000 : ℝ)] ![(3389762508927/25000000000000 : ℝ), (1177281677139/2500000000000 : ℝ), (19674841434979/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-97901487/500000000 : ℝ)|^87 ≤ (3389762508927/25000000000000 : ℝ)^71
        have hw : |(-97901487/500000000 : ℝ)|=(97901487/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1081730981/2000000000 : ℝ)|^87 ≤ (1177281677139/2500000000000 : ℝ)^71
        have hw : |(1081730981/2000000000 : ℝ)|=(1081730981/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4671268193/10000000000 : ℝ)|^87 ≤ (19674841434979/50000000000000 : ℝ)^71
        have hw : |(4671268193/10000000000 : ℝ)|=(4671268193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325055_s2_s2_1 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4670233073/10000000000 : ℝ)*x 0 + (-1220850587/10000000000 : ℝ)*x 1 + (2980975263/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4670233073/10000000000 : ℝ)^87 ≤ (4917374817801/12500000000000 : ℝ)^71 := by
    have hnat : (4670233073 : ℕ)^87*12500000000000^71 ≤ 4917374817801^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4670233073 10000000000 4917374817801 12500000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1220850587/10000000000 : ℝ)^87 ≤ (7600461874227/100000000000000 : ℝ)^71 := by
    have hnat : (1220850587 : ℕ)^87*100000000000000^71 ≤ 7600461874227^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1220850587 10000000000 7600461874227 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2980975263/5000000000 : ℝ)^87 ≤ (1658141861471/3125000000000 : ℝ)^71 := by
    have hnat : (2980975263 : ℕ)^87*3125000000000^71 ≤ 1658141861471^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2980975263 5000000000 1658141861471 3125000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4670233073/10000000000 : ℝ), (-1220850587/10000000000 : ℝ), (2980975263/5000000000 : ℝ)] ![(4917374817801/12500000000000 : ℝ), (7600461874227/100000000000000 : ℝ), (1658141861471/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4670233073/10000000000 : ℝ)|^87 ≤ (4917374817801/12500000000000 : ℝ)^71
        have hw : |(4670233073/10000000000 : ℝ)|=(4670233073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1220850587/10000000000 : ℝ)|^87 ≤ (7600461874227/100000000000000 : ℝ)^71
        have hw : |(-1220850587/10000000000 : ℝ)|=(1220850587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2980975263/5000000000 : ℝ)|^87 ≤ (1658141861471/3125000000000 : ℝ)^71
        have hw : |(2980975263/5000000000 : ℝ)|=(2980975263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325055_s2_s2_2 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4671176531/10000000000 : ℝ)*x 0 + (1352119497/2500000000 : ℝ)*x 1 + (-979181837/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4671176531/10000000000 : ℝ)^87 ≤ (39348736729297/100000000000000 : ℝ)^71 := by
    have hnat : (4671176531 : ℕ)^87*100000000000000^71 ≤ 39348736729297^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4671176531 10000000000 39348736729297 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352119497/2500000000 : ℝ)^87 ≤ (47089379615927/100000000000000 : ℝ)^71 := by
    have hnat : (1352119497 : ℕ)^87*100000000000000^71 ≤ 47089379615927^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352119497 2500000000 47089379615927 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (979181837/5000000000 : ℝ)^87 ≤ (13561883644349/100000000000000 : ℝ)^71 := by
    have hnat : (979181837 : ℕ)^87*100000000000000^71 ≤ 13561883644349^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      979181837 5000000000 13561883644349 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4671176531/10000000000 : ℝ), (1352119497/2500000000 : ℝ), (-979181837/5000000000 : ℝ)] ![(39348736729297/100000000000000 : ℝ), (47089379615927/100000000000000 : ℝ), (13561883644349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4671176531/10000000000 : ℝ)|^87 ≤ (39348736729297/100000000000000 : ℝ)^71
        have hw : |(4671176531/10000000000 : ℝ)|=(4671176531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352119497/2500000000 : ℝ)|^87 ≤ (47089379615927/100000000000000 : ℝ)^71
        have hw : |(1352119497/2500000000 : ℝ)|=(1352119497/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-979181837/5000000000 : ℝ)|^87 ≤ (13561883644349/100000000000000 : ℝ)^71
        have hw : |(-979181837/5000000000 : ℝ)|=(979181837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325055_s2_s2_6 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1513023653/2500000000 : ℝ)*x 0 + (955235839/2500000000 : ℝ)*x 1 + (268567859/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1513023653/2500000000 : ℝ)^87 ≤ (54045271064943/100000000000000 : ℝ)^71 := by
    have hnat : (1513023653 : ℕ)^87*100000000000000^71 ≤ 54045271064943^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1513023653 2500000000 54045271064943 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (955235839/2500000000 : ℝ)^87 ≤ (7690452073753/25000000000000 : ℝ)^71 := by
    have hnat : (955235839 : ℕ)^87*25000000000000^71 ≤ 7690452073753^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      955235839 2500000000 7690452073753 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (268567859/1250000000 : ℝ)^87 ≤ (15192920624163/100000000000000 : ℝ)^71 := by
    have hnat : (268567859 : ℕ)^87*100000000000000^71 ≤ 15192920624163^71*1250000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268567859 1250000000 15192920624163 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1513023653/2500000000 : ℝ), (955235839/2500000000 : ℝ), (268567859/1250000000 : ℝ)] ![(54045271064943/100000000000000 : ℝ), (7690452073753/25000000000000 : ℝ), (15192920624163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1513023653/2500000000 : ℝ)|^87 ≤ (54045271064943/100000000000000 : ℝ)^71
        have hw : |(1513023653/2500000000 : ℝ)|=(1513023653/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(955235839/2500000000 : ℝ)|^87 ≤ (7690452073753/25000000000000 : ℝ)^71
        have hw : |(955235839/2500000000 : ℝ)|=(955235839/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(268567859/1250000000 : ℝ)|^87 ≤ (15192920624163/100000000000000 : ℝ)^71
        have hw : |(268567859/1250000000 : ℝ)|=(268567859/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325055_s2_s2_7 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-14566127/78125000 : ℝ)*x 0 + (5178850827/10000000000 : ℝ)*x 1 + (2490924373/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (14566127/78125000 : ℝ)^87 ≤ (319236019671/2500000000000 : ℝ)^71 := by
    have hnat : (14566127 : ℕ)^87*2500000000000^71 ≤ 319236019671^71*78125000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14566127 78125000 319236019671 2500000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5178850827/10000000000 : ℝ)^87 ≤ (22325711036507/50000000000000 : ℝ)^71 := by
    have hnat : (5178850827 : ℕ)^87*50000000000000^71 ≤ 22325711036507^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178850827 10000000000 22325711036507 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2490924373/5000000000 : ℝ)^87 ≤ (42579137127583/100000000000000 : ℝ)^71 := by
    have hnat : (2490924373 : ℕ)^87*100000000000000^71 ≤ 42579137127583^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2490924373 5000000000 42579137127583 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-14566127/78125000 : ℝ), (5178850827/10000000000 : ℝ), (2490924373/5000000000 : ℝ)] ![(319236019671/2500000000000 : ℝ), (22325711036507/50000000000000 : ℝ), (42579137127583/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-14566127/78125000 : ℝ)|^87 ≤ (319236019671/2500000000000 : ℝ)^71
        have hw : |(-14566127/78125000 : ℝ)|=(14566127/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5178850827/10000000000 : ℝ)|^87 ≤ (22325711036507/50000000000000 : ℝ)^71
        have hw : |(5178850827/10000000000 : ℝ)|=(5178850827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2490924373/5000000000 : ℝ)|^87 ≤ (42579137127583/100000000000000 : ℝ)^71
        have hw : |(2490924373/5000000000 : ℝ)|=(2490924373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325055_s2_s2_8 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4668911079/10000000000 : ℝ)*x 0 + (-986960039/10000000000 : ℝ)*x 1 + (122452061/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4668911079/10000000000 : ℝ)^87 ≤ (19662676963803/50000000000000 : ℝ)^71 := by
    have hnat : (4668911079 : ℕ)^87*50000000000000^71 ≤ 19662676963803^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4668911079 10000000000 19662676963803 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (986960039/10000000000 : ℝ)^87 ≤ (1171366630091/20000000000000 : ℝ)^71 := by
    have hnat : (986960039 : ℕ)^87*20000000000000^71 ≤ 1171366630091^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      986960039 10000000000 1171366630091 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (122452061/200000000 : ℝ)^87 ≤ (54817812907069/100000000000000 : ℝ)^71 := by
    have hnat : (122452061 : ℕ)^87*100000000000000^71 ≤ 54817812907069^71*200000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      122452061 200000000 54817812907069 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4668911079/10000000000 : ℝ), (-986960039/10000000000 : ℝ), (122452061/200000000 : ℝ)] ![(19662676963803/50000000000000 : ℝ), (1171366630091/20000000000000 : ℝ), (54817812907069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4668911079/10000000000 : ℝ)|^87 ≤ (19662676963803/50000000000000 : ℝ)^71
        have hw : |(4668911079/10000000000 : ℝ)|=(4668911079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-986960039/10000000000 : ℝ)|^87 ≤ (1171366630091/20000000000000 : ℝ)^71
        have hw : |(-986960039/10000000000 : ℝ)|=(986960039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(122452061/200000000 : ℝ)|^87 ≤ (54817812907069/100000000000000 : ℝ)^71
        have hw : |(122452061/200000000 : ℝ)|=(122452061/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325055_s2_s2_9 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4669854071/10000000000 : ℝ)*x 0 + (2823631589/5000000000 : ℝ)*x 1 + (-413168359/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4669854071/10000000000 : ℝ)^87 ≤ (4916885835441/12500000000000 : ℝ)^71 := by
    have hnat : (4669854071 : ℕ)^87*12500000000000^71 ≤ 4916885835441^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4669854071 10000000000 4916885835441 12500000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2823631589/5000000000 : ℝ)^87 ≤ (24824711330183/50000000000000 : ℝ)^71 := by
    have hnat : (2823631589 : ℕ)^87*50000000000000^71 ≤ 24824711330183^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2823631589 5000000000 24824711330183 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (413168359/2500000000 : ℝ)^87 ≤ (5507745320269/50000000000000 : ℝ)^71 := by
    have hnat : (413168359 : ℕ)^87*50000000000000^71 ≤ 5507745320269^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413168359 2500000000 5507745320269 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4669854071/10000000000 : ℝ), (2823631589/5000000000 : ℝ), (-413168359/2500000000 : ℝ)] ![(4916885835441/12500000000000 : ℝ), (24824711330183/50000000000000 : ℝ), (5507745320269/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4669854071/10000000000 : ℝ)|^87 ≤ (4916885835441/12500000000000 : ℝ)^71
        have hw : |(4669854071/10000000000 : ℝ)|=(4669854071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2823631589/5000000000 : ℝ)|^87 ≤ (24824711330183/50000000000000 : ℝ)^71
        have hw : |(2823631589/5000000000 : ℝ)|=(2823631589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-413168359/2500000000 : ℝ)|^87 ≤ (5507745320269/50000000000000 : ℝ)^71
        have hw : |(-413168359/2500000000 : ℝ)|=(413168359/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325055_s2_s2_13 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1441320191/2500000000 : ℝ)*x 0 + (4526725869/10000000000 : ℝ)*x 1 + (1676846837/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1441320191/2500000000 : ℝ)^87 ≤ (50923805143881/100000000000000 : ℝ)^71 := by
    have hnat : (1441320191 : ℕ)^87*100000000000000^71 ≤ 50923805143881^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1441320191 2500000000 50923805143881 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4526725869/10000000000 : ℝ)^87 ≤ (7572589796847/20000000000000 : ℝ)^71 := by
    have hnat : (4526725869 : ℕ)^87*20000000000000^71 ≤ 7572589796847^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4526725869 10000000000 7572589796847 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1676846837/10000000000 : ℝ)^87 ≤ (5606622928331/50000000000000 : ℝ)^71 := by
    have hnat : (1676846837 : ℕ)^87*50000000000000^71 ≤ 5606622928331^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1676846837 10000000000 5606622928331 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1441320191/2500000000 : ℝ), (4526725869/10000000000 : ℝ), (1676846837/10000000000 : ℝ)] ![(50923805143881/100000000000000 : ℝ), (7572589796847/20000000000000 : ℝ), (5606622928331/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1441320191/2500000000 : ℝ)|^87 ≤ (50923805143881/100000000000000 : ℝ)^71
        have hw : |(1441320191/2500000000 : ℝ)|=(1441320191/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4526725869/10000000000 : ℝ)|^87 ≤ (7572589796847/20000000000000 : ℝ)^71
        have hw : |(4526725869/10000000000 : ℝ)|=(4526725869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1676846837/10000000000 : ℝ)|^87 ≤ (5606622928331/50000000000000 : ℝ)^71
        have hw : |(1676846837/10000000000 : ℝ)|=(1676846837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325055_s2_s2_14 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-321932439/2000000000 : ℝ)*x 0 + (5335153713/10000000000 : ℝ)*x 1 + (1256129733/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (321932439/2000000000 : ℝ)^87 ≤ (10665242703091/100000000000000 : ℝ)^71 := by
    have hnat : (321932439 : ℕ)^87*100000000000000^71 ≤ 10665242703091^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      321932439 2000000000 10665242703091 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5335153713/10000000000 : ℝ)^87 ≤ (1157707724261/2500000000000 : ℝ)^71 := by
    have hnat : (5335153713 : ℕ)^87*2500000000000^71 ≤ 1157707724261^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5335153713 10000000000 1157707724261 2500000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1256129733/2500000000 : ℝ)^87 ≤ (43026448319657/100000000000000 : ℝ)^71 := by
    have hnat : (1256129733 : ℕ)^87*100000000000000^71 ≤ 43026448319657^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1256129733 2500000000 43026448319657 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-321932439/2000000000 : ℝ), (5335153713/10000000000 : ℝ), (1256129733/2500000000 : ℝ)] ![(10665242703091/100000000000000 : ℝ), (1157707724261/2500000000000 : ℝ), (43026448319657/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-321932439/2000000000 : ℝ)|^87 ≤ (10665242703091/100000000000000 : ℝ)^71
        have hw : |(-321932439/2000000000 : ℝ)|=(321932439/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5335153713/10000000000 : ℝ)|^87 ≤ (1157707724261/2500000000000 : ℝ)^71
        have hw : |(5335153713/10000000000 : ℝ)|=(5335153713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1256129733/2500000000 : ℝ)|^87 ≤ (43026448319657/100000000000000 : ℝ)^71
        have hw : |(1256129733/2500000000 : ℝ)|=(1256129733/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325055_s2_s2_15 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (565805439/1250000000 : ℝ)*x 0 + (-1188306899/10000000000 : ℝ)*x 1 + (6119793533/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (565805439/1250000000 : ℝ)^87 ≤ (18930027531683/50000000000000 : ℝ)^71 := by
    have hnat : (565805439 : ℕ)^87*50000000000000^71 ≤ 18930027531683^71*1250000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565805439 1250000000 18930027531683 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1188306899/10000000000 : ℝ)^87 ≤ (1470590729917/20000000000000 : ℝ)^71 := by
    have hnat : (1188306899 : ℕ)^87*20000000000000^71 ≤ 1470590729917^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1188306899 10000000000 1470590729917 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6119793533/10000000000 : ℝ)^87 ≤ (54786991269391/100000000000000 : ℝ)^71 := by
    have hnat : (6119793533 : ℕ)^87*100000000000000^71 ≤ 54786991269391^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6119793533 10000000000 54786991269391 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(565805439/1250000000 : ℝ), (-1188306899/10000000000 : ℝ), (6119793533/10000000000 : ℝ)] ![(18930027531683/50000000000000 : ℝ), (1470590729917/20000000000000 : ℝ), (54786991269391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(565805439/1250000000 : ℝ)|^87 ≤ (18930027531683/50000000000000 : ℝ)^71
        have hw : |(565805439/1250000000 : ℝ)|=(565805439/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1188306899/10000000000 : ℝ)|^87 ≤ (1470590729917/20000000000000 : ℝ)^71
        have hw : |(-1188306899/10000000000 : ℝ)|=(1188306899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6119793533/10000000000 : ℝ)|^87 ≤ (54786991269391/100000000000000 : ℝ)^71
        have hw : |(6119793533/10000000000 : ℝ)|=(6119793533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325055_s2_s2_16 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2512218719/5000000000 : ℝ)*x 0 + (5334975361/10000000000 : ℝ)*x 1 + (-1610001153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2512218719/5000000000 : ℝ)^87 ≤ (43025593200263/100000000000000 : ℝ)^71 := by
    have hnat : (2512218719 : ℕ)^87*100000000000000^71 ≤ 43025593200263^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2512218719 5000000000 43025593200263 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5334975361/10000000000 : ℝ)^87 ≤ (4630641204947/10000000000000 : ℝ)^71 := by
    have hnat : (5334975361 : ℕ)^87*10000000000000^71 ≤ 4630641204947^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5334975361 10000000000 4630641204947 10000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1610001153/10000000000 : ℝ)^87 ≤ (5333997366327/50000000000000 : ℝ)^71 := by
    have hnat : (1610001153 : ℕ)^87*50000000000000^71 ≤ 5333997366327^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1610001153 10000000000 5333997366327 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2512218719/5000000000 : ℝ), (5334975361/10000000000 : ℝ), (-1610001153/10000000000 : ℝ)] ![(43025593200263/100000000000000 : ℝ), (4630641204947/10000000000000 : ℝ), (5333997366327/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2512218719/5000000000 : ℝ)|^87 ≤ (43025593200263/100000000000000 : ℝ)^71
        have hw : |(2512218719/5000000000 : ℝ)|=(2512218719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5334975361/10000000000 : ℝ)|^87 ≤ (4630641204947/10000000000000 : ℝ)^71
        have hw : |(5334975361/10000000000 : ℝ)|=(5334975361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1610001153/10000000000 : ℝ)|^87 ≤ (5333997366327/50000000000000 : ℝ)^71
        have hw : |(-1610001153/10000000000 : ℝ)|=(1610001153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325055_s2_s2_20 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1624143079/2500000000 : ℝ)*x 0 + (232498661/625000000 : ℝ)*x 1 + (1685330301/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1624143079/2500000000 : ℝ)^87 ≤ (11789687096957/20000000000000 : ℝ)^71 := by
    have hnat : (1624143079 : ℕ)^87*20000000000000^71 ≤ 11789687096957^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1624143079 2500000000 11789687096957 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (232498661/625000000 : ℝ)^87 ≤ (2976876510811/10000000000000 : ℝ)^71 := by
    have hnat : (232498661 : ℕ)^87*10000000000000^71 ≤ 2976876510811^71*625000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      232498661 625000000 2976876510811 10000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1685330301/10000000000 : ℝ)^87 ≤ (2256559879667/20000000000000 : ℝ)^71 := by
    have hnat : (1685330301 : ℕ)^87*20000000000000^71 ≤ 2256559879667^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1685330301 10000000000 2256559879667 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1624143079/2500000000 : ℝ), (232498661/625000000 : ℝ), (1685330301/10000000000 : ℝ)] ![(11789687096957/20000000000000 : ℝ), (2976876510811/10000000000000 : ℝ), (2256559879667/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1624143079/2500000000 : ℝ)|^87 ≤ (11789687096957/20000000000000 : ℝ)^71
        have hw : |(1624143079/2500000000 : ℝ)|=(1624143079/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(232498661/625000000 : ℝ)|^87 ≤ (2976876510811/10000000000000 : ℝ)^71
        have hw : |(232498661/625000000 : ℝ)|=(232498661/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1685330301/10000000000 : ℝ)|^87 ≤ (2256559879667/20000000000000 : ℝ)^71
        have hw : |(1685330301/10000000000 : ℝ)|=(1685330301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325055_s2_s2_21 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-415175431/2500000000 : ℝ)*x 0 + (1131762789/2000000000 : ℝ)*x 1 + (4651430663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (415175431/2500000000 : ℝ)^87 ≤ (11081095800197/100000000000000 : ℝ)^71 := by
    have hnat : (415175431 : ℕ)^87*100000000000000^71 ≤ 11081095800197^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415175431 2500000000 11081095800197 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1131762789/2000000000 : ℝ)^87 ≤ (9954777571297/20000000000000 : ℝ)^71 := by
    have hnat : (1131762789 : ℕ)^87*20000000000000^71 ≤ 9954777571297^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1131762789 2000000000 9954777571297 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4651430663/10000000000 : ℝ)^87 ≤ (7829003266193/20000000000000 : ℝ)^71 := by
    have hnat : (4651430663 : ℕ)^87*20000000000000^71 ≤ 7829003266193^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4651430663 10000000000 7829003266193 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-415175431/2500000000 : ℝ), (1131762789/2000000000 : ℝ), (4651430663/10000000000 : ℝ)] ![(11081095800197/100000000000000 : ℝ), (9954777571297/20000000000000 : ℝ), (7829003266193/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-415175431/2500000000 : ℝ)|^87 ≤ (11081095800197/100000000000000 : ℝ)^71
        have hw : |(-415175431/2500000000 : ℝ)|=(415175431/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1131762789/2000000000 : ℝ)|^87 ≤ (9954777571297/20000000000000 : ℝ)^71
        have hw : |(1131762789/2000000000 : ℝ)|=(1131762789/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4651430663/10000000000 : ℝ)|^87 ≤ (7829003266193/20000000000000 : ℝ)^71
        have hw : |(4651430663/10000000000 : ℝ)|=(4651430663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325055_s2_s2_22 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2486227023/5000000000 : ℝ)*x 0 + (-487794007/5000000000 : ℝ)*x 1 + (5841039961/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2486227023/5000000000 : ℝ)^87 ≤ (42480768230133/100000000000000 : ℝ)^71 := by
    have hnat : (2486227023 : ℕ)^87*100000000000000^71 ≤ 42480768230133^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2486227023 5000000000 42480768230133 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (487794007/5000000000 : ℝ)^87 ≤ (2887124557547/50000000000000 : ℝ)^71 := by
    have hnat : (487794007 : ℕ)^87*50000000000000^71 ≤ 2887124557547^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      487794007 5000000000 2887124557547 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5841039961/10000000000 : ℝ)^87 ≤ (6468122830233/12500000000000 : ℝ)^71 := by
    have hnat : (5841039961 : ℕ)^87*12500000000000^71 ≤ 6468122830233^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5841039961 10000000000 6468122830233 12500000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2486227023/5000000000 : ℝ), (-487794007/5000000000 : ℝ), (5841039961/10000000000 : ℝ)] ![(42480768230133/100000000000000 : ℝ), (2887124557547/50000000000000 : ℝ), (6468122830233/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2486227023/5000000000 : ℝ)|^87 ≤ (42480768230133/100000000000000 : ℝ)^71
        have hw : |(2486227023/5000000000 : ℝ)|=(2486227023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-487794007/5000000000 : ℝ)|^87 ≤ (2887124557547/50000000000000 : ℝ)^71
        have hw : |(-487794007/5000000000 : ℝ)|=(487794007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5841039961/10000000000 : ℝ)|^87 ≤ (6468122830233/12500000000000 : ℝ)^71
        have hw : |(5841039961/10000000000 : ℝ)|=(5841039961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325055_s2_s2_23 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4476082077/10000000000 : ℝ)*x 0 + (565863627/1000000000 : ℝ)*x 1 + (-469510489/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4476082077/10000000000 : ℝ)^87 ≤ (7468909089059/20000000000000 : ℝ)^71 := by
    have hnat : (4476082077 : ℕ)^87*20000000000000^71 ≤ 7468909089059^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4476082077 10000000000 7468909089059 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (565863627/1000000000 : ℝ)^87 ≤ (49771972887073/100000000000000 : ℝ)^71 := by
    have hnat : (565863627 : ℕ)^87*100000000000000^71 ≤ 49771972887073^71*1000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565863627 1000000000 49771972887073 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (469510489/2500000000 : ℝ)^87 ≤ (402608801393/3125000000000 : ℝ)^71 := by
    have hnat : (469510489 : ℕ)^87*3125000000000^71 ≤ 402608801393^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      469510489 2500000000 402608801393 3125000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4476082077/10000000000 : ℝ), (565863627/1000000000 : ℝ), (-469510489/2500000000 : ℝ)] ![(7468909089059/20000000000000 : ℝ), (49771972887073/100000000000000 : ℝ), (402608801393/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4476082077/10000000000 : ℝ)|^87 ≤ (7468909089059/20000000000000 : ℝ)^71
        have hw : |(4476082077/10000000000 : ℝ)|=(4476082077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(565863627/1000000000 : ℝ)|^87 ≤ (49771972887073/100000000000000 : ℝ)^71
        have hw : |(565863627/1000000000 : ℝ)|=(565863627/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-469510489/2500000000 : ℝ)|^87 ≤ (402608801393/3125000000000 : ℝ)^71
        have hw : |(-469510489/2500000000 : ℝ)|=(469510489/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325055_s2_s2_27 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1662863441/2500000000 : ℝ)*x 0 + (615564857/2000000000 : ℝ)*x 1 + (1767763/8000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1662863441/2500000000 : ℝ)^87 ≤ (30337546658167/50000000000000 : ℝ)^71 := by
    have hnat : (1662863441 : ℕ)^87*50000000000000^71 ≤ 30337546658167^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1662863441 2500000000 30337546658167 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (615564857/2000000000 : ℝ)^87 ≤ (1475022019143/6250000000000 : ℝ)^71 := by
    have hnat : (615564857 : ℕ)^87*6250000000000^71 ≤ 1475022019143^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      615564857 2000000000 1475022019143 6250000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1767763/8000000 : ℝ)^87 ≤ (15724554362043/100000000000000 : ℝ)^71 := by
    have hnat : (1767763 : ℕ)^87*100000000000000^71 ≤ 15724554362043^71*8000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1767763 8000000 15724554362043 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1662863441/2500000000 : ℝ), (615564857/2000000000 : ℝ), (1767763/8000000 : ℝ)] ![(30337546658167/50000000000000 : ℝ), (1475022019143/6250000000000 : ℝ), (15724554362043/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1662863441/2500000000 : ℝ)|^87 ≤ (30337546658167/50000000000000 : ℝ)^71
        have hw : |(1662863441/2500000000 : ℝ)|=(1662863441/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(615564857/2000000000 : ℝ)|^87 ≤ (1475022019143/6250000000000 : ℝ)^71
        have hw : |(615564857/2000000000 : ℝ)|=(615564857/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1767763/8000000 : ℝ)|^87 ≤ (15724554362043/100000000000000 : ℝ)^71
        have hw : |(1767763/8000000 : ℝ)|=(1767763/8000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c325055_s2 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (200939/100000 : ℝ) (33069/20000 : ℝ) (81317/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((783/2000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(783/2000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(39657/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(39657/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1571/4000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(1571/4000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((4259/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4259/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22321/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(22321/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5281/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(5281/25000 : ℝ)*X 1 2) := by
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
  have main2 : (81317/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (81317/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (783/2000 : ℝ) ^ (85/16 : ℝ) ≤ (686100141616002909/100000000000000000000 : ℝ) := by
    have hpowers : (783/2000 : ℝ)^85 ≤ (686100141616002909/100000000000000000000 : ℝ)^16 := by
      have hnat : (783 : ℕ)^85*100000000000000000000^16 ≤ 686100141616002909^16*2000^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        783 2000 686100141616002909 100000000000000000000 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (783/2000 : ℝ)) (X := (686100141616002909/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s2_corner0a : (100686100141616002909/100000000000000000000 : ℝ) ≤ (10012879009816443/10000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (100686100141616002909/100000000000000000000 : ℝ)^16 ≤ (10012879009816443/10000000000000000 : ℝ)^85 := by
      have hnat : (100686100141616002909 : ℕ)^16*10000000000000000^85 ≤ 10012879009816443^85*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100686100141616002909 100000000000000000000 10012879009816443 10000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10012879009816443/10000000000000000 : ℝ)) (X := (100686100141616002909/100000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s2_corner0b : (50686100141616002909/50000000000000000000 : ℝ) ≤ (401027478977389/400000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (50686100141616002909/50000000000000000000 : ℝ)^16 ≤ (401027478977389/400000000000000 : ℝ)^85 := by
      have hnat : (50686100141616002909 : ℕ)^16*400000000000000^85 ≤ 401027478977389^85*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50686100141616002909 50000000000000000000 401027478977389 400000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (401027478977389/400000000000000 : ℝ)) (X := (50686100141616002909/50000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(12879009816443/3915000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(6403982309141/1957500000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (783/2000 : ℝ)) (alpha := (12879009816443/3915000000000000 : ℝ)) (beta := (6403982309141/1957500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (783/2000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(12879009816443/3915000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(6403982309141/1957500000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (39657/100000 : ℝ) ^ (85/16 : ℝ) ≤ (734639442831248847/100000000000000000000 : ℝ) := by
    have hpowers : (39657/100000 : ℝ)^85 ≤ (734639442831248847/100000000000000000000 : ℝ)^16 := by
      have hnat : (39657 : ℕ)^85*100000000000000000000^16 ≤ 734639442831248847^16*100000^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        39657 100000 734639442831248847 100000000000000000000 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (39657/100000 : ℝ)) (X := (734639442831248847/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s2_corner1a : (100734639442831248847/100000000000000000000 : ℝ) ≤ (5006893727852253/5000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (100734639442831248847/100000000000000000000 : ℝ)^16 ≤ (5006893727852253/5000000000000000 : ℝ)^85 := by
      have hnat : (100734639442831248847 : ℕ)^16*5000000000000000^85 ≤ 5006893727852253^85*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100734639442831248847 100000000000000000000 5006893727852253 5000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5006893727852253/5000000000000000 : ℝ)) (X := (100734639442831248847/100000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s2_corner1b : (50734639442831248847/50000000000000000000 : ℝ) ≤ (10027493529062423/10000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (50734639442831248847/50000000000000000000 : ℝ)^16 ≤ (10027493529062423/10000000000000000 : ℝ)^85 := by
      have hnat : (50734639442831248847 : ℕ)^16*10000000000000000^85 ≤ 10027493529062423^85*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50734639442831248847 50000000000000000000 10027493529062423 10000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10027493529062423/10000000000000000 : ℝ)) (X := (50734639442831248847/50000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(6893727852253/1982850000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(13706073357917/3965700000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (39657/100000 : ℝ)) (alpha := (6893727852253/1982850000000000 : ℝ)) (beta := (13706073357917/3965700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (39657/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(6893727852253/1982850000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(13706073357917/3965700000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (1571/4000 : ℝ) ^ (85/16 : ℝ) ≤ (697818178909657381/100000000000000000000 : ℝ) := by
    have hpowers : (1571/4000 : ℝ)^85 ≤ (697818178909657381/100000000000000000000 : ℝ)^16 := by
      have hnat : (1571 : ℕ)^85*100000000000000000000^16 ≤ 697818178909657381^16*4000^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1571 4000 697818178909657381 100000000000000000000 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1571/4000 : ℝ)) (X := (697818178909657381/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s2_corner2a : (100697818178909657381/100000000000000000000 : ℝ) ≤ (5006549176683077/5000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (100697818178909657381/100000000000000000000 : ℝ)^16 ≤ (5006549176683077/5000000000000000 : ℝ)^85 := by
      have hnat : (100697818178909657381 : ℕ)^16*5000000000000000^85 ≤ 5006549176683077^85*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100697818178909657381 100000000000000000000 5006549176683077 5000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5006549176683077/5000000000000000 : ℝ)) (X := (100697818178909657381/100000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s2_corner2b : (50697818178909657381/50000000000000000000 : ℝ) ≤ (5013061614732631/5000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (50697818178909657381/50000000000000000000 : ℝ)^16 ≤ (5013061614732631/5000000000000000 : ℝ)^85 := by
      have hnat : (50697818178909657381 : ℕ)^16*5000000000000000^85 ≤ 5013061614732631^85*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50697818178909657381 50000000000000000000 5013061614732631 5000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5013061614732631/5000000000000000 : ℝ)) (X := (50697818178909657381/50000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(6549176683077/1963750000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(3256219024777/981875000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (1571/4000 : ℝ)) (alpha := (6549176683077/1963750000000000 : ℝ)) (beta := (3256219024777/981875000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1571/4000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(6549176683077/1963750000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(3256219024777/981875000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-97901487/500000000 : ℝ)*X 0 0+(1081730981/2000000000 : ℝ)*X 0 1+(4671268193/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325055_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((4670233073/10000000000 : ℝ)*X 1 0+(-1220850587/10000000000 : ℝ)*X 1 1+(2980975263/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325055_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((4671176531/10000000000 : ℝ)*X 2 0+(1352119497/2500000000 : ℝ)*X 2 1+(-979181837/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325055_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((1513023653/2500000000 : ℝ)*X 0 0+(955235839/2500000000 : ℝ)*X 0 1+(268567859/1250000000 : ℝ)*X 0 2+(1513023653/2500000000 : ℝ)*X 1 0+(955235839/2500000000 : ℝ)*X 1 1+(268567859/1250000000 : ℝ)*X 1 2+(1513023653/2500000000 : ℝ)*X 2 0+(955235839/2500000000 : ℝ)*X 2 1+(268567859/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325055_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-14566127/78125000 : ℝ)*X 0 0+(5178850827/10000000000 : ℝ)*X 0 1+(2490924373/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325055_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((4668911079/10000000000 : ℝ)*X 1 0+(-986960039/10000000000 : ℝ)*X 1 1+(122452061/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325055_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((4669854071/10000000000 : ℝ)*X 2 0+(2823631589/5000000000 : ℝ)*X 2 1+(-413168359/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325055_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((1441320191/2500000000 : ℝ)*X 0 0+(4526725869/10000000000 : ℝ)*X 0 1+(1676846837/10000000000 : ℝ)*X 0 2+(1441320191/2500000000 : ℝ)*X 1 0+(4526725869/10000000000 : ℝ)*X 1 1+(1676846837/10000000000 : ℝ)*X 1 2+(1441320191/2500000000 : ℝ)*X 2 0+(4526725869/10000000000 : ℝ)*X 2 1+(1676846837/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325055_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-321932439/2000000000 : ℝ)*X 0 0+(5335153713/10000000000 : ℝ)*X 0 1+(1256129733/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325055_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((565805439/1250000000 : ℝ)*X 1 0+(-1188306899/10000000000 : ℝ)*X 1 1+(6119793533/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325055_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((2512218719/5000000000 : ℝ)*X 2 0+(5334975361/10000000000 : ℝ)*X 2 1+(-1610001153/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325055_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((1624143079/2500000000 : ℝ)*X 0 0+(232498661/625000000 : ℝ)*X 0 1+(1685330301/10000000000 : ℝ)*X 0 2+(1624143079/2500000000 : ℝ)*X 1 0+(232498661/625000000 : ℝ)*X 1 1+(1685330301/10000000000 : ℝ)*X 1 2+(1624143079/2500000000 : ℝ)*X 2 0+(232498661/625000000 : ℝ)*X 2 1+(1685330301/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325055_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-415175431/2500000000 : ℝ)*X 0 0+(1131762789/2000000000 : ℝ)*X 0 1+(4651430663/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325055_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((2486227023/5000000000 : ℝ)*X 1 0+(-487794007/5000000000 : ℝ)*X 1 1+(5841039961/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325055_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((4476082077/10000000000 : ℝ)*X 2 0+(565863627/1000000000 : ℝ)*X 2 1+(-469510489/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325055_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((1662863441/2500000000 : ℝ)*X 0 0+(615564857/2000000000 : ℝ)*X 0 1+(1767763/8000000 : ℝ)*X 0 2+(1662863441/2500000000 : ℝ)*X 1 0+(615564857/2000000000 : ℝ)*X 1 1+(1767763/8000000 : ℝ)*X 1 2+(1662863441/2500000000 : ℝ)*X 2 0+(615564857/2000000000 : ℝ)*X 2 1+(1767763/8000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325055_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((4259/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4259/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (6882609911402844581963157239/376402763125000000000000000000000 : ℝ) := by norm_num
    linear_combination (46778300019/20000000000 : ℝ)*(base49) + (7102570303051/500000000000 : ℝ)*(major_s2_0) + (7102570303051/500000000000 : ℝ)*(major_s2_1) + (7102570303051/500000000000 : ℝ)*(major_s2_2) + (348540669/1000000000000 : ℝ)*(sp_s2_0) + (100653419/500000000000 : ℝ)*(sp_s2_2) + (16509661/250000000000 : ℝ)*(sp_s2_6) + (10670261926823/500000000000 : ℝ)*(sp_s2_7) + (21340417931301/1000000000000 : ℝ)*(sp_s2_8) + (21340320791723/1000000000000 : ℝ)*(sp_s2_9) + (441832095459/62500000000 : ℝ)*(sp_s2_13) + (23156817/1000000000000 : ℝ)*(sp_s2_14) + (59702479/125000000000 : ℝ)*(sp_s2_15) + (93363143/250000000000 : ℝ)*(sp_s2_23) + (7069379565989/1000000000000 : ℝ)*(f.failure) + (21340895551133/1000000000000 : ℝ)*(f.sum) + (19324214055817121353/77876433750000000000000000000000 : ℝ)*base63 + (368476539883127/490937500000000000000000000 : ℝ)*base65 + (240914937690491/247856250000000000000000000 : ℝ)*base67 + (648059256248729/1963750000000000000000000000 : ℝ)*base69 + (941780900215919881/3075232500000000000000000000000 : ℝ)*base71 + (24085950668441/978750000000000000000000000 : ℝ)*base73 + (670429487690591/1982850000000000000000000000 : ℝ)*base75 + (372989122199093/1957500000000000000000000000 : ℝ)*base77 + (3789515534115402577/6469048125000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (63671/100000000000000000 : ℝ)*base87 + (63671/100000000000000000 : ℝ)*base89 + (63671/100000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22321/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(22321/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (20172546349973281408522991789/1355049947250000000000000000000000 : ℝ) := by norm_num
    linear_combination (33022993747/15625000000 : ℝ)*(base49) + (1072579/250000000000 : ℝ)*(base60) + (6695869250899/500000000000 : ℝ)*(major_s2_0) + (6695869250899/500000000000 : ℝ)*(major_s2_1) + (6695869250899/500000000000 : ℝ)*(major_s2_2) + (90226163/250000000000 : ℝ)*(sp_s2_1) + (12146089/50000000000 : ℝ)*(sp_s2_2) + (267079849/1000000000000 : ℝ)*(sp_s2_7) + (33084107/200000000000 : ℝ)*(sp_s2_8) + (10059312954591/500000000000 : ℝ)*(sp_s2_14) + (5029591665961/250000000000 : ℝ)*(sp_s2_15) + (20118650067251/1000000000000 : ℝ)*(sp_s2_16) + (6664454218041/1000000000000 : ℝ)*(sp_s2_20) + (3901069/31250000000 : ℝ)*(sp_s2_27) + (6664579052249/1000000000000 : ℝ)*(f.failure) + (20118892989031/1000000000000 : ℝ)*(f.sum) + (553955045339410939/38938216875000000000000000000000 : ℝ)*base62 + (876427558056283/1963750000000000000000000000 : ℝ)*base64 + (74617968362351/991425000000000000000000000 : ℝ)*base67 + (489452256870929/1963750000000000000000000000 : ℝ)*base68 + (573909407659072931/3075232500000000000000000000000 : ℝ)*base70 + (129518559777683/489375000000000000000000000 : ℝ)*base72 + (182130881593279/495712500000000000000000000 : ℝ)*base74 + (651237175042993/1957500000000000000000000000 : ℝ)*base76 + (544075219959210487/1617262031250000000000000000000 : ℝ)*base79 + (61811/100000000000000000 : ℝ)*base87 + (61811/100000000000000000 : ℝ)*base89 + (61811/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5281/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(5281/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (9083033760988120296414451929/752805526250000000000000000000000 : ℝ) := by norm_num
    linear_combination (57819/50000000000 : ℝ)*(base39) + (311593/62500000000 : ℝ)*(base40) + (575513853153/250000000000 : ℝ)*(base49) + (6692327589807/500000000000 : ℝ)*(major_s2_0) + (6692327589807/500000000000 : ℝ)*(major_s2_1) + (6692327589807/500000000000 : ℝ)*(major_s2_2) + (10786249/25000000000 : ℝ)*(sp_s2_0) + (9103573/31250000000 : ℝ)*(sp_s2_1) + (219863183/1000000000000 : ℝ)*(sp_s2_2) + (196324159/1000000000000 : ℝ)*(sp_s2_20) + (20107820945851/1000000000000 : ℝ)*(sp_s2_21) + (804318443259/40000000000 : ℝ)*(sp_s2_22) + (5027008133157/250000000000 : ℝ)*(sp_s2_23) + (6660857617393/1000000000000 : ℝ)*(sp_s2_27) + (416315871347/62500000000 : ℝ)*(f.failure) + (20108252395811/1000000000000 : ℝ)*(f.sum) + (1665374870090157067/6489702812500000000000000000000 : ℝ)*base62 + (273436490272711/490937500000000000000000000 : ℝ)*base64 + (488438663507363/660950000000000000000000000 : ℝ)*base66 + (169757254070559/245468750000000000000000000 : ℝ)*base68 + (103227076112646487/341692500000000000000000000000 : ℝ)*base70 + (40656657636857/108750000000000000000000000 : ℝ)*base72 + (454502290232261/660950000000000000000000000 : ℝ)*base74 + (161428792000361/217500000000000000000000000 : ℝ)*base76 + (228351213141849833/1437566250000000000000000000000 : ℝ)*base78 + (7333/6250000000000000 : ℝ)*base87 + (7333/6250000000000000 : ℝ)*base89 + (7333/6250000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (200939/100000 : ℝ) (33069/20000 : ℝ) (81317/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((783/2000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(783/2000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(39657/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(39657/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1571/4000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(1571/4000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((4259/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4259/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22321/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(22321/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5281/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(5281/25000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c325055_s2 p hpa hpb X hX hprev1

#print axioms solution
