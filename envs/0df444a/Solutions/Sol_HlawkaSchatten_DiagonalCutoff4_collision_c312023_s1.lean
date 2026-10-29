-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c312023_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:17:14.563992+00:00
-- url     : https://prove2.me/submissions/098def45-3633-4e48-976c-17e0145b2230

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
theorem collision_support_c312023_s1_s1_0 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-3303754203/10000000000 : ℝ)*x 0 + (278041869/500000000 : ℝ)*x 1 + (3724566087/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3303754203/10000000000 : ℝ)^37 ≤ (12169989677043/50000000000000 : ℝ)^29 := by
    have hnat : (3303754203 : ℕ)^37*50000000000000^29 ≤ 12169989677043^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3303754203 10000000000 12169989677043 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (278041869/500000000 : ℝ)^37 ≤ (236485243369/500000000000 : ℝ)^29 := by
    have hnat : (278041869 : ℕ)^37*500000000000^29 ≤ 236485243369^29*500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      278041869 500000000 236485243369 500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3724566087/10000000000 : ℝ)^37 ≤ (7090742988541/25000000000000 : ℝ)^29 := by
    have hnat : (3724566087 : ℕ)^37*25000000000000^29 ≤ 7090742988541^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3724566087 10000000000 7090742988541 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3303754203/10000000000 : ℝ), (278041869/500000000 : ℝ), (3724566087/10000000000 : ℝ)] ![(12169989677043/50000000000000 : ℝ), (236485243369/500000000000 : ℝ), (7090742988541/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3303754203/10000000000 : ℝ)|^37 ≤ (12169989677043/50000000000000 : ℝ)^29
        have hw : |(-3303754203/10000000000 : ℝ)|=(3303754203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(278041869/500000000 : ℝ)|^37 ≤ (236485243369/500000000000 : ℝ)^29
        have hw : |(278041869/500000000 : ℝ)|=(278041869/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3724566087/10000000000 : ℝ)|^37 ≤ (7090742988541/25000000000000 : ℝ)^29
        have hw : |(3724566087/10000000000 : ℝ)|=(3724566087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312023_s1_s1_1 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (302085389/500000000 : ℝ)*x 0 + (-204753237/5000000000 : ℝ)*x 1 + (1083138071/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (302085389/500000000 : ℝ)^37 ≤ (52576295457353/100000000000000 : ℝ)^29 := by
    have hnat : (302085389 : ℕ)^37*100000000000000^29 ≤ 52576295457353^29*500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      302085389 500000000 52576295457353 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (204753237/5000000000 : ℝ)^37 ≤ (169604026097/10000000000000 : ℝ)^29 := by
    have hnat : (204753237 : ℕ)^37*10000000000000^29 ≤ 169604026097^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      204753237 5000000000 169604026097 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1083138071/2000000000 : ℝ)^37 ≤ (45727664271623/100000000000000 : ℝ)^29 := by
    have hnat : (1083138071 : ℕ)^37*100000000000000^29 ≤ 45727664271623^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083138071 2000000000 45727664271623 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(302085389/500000000 : ℝ), (-204753237/5000000000 : ℝ), (1083138071/2000000000 : ℝ)] ![(52576295457353/100000000000000 : ℝ), (169604026097/10000000000000 : ℝ), (45727664271623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(302085389/500000000 : ℝ)|^37 ≤ (52576295457353/100000000000000 : ℝ)^29
        have hw : |(302085389/500000000 : ℝ)|=(302085389/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-204753237/5000000000 : ℝ)|^37 ≤ (169604026097/10000000000000 : ℝ)^29
        have hw : |(-204753237/5000000000 : ℝ)|=(204753237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1083138071/2000000000 : ℝ)|^37 ≤ (45727664271623/100000000000000 : ℝ)^29
        have hw : |(1083138071/2000000000 : ℝ)|=(1083138071/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312023_s1_s1_2 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1511248229/5000000000 : ℝ)*x 0 + (3037799131/5000000000 : ℝ)*x 1 + (-170374173/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1511248229/5000000000 : ℝ)^37 ≤ (5431983522937/25000000000000 : ℝ)^29 := by
    have hnat : (1511248229 : ℕ)^37*25000000000000^29 ≤ 5431983522937^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1511248229 5000000000 5431983522937 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3037799131/5000000000 : ℝ)^37 ≤ (52952866719607/100000000000000 : ℝ)^29 := by
    have hnat : (3037799131 : ℕ)^37*100000000000000^29 ≤ 52952866719607^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3037799131 5000000000 52952866719607 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (170374173/500000000 : ℝ)^37 ≤ (2531919917011/10000000000000 : ℝ)^29 := by
    have hnat : (170374173 : ℕ)^37*10000000000000^29 ≤ 2531919917011^29*500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170374173 500000000 2531919917011 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1511248229/5000000000 : ℝ), (3037799131/5000000000 : ℝ), (-170374173/500000000 : ℝ)] ![(5431983522937/25000000000000 : ℝ), (52952866719607/100000000000000 : ℝ), (2531919917011/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1511248229/5000000000 : ℝ)|^37 ≤ (5431983522937/25000000000000 : ℝ)^29
        have hw : |(1511248229/5000000000 : ℝ)|=(1511248229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3037799131/5000000000 : ℝ)|^37 ≤ (52952866719607/100000000000000 : ℝ)^29
        have hw : |(3037799131/5000000000 : ℝ)|=(3037799131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-170374173/500000000 : ℝ)|^37 ≤ (2531919917011/10000000000000 : ℝ)^29
        have hw : |(-170374173/500000000 : ℝ)|=(170374173/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312023_s1_s1_6 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (821403501/2000000000 : ℝ)*x 0 + (1217311511/2500000000 : ℝ)*x 1 + (3681464893/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (821403501/2000000000 : ℝ)^37 ≤ (62754262279/195312500000 : ℝ)^29 := by
    have hnat : (821403501 : ℕ)^37*195312500000^29 ≤ 62754262279^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      821403501 2000000000 62754262279 195312500000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1217311511/2500000000 : ℝ)^37 ≤ (19962469605521/50000000000000 : ℝ)^29 := by
    have hnat : (1217311511 : ℕ)^37*50000000000000^29 ≤ 19962469605521^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1217311511 2500000000 19962469605521 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3681464893/10000000000 : ℝ)^37 ≤ (5588975699019/20000000000000 : ℝ)^29 := by
    have hnat : (3681464893 : ℕ)^37*20000000000000^29 ≤ 5588975699019^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3681464893 10000000000 5588975699019 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(821403501/2000000000 : ℝ), (1217311511/2500000000 : ℝ), (3681464893/10000000000 : ℝ)] ![(62754262279/195312500000 : ℝ), (19962469605521/50000000000000 : ℝ), (5588975699019/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(821403501/2000000000 : ℝ)|^37 ≤ (62754262279/195312500000 : ℝ)^29
        have hw : |(821403501/2000000000 : ℝ)|=(821403501/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1217311511/2500000000 : ℝ)|^37 ≤ (19962469605521/50000000000000 : ℝ)^29
        have hw : |(1217311511/2500000000 : ℝ)|=(1217311511/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3681464893/10000000000 : ℝ)|^37 ≤ (5588975699019/20000000000000 : ℝ)^29
        have hw : |(3681464893/10000000000 : ℝ)|=(3681464893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312023_s1_s1_7 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-413298391/1250000000 : ℝ)*x 0 + (5499844047/10000000000 : ℝ)*x 1 + (3789881879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (413298391/1250000000 : ℝ)^37 ≤ (24364730905123/100000000000000 : ℝ)^29 := by
    have hnat : (413298391 : ℕ)^37*100000000000000^29 ≤ 24364730905123^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413298391 1250000000 24364730905123 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5499844047/10000000000 : ℝ)^37 ≤ (46636171645559/100000000000000 : ℝ)^29 := by
    have hnat : (5499844047 : ℕ)^37*100000000000000^29 ≤ 46636171645559^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5499844047 10000000000 46636171645559 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3789881879/10000000000 : ℝ)^37 ≤ (1159963897027/4000000000000 : ℝ)^29 := by
    have hnat : (3789881879 : ℕ)^37*4000000000000^29 ≤ 1159963897027^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3789881879 10000000000 1159963897027 4000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-413298391/1250000000 : ℝ), (5499844047/10000000000 : ℝ), (3789881879/10000000000 : ℝ)] ![(24364730905123/100000000000000 : ℝ), (46636171645559/100000000000000 : ℝ), (1159963897027/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-413298391/1250000000 : ℝ)|^37 ≤ (24364730905123/100000000000000 : ℝ)^29
        have hw : |(-413298391/1250000000 : ℝ)|=(413298391/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5499844047/10000000000 : ℝ)|^37 ≤ (46636171645559/100000000000000 : ℝ)^29
        have hw : |(5499844047/10000000000 : ℝ)|=(5499844047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3789881879/10000000000 : ℝ)|^37 ≤ (1159963897027/4000000000000 : ℝ)^29
        have hw : |(3789881879/10000000000 : ℝ)|=(3789881879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312023_s1_s1_8 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (568792861/1000000000 : ℝ)*x 0 + (1099949/1000000000 : ℝ)*x 1 + (740836657/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (568792861/1000000000 : ℝ)^37 ≤ (12170131944753/25000000000000 : ℝ)^29 := by
    have hnat : (568792861 : ℕ)^37*25000000000000^29 ≤ 12170131944753^29*1000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      568792861 1000000000 12170131944753 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1099949/1000000000 : ℝ)^37 ≤ (16795752231/100000000000000 : ℝ)^29 := by
    have hnat : (1099949 : ℕ)^37*100000000000000^29 ≤ 16795752231^29*1000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099949 1000000000 16795752231 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (740836657/1250000000 : ℝ)^37 ≤ (51302676458447/100000000000000 : ℝ)^29 := by
    have hnat : (740836657 : ℕ)^37*100000000000000^29 ≤ 51302676458447^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      740836657 1250000000 51302676458447 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(568792861/1000000000 : ℝ), (1099949/1000000000 : ℝ), (740836657/1250000000 : ℝ)] ![(12170131944753/25000000000000 : ℝ), (16795752231/100000000000000 : ℝ), (51302676458447/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(568792861/1000000000 : ℝ)|^37 ≤ (12170131944753/25000000000000 : ℝ)^29
        have hw : |(568792861/1000000000 : ℝ)|=(568792861/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1099949/1000000000 : ℝ)|^37 ≤ (16795752231/100000000000000 : ℝ)^29
        have hw : |(1099949/1000000000 : ℝ)|=(1099949/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(740836657/1250000000 : ℝ)|^37 ≤ (51302676458447/100000000000000 : ℝ)^29
        have hw : |(740836657/1250000000 : ℝ)|=(740836657/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312023_s1_s1_9 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2634427887/10000000000 : ℝ)*x 0 + (6706304917/10000000000 : ℝ)*x 1 + (-37745771/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2634427887/10000000000 : ℝ)^37 ≤ (18233735192303/100000000000000 : ℝ)^29 := by
    have hnat : (2634427887 : ℕ)^37*100000000000000^29 ≤ 18233735192303^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2634427887 10000000000 18233735192303 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6706304917/10000000000 : ℝ)^37 ≤ (30032163730711/50000000000000 : ℝ)^29 := by
    have hnat : (6706304917 : ℕ)^37*50000000000000^29 ≤ 30032163730711^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6706304917 10000000000 30032163730711 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (37745771/125000000 : ℝ)^37 ≤ (339092770817/1562500000000 : ℝ)^29 := by
    have hnat : (37745771 : ℕ)^37*1562500000000^29 ≤ 339092770817^29*125000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37745771 125000000 339092770817 1562500000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2634427887/10000000000 : ℝ), (6706304917/10000000000 : ℝ), (-37745771/125000000 : ℝ)] ![(18233735192303/100000000000000 : ℝ), (30032163730711/50000000000000 : ℝ), (339092770817/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2634427887/10000000000 : ℝ)|^37 ≤ (18233735192303/100000000000000 : ℝ)^29
        have hw : |(2634427887/10000000000 : ℝ)|=(2634427887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6706304917/10000000000 : ℝ)|^37 ≤ (30032163730711/50000000000000 : ℝ)^29
        have hw : |(6706304917/10000000000 : ℝ)|=(6706304917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-37745771/125000000 : ℝ)|^37 ≤ (339092770817/1562500000000 : ℝ)^29
        have hw : |(-37745771/125000000 : ℝ)|=(37745771/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312023_s1_s1_12 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1863867727/5000000000 : ℝ)*x 0 + (1007303623/2000000000 : ℝ)*x 1 + (1942108111/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1863867727/5000000000 : ℝ)^37 ≤ (7098442147341/25000000000000 : ℝ)^29 := by
    have hnat : (1863867727 : ℕ)^37*25000000000000^29 ≤ 7098442147341^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1863867727 5000000000 7098442147341 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1007303623/2000000000 : ℝ)^37 ≤ (8336609749841/20000000000000 : ℝ)^29 := by
    have hnat : (1007303623 : ℕ)^37*20000000000000^29 ≤ 8336609749841^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1007303623 2000000000 8336609749841 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1942108111/5000000000 : ℝ)^37 ≤ (374039782931/1250000000000 : ℝ)^29 := by
    have hnat : (1942108111 : ℕ)^37*1250000000000^29 ≤ 374039782931^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1942108111 5000000000 374039782931 1250000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1863867727/5000000000 : ℝ), (1007303623/2000000000 : ℝ), (1942108111/5000000000 : ℝ)] ![(7098442147341/25000000000000 : ℝ), (8336609749841/20000000000000 : ℝ), (374039782931/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1863867727/5000000000 : ℝ)|^37 ≤ (7098442147341/25000000000000 : ℝ)^29
        have hw : |(1863867727/5000000000 : ℝ)|=(1863867727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1007303623/2000000000 : ℝ)|^37 ≤ (8336609749841/20000000000000 : ℝ)^29
        have hw : |(1007303623/2000000000 : ℝ)|=(1007303623/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1942108111/5000000000 : ℝ)|^37 ≤ (374039782931/1250000000000 : ℝ)^29
        have hw : |(1942108111/5000000000 : ℝ)|=(1942108111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312023_s1_s1_13 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2030716887/5000000000 : ℝ)*x 0 + (5140862289/10000000000 : ℝ)*x 1 + (3430344771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2030716887/5000000000 : ℝ)^37 ≤ (15837946199579/50000000000000 : ℝ)^29 := by
    have hnat : (2030716887 : ℕ)^37*50000000000000^29 ≤ 15837946199579^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2030716887 5000000000 15837946199579 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5140862289/10000000000 : ℝ)^37 ≤ (21393988578117/50000000000000 : ℝ)^29 := by
    have hnat : (5140862289 : ℕ)^37*50000000000000^29 ≤ 21393988578117^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5140862289 10000000000 21393988578117 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3430344771/10000000000 : ℝ)^37 ≤ (25536130424907/100000000000000 : ℝ)^29 := by
    have hnat : (3430344771 : ℕ)^37*100000000000000^29 ≤ 25536130424907^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3430344771 10000000000 25536130424907 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2030716887/5000000000 : ℝ), (5140862289/10000000000 : ℝ), (3430344771/10000000000 : ℝ)] ![(15837946199579/50000000000000 : ℝ), (21393988578117/50000000000000 : ℝ), (25536130424907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2030716887/5000000000 : ℝ)|^37 ≤ (15837946199579/50000000000000 : ℝ)^29
        have hw : |(-2030716887/5000000000 : ℝ)|=(2030716887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5140862289/10000000000 : ℝ)|^37 ≤ (21393988578117/50000000000000 : ℝ)^29
        have hw : |(5140862289/10000000000 : ℝ)|=(5140862289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3430344771/10000000000 : ℝ)|^37 ≤ (25536130424907/100000000000000 : ℝ)^29
        have hw : |(3430344771/10000000000 : ℝ)|=(3430344771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312023_s1_s1_14 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3243758773/5000000000 : ℝ)*x 0 + (-28685253/1000000000 : ℝ)*x 1 + (1000942891/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3243758773/5000000000 : ℝ)^37 ≤ (1799236139913/3125000000000 : ℝ)^29 := by
    have hnat : (3243758773 : ℕ)^37*3125000000000^29 ≤ 1799236139913^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3243758773 5000000000 1799236139913 3125000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (28685253/1000000000 : ℝ)^37 ≤ (269231100879/25000000000000 : ℝ)^29 := by
    have hnat : (28685253 : ℕ)^37*25000000000000^29 ≤ 269231100879^29*1000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28685253 1000000000 269231100879 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1000942891/2000000000 : ℝ)^37 ≤ (20673759551717/50000000000000 : ℝ)^29 := by
    have hnat : (1000942891 : ℕ)^37*50000000000000^29 ≤ 20673759551717^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1000942891 2000000000 20673759551717 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3243758773/5000000000 : ℝ), (-28685253/1000000000 : ℝ), (1000942891/2000000000 : ℝ)] ![(1799236139913/3125000000000 : ℝ), (269231100879/25000000000000 : ℝ), (20673759551717/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3243758773/5000000000 : ℝ)|^37 ≤ (1799236139913/3125000000000 : ℝ)^29
        have hw : |(3243758773/5000000000 : ℝ)|=(3243758773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-28685253/1000000000 : ℝ)|^37 ≤ (269231100879/25000000000000 : ℝ)^29
        have hw : |(-28685253/1000000000 : ℝ)|=(28685253/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1000942891/2000000000 : ℝ)|^37 ≤ (20673759551717/50000000000000 : ℝ)^29
        have hw : |(1000942891/2000000000 : ℝ)|=(1000942891/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312023_s1_s1_15 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1171355303/5000000000 : ℝ)*x 0 + (374563561/625000000 : ℝ)*x 1 + (-412057621/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1171355303/5000000000 : ℝ)^37 ≤ (15698130125383/100000000000000 : ℝ)^29 := by
    have hnat : (1171355303 : ℕ)^37*100000000000000^29 ≤ 15698130125383^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1171355303 5000000000 15698130125383 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (374563561/625000000 : ℝ)^37 ≤ (5203629147331/10000000000000 : ℝ)^29 := by
    have hnat : (374563561 : ℕ)^37*10000000000000^29 ≤ 5203629147331^29*625000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      374563561 625000000 5203629147331 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (412057621/1000000000 : ℝ)^37 ≤ (16132789189689/50000000000000 : ℝ)^29 := by
    have hnat : (412057621 : ℕ)^37*50000000000000^29 ≤ 16132789189689^29*1000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412057621 1000000000 16132789189689 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1171355303/5000000000 : ℝ), (374563561/625000000 : ℝ), (-412057621/1000000000 : ℝ)] ![(15698130125383/100000000000000 : ℝ), (5203629147331/10000000000000 : ℝ), (16132789189689/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1171355303/5000000000 : ℝ)|^37 ≤ (15698130125383/100000000000000 : ℝ)^29
        have hw : |(1171355303/5000000000 : ℝ)|=(1171355303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(374563561/625000000 : ℝ)|^37 ≤ (5203629147331/10000000000000 : ℝ)^29
        have hw : |(374563561/625000000 : ℝ)|=(374563561/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-412057621/1000000000 : ℝ)|^37 ≤ (16132789189689/50000000000000 : ℝ)^29
        have hw : |(-412057621/1000000000 : ℝ)|=(412057621/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312023_s1_s1_19 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1619271267/5000000000 : ℝ)*x 0 + (5344753639/10000000000 : ℝ)*x 1 + (100606499/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1619271267/5000000000 : ℝ)^37 ≤ (4745736598773/20000000000000 : ℝ)^29 := by
    have hnat : (1619271267 : ℕ)^37*20000000000000^29 ≤ 4745736598773^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1619271267 5000000000 4745736598773 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5344753639/10000000000 : ℝ)^37 ≤ (22482430838289/50000000000000 : ℝ)^29 := by
    have hnat : (5344753639 : ℕ)^37*50000000000000^29 ≤ 22482430838289^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344753639 10000000000 22482430838289 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (100606499/250000000 : ℝ)^37 ≤ (313064553177/1000000000000 : ℝ)^29 := by
    have hnat : (100606499 : ℕ)^37*1000000000000^29 ≤ 313064553177^29*250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100606499 250000000 313064553177 1000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1619271267/5000000000 : ℝ), (5344753639/10000000000 : ℝ), (100606499/250000000 : ℝ)] ![(4745736598773/20000000000000 : ℝ), (22482430838289/50000000000000 : ℝ), (313064553177/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1619271267/5000000000 : ℝ)|^37 ≤ (4745736598773/20000000000000 : ℝ)^29
        have hw : |(1619271267/5000000000 : ℝ)|=(1619271267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5344753639/10000000000 : ℝ)|^37 ≤ (22482430838289/50000000000000 : ℝ)^29
        have hw : |(5344753639/10000000000 : ℝ)|=(5344753639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(100606499/250000000 : ℝ)|^37 ≤ (313064553177/1000000000000 : ℝ)^29
        have hw : |(100606499/250000000 : ℝ)|=(100606499/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312023_s1_s1_20 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2920074591/10000000000 : ℝ)*x 0 + (2948678973/5000000000 : ℝ)*x 1 + (1855339679/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2920074591/10000000000 : ℝ)^37 ≤ (10396482270967/50000000000000 : ℝ)^29 := by
    have hnat : (2920074591 : ℕ)^37*50000000000000^29 ≤ 10396482270967^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2920074591 10000000000 10396482270967 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2948678973/5000000000 : ℝ)^37 ≤ (5097891509207/10000000000000 : ℝ)^29 := by
    have hnat : (2948678973 : ℕ)^37*10000000000000^29 ≤ 5097891509207^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2948678973 5000000000 5097891509207 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1855339679/5000000000 : ℝ)^37 ≤ (3528515042999/12500000000000 : ℝ)^29 := by
    have hnat : (1855339679 : ℕ)^37*12500000000000^29 ≤ 3528515042999^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1855339679 5000000000 3528515042999 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2920074591/10000000000 : ℝ), (2948678973/5000000000 : ℝ), (1855339679/5000000000 : ℝ)] ![(10396482270967/50000000000000 : ℝ), (5097891509207/10000000000000 : ℝ), (3528515042999/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2920074591/10000000000 : ℝ)|^37 ≤ (10396482270967/50000000000000 : ℝ)^29
        have hw : |(-2920074591/10000000000 : ℝ)|=(2920074591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2948678973/5000000000 : ℝ)|^37 ≤ (5097891509207/10000000000000 : ℝ)^29
        have hw : |(2948678973/5000000000 : ℝ)|=(2948678973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1855339679/5000000000 : ℝ)|^37 ≤ (3528515042999/12500000000000 : ℝ)^29
        have hw : |(1855339679/5000000000 : ℝ)|=(1855339679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312023_s1_s1_21 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1686695451/2500000000 : ℝ)*x 0 + (5376103/10000000000 : ℝ)*x 1 + (2412661317/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1686695451/2500000000 : ℝ)^37 ≤ (3782952905391/6250000000000 : ℝ)^29 := by
    have hnat : (1686695451 : ℕ)^37*6250000000000^29 ≤ 3782952905391^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1686695451 2500000000 3782952905391 6250000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5376103/10000000000 : ℝ)^37 ≤ (6737947193/100000000000000 : ℝ)^29 := by
    have hnat : (5376103 : ℕ)^37*100000000000000^29 ≤ 6737947193^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376103 10000000000 6737947193 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2412661317/5000000000 : ℝ)^37 ≤ (19733007778421/50000000000000 : ℝ)^29 := by
    have hnat : (2412661317 : ℕ)^37*50000000000000^29 ≤ 19733007778421^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2412661317 5000000000 19733007778421 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1686695451/2500000000 : ℝ), (5376103/10000000000 : ℝ), (2412661317/5000000000 : ℝ)] ![(3782952905391/6250000000000 : ℝ), (6737947193/100000000000000 : ℝ), (19733007778421/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1686695451/2500000000 : ℝ)|^37 ≤ (3782952905391/6250000000000 : ℝ)^29
        have hw : |(1686695451/2500000000 : ℝ)|=(1686695451/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5376103/10000000000 : ℝ)|^37 ≤ (6737947193/100000000000000 : ℝ)^29
        have hw : |(5376103/10000000000 : ℝ)|=(5376103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2412661317/5000000000 : ℝ)|^37 ≤ (19733007778421/50000000000000 : ℝ)^29
        have hw : |(2412661317/5000000000 : ℝ)|=(2412661317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312023_s1_s1_22 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2536404147/10000000000 : ℝ)*x 0 + (6616734753/10000000000 : ℝ)*x 1 + (-1611565427/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2536404147/10000000000 : ℝ)^37 ≤ (17372604183109/100000000000000 : ℝ)^29 := by
    have hnat : (2536404147 : ℕ)^37*100000000000000^29 ≤ 17372604183109^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2536404147 10000000000 17372604183109 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6616734753/10000000000 : ℝ)^37 ≤ (59042689517117/100000000000000 : ℝ)^29 := by
    have hnat : (6616734753 : ℕ)^37*100000000000000^29 ≤ 59042689517117^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6616734753 10000000000 59042689517117 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1611565427/5000000000 : ℝ)^37 ≤ (23584706282501/100000000000000 : ℝ)^29 := by
    have hnat : (1611565427 : ℕ)^37*100000000000000^29 ≤ 23584706282501^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1611565427 5000000000 23584706282501 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2536404147/10000000000 : ℝ), (6616734753/10000000000 : ℝ), (-1611565427/5000000000 : ℝ)] ![(17372604183109/100000000000000 : ℝ), (59042689517117/100000000000000 : ℝ), (23584706282501/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2536404147/10000000000 : ℝ)|^37 ≤ (17372604183109/100000000000000 : ℝ)^29
        have hw : |(2536404147/10000000000 : ℝ)|=(2536404147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6616734753/10000000000 : ℝ)|^37 ≤ (59042689517117/100000000000000 : ℝ)^29
        have hw : |(6616734753/10000000000 : ℝ)|=(6616734753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1611565427/5000000000 : ℝ)|^37 ≤ (23584706282501/100000000000000 : ℝ)^29
        have hw : |(-1611565427/5000000000 : ℝ)|=(1611565427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312023_s1_s1_25 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (982561183/2000000000 : ℝ)*x 0 + (1055661519/2500000000 : ℝ)*x 1 + (878414119/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (982561183/2000000000 : ℝ)^37 ≤ (10095298453107/25000000000000 : ℝ)^29 := by
    have hnat : (982561183 : ℕ)^37*25000000000000^29 ≤ 10095298453107^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      982561183 2000000000 10095298453107 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1055661519/2500000000 : ℝ)^37 ≤ (33288766130681/100000000000000 : ℝ)^29 := by
    have hnat : (1055661519 : ℕ)^37*100000000000000^29 ≤ 33288766130681^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055661519 2500000000 33288766130681 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (878414119/2500000000 : ℝ)^37 ≤ (1316502001739/5000000000000 : ℝ)^29 := by
    have hnat : (878414119 : ℕ)^37*5000000000000^29 ≤ 1316502001739^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      878414119 2500000000 1316502001739 5000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(982561183/2000000000 : ℝ), (1055661519/2500000000 : ℝ), (878414119/2500000000 : ℝ)] ![(10095298453107/25000000000000 : ℝ), (33288766130681/100000000000000 : ℝ), (1316502001739/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(982561183/2000000000 : ℝ)|^37 ≤ (10095298453107/25000000000000 : ℝ)^29
        have hw : |(982561183/2000000000 : ℝ)|=(982561183/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1055661519/2500000000 : ℝ)|^37 ≤ (33288766130681/100000000000000 : ℝ)^29
        have hw : |(1055661519/2500000000 : ℝ)|=(1055661519/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(878414119/2500000000 : ℝ)|^37 ≤ (1316502001739/5000000000000 : ℝ)^29
        have hw : |(878414119/2500000000 : ℝ)|=(878414119/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c312023_s1 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((76149/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(76149/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(1837/4000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(1837/4000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(83759/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(83759/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((48059/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(48059/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(431/5000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(431/5000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13387/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(13387/25000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (78337/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (78337/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (78337/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (78337/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (78337/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (78337/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (178281/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (76149/100000 : ℝ) ^ (9/2 : ℝ) ≤ (29341946453183204853/100000000000000000000 : ℝ) := by
    have hpowers : (76149/100000 : ℝ)^9 ≤ (29341946453183204853/100000000000000000000 : ℝ)^2 := by
      have hnat : (76149 : ℕ)^9*100000000000000000000^2 ≤ 29341946453183204853^2*100000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        76149 100000 29341946453183204853 100000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (76149/100000 : ℝ)) (X := (29341946453183204853/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner0a : (129341946453183204853/100000000000000000000 : ℝ) ≤ (423536620932637/400000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (129341946453183204853/100000000000000000000 : ℝ)^2 ≤ (423536620932637/400000000000000 : ℝ)^9 := by
      have hnat : (129341946453183204853 : ℕ)^2*400000000000000^9 ≤ 423536620932637^9*100000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        129341946453183204853 100000000000000000000 423536620932637 400000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (423536620932637/400000000000000 : ℝ)) (X := (129341946453183204853/100000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner0b : (79341946453183204853/50000000000000000000 : ℝ) ≤ (443223568521049/400000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (79341946453183204853/50000000000000000000 : ℝ)^2 ≤ (443223568521049/400000000000000 : ℝ)^9 := by
      have hnat : (79341946453183204853 : ℕ)^2*400000000000000^9 ≤ 443223568521049^9*50000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        79341946453183204853 50000000000000000000 443223568521049 400000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (443223568521049/400000000000000 : ℝ)) (X := (79341946453183204853/50000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(7845540310879/101532000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1640578965701/25383000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (76149/100000 : ℝ)) (alpha := (7845540310879/101532000000000 : ℝ)) (beta := (1640578965701/25383000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (76149/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(7845540310879/101532000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1640578965701/25383000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (1837/4000 : ℝ) ^ (9/2 : ℝ) ≤ (3014541329228160249/100000000000000000000 : ℝ) := by
    have hpowers : (1837/4000 : ℝ)^9 ≤ (3014541329228160249/100000000000000000000 : ℝ)^2 := by
      have hnat : (1837 : ℕ)^9*100000000000000000000^2 ≤ 3014541329228160249^2*4000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1837 4000 3014541329228160249 100000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1837/4000 : ℝ)) (X := (3014541329228160249/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner1a : (103014541329228160249/100000000000000000000 : ℝ) ≤ (2013243642671851/2000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (103014541329228160249/100000000000000000000 : ℝ)^2 ≤ (2013243642671851/2000000000000000 : ℝ)^9 := by
      have hnat : (103014541329228160249 : ℕ)^2*2000000000000000^9 ≤ 2013243642671851^9*100000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        103014541329228160249 100000000000000000000 2013243642671851 2000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2013243642671851/2000000000000000 : ℝ)) (X := (103014541329228160249/100000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner1b : (53014541329228160249/50000000000000000000 : ℝ) ≤ (5065473004724039/5000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (53014541329228160249/50000000000000000000 : ℝ)^2 ≤ (5065473004724039/5000000000000000 : ℝ)^9 := by
      have hnat : (53014541329228160249 : ℕ)^2*5000000000000000^9 ≤ 5065473004724039^9*50000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        53014541329228160249 50000000000000000000 5065473004724039 5000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5065473004724039/5000000000000000 : ℝ)) (X := (53014541329228160249/50000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(13243642671851/918500000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(64727796088823/4592500000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (1837/4000 : ℝ)) (alpha := (13243642671851/918500000000000 : ℝ)) (beta := (64727796088823/4592500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1837/4000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(13243642671851/918500000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(64727796088823/4592500000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (83759/100000 : ℝ) ^ (9/2 : ℝ) ≤ (45044490238505300063/100000000000000000000 : ℝ) := by
    have hpowers : (83759/100000 : ℝ)^9 ≤ (45044490238505300063/100000000000000000000 : ℝ)^2 := by
      have hnat : (83759 : ℕ)^9*100000000000000000000^2 ≤ 45044490238505300063^2*100000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        83759 100000 45044490238505300063 100000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (83759/100000 : ℝ)) (X := (45044490238505300063/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner2a : (145044490238505300063/100000000000000000000 : ℝ) ≤ (10861483919579211/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (145044490238505300063/100000000000000000000 : ℝ)^2 ≤ (10861483919579211/10000000000000000 : ℝ)^9 := by
      have hnat : (145044490238505300063 : ℕ)^2*10000000000000000^9 ≤ 10861483919579211^9*100000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        145044490238505300063 100000000000000000000 10861483919579211 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10861483919579211/10000000000000000 : ℝ)) (X := (145044490238505300063/100000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner2b : (95044490238505300063/50000000000000000000 : ℝ) ≤ (2306855689361357/2000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (95044490238505300063/50000000000000000000 : ℝ)^2 ≤ (2306855689361357/2000000000000000 : ℝ)^9 := by
      have hnat : (95044490238505300063 : ℕ)^2*2000000000000000^9 ≤ 2306855689361357^9*50000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        95044490238505300063 50000000000000000000 2306855689361357 2000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2306855689361357/2000000000000000 : ℝ)) (X := (95044490238505300063/50000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(861483919579211/8375900000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(336397263613787/4187950000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (83759/100000 : ℝ)) (alpha := (861483919579211/8375900000000000 : ℝ)) (beta := (336397263613787/4187950000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (83759/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(861483919579211/8375900000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(336397263613787/4187950000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-3303754203/10000000000 : ℝ)*X 0 0+(278041869/500000000 : ℝ)*X 0 1+(3724566087/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312023_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((302085389/500000000 : ℝ)*X 1 0+(-204753237/5000000000 : ℝ)*X 1 1+(1083138071/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312023_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((1511248229/5000000000 : ℝ)*X 2 0+(3037799131/5000000000 : ℝ)*X 2 1+(-170374173/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312023_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((821403501/2000000000 : ℝ)*X 0 0+(1217311511/2500000000 : ℝ)*X 0 1+(3681464893/10000000000 : ℝ)*X 0 2+(821403501/2000000000 : ℝ)*X 1 0+(1217311511/2500000000 : ℝ)*X 1 1+(3681464893/10000000000 : ℝ)*X 1 2+(821403501/2000000000 : ℝ)*X 2 0+(1217311511/2500000000 : ℝ)*X 2 1+(3681464893/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312023_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-413298391/1250000000 : ℝ)*X 0 0+(5499844047/10000000000 : ℝ)*X 0 1+(3789881879/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312023_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((568792861/1000000000 : ℝ)*X 1 0+(1099949/1000000000 : ℝ)*X 1 1+(740836657/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312023_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((2634427887/10000000000 : ℝ)*X 2 0+(6706304917/10000000000 : ℝ)*X 2 1+(-37745771/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312023_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_12 : ((1863867727/5000000000 : ℝ)*X 0 0+(1007303623/2000000000 : ℝ)*X 0 1+(1942108111/5000000000 : ℝ)*X 0 2+(1863867727/5000000000 : ℝ)*X 1 0+(1007303623/2000000000 : ℝ)*X 1 1+(1942108111/5000000000 : ℝ)*X 1 2+(1863867727/5000000000 : ℝ)*X 2 0+(1007303623/2000000000 : ℝ)*X 2 1+(1942108111/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312023_s1_s1_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((-2030716887/5000000000 : ℝ)*X 0 0+(5140862289/10000000000 : ℝ)*X 0 1+(3430344771/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312023_s1_s1_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((3243758773/5000000000 : ℝ)*X 1 0+(-28685253/1000000000 : ℝ)*X 1 1+(1000942891/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312023_s1_s1_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((1171355303/5000000000 : ℝ)*X 2 0+(374563561/625000000 : ℝ)*X 2 1+(-412057621/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312023_s1_s1_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_19 : ((1619271267/5000000000 : ℝ)*X 0 0+(5344753639/10000000000 : ℝ)*X 0 1+(100606499/250000000 : ℝ)*X 0 2+(1619271267/5000000000 : ℝ)*X 1 0+(5344753639/10000000000 : ℝ)*X 1 1+(100606499/250000000 : ℝ)*X 1 2+(1619271267/5000000000 : ℝ)*X 2 0+(5344753639/10000000000 : ℝ)*X 2 1+(100606499/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312023_s1_s1_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((-2920074591/10000000000 : ℝ)*X 0 0+(2948678973/5000000000 : ℝ)*X 0 1+(1855339679/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312023_s1_s1_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((1686695451/2500000000 : ℝ)*X 1 0+(5376103/10000000000 : ℝ)*X 1 1+(2412661317/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312023_s1_s1_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((2536404147/10000000000 : ℝ)*X 2 0+(6616734753/10000000000 : ℝ)*X 2 1+(-1611565427/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312023_s1_s1_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_25 : ((982561183/2000000000 : ℝ)*X 0 0+(1055661519/2500000000 : ℝ)*X 0 1+(878414119/2500000000 : ℝ)*X 0 2+(982561183/2000000000 : ℝ)*X 1 0+(1055661519/2500000000 : ℝ)*X 1 1+(878414119/2500000000 : ℝ)*X 1 2+(982561183/2000000000 : ℝ)*X 2 0+(1055661519/2500000000 : ℝ)*X 2 1+(878414119/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312023_s1_s1_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((48059/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(48059/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (8792255884562162903416569/607142851562500000000000000000 : ℝ) := by norm_num
    linear_combination (271917471697/1000000000000 : ℝ)*(base7) + (50249/15625000000 : ℝ)*(base40) + (306300328077/100000000000 : ℝ)*(base49) + (1790348672379/1000000000000 : ℝ)*(base50) + (2962567778241/500000000000 : ℝ)*(major_s1_0) + (2962567778241/500000000000 : ℝ)*(major_s1_1) + (2962567778241/500000000000 : ℝ)*(major_s1_2) + (317207107/500000000000 : ℝ)*(sp_s1_0) + (4069084502337/500000000000 : ℝ)*(sp_s1_7) + (508677450731/62500000000 : ℝ)*(sp_s1_8) + (4069271904887/500000000000 : ℝ)*(sp_s1_9) + (955438037483/250000000000 : ℝ)*(sp_s1_12) + (4474101/125000000000 : ℝ)*(sp_s1_20) + (295401923/1000000000000 : ℝ)*(sp_s1_22) + (709966935647/200000000000 : ℝ)*(f.failure) + (508677450731/62500000000 : ℝ)*(f.sum) + (4912302591181062521/9616580187500000000000000000000 : ℝ)*base62 + (108727297135033/523493750000000000000000000 : ℝ)*base65 + (1639689102901657/2296250000000000000000000000 : ℝ)*base67 + (929811932371891/4187950000000000000000000000 : ℝ)*base69 + (16862591096113804251/35434244950000000000000000000000 : ℝ)*base70 + (2642569493853/4230500000000000000000000 : ℝ)*base73 + (121321002802533/229625000000000000000000000 : ℝ)*base74 + (1149481654533/1322031250000000000000000 : ℝ)*base76 + (22598009187525608627/19428571250000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (7711/20000000000000000 : ℝ)*base87 + (7711/20000000000000000 : ℝ)*base89 + (7711/20000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(431/5000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(431/5000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (12837241266625619807234234182191/813658849664375000000000000000000000 : ℝ) := by norm_num
    linear_combination (264218747341/1000000000000 : ℝ)*(base40) + (570305702077/1000000000000 : ℝ)*(base49) + (1731823/500000000000 : ℝ)*(base60) + (1079071718811/500000000000 : ℝ)*(major_s1_0) + (1079071718811/500000000000 : ℝ)*(major_s1_1) + (1079071718811/500000000000 : ℝ)*(major_s1_2) + (10733509/500000000000 : ℝ)*(sp_s1_1) + (1076711/1000000000000 : ℝ)*(sp_s1_7) + (57082499/500000000000 : ℝ)*(sp_s1_8) + (43319341/125000000000 : ℝ)*(sp_s1_12) + (604661098803/200000000000 : ℝ)*(sp_s1_13) + (302317093871/100000000000 : ℝ)*(sp_s1_14) + (1511653285363/500000000000 : ℝ)*(sp_s1_15) + (161578561341/125000000000 : ℝ)*(sp_s1_19) + (80810940341/62500000000 : ℝ)*(f.failure) + (1511653285363/500000000000 : ℝ)*(f.sum) + (64640393314412023/1202072523437500000000000000000 : ℝ)*base63 + (409650556977683/2093975000000000000000000000 : ℝ)*base64 + (773786279911797/2296250000000000000000000000 : ℝ)*base67 + (608989650199641/4187950000000000000000000000 : ℝ)*base69 + (12651226036495160121/35434244950000000000000000000000 : ℝ)*base70 + (4692167890819/21152500000000000000000000 : ℝ)*base73 + (69186677667661/459250000000000000000000000 : ℝ)*base74 + (18519099481853/84610000000000000000000000 : ℝ)*base76 + (10487736451842744167/19428571250000000000000000000000 : ℝ)*base79 + (167/6250000000000000 : ℝ)*base86 + (167/6250000000000000 : ℝ)*base88 + (167/6250000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13387/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(13387/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (14218634887157636609482321743027/813658849664375000000000000000000000 : ℝ) := by norm_num
    linear_combination (11978122607/100000000000 : ℝ)*(base7) + (746610047653/1000000000000 : ℝ)*(base40) + (1845266335071/500000000000 : ℝ)*(base49) + (2391323563393/1000000000000 : ℝ)*(base50) + (3620013360963/500000000000 : ℝ)*(major_s1_0) + (3620013360963/500000000000 : ℝ)*(major_s1_1) + (3620013360963/500000000000 : ℝ)*(major_s1_2) + (16286239/200000000000 : ℝ)*(sp_s1_2) + (47762701/1000000000000 : ℝ)*(sp_s1_6) + (2435229/5000000000 : ℝ)*(sp_s1_9) + (2517815044191/250000000000 : ℝ)*(sp_s1_20) + (2517815044191/250000000000 : ℝ)*(sp_s1_21) + (10070691699769/1000000000000 : ℝ)*(sp_s1_22) + (139291828633/31250000000 : ℝ)*(sp_s1_25) + (4337605052887/1000000000000 : ℝ)*(f.failure) + (2517815044191/250000000000 : ℝ)*(f.sum) + (11441717954125985263/38466320750000000000000000000000 : ℝ)*base63 + (258378703940891/2093975000000000000000000000 : ℝ)*base65 + (511554013293087/1148125000000000000000000000 : ℝ)*base66 + (280934115004449/2093975000000000000000000000 : ℝ)*base69 + (6356998516649493267/35434244950000000000000000000000 : ℝ)*base71 + (1352635713861/16922000000000000000000000 : ℝ)*base72 + (185561392729337/459250000000000000000000000 : ℝ)*base75 + (2964359749141/10576250000000000000000000 : ℝ)*base77 + (911042220943574529/1214285703125000000000000000000 : ℝ)*base78 + (72169/100000000000000000 : ℝ)*base86 + (72169/100000000000000000 : ℝ)*base88 + (72169/100000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((76149/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(76149/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(1837/4000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(1837/4000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(83759/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(83759/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((48059/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(48059/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(431/5000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(431/5000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13387/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(13387/25000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c312023_s1 p hpa hpb X hX hprev0

#print axioms solution
