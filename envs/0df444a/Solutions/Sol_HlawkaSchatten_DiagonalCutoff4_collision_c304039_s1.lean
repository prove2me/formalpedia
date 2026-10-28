-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c304039_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:39:00.883197+00:00
-- url     : https://prove2.me/submissions/9c8b6f8e-65e1-4acc-9c34-7fff1b71c0a5

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
theorem collision_support_c304039_s1_s1_0 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1545503289/10000000000 : ℝ)*x 0 + (-3077048791/5000000000 : ℝ)*x 1 + (4800062003/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1545503289/10000000000 : ℝ)^17 ≤ (108758448407/1250000000000 : ℝ)^13 := by
    have hnat : (1545503289 : ℕ)^17*1250000000000^13 ≤ 108758448407^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1545503289 10000000000 108758448407 1250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3077048791/5000000000 : ℝ)^17 ≤ (26500976908839/50000000000000 : ℝ)^13 := by
    have hnat : (3077048791 : ℕ)^17*50000000000000^13 ≤ 26500976908839^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3077048791 5000000000 26500976908839 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4800062003/10000000000 : ℝ)^17 ≤ (38297370305031/100000000000000 : ℝ)^13 := by
    have hnat : (4800062003 : ℕ)^17*100000000000000^13 ≤ 38297370305031^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4800062003 10000000000 38297370305031 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1545503289/10000000000 : ℝ), (-3077048791/5000000000 : ℝ), (4800062003/10000000000 : ℝ)] ![(108758448407/1250000000000 : ℝ), (26500976908839/50000000000000 : ℝ), (38297370305031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1545503289/10000000000 : ℝ)|^17 ≤ (108758448407/1250000000000 : ℝ)^13
        have hw : |(-1545503289/10000000000 : ℝ)|=(1545503289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3077048791/5000000000 : ℝ)|^17 ≤ (26500976908839/50000000000000 : ℝ)^13
        have hw : |(-3077048791/5000000000 : ℝ)|=(3077048791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4800062003/10000000000 : ℝ)|^17 ≤ (38297370305031/100000000000000 : ℝ)^13
        have hw : |(4800062003/10000000000 : ℝ)|=(4800062003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304039_s1_s1_1 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1198425771/2500000000 : ℝ)*x 0 + (8109951/20000000 : ℝ)*x 1 + (2044441759/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1198425771/2500000000 : ℝ)^17 ≤ (19115519203861/50000000000000 : ℝ)^13 := by
    have hnat : (1198425771 : ℕ)^17*50000000000000^13 ≤ 19115519203861^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1198425771 2500000000 19115519203861 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8109951/20000000 : ℝ)^17 ≤ (15358161642021/50000000000000 : ℝ)^13 := by
    have hnat : (8109951 : ℕ)^17*50000000000000^13 ≤ 15358161642021^13*20000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8109951 20000000 15358161642021 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2044441759/5000000000 : ℝ)^17 ≤ (15526319145071/50000000000000 : ℝ)^13 := by
    have hnat : (2044441759 : ℕ)^17*50000000000000^13 ≤ 15526319145071^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2044441759 5000000000 15526319145071 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1198425771/2500000000 : ℝ), (8109951/20000000 : ℝ), (2044441759/5000000000 : ℝ)] ![(19115519203861/50000000000000 : ℝ), (15358161642021/50000000000000 : ℝ), (15526319145071/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1198425771/2500000000 : ℝ)|^17 ≤ (19115519203861/50000000000000 : ℝ)^13
        have hw : |(1198425771/2500000000 : ℝ)|=(1198425771/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8109951/20000000 : ℝ)|^17 ≤ (15358161642021/50000000000000 : ℝ)^13
        have hw : |(8109951/20000000 : ℝ)|=(8109951/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2044441759/5000000000 : ℝ)|^17 ≤ (15526319145071/50000000000000 : ℝ)^13
        have hw : |(2044441759/5000000000 : ℝ)|=(2044441759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304039_s1_s1_2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (228611727/500000000 : ℝ)*x 0 + (-208234037/500000000 : ℝ)*x 1 + (-4209367923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (228611727/500000000 : ℝ)^17 ≤ (898447413331/2500000000000 : ℝ)^13 := by
    have hnat : (228611727 : ℕ)^17*2500000000000^13 ≤ 898447413331^13*500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      228611727 500000000 898447413331 2500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (208234037/500000000 : ℝ)^17 ≤ (198797057389/625000000000 : ℝ)^13 := by
    have hnat : (208234037 : ℕ)^17*625000000000^13 ≤ 198797057389^13*500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208234037 500000000 198797057389 625000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4209367923/10000000000 : ℝ)^17 ≤ (32254574277519/100000000000000 : ℝ)^13 := by
    have hnat : (4209367923 : ℕ)^17*100000000000000^13 ≤ 32254574277519^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4209367923 10000000000 32254574277519 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(228611727/500000000 : ℝ), (-208234037/500000000 : ℝ), (-4209367923/10000000000 : ℝ)] ![(898447413331/2500000000000 : ℝ), (198797057389/625000000000 : ℝ), (32254574277519/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(228611727/500000000 : ℝ)|^17 ≤ (898447413331/2500000000000 : ℝ)^13
        have hw : |(228611727/500000000 : ℝ)|=(228611727/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-208234037/500000000 : ℝ)|^17 ≤ (198797057389/625000000000 : ℝ)^13
        have hw : |(-208234037/500000000 : ℝ)|=(208234037/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4209367923/10000000000 : ℝ)|^17 ≤ (32254574277519/100000000000000 : ℝ)^13
        have hw : |(-4209367923/10000000000 : ℝ)|=(4209367923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304039_s1_s1_7 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-88084301/1000000000 : ℝ)*x 0 + (-3308908013/5000000000 : ℝ)*x 1 + (2363881801/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (88084301/1000000000 : ℝ)^17 ≤ (260694529603/6250000000000 : ℝ)^13 := by
    have hnat : (88084301 : ℕ)^17*6250000000000^13 ≤ 260694529603^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88084301 1000000000 260694529603 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3308908013/5000000000 : ℝ)^17 ≤ (3642755278443/6250000000000 : ℝ)^13 := by
    have hnat : (3308908013 : ℕ)^17*6250000000000^13 ≤ 3642755278443^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3308908013 5000000000 3642755278443 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2363881801/5000000000 : ℝ)^17 ≤ (7508960611631/20000000000000 : ℝ)^13 := by
    have hnat : (2363881801 : ℕ)^17*20000000000000^13 ≤ 7508960611631^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2363881801 5000000000 7508960611631 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-88084301/1000000000 : ℝ), (-3308908013/5000000000 : ℝ), (2363881801/5000000000 : ℝ)] ![(260694529603/6250000000000 : ℝ), (3642755278443/6250000000000 : ℝ), (7508960611631/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-88084301/1000000000 : ℝ)|^17 ≤ (260694529603/6250000000000 : ℝ)^13
        have hw : |(-88084301/1000000000 : ℝ)|=(88084301/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3308908013/5000000000 : ℝ)|^17 ≤ (3642755278443/6250000000000 : ℝ)^13
        have hw : |(-3308908013/5000000000 : ℝ)|=(3308908013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2363881801/5000000000 : ℝ)|^17 ≤ (7508960611631/20000000000000 : ℝ)^13
        have hw : |(2363881801/5000000000 : ℝ)|=(2363881801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304039_s1_s1_8 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (954490211/2000000000 : ℝ)*x 0 + (2033597453/5000000000 : ℝ)*x 1 + (4098988469/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (954490211/2000000000 : ℝ)^17 ≤ (9502387077207/25000000000000 : ℝ)^13 := by
    have hnat : (954490211 : ℕ)^17*25000000000000^13 ≤ 9502387077207^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      954490211 2000000000 9502387077207 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2033597453/5000000000 : ℝ)^17 ≤ (1541871075961/5000000000000 : ℝ)^13 := by
    have hnat : (2033597453 : ℕ)^17*5000000000000^13 ≤ 1541871075961^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2033597453 5000000000 1541871075961 5000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4098988469/10000000000 : ℝ)^17 ≤ (6230606031923/20000000000000 : ℝ)^13 := by
    have hnat : (4098988469 : ℕ)^17*20000000000000^13 ≤ 6230606031923^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4098988469 10000000000 6230606031923 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(954490211/2000000000 : ℝ), (2033597453/5000000000 : ℝ), (4098988469/10000000000 : ℝ)] ![(9502387077207/25000000000000 : ℝ), (1541871075961/5000000000000 : ℝ), (6230606031923/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(954490211/2000000000 : ℝ)|^17 ≤ (9502387077207/25000000000000 : ℝ)^13
        have hw : |(954490211/2000000000 : ℝ)|=(954490211/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2033597453/5000000000 : ℝ)|^17 ≤ (1541871075961/5000000000000 : ℝ)^13
        have hw : |(2033597453/5000000000 : ℝ)|=(2033597453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4098988469/10000000000 : ℝ)|^17 ≤ (6230606031923/20000000000000 : ℝ)^13
        have hw : |(4098988469/10000000000 : ℝ)|=(4098988469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304039_s1_s1_9 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (304678269/625000000 : ℝ)*x 0 + (-995698989/2500000000 : ℝ)*x 1 + (-2037616731/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (304678269/625000000 : ℝ)^17 ≤ (1563182180711/4000000000000 : ℝ)^13 := by
    have hnat : (304678269 : ℕ)^17*4000000000000^13 ≤ 1563182180711^13*625000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      304678269 625000000 1563182180711 4000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (995698989/2500000000 : ℝ)^17 ≤ (30003298187781/100000000000000 : ℝ)^13 := by
    have hnat : (995698989 : ℕ)^17*100000000000000^13 ≤ 30003298187781^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      995698989 2500000000 30003298187781 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2037616731/5000000000 : ℝ)^17 ≤ (309171472773/1000000000000 : ℝ)^13 := by
    have hnat : (2037616731 : ℕ)^17*1000000000000^13 ≤ 309171472773^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2037616731 5000000000 309171472773 1000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(304678269/625000000 : ℝ), (-995698989/2500000000 : ℝ), (-2037616731/5000000000 : ℝ)] ![(1563182180711/4000000000000 : ℝ), (30003298187781/100000000000000 : ℝ), (309171472773/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(304678269/625000000 : ℝ)|^17 ≤ (1563182180711/4000000000000 : ℝ)^13
        have hw : |(304678269/625000000 : ℝ)|=(304678269/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-995698989/2500000000 : ℝ)|^17 ≤ (30003298187781/100000000000000 : ℝ)^13
        have hw : |(-995698989/2500000000 : ℝ)|=(995698989/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2037616731/5000000000 : ℝ)|^17 ≤ (309171472773/1000000000000 : ℝ)^13
        have hw : |(-2037616731/5000000000 : ℝ)|=(2037616731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304039_s1_s1_13 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (750464723/1000000000 : ℝ)*x 0 + (33715043/5000000000 : ℝ)*x 1 + (4098988469/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (750464723/1000000000 : ℝ)^17 ≤ (68702156449527/100000000000000 : ℝ)^13 := by
    have hnat : (750464723 : ℕ)^17*100000000000000^13 ≤ 68702156449527^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      750464723 1000000000 68702156449527 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (33715043/5000000000 : ℝ)^17 ≤ (72406692019/50000000000000 : ℝ)^13 := by
    have hnat : (33715043 : ℕ)^17*50000000000000^13 ≤ 72406692019^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33715043 5000000000 72406692019 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4098988469/10000000000 : ℝ)^17 ≤ (6230606031923/20000000000000 : ℝ)^13 := by
    have hnat : (4098988469 : ℕ)^17*20000000000000^13 ≤ 6230606031923^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4098988469 10000000000 6230606031923 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(750464723/1000000000 : ℝ), (33715043/5000000000 : ℝ), (4098988469/10000000000 : ℝ)] ![(68702156449527/100000000000000 : ℝ), (72406692019/50000000000000 : ℝ), (6230606031923/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(750464723/1000000000 : ℝ)|^17 ≤ (68702156449527/100000000000000 : ℝ)^13
        have hw : |(750464723/1000000000 : ℝ)|=(750464723/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(33715043/5000000000 : ℝ)|^17 ≤ (72406692019/50000000000000 : ℝ)^13
        have hw : |(33715043/5000000000 : ℝ)|=(33715043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4098988469/10000000000 : ℝ)|^17 ≤ (6230606031923/20000000000000 : ℝ)^13
        have hw : |(4098988469/10000000000 : ℝ)|=(4098988469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304039_s1_s1_14 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-397567579/10000000000 : ℝ)*x 0 + (-5775169893/10000000000 : ℝ)*x 1 + (5863289037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (397567579/10000000000 : ℝ)^17 ≤ (46058576281/3125000000000 : ℝ)^13 := by
    have hnat : (397567579 : ℕ)^17*3125000000000^13 ≤ 46058576281^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397567579 10000000000 46058576281 3125000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5775169893/10000000000 : ℝ)^17 ≤ (24387657171991/50000000000000 : ℝ)^13 := by
    have hnat : (5775169893 : ℕ)^17*50000000000000^13 ≤ 24387657171991^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5775169893 10000000000 24387657171991 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5863289037/10000000000 : ℝ)^17 ≤ (12437702799223/25000000000000 : ℝ)^13 := by
    have hnat : (5863289037 : ℕ)^17*25000000000000^13 ≤ 12437702799223^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5863289037 10000000000 12437702799223 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-397567579/10000000000 : ℝ), (-5775169893/10000000000 : ℝ), (5863289037/10000000000 : ℝ)] ![(46058576281/3125000000000 : ℝ), (24387657171991/50000000000000 : ℝ), (12437702799223/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-397567579/10000000000 : ℝ)|^17 ≤ (46058576281/3125000000000 : ℝ)^13
        have hw : |(-397567579/10000000000 : ℝ)|=(397567579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5775169893/10000000000 : ℝ)|^17 ≤ (24387657171991/50000000000000 : ℝ)^13
        have hw : |(-5775169893/10000000000 : ℝ)|=(5775169893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5863289037/10000000000 : ℝ)|^17 ≤ (12437702799223/25000000000000 : ℝ)^13
        have hw : |(5863289037/10000000000 : ℝ)|=(5863289037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304039_s1_s1_15 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2090512531/5000000000 : ℝ)*x 0 + (2112296639/5000000000 : ℝ)*x 1 + (2270730223/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2090512531/5000000000 : ℝ)^17 ≤ (15985432719179/50000000000000 : ℝ)^13 := by
    have hnat : (2090512531 : ℕ)^17*50000000000000^13 ≤ 15985432719179^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2090512531 5000000000 15985432719179 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2112296639/5000000000 : ℝ)^17 ≤ (16203610735567/50000000000000 : ℝ)^13 := by
    have hnat : (2112296639 : ℕ)^17*50000000000000^13 ≤ 16203610735567^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112296639 5000000000 16203610735567 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2270730223/5000000000 : ℝ)^17 ≤ (8905478266589/25000000000000 : ℝ)^13 := by
    have hnat : (2270730223 : ℕ)^17*25000000000000^13 ≤ 8905478266589^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2270730223 5000000000 8905478266589 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2090512531/5000000000 : ℝ), (2112296639/5000000000 : ℝ), (2270730223/5000000000 : ℝ)] ![(15985432719179/50000000000000 : ℝ), (16203610735567/50000000000000 : ℝ), (8905478266589/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2090512531/5000000000 : ℝ)|^17 ≤ (15985432719179/50000000000000 : ℝ)^13
        have hw : |(2090512531/5000000000 : ℝ)|=(2090512531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2112296639/5000000000 : ℝ)|^17 ≤ (16203610735567/50000000000000 : ℝ)^13
        have hw : |(2112296639/5000000000 : ℝ)|=(2112296639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2270730223/5000000000 : ℝ)|^17 ≤ (8905478266589/25000000000000 : ℝ)^13
        have hw : |(2270730223/5000000000 : ℝ)|=(2270730223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304039_s1_s1_16 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5801177399/10000000000 : ℝ)*x 0 + (-834920579/2500000000 : ℝ)*x 1 + (-184258583/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5801177399/10000000000 : ℝ)^17 ≤ (12265687404001/25000000000000 : ℝ)^13 := by
    have hnat : (5801177399 : ℕ)^17*25000000000000^13 ≤ 12265687404001^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5801177399 10000000000 12265687404001 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (834920579/2500000000 : ℝ)^17 ≤ (4766316670863/20000000000000 : ℝ)^13 := by
    have hnat : (834920579 : ℕ)^17*20000000000000^13 ≤ 4766316670863^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      834920579 2500000000 4766316670863 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (184258583/500000000 : ℝ)^17 ≤ (27105667015831/100000000000000 : ℝ)^13 := by
    have hnat : (184258583 : ℕ)^17*100000000000000^13 ≤ 27105667015831^13*500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      184258583 500000000 27105667015831 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5801177399/10000000000 : ℝ), (-834920579/2500000000 : ℝ), (-184258583/500000000 : ℝ)] ![(12265687404001/25000000000000 : ℝ), (4766316670863/20000000000000 : ℝ), (27105667015831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5801177399/10000000000 : ℝ)|^17 ≤ (12265687404001/25000000000000 : ℝ)^13
        have hw : |(5801177399/10000000000 : ℝ)|=(5801177399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-834920579/2500000000 : ℝ)|^17 ≤ (4766316670863/20000000000000 : ℝ)^13
        have hw : |(-834920579/2500000000 : ℝ)|=(834920579/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-184258583/500000000 : ℝ)|^17 ≤ (27105667015831/100000000000000 : ℝ)^13
        have hw : |(-184258583/500000000 : ℝ)|=(184258583/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304039_s1_s1_20 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2306938899/2500000000 : ℝ)*x 0 + (-20284561/2000000000 : ℝ)*x 1 + (1683388269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2306938899/2500000000 : ℝ)^17 ≤ (45011804204063/50000000000000 : ℝ)^13 := by
    have hnat : (2306938899 : ℕ)^17*50000000000000^13 ≤ 45011804204063^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2306938899 2500000000 45011804204063 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (20284561/2000000000 : ℝ)^17 ≤ (246966976183/100000000000000 : ℝ)^13 := by
    have hnat : (20284561 : ℕ)^17*100000000000000^13 ≤ 246966976183^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20284561 2000000000 246966976183 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1683388269/10000000000 : ℝ)^17 ≤ (9729424601047/100000000000000 : ℝ)^13 := by
    have hnat : (1683388269 : ℕ)^17*100000000000000^13 ≤ 9729424601047^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1683388269 10000000000 9729424601047 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2306938899/2500000000 : ℝ), (-20284561/2000000000 : ℝ), (1683388269/10000000000 : ℝ)] ![(45011804204063/50000000000000 : ℝ), (246966976183/100000000000000 : ℝ), (9729424601047/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2306938899/2500000000 : ℝ)|^17 ≤ (45011804204063/50000000000000 : ℝ)^13
        have hw : |(2306938899/2500000000 : ℝ)|=(2306938899/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-20284561/2000000000 : ℝ)|^17 ≤ (246966976183/100000000000000 : ℝ)^13
        have hw : |(-20284561/2000000000 : ℝ)|=(20284561/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1683388269/10000000000 : ℝ)|^17 ≤ (9729424601047/100000000000000 : ℝ)^13
        have hw : |(1683388269/10000000000 : ℝ)|=(1683388269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304039_s1_s1_21 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-204485883/2000000000 : ℝ)*x 0 + (-1321744663/2000000000 : ℝ)*x 1 + (4651211979/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (204485883/2000000000 : ℝ)^17 ≤ (506879971397/10000000000000 : ℝ)^13 := by
    have hnat : (204485883 : ℕ)^17*10000000000000^13 ≤ 506879971397^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      204485883 2000000000 506879971397 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1321744663/2000000000 : ℝ)^17 ≤ (29089692742967/50000000000000 : ℝ)^13 := by
    have hnat : (1321744663 : ℕ)^17*50000000000000^13 ≤ 29089692742967^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321744663 2000000000 29089692742967 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4651211979/10000000000 : ℝ)^17 ≤ (4593976848581/12500000000000 : ℝ)^13 := by
    have hnat : (4651211979 : ℕ)^17*12500000000000^13 ≤ 4593976848581^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4651211979 10000000000 4593976848581 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-204485883/2000000000 : ℝ), (-1321744663/2000000000 : ℝ), (4651211979/10000000000 : ℝ)] ![(506879971397/10000000000000 : ℝ), (29089692742967/50000000000000 : ℝ), (4593976848581/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-204485883/2000000000 : ℝ)|^17 ≤ (506879971397/10000000000000 : ℝ)^13
        have hw : |(-204485883/2000000000 : ℝ)|=(204485883/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1321744663/2000000000 : ℝ)|^17 ≤ (29089692742967/50000000000000 : ℝ)^13
        have hw : |(-1321744663/2000000000 : ℝ)|=(1321744663/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4651211979/10000000000 : ℝ)|^17 ≤ (4593976848581/12500000000000 : ℝ)^13
        have hw : |(4651211979/10000000000 : ℝ)|=(4651211979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304039_s1_s1_22 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5400721807/10000000000 : ℝ)*x 0 + (95531691/250000000 : ℝ)*x 1 + (1831690191/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5400721807/10000000000 : ℝ)^17 ≤ (8936331728721/20000000000000 : ℝ)^13 := by
    have hnat : (5400721807 : ℕ)^17*20000000000000^13 ≤ 8936331728721^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400721807 10000000000 8936331728721 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (95531691/250000000 : ℝ)^17 ≤ (28422083089187/100000000000000 : ℝ)^13 := by
    have hnat : (95531691 : ℕ)^17*100000000000000^13 ≤ 28422083089187^13*250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      95531691 250000000 28422083089187 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1831690191/5000000000 : ℝ)^17 ≤ (26896258260359/100000000000000 : ℝ)^13 := by
    have hnat : (1831690191 : ℕ)^17*100000000000000^13 ≤ 26896258260359^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1831690191 5000000000 26896258260359 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5400721807/10000000000 : ℝ), (95531691/250000000 : ℝ), (1831690191/5000000000 : ℝ)] ![(8936331728721/20000000000000 : ℝ), (28422083089187/100000000000000 : ℝ), (26896258260359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5400721807/10000000000 : ℝ)|^17 ≤ (8936331728721/20000000000000 : ℝ)^13
        have hw : |(5400721807/10000000000 : ℝ)|=(5400721807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(95531691/250000000 : ℝ)|^17 ≤ (28422083089187/100000000000000 : ℝ)^13
        have hw : |(95531691/250000000 : ℝ)|=(95531691/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1831690191/5000000000 : ℝ)|^17 ≤ (26896258260359/100000000000000 : ℝ)^13
        have hw : |(1831690191/5000000000 : ℝ)|=(1831690191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304039_s1_s1_23 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (550604353/1250000000 : ℝ)*x 0 + (-4507233483/10000000000 : ℝ)*x 1 + (-2016645393/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (550604353/1250000000 : ℝ)^17 ≤ (34227053439721/100000000000000 : ℝ)^13 := by
    have hnat : (550604353 : ℕ)^17*100000000000000^13 ≤ 34227053439721^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550604353 1250000000 34227053439721 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4507233483/10000000000 : ℝ)^17 ≤ (35271249282551/100000000000000 : ℝ)^13 := by
    have hnat : (4507233483 : ℕ)^17*100000000000000^13 ≤ 35271249282551^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4507233483 10000000000 35271249282551 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2016645393/5000000000 : ℝ)^17 ≤ (30501697264721/100000000000000 : ℝ)^13 := by
    have hnat : (2016645393 : ℕ)^17*100000000000000^13 ≤ 30501697264721^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2016645393 5000000000 30501697264721 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(550604353/1250000000 : ℝ), (-4507233483/10000000000 : ℝ), (-2016645393/5000000000 : ℝ)] ![(34227053439721/100000000000000 : ℝ), (35271249282551/100000000000000 : ℝ), (30501697264721/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(550604353/1250000000 : ℝ)|^17 ≤ (34227053439721/100000000000000 : ℝ)^13
        have hw : |(550604353/1250000000 : ℝ)|=(550604353/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4507233483/10000000000 : ℝ)|^17 ≤ (35271249282551/100000000000000 : ℝ)^13
        have hw : |(-4507233483/10000000000 : ℝ)|=(4507233483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2016645393/5000000000 : ℝ)|^17 ≤ (30501697264721/100000000000000 : ℝ)^13
        have hw : |(-2016645393/5000000000 : ℝ)|=(2016645393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304039_s1_s1_27 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (519771297/625000000 : ℝ)*x 0 + (7910119/2000000000 : ℝ)*x 1 + (3070430053/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (519771297/625000000 : ℝ)^17 ≤ (15715422038869/20000000000000 : ℝ)^13 := by
    have hnat : (519771297 : ℕ)^17*20000000000000^13 ≤ 15715422038869^13*625000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519771297 625000000 15715422038869 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7910119/2000000000 : ℝ)^17 ≤ (72080118101/100000000000000 : ℝ)^13 := by
    have hnat : (7910119 : ℕ)^17*100000000000000^13 ≤ 72080118101^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7910119 2000000000 72080118101 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3070430053/10000000000 : ℝ)^17 ≤ (10675404838623/50000000000000 : ℝ)^13 := by
    have hnat : (3070430053 : ℕ)^17*50000000000000^13 ≤ 10675404838623^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3070430053 10000000000 10675404838623 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(519771297/625000000 : ℝ), (7910119/2000000000 : ℝ), (3070430053/10000000000 : ℝ)] ![(15715422038869/20000000000000 : ℝ), (72080118101/100000000000000 : ℝ), (10675404838623/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(519771297/625000000 : ℝ)|^17 ≤ (15715422038869/20000000000000 : ℝ)^13
        have hw : |(519771297/625000000 : ℝ)|=(519771297/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7910119/2000000000 : ℝ)|^17 ≤ (72080118101/100000000000000 : ℝ)^13
        have hw : |(7910119/2000000000 : ℝ)|=(7910119/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3070430053/10000000000 : ℝ)|^17 ≤ (10675404838623/50000000000000 : ℝ)^13
        have hw : |(3070430053/10000000000 : ℝ)|=(3070430053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c304039_s1 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((37471/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(37471/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-88941/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-88941/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(48273/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(48273/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((9377/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9377/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-5179/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-5179/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13739/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(13739/20000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76617/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76617/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76617/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76617/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76617/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76617/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base10 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
  have s1_pow0 : (37471/50000 : ℝ) ^ (33/8 : ℝ) ≤ (30425783884299325533/100000000000000000000 : ℝ) := by
    have hpowers : (37471/50000 : ℝ)^33 ≤ (30425783884299325533/100000000000000000000 : ℝ)^8 := by
      have hnat : (37471 : ℕ)^33*100000000000000000000^8 ≤ 30425783884299325533^8*50000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        37471 50000 30425783884299325533 100000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (37471/50000 : ℝ)) (X := (30425783884299325533/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (130425783884299325533/100000000000000000000 : ℝ) ≤ (266628707247607/250000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (130425783884299325533/100000000000000000000 : ℝ)^8 ≤ (266628707247607/250000000000000 : ℝ)^33 := by
      have hnat : (130425783884299325533 : ℕ)^8*250000000000000^33 ≤ 266628707247607^33*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        130425783884299325533 100000000000000000000 266628707247607 250000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (266628707247607/250000000000000 : ℝ)) (X := (130425783884299325533/100000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (80425783884299325533/50000000000000000000 : ℝ) ≤ (11221282512857967/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (80425783884299325533/50000000000000000000 : ℝ)^8 ≤ (11221282512857967/10000000000000000 : ℝ)^33 := by
      have hnat : (80425783884299325533 : ℕ)^8*10000000000000000^33 ≤ 11221282512857967^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        80425783884299325533 50000000000000000000 11221282512857967 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11221282512857967/10000000000000000 : ℝ)) (X := (80425783884299325533/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(2375529606801/26765000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(79447746136241/1070600000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (37471/50000 : ℝ)) (alpha := (2375529606801/26765000000000 : ℝ)) (beta := (79447746136241/1070600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (37471/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(2375529606801/26765000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(79447746136241/1070600000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (88941/100000 : ℝ) ^ (33/8 : ℝ) ≤ (30833000340173552843/50000000000000000000 : ℝ) := by
    have hpowers : (88941/100000 : ℝ)^33 ≤ (30833000340173552843/50000000000000000000 : ℝ)^8 := by
      have hnat : (88941 : ℕ)^33*50000000000000000000^8 ≤ 30833000340173552843^8*100000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        88941 100000 30833000340173552843 50000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (88941/100000 : ℝ)) (X := (30833000340173552843/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (80833000340173552843/50000000000000000000 : ℝ) ≤ (11235029809194749/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (80833000340173552843/50000000000000000000 : ℝ)^8 ≤ (11235029809194749/10000000000000000 : ℝ)^33 := by
      have hnat : (80833000340173552843 : ℕ)^8*10000000000000000^33 ≤ 11235029809194749^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        80833000340173552843 50000000000000000000 11235029809194749 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11235029809194749/10000000000000000 : ℝ)) (X := (80833000340173552843/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (55833000340173552843/25000000000000000000 : ℝ) ≤ (12150500610593327/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (55833000340173552843/25000000000000000000 : ℝ)^8 ≤ (12150500610593327/10000000000000000 : ℝ)^33 := by
      have hnat : (55833000340173552843 : ℕ)^8*10000000000000000^33 ≤ 12150500610593327^33*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        55833000340173552843 25000000000000000000 12150500610593327 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12150500610593327/10000000000000000 : ℝ)) (X := (55833000340173552843/25000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1235029809194749/8894100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(152578466899763/1482350000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (88941/100000 : ℝ)) (alpha := (1235029809194749/8894100000000000 : ℝ)) (beta := (152578466899763/1482350000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (88941/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1235029809194749/8894100000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(152578466899763/1482350000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (48273/50000 : ℝ) ^ (33/8 : ℝ) ≤ (43251276629427829829/50000000000000000000 : ℝ) := by
    have hpowers : (48273/50000 : ℝ)^33 ≤ (43251276629427829829/50000000000000000000 : ℝ)^8 := by
      have hnat : (48273 : ℕ)^33*50000000000000000000^8 ≤ 43251276629427829829^8*50000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        48273 50000 43251276629427829829 50000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (48273/50000 : ℝ)) (X := (43251276629427829829/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (93251276629427829829/50000000000000000000 : ℝ) ≤ (1163109366630411/1000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (93251276629427829829/50000000000000000000 : ℝ)^8 ≤ (1163109366630411/1000000000000000 : ℝ)^33 := by
      have hnat : (93251276629427829829 : ℕ)^8*1000000000000000^33 ≤ 1163109366630411^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        93251276629427829829 50000000000000000000 1163109366630411 1000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1163109366630411/1000000000000000 : ℝ)) (X := (93251276629427829829/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (68251276629427829829/25000000000000000000 : ℝ) ≤ (12756700772290713/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (68251276629427829829/25000000000000000000 : ℝ)^8 ≤ (12756700772290713/10000000000000000 : ℝ)^33 := by
      have hnat : (68251276629427829829 : ℕ)^8*10000000000000000^33 ≤ 12756700772290713^33*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        68251276629427829829 25000000000000000000 12756700772290713 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12756700772290713/10000000000000000 : ℝ)) (X := (68251276629427829829/25000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(163109366630411/965460000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(375202368662201/3218200000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (48273/50000 : ℝ)) (alpha := (163109366630411/965460000000000 : ℝ)) (beta := (375202368662201/3218200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (48273/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(163109366630411/965460000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(375202368662201/3218200000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1545503289/10000000000 : ℝ)*X 0 0+(-3077048791/5000000000 : ℝ)*X 0 1+(4800062003/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304039_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((1198425771/2500000000 : ℝ)*X 1 0+(8109951/20000000 : ℝ)*X 1 1+(2044441759/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304039_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((228611727/500000000 : ℝ)*X 2 0+(-208234037/500000000 : ℝ)*X 2 1+(-4209367923/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304039_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-88084301/1000000000 : ℝ)*X 0 0+(-3308908013/5000000000 : ℝ)*X 0 1+(2363881801/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304039_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((954490211/2000000000 : ℝ)*X 1 0+(2033597453/5000000000 : ℝ)*X 1 1+(4098988469/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304039_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((304678269/625000000 : ℝ)*X 2 0+(-995698989/2500000000 : ℝ)*X 2 1+(-2037616731/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304039_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((750464723/1000000000 : ℝ)*X 0 0+(33715043/5000000000 : ℝ)*X 0 1+(4098988469/10000000000 : ℝ)*X 0 2+(750464723/1000000000 : ℝ)*X 1 0+(33715043/5000000000 : ℝ)*X 1 1+(4098988469/10000000000 : ℝ)*X 1 2+(750464723/1000000000 : ℝ)*X 2 0+(33715043/5000000000 : ℝ)*X 2 1+(4098988469/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304039_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-397567579/10000000000 : ℝ)*X 0 0+(-5775169893/10000000000 : ℝ)*X 0 1+(5863289037/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304039_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((2090512531/5000000000 : ℝ)*X 1 0+(2112296639/5000000000 : ℝ)*X 1 1+(2270730223/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304039_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((5801177399/10000000000 : ℝ)*X 2 0+(-834920579/2500000000 : ℝ)*X 2 1+(-184258583/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304039_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((2306938899/2500000000 : ℝ)*X 0 0+(-20284561/2000000000 : ℝ)*X 0 1+(1683388269/10000000000 : ℝ)*X 0 2+(2306938899/2500000000 : ℝ)*X 1 0+(-20284561/2000000000 : ℝ)*X 1 1+(1683388269/10000000000 : ℝ)*X 1 2+(2306938899/2500000000 : ℝ)*X 2 0+(-20284561/2000000000 : ℝ)*X 2 1+(1683388269/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304039_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-204485883/2000000000 : ℝ)*X 0 0+(-1321744663/2000000000 : ℝ)*X 0 1+(4651211979/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304039_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((5400721807/10000000000 : ℝ)*X 1 0+(95531691/250000000 : ℝ)*X 1 1+(1831690191/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304039_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((550604353/1250000000 : ℝ)*X 2 0+(-4507233483/10000000000 : ℝ)*X 2 1+(-2016645393/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304039_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((519771297/625000000 : ℝ)*X 0 0+(7910119/2000000000 : ℝ)*X 0 1+(3070430053/10000000000 : ℝ)*X 0 2+(519771297/625000000 : ℝ)*X 1 0+(7910119/2000000000 : ℝ)*X 1 1+(3070430053/10000000000 : ℝ)*X 1 2+(519771297/625000000 : ℝ)*X 2 0+(7910119/2000000000 : ℝ)*X 2 1+(3070430053/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304039_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((9377/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9377/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2234509718682101518796533003347/127682399579050000000000000000000000 : ℝ) := by norm_num
    linear_combination (724626624119/1000000000000 : ℝ)*(base3) + (633517/50000000000 : ℝ)*(base10) + (1004027613119/500000000000 : ℝ)*(base40) + (30196439393/125000000000 : ℝ)*(base49) + (3946492945563/500000000000 : ℝ)*(major_s1_0) + (3946492945563/500000000000 : ℝ)*(major_s1_1) + (3946492945563/500000000000 : ℝ)*(major_s1_2) + (3903749583/1000000000000 : ℝ)*(sp_s1_1) + (261947893/1000000000000 : ℝ)*(sp_s1_2) + (5290984876999/500000000000 : ℝ)*(sp_s1_7) + (11302412789491/1000000000000 : ℝ)*(sp_s1_8) + (2116344095289/200000000000 : ℝ)*(sp_s1_9) + (4479356900279/1000000000000 : ℝ)*(sp_s1_13) + (36563673/125000000000 : ℝ)*(sp_s1_15) + (5203983524399/1000000000000 : ℝ)*(f.failure) + (5290991212169/500000000000 : ℝ)*(f.sum) + (2747758931024020737/11926246925000000000000000000000 : ℝ)*base63 + (373929922657697/1609100000000000000000000000 : ℝ)*base64 + (482735024916183/1482350000000000000000000000 : ℝ)*base66 + (2520724410113/80455000000000000000000000 : ℝ)*base69 + (1075558507965076699/8613512300000000000000000000000 : ℝ)*base71 + (188613241120957/535300000000000000000000000 : ℝ)*base72 + (433966472198779/1482350000000000000000000000 : ℝ)*base75 + (1259088729169/5353000000000000000000000 : ℝ)*base77 + (9233311894292816547/15870039100000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (5641/12500000000000000 : ℝ)*base87 + (5641/12500000000000000 : ℝ)*base89 + (5641/12500000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-5179/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-5179/12500 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (501402710211406094292079875439/127682399579050000000000000000000000 : ℝ) := by norm_num
    linear_combination (1432917741111/1000000000000 : ℝ)*(base40) + (1099543/1000000000000 : ℝ)*(base50) + (2512603/500000000000 : ℝ)*(base53) + (4043753084697/1000000000000 : ℝ)*(major_s1_0) + (4043753084697/1000000000000 : ℝ)*(major_s1_1) + (4043748059491/1000000000000 : ℝ)*(major_s1_2) + (533381/15625000000 : ℝ)*(sp_s1_0) + (36120451/500000000000 : ℝ)*(sp_s1_1) + (5822549/1000000000000 : ℝ)*(sp_s1_9) + (5421348627307/1000000000000 : ℝ)*(sp_s1_14) + (5421310522789/1000000000000 : ℝ)*(sp_s1_15) + (1355345491587/250000000000 : ℝ)*(sp_s1_16) + (533217133187/200000000000 : ℝ)*(sp_s1_20) + (31405573/1000000000000 : ℝ)*(sp_s1_27) + (666529267877/250000000000 : ℝ)*(f.failure) + (5421387788897/1000000000000 : ℝ)*(f.sum) + (3344985151773187457/8944685193750000000000000000000 : ℝ)*base62 + (1272973261829471/3218200000000000000000000000 : ℝ)*base65 + (284331336624909/370587500000000000000000000 : ℝ)*base66 + (641284348662931/965460000000000000000000000 : ℝ)*base68 + (10342087027749273917/17227024600000000000000000000000 : ℝ)*base70 + (244949509834863/1070600000000000000000000000 : ℝ)*base72 + (2480652901003529/2964700000000000000000000000 : ℝ)*base74 + (2510825231/1070600000000000000000000 : ℝ)*base76 + (11785500299454822867/31740078200000000000000000000000 : ℝ)*base79 + (959/1562500000000000 : ℝ)*base87 + (959/1562500000000000 : ℝ)*base89 + (959/1562500000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13739/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(13739/20000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (119150282346615487578687561129/7980149973690625000000000000000000 : ℝ) := by norm_num
    linear_combination (789233/62500000000 : ℝ)*(base10) + (1496520327081/500000000000 : ℝ)*(base40) + (10189669/1000000000000 : ℝ)*(base43) + (1556581/200000000000 : ℝ)*(base49) + (4834107373533/500000000000 : ℝ)*(major_s1_0) + (9668204557397/1000000000000 : ℝ)*(major_s1_1) + (4834107373533/500000000000 : ℝ)*(major_s1_2) + (112923729/1000000000000 : ℝ)*(sp_s1_0) + (155831/20000000000 : ℝ)*(sp_s1_16) + (26174039/500000000000 : ℝ)*(sp_s1_20) + (1296186584561/100000000000 : ℝ)*(sp_s1_21) + (12962001586737/1000000000000 : ℝ)*(sp_s1_22) + (12961983605517/1000000000000 : ℝ)*(sp_s1_23) + (199199080699/31250000000 : ℝ)*(sp_s1_27) + (3187211465223/500000000000 : ℝ)*(f.failure) + (12962001586737/1000000000000 : ℝ)*(f.sum) + (20018688185775844097/143114963100000000000000000000000 : ℝ)*base62 + (931276087259087/1609100000000000000000000000 : ℝ)*base64 + (167415114655321/370587500000000000000000000 : ℝ)*base67 + (3686059251429/20113750000000000000000000 : ℝ)*base68 + (2210562101969759431/8613512300000000000000000000000 : ℝ)*base70 + (99205022558853/535300000000000000000000000 : ℝ)*base73 + (2160357922060733/8894100000000000000000000000 : ℝ)*base75 + (7118904907579/10706000000000000000000000 : ℝ)*base76 + (262137087929161817/3174007820000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base84 + (357/6250000000000000 : ℝ)*base87 + (357/6250000000000000 : ℝ)*base89 + (357/6250000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((37471/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(37471/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-88941/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-88941/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(48273/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(48273/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((9377/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9377/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-5179/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-5179/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13739/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(13739/20000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c304039_s1 p hpa hpb X hX hprev0

#print axioms solution
