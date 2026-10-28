-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c302054_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:22:35.276809+00:00
-- url     : https://prove2.me/submissions/da2f00ed-d0bb-4c63-aa2d-fa65d4cd6397

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
theorem collision_support_c302054_s1_s1_1 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2966997283/5000000000 : ℝ)*x 0 + (-13446249/100000000 : ℝ)*x 1 + (-5249383879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2966997283/5000000000 : ℝ)^33 ≤ (25106619155977/50000000000000 : ℝ)^25 := by
    have hnat : (2966997283 : ℕ)^33*50000000000000^25 ≤ 25106619155977^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2966997283 5000000000 25106619155977 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (13446249/100000000 : ℝ)^33 ≤ (7075441053077/100000000000000 : ℝ)^25 := by
    have hnat : (13446249 : ℕ)^33*100000000000000^25 ≤ 7075441053077^25*100000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13446249 100000000 7075441053077 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5249383879/10000000000 : ℝ)^33 ≤ (42711320613011/100000000000000 : ℝ)^25 := by
    have hnat : (5249383879 : ℕ)^33*100000000000000^25 ≤ 42711320613011^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5249383879 10000000000 42711320613011 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2966997283/5000000000 : ℝ), (-13446249/100000000 : ℝ), (-5249383879/10000000000 : ℝ)] ![(25106619155977/50000000000000 : ℝ), (7075441053077/100000000000000 : ℝ), (42711320613011/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2966997283/5000000000 : ℝ)|^33 ≤ (25106619155977/50000000000000 : ℝ)^25
        have hw : |(2966997283/5000000000 : ℝ)|=(2966997283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-13446249/100000000 : ℝ)|^33 ≤ (7075441053077/100000000000000 : ℝ)^25
        have hw : |(-13446249/100000000 : ℝ)|=(13446249/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5249383879/10000000000 : ℝ)|^33 ≤ (42711320613011/100000000000000 : ℝ)^25
        have hw : |(-5249383879/10000000000 : ℝ)|=(5249383879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s1_s1_6 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1091637107/2000000000 : ℝ)*x 0 + (5442259977/10000000000 : ℝ)*x 1 + (-1778824843/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1091637107/2000000000 : ℝ)^33 ≤ (5621002277871/12500000000000 : ℝ)^25 := by
    have hnat : (1091637107 : ℕ)^33*12500000000000^25 ≤ 5621002277871^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091637107 2000000000 5621002277871 12500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5442259977/10000000000 : ℝ)^33 ≤ (44794908637447/100000000000000 : ℝ)^25 := by
    have hnat : (5442259977 : ℕ)^33*100000000000000^25 ≤ 44794908637447^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5442259977 10000000000 44794908637447 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1778824843/10000000000 : ℝ)^33 ≤ (1023707312971/10000000000000 : ℝ)^25 := by
    have hnat : (1778824843 : ℕ)^33*10000000000000^25 ≤ 1023707312971^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1778824843 10000000000 1023707312971 10000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1091637107/2000000000 : ℝ), (5442259977/10000000000 : ℝ), (-1778824843/10000000000 : ℝ)] ![(5621002277871/12500000000000 : ℝ), (44794908637447/100000000000000 : ℝ), (1023707312971/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1091637107/2000000000 : ℝ)|^33 ≤ (5621002277871/12500000000000 : ℝ)^25
        have hw : |(1091637107/2000000000 : ℝ)|=(1091637107/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5442259977/10000000000 : ℝ)|^33 ≤ (44794908637447/100000000000000 : ℝ)^25
        have hw : |(5442259977/10000000000 : ℝ)|=(5442259977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1778824843/10000000000 : ℝ)|^33 ≤ (1023707312971/10000000000000 : ℝ)^25
        have hw : |(-1778824843/10000000000 : ℝ)|=(1778824843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s1_s1_7 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (249/1000000000 : ℝ)*x 0 + (647876177/5000000000 : ℝ)*x 1 + (-4742628913/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (249/1000000000 : ℝ)^33 ≤ (9593/5000000000000 : ℝ)^25 := by
    have hnat : (249 : ℕ)^33*5000000000000^25 ≤ 9593^25*1000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249 1000000000 9593 5000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (647876177/5000000000 : ℝ)^33 ≤ (673796962099/10000000000000 : ℝ)^25 := by
    have hnat : (647876177 : ℕ)^33*10000000000000^25 ≤ 673796962099^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647876177 5000000000 673796962099 10000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4742628913/5000000000 : ℝ)^33 ≤ (1457219221477/1562500000000 : ℝ)^25 := by
    have hnat : (4742628913 : ℕ)^33*1562500000000^25 ≤ 1457219221477^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4742628913 5000000000 1457219221477 1562500000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(249/1000000000 : ℝ), (647876177/5000000000 : ℝ), (-4742628913/5000000000 : ℝ)] ![(9593/5000000000000 : ℝ), (673796962099/10000000000000 : ℝ), (1457219221477/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(249/1000000000 : ℝ)|^33 ≤ (9593/5000000000000 : ℝ)^25
        have hw : |(249/1000000000 : ℝ)|=(249/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(647876177/5000000000 : ℝ)|^33 ≤ (673796962099/10000000000000 : ℝ)^25
        have hw : |(647876177/5000000000 : ℝ)|=(647876177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4742628913/5000000000 : ℝ)|^33 ≤ (1457219221477/1562500000000 : ℝ)^25
        have hw : |(-4742628913/5000000000 : ℝ)|=(4742628913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s1_s1_8 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4158546451/10000000000 : ℝ)*x 0 + (-977203989/5000000000 : ℝ)*x 1 + (-6532435741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4158546451/10000000000 : ℝ)^33 ≤ (7851323350603/25000000000000 : ℝ)^25 := by
    have hnat : (4158546451 : ℕ)^33*25000000000000^25 ≤ 7851323350603^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4158546451 10000000000 7851323350603 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (977203989/5000000000 : ℝ)^33 ≤ (724469517021/6250000000000 : ℝ)^25 := by
    have hnat : (977203989 : ℕ)^33*6250000000000^25 ≤ 724469517021^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      977203989 5000000000 724469517021 6250000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6532435741/10000000000 : ℝ)^33 ≤ (57003194315079/100000000000000 : ℝ)^25 := by
    have hnat : (6532435741 : ℕ)^33*100000000000000^25 ≤ 57003194315079^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6532435741 10000000000 57003194315079 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4158546451/10000000000 : ℝ), (-977203989/5000000000 : ℝ), (-6532435741/10000000000 : ℝ)] ![(7851323350603/25000000000000 : ℝ), (724469517021/6250000000000 : ℝ), (57003194315079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4158546451/10000000000 : ℝ)|^33 ≤ (7851323350603/25000000000000 : ℝ)^25
        have hw : |(4158546451/10000000000 : ℝ)|=(4158546451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-977203989/5000000000 : ℝ)|^33 ≤ (724469517021/6250000000000 : ℝ)^25
        have hw : |(-977203989/5000000000 : ℝ)|=(977203989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6532435741/10000000000 : ℝ)|^33 ≤ (57003194315079/100000000000000 : ℝ)^25
        have hw : |(-6532435741/10000000000 : ℝ)|=(6532435741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s1_s1_9 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1397658233/5000000000 : ℝ)*x 0 + (8270105557/10000000000 : ℝ)*x 1 + (200859947/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1397658233/5000000000 : ℝ)^33 ≤ (9295203486201/50000000000000 : ℝ)^25 := by
    have hnat : (1397658233 : ℕ)^33*50000000000000^25 ≤ 9295203486201^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1397658233 5000000000 9295203486201 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8270105557/10000000000 : ℝ)^33 ≤ (15564837299959/20000000000000 : ℝ)^25 := by
    have hnat : (8270105557 : ℕ)^33*20000000000000^25 ≤ 15564837299959^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8270105557 10000000000 15564837299959 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (200859947/2500000000 : ℝ)^33 ≤ (3585406506901/100000000000000 : ℝ)^25 := by
    have hnat : (200859947 : ℕ)^33*100000000000000^25 ≤ 3585406506901^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200859947 2500000000 3585406506901 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1397658233/5000000000 : ℝ), (8270105557/10000000000 : ℝ), (200859947/2500000000 : ℝ)] ![(9295203486201/50000000000000 : ℝ), (15564837299959/20000000000000 : ℝ), (3585406506901/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1397658233/5000000000 : ℝ)|^33 ≤ (9295203486201/50000000000000 : ℝ)^25
        have hw : |(1397658233/5000000000 : ℝ)|=(1397658233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8270105557/10000000000 : ℝ)|^33 ≤ (15564837299959/20000000000000 : ℝ)^25
        have hw : |(8270105557/10000000000 : ℝ)|=(8270105557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(200859947/2500000000 : ℝ)|^33 ≤ (3585406506901/100000000000000 : ℝ)^25
        have hw : |(200859947/2500000000 : ℝ)|=(200859947/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s1_s1_13 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (675151521/2000000000 : ℝ)*x 0 + (245072839/312500000 : ℝ)*x 1 + (-161083481/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (675151521/2000000000 : ℝ)^33 ≤ (2980986911799/12500000000000 : ℝ)^25 := by
    have hnat : (675151521 : ℕ)^33*12500000000000^25 ≤ 2980986911799^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675151521 2000000000 2980986911799 12500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (245072839/312500000 : ℝ)^33 ≤ (18138761065007/25000000000000 : ℝ)^25 := by
    have hnat : (245072839 : ℕ)^33*25000000000000^25 ≤ 18138761065007^25*312500000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      245072839 312500000 18138761065007 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (161083481/2000000000 : ℝ)^33 ≤ (1798530214281/50000000000000 : ℝ)^25 := by
    have hnat : (161083481 : ℕ)^33*50000000000000^25 ≤ 1798530214281^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161083481 2000000000 1798530214281 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(675151521/2000000000 : ℝ), (245072839/312500000 : ℝ), (-161083481/2000000000 : ℝ)] ![(2980986911799/12500000000000 : ℝ), (18138761065007/25000000000000 : ℝ), (1798530214281/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(675151521/2000000000 : ℝ)|^33 ≤ (2980986911799/12500000000000 : ℝ)^25
        have hw : |(675151521/2000000000 : ℝ)|=(675151521/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(245072839/312500000 : ℝ)|^33 ≤ (18138761065007/25000000000000 : ℝ)^25
        have hw : |(245072839/312500000 : ℝ)|=(245072839/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-161083481/2000000000 : ℝ)|^33 ≤ (1798530214281/50000000000000 : ℝ)^25
        have hw : |(-161083481/2000000000 : ℝ)|=(161083481/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s1_s1_14 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (7528/9765625 : ℝ)*x 0 + (1560694579/10000000000 : ℝ)*x 1 + (-9339791587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7528/9765625 : ℝ)^33 ≤ (3888508323/50000000000000 : ℝ)^25 := by
    have hnat : (7528 : ℕ)^33*50000000000000^25 ≤ 3888508323^25*9765625^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7528 9765625 3888508323 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1560694579/10000000000 : ℝ)^33 ≤ (4306749988323/50000000000000 : ℝ)^25 := by
    have hnat : (1560694579 : ℕ)^33*50000000000000^25 ≤ 4306749988323^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1560694579 10000000000 4306749988323 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9339791587/10000000000 : ℝ)^33 ≤ (5711170187073/6250000000000 : ℝ)^25 := by
    have hnat : (9339791587 : ℕ)^33*6250000000000^25 ≤ 5711170187073^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9339791587 10000000000 5711170187073 6250000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7528/9765625 : ℝ), (1560694579/10000000000 : ℝ), (-9339791587/10000000000 : ℝ)] ![(3888508323/50000000000000 : ℝ), (4306749988323/50000000000000 : ℝ), (5711170187073/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7528/9765625 : ℝ)|^33 ≤ (3888508323/50000000000000 : ℝ)^25
        have hw : |(7528/9765625 : ℝ)|=(7528/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1560694579/10000000000 : ℝ)|^33 ≤ (4306749988323/50000000000000 : ℝ)^25
        have hw : |(1560694579/10000000000 : ℝ)|=(1560694579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-9339791587/10000000000 : ℝ)|^33 ≤ (5711170187073/6250000000000 : ℝ)^25
        have hw : |(-9339791587/10000000000 : ℝ)|=(9339791587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s1_s1_15 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3917879103/10000000000 : ℝ)*x 0 + (-419985941/1250000000 : ℝ)*x 1 + (-1133738703/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3917879103/10000000000 : ℝ)^33 ≤ (1451434241783/5000000000000 : ℝ)^25 := by
    have hnat : (3917879103 : ℕ)^33*5000000000000^25 ≤ 1451434241783^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3917879103 10000000000 1451434241783 5000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (419985941/1250000000 : ℝ)^33 ≤ (1481251058463/6250000000000 : ℝ)^25 := by
    have hnat : (419985941 : ℕ)^33*6250000000000^25 ≤ 1481251058463^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419985941 1250000000 1481251058463 6250000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1133738703/2000000000 : ℝ)^33 ≤ (11817824555099/25000000000000 : ℝ)^25 := by
    have hnat : (1133738703 : ℕ)^33*25000000000000^25 ≤ 11817824555099^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1133738703 2000000000 11817824555099 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3917879103/10000000000 : ℝ), (-419985941/1250000000 : ℝ), (-1133738703/2000000000 : ℝ)] ![(1451434241783/5000000000000 : ℝ), (1481251058463/6250000000000 : ℝ), (11817824555099/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3917879103/10000000000 : ℝ)|^33 ≤ (1451434241783/5000000000000 : ℝ)^25
        have hw : |(3917879103/10000000000 : ℝ)|=(3917879103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-419985941/1250000000 : ℝ)|^33 ≤ (1481251058463/6250000000000 : ℝ)^25
        have hw : |(-419985941/1250000000 : ℝ)|=(419985941/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1133738703/2000000000 : ℝ)|^33 ≤ (11817824555099/25000000000000 : ℝ)^25
        have hw : |(-1133738703/2000000000 : ℝ)|=(1133738703/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s1_s1_16 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (8308567711/10000000000 : ℝ)*x 0 + (508346837/2000000000 : ℝ)*x 1 + (6752247/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8308567711/10000000000 : ℝ)^33 ≤ (15660460610049/20000000000000 : ℝ)^25 := by
    have hnat : (8308567711 : ℕ)^33*20000000000000^25 ≤ 15660460610049^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8308567711 10000000000 15660460610049 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (508346837/2000000000 : ℝ)^33 ≤ (16397278446561/100000000000000 : ℝ)^25 := by
    have hnat : (508346837 : ℕ)^33*100000000000000^25 ≤ 16397278446561^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508346837 2000000000 16397278446561 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6752247/62500000 : ℝ)^33 ≤ (42403347917/800000000000 : ℝ)^25 := by
    have hnat : (6752247 : ℕ)^33*800000000000^25 ≤ 42403347917^25*62500000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6752247 62500000 42403347917 800000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8308567711/10000000000 : ℝ), (508346837/2000000000 : ℝ), (6752247/62500000 : ℝ)] ![(15660460610049/20000000000000 : ℝ), (16397278446561/100000000000000 : ℝ), (42403347917/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8308567711/10000000000 : ℝ)|^33 ≤ (15660460610049/20000000000000 : ℝ)^25
        have hw : |(8308567711/10000000000 : ℝ)|=(8308567711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(508346837/2000000000 : ℝ)|^33 ≤ (16397278446561/100000000000000 : ℝ)^25
        have hw : |(508346837/2000000000 : ℝ)|=(508346837/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6752247/62500000 : ℝ)|^33 ≤ (42403347917/800000000000 : ℝ)^25
        have hw : |(6752247/62500000 : ℝ)|=(6752247/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s1_s1_20 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (777797129/1000000000 : ℝ)*x 0 + (3323726597/10000000000 : ℝ)*x 1 + (-253147193/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (777797129/1000000000 : ℝ)^33 ≤ (358850509781/500000000000 : ℝ)^25 := by
    have hnat : (777797129 : ℕ)^33*500000000000^25 ≤ 358850509781^25*1000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      777797129 1000000000 358850509781 500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3323726597/10000000000 : ℝ)^33 ≤ (4672780508087/20000000000000 : ℝ)^25 := by
    have hnat : (3323726597 : ℕ)^33*20000000000000^25 ≤ 4672780508087^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3323726597 10000000000 4672780508087 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (253147193/2500000000 : ℝ)^33 ≤ (6082494359/125000000000 : ℝ)^25 := by
    have hnat : (253147193 : ℕ)^33*125000000000^25 ≤ 6082494359^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      253147193 2500000000 6082494359 125000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(777797129/1000000000 : ℝ), (3323726597/10000000000 : ℝ), (-253147193/2500000000 : ℝ)] ![(358850509781/500000000000 : ℝ), (4672780508087/20000000000000 : ℝ), (6082494359/125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(777797129/1000000000 : ℝ)|^33 ≤ (358850509781/500000000000 : ℝ)^25
        have hw : |(777797129/1000000000 : ℝ)|=(777797129/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3323726597/10000000000 : ℝ)|^33 ≤ (4672780508087/20000000000000 : ℝ)^25
        have hw : |(3323726597/10000000000 : ℝ)|=(3323726597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-253147193/2500000000 : ℝ)|^33 ≤ (6082494359/125000000000 : ℝ)^25
        have hw : |(-253147193/2500000000 : ℝ)|=(253147193/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s1_s1_21 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (26181427/5000000000 : ℝ)*x 0 + (1680638009/2500000000 : ℝ)*x 1 + (-5060954333/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26181427/5000000000 : ℝ)^33 ≤ (12190479303/12500000000000 : ℝ)^25 := by
    have hnat : (26181427 : ℕ)^33*12500000000000^25 ≤ 12190479303^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26181427 5000000000 12190479303 12500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1680638009/2500000000 : ℝ)^33 ≤ (11840637991373/20000000000000 : ℝ)^25 := by
    have hnat : (1680638009 : ℕ)^33*20000000000000^25 ≤ 11840637991373^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1680638009 2500000000 11840637991373 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5060954333/10000000000 : ℝ)^33 ≤ (2543705387349/6250000000000 : ℝ)^25 := by
    have hnat : (5060954333 : ℕ)^33*6250000000000^25 ≤ 2543705387349^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5060954333 10000000000 2543705387349 6250000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(26181427/5000000000 : ℝ), (1680638009/2500000000 : ℝ), (-5060954333/10000000000 : ℝ)] ![(12190479303/12500000000000 : ℝ), (11840637991373/20000000000000 : ℝ), (2543705387349/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(26181427/5000000000 : ℝ)|^33 ≤ (12190479303/12500000000000 : ℝ)^25
        have hw : |(26181427/5000000000 : ℝ)|=(26181427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1680638009/2500000000 : ℝ)|^33 ≤ (11840637991373/20000000000000 : ℝ)^25
        have hw : |(1680638009/2500000000 : ℝ)|=(1680638009/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5060954333/10000000000 : ℝ)|^33 ≤ (2543705387349/6250000000000 : ℝ)^25
        have hw : |(-5060954333/10000000000 : ℝ)|=(5060954333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s1_s1_22 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (8397734001/10000000000 : ℝ)*x 0 + (-1670906469/10000000000 : ℝ)*x 1 + (-949597749/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8397734001/10000000000 : ℝ)^33 ≤ (1588268733153/2000000000000 : ℝ)^25 := by
    have hnat : (8397734001 : ℕ)^33*2000000000000^25 ≤ 1588268733153^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8397734001 10000000000 1588268733153 2000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1670906469/10000000000 : ℝ)^33 ≤ (9425335657287/100000000000000 : ℝ)^25 := by
    have hnat : (1670906469 : ℕ)^33*100000000000000^25 ≤ 9425335657287^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1670906469 10000000000 9425335657287 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (949597749/5000000000 : ℝ)^33 ≤ (11161227672979/100000000000000 : ℝ)^25 := by
    have hnat : (949597749 : ℕ)^33*100000000000000^25 ≤ 11161227672979^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      949597749 5000000000 11161227672979 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8397734001/10000000000 : ℝ), (-1670906469/10000000000 : ℝ), (-949597749/5000000000 : ℝ)] ![(1588268733153/2000000000000 : ℝ), (9425335657287/100000000000000 : ℝ), (11161227672979/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8397734001/10000000000 : ℝ)|^33 ≤ (1588268733153/2000000000000 : ℝ)^25
        have hw : |(8397734001/10000000000 : ℝ)|=(8397734001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1670906469/10000000000 : ℝ)|^33 ≤ (9425335657287/100000000000000 : ℝ)^25
        have hw : |(-1670906469/10000000000 : ℝ)|=(1670906469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-949597749/5000000000 : ℝ)|^33 ≤ (11161227672979/100000000000000 : ℝ)^25
        have hw : |(-949597749/5000000000 : ℝ)|=(949597749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s1_s1_23 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2641224679/10000000000 : ℝ)*x 0 + (148213159/200000000 : ℝ)*x 1 + (485221289/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2641224679/10000000000 : ℝ)^33 ≤ (1724976001831/10000000000000 : ℝ)^25 := by
    have hnat : (2641224679 : ℕ)^33*10000000000000^25 ≤ 1724976001831^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2641224679 10000000000 1724976001831 10000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (148213159/200000000 : ℝ)^33 ≤ (33665179806261/50000000000000 : ℝ)^25 := by
    have hnat : (148213159 : ℕ)^33*50000000000000^25 ≤ 33665179806261^25*200000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      148213159 200000000 33665179806261 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (485221289/2000000000 : ℝ)^33 ≤ (1541988035717/10000000000000 : ℝ)^25 := by
    have hnat : (485221289 : ℕ)^33*10000000000000^25 ≤ 1541988035717^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      485221289 2000000000 1541988035717 10000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2641224679/10000000000 : ℝ), (148213159/200000000 : ℝ), (485221289/2000000000 : ℝ)] ![(1724976001831/10000000000000 : ℝ), (33665179806261/50000000000000 : ℝ), (1541988035717/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2641224679/10000000000 : ℝ)|^33 ≤ (1724976001831/10000000000000 : ℝ)^25
        have hw : |(2641224679/10000000000 : ℝ)|=(2641224679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(148213159/200000000 : ℝ)|^33 ≤ (33665179806261/50000000000000 : ℝ)^25
        have hw : |(148213159/200000000 : ℝ)|=(148213159/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(485221289/2000000000 : ℝ)|^33 ≤ (1541988035717/10000000000000 : ℝ)^25
        have hw : |(485221289/2000000000 : ℝ)|=(485221289/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302054_s1_s1_27 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1863381689/2500000000 : ℝ)*x 0 + (3513354567/10000000000 : ℝ)*x 1 + (-1336022159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1863381689/2500000000 : ℝ)^33 ≤ (67844960746607/100000000000000 : ℝ)^25 := by
    have hnat : (1863381689 : ℕ)^33*100000000000000^25 ≤ 67844960746607^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1863381689 2500000000 67844960746607 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3513354567/10000000000 : ℝ)^33 ≤ (25139290399617/100000000000000 : ℝ)^25 := by
    have hnat : (3513354567 : ℕ)^33*100000000000000^25 ≤ 25139290399617^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3513354567 10000000000 25139290399617 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1336022159/10000000000 : ℝ)^33 ≤ (7015748837017/100000000000000 : ℝ)^25 := by
    have hnat : (1336022159 : ℕ)^33*100000000000000^25 ≤ 7015748837017^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336022159 10000000000 7015748837017 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1863381689/2500000000 : ℝ), (3513354567/10000000000 : ℝ), (-1336022159/10000000000 : ℝ)] ![(67844960746607/100000000000000 : ℝ), (25139290399617/100000000000000 : ℝ), (7015748837017/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1863381689/2500000000 : ℝ)|^33 ≤ (67844960746607/100000000000000 : ℝ)^25
        have hw : |(1863381689/2500000000 : ℝ)|=(1863381689/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3513354567/10000000000 : ℝ)|^33 ≤ (25139290399617/100000000000000 : ℝ)^25
        have hw : |(3513354567/10000000000 : ℝ)|=(3513354567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1336022159/10000000000 : ℝ)|^33 ≤ (7015748837017/100000000000000 : ℝ)^25
        have hw : |(-1336022159/10000000000 : ℝ)|=(1336022159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c302054_s1 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((11843/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11843/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(47969/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(47969/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-16881/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-16881/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((43367/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(43367/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(44881/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(44881/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-73149/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-73149/100000 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4769/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4769/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (36753/20000 : ℝ) := by
    linarith only [f.Tcap]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (11843/12500 : ℝ) ^ (65/16 : ℝ) ≤ (80304770883101828757/100000000000000000000 : ℝ) := by
    have hpowers : (11843/12500 : ℝ)^65 ≤ (80304770883101828757/100000000000000000000 : ℝ)^16 := by
      have hnat : (11843 : ℕ)^65*100000000000000000000^16 ≤ 80304770883101828757^16*12500^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11843 12500 80304770883101828757 100000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11843/12500 : ℝ)) (X := (80304770883101828757/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (180304770883101828757/100000000000000000000 : ℝ) ≤ (361299352391453/312500000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (180304770883101828757/100000000000000000000 : ℝ)^16 ≤ (361299352391453/312500000000000 : ℝ)^65 := by
      have hnat : (180304770883101828757 : ℕ)^16*312500000000000^65 ≤ 361299352391453^65*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        180304770883101828757 100000000000000000000 361299352391453 312500000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (361299352391453/312500000000000 : ℝ)) (X := (180304770883101828757/100000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (130304770883101828757/50000000000000000000 : ℝ) ≤ (12658947986080129/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (130304770883101828757/50000000000000000000 : ℝ)^16 ≤ (12658947986080129/10000000000000000 : ℝ)^65 := by
      have hnat : (130304770883101828757 : ℕ)^16*10000000000000000^65 ≤ 12658947986080129^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        130304770883101828757 50000000000000000000 12658947986080129 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12658947986080129/10000000000000000 : ℝ)) (X := (130304770883101828757/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(48799352391453/296075000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1097368709553633/9474400000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (11843/12500 : ℝ)) (alpha := (48799352391453/296075000000000 : ℝ)) (beta := (1097368709553633/9474400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (11843/12500 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(48799352391453/296075000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1097368709553633/9474400000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (47969/50000 : ℝ) ^ (65/16 : ℝ) ≤ (84496176746177150237/100000000000000000000 : ℝ) := by
    have hpowers : (47969/50000 : ℝ)^65 ≤ (84496176746177150237/100000000000000000000 : ℝ)^16 := by
      have hnat : (47969 : ℕ)^65*100000000000000000000^16 ≤ 84496176746177150237^16*50000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        47969 50000 84496176746177150237 100000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (47969/50000 : ℝ)) (X := (84496176746177150237/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (184496176746177150237/100000000000000000000 : ℝ) ≤ (581358221648911/500000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (184496176746177150237/100000000000000000000 : ℝ)^16 ≤ (581358221648911/500000000000000 : ℝ)^65 := by
      have hnat : (184496176746177150237 : ℕ)^16*500000000000000^65 ≤ 581358221648911^65*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        184496176746177150237 100000000000000000000 581358221648911 500000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (581358221648911/500000000000000 : ℝ)) (X := (184496176746177150237/100000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (134496176746177150237/50000000000000000000 : ℝ) ≤ (12757986485716911/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (134496176746177150237/50000000000000000000 : ℝ)^16 ≤ (12757986485716911/10000000000000000 : ℝ)^65 := by
      have hnat : (134496176746177150237 : ℕ)^16*10000000000000000^65 ≤ 12757986485716911^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        134496176746177150237 50000000000000000000 12757986485716911 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12757986485716911/10000000000000000 : ℝ)) (X := (134496176746177150237/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(81358221648911/479690000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(1130822052738691/9593800000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (47969/50000 : ℝ)) (alpha := (81358221648911/479690000000000 : ℝ)) (beta := (1130822052738691/9593800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (47969/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(81358221648911/479690000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(1130822052738691/9593800000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (16881/20000 : ℝ) ^ (65/16 : ℝ) ≤ (125548265286695653/250000000000000000 : ℝ) := by
    have hpowers : (16881/20000 : ℝ)^65 ≤ (125548265286695653/250000000000000000 : ℝ)^16 := by
      have hnat : (16881 : ℕ)^65*250000000000000000^16 ≤ 125548265286695653^16*20000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16881 20000 125548265286695653 250000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16881/20000 : ℝ)) (X := (125548265286695653/250000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (375548265286695653/250000000000000000 : ℝ) ≤ (10794481014577/9765625000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (375548265286695653/250000000000000000 : ℝ)^16 ≤ (10794481014577/9765625000000 : ℝ)^65 := by
      have hnat : (375548265286695653 : ℕ)^16*9765625000000^65 ≤ 10794481014577^65*250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        375548265286695653 250000000000000000 10794481014577 9765625000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10794481014577/9765625000000 : ℝ)) (X := (375548265286695653/250000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (250548265286695653/125000000000000000 : ℝ) ≤ (11866807021793361/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (250548265286695653/125000000000000000 : ℝ)^16 ≤ (11866807021793361/10000000000000000 : ℝ)^65 := by
      have hnat : (250548265286695653 : ℕ)^16*10000000000000000^65 ≤ 11866807021793361^65*125000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        250548265286695653 125000000000000000 11866807021793361 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11866807021793361/10000000000000000 : ℝ)) (X := (250548265286695653/125000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(342952004859/2747558593750 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(813258462866513/8440500000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (16881/20000 : ℝ)) (alpha := (342952004859/2747558593750 : ℝ)) (beta := (813258462866513/8440500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (16881/20000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(342952004859/2747558593750 : ℝ)*((1 : ℝ)*pair X 2 0)+(813258462866513/8440500000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_1 : ((2966997283/5000000000 : ℝ)*X 1 0+(-13446249/100000000 : ℝ)*X 1 1+(-5249383879/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((1091637107/2000000000 : ℝ)*X 0 0+(5442259977/10000000000 : ℝ)*X 0 1+(-1778824843/10000000000 : ℝ)*X 0 2+(1091637107/2000000000 : ℝ)*X 1 0+(5442259977/10000000000 : ℝ)*X 1 1+(-1778824843/10000000000 : ℝ)*X 1 2+(1091637107/2000000000 : ℝ)*X 2 0+(5442259977/10000000000 : ℝ)*X 2 1+(-1778824843/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((249/1000000000 : ℝ)*X 0 0+(647876177/5000000000 : ℝ)*X 0 1+(-4742628913/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((4158546451/10000000000 : ℝ)*X 1 0+(-977203989/5000000000 : ℝ)*X 1 1+(-6532435741/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((1397658233/5000000000 : ℝ)*X 2 0+(8270105557/10000000000 : ℝ)*X 2 1+(200859947/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((675151521/2000000000 : ℝ)*X 0 0+(245072839/312500000 : ℝ)*X 0 1+(-161083481/2000000000 : ℝ)*X 0 2+(675151521/2000000000 : ℝ)*X 1 0+(245072839/312500000 : ℝ)*X 1 1+(-161083481/2000000000 : ℝ)*X 1 2+(675151521/2000000000 : ℝ)*X 2 0+(245072839/312500000 : ℝ)*X 2 1+(-161083481/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((7528/9765625 : ℝ)*X 0 0+(1560694579/10000000000 : ℝ)*X 0 1+(-9339791587/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((3917879103/10000000000 : ℝ)*X 1 0+(-419985941/1250000000 : ℝ)*X 1 1+(-1133738703/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((8308567711/10000000000 : ℝ)*X 2 0+(508346837/2000000000 : ℝ)*X 2 1+(6752247/62500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((777797129/1000000000 : ℝ)*X 0 0+(3323726597/10000000000 : ℝ)*X 0 1+(-253147193/2500000000 : ℝ)*X 0 2+(777797129/1000000000 : ℝ)*X 1 0+(3323726597/10000000000 : ℝ)*X 1 1+(-253147193/2500000000 : ℝ)*X 1 2+(777797129/1000000000 : ℝ)*X 2 0+(3323726597/10000000000 : ℝ)*X 2 1+(-253147193/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((26181427/5000000000 : ℝ)*X 0 0+(1680638009/2500000000 : ℝ)*X 0 1+(-5060954333/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((8397734001/10000000000 : ℝ)*X 1 0+(-1670906469/10000000000 : ℝ)*X 1 1+(-949597749/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((2641224679/10000000000 : ℝ)*X 2 0+(148213159/200000000 : ℝ)*X 2 1+(485221289/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((1863381689/2500000000 : ℝ)*X 0 0+(3513354567/10000000000 : ℝ)*X 0 1+(-1336022159/10000000000 : ℝ)*X 0 2+(1863381689/2500000000 : ℝ)*X 1 0+(3513354567/10000000000 : ℝ)*X 1 1+(-1336022159/10000000000 : ℝ)*X 1 2+(1863381689/2500000000 : ℝ)*X 2 0+(3513354567/10000000000 : ℝ)*X 2 1+(-1336022159/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302054_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((43367/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(43367/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (11011979786463227235309/959380000000000000000000000 : ℝ) := by norm_num
    linear_combination (365893655509/500000000000 : ℝ)*(base7) + (317429/250000000000 : ℝ)*(base50) + (482993309293/1000000000000 : ℝ)*(base53) + (94724448911/500000000000 : ℝ)*(base60) + (346051640621/200000000000 : ℝ)*(major_s1_0) + (346051640621/200000000000 : ℝ)*(major_s1_1) + (1247264893813/1000000000000 : ℝ)*(major_s1_2) + (8146591/125000000000 : ℝ)*(sp_s1_1) + (1368929409143/1000000000000 : ℝ)*(sp_s1_7) + (684596581347/500000000000 : ℝ)*(sp_s1_8) + (926166274741/500000000000 : ℝ)*(sp_s1_9) + (945855512151/500000000000 : ℝ)*(sp_s1_13) + (409831047/1000000000000 : ℝ)*(sp_s1_14) + (1264137/15625000000 : ℝ)*(sp_s1_15) + (289980928321/250000000000 : ℝ)*(f.failure) + (926166274741/500000000000 : ℝ)*(f.sum) + (27061339579075471801/67480390750000000000000000000000 : ℝ)*base63 + (602508664926481/8440500000000000000000000000 : ℝ)*base64 + (1098304433650781/1918760000000000000000000000 : ℝ)*base67 + (72790603904487/175843750000000000000000000 : ℝ)*base68 + (22397992191060065467/99960841500000000000000000000000 : ℝ)*base71 + (134495287479859/1894880000000000000000000000 : ℝ)*base72 + (124796979919637/479690000000000000000000000 : ℝ)*base75 + (4819605575721/29607500000000000000000000 : ℝ)*base76 + (35521063146519601593/90895498720000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (1857/2500000000000000 : ℝ)*base87 + (1857/2500000000000000 : ℝ)*base89 + (643/2500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(44881/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(44881/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (65792442575334668134549374805983/6393362141218000000000000000000000000 : ℝ) := by norm_num
    linear_combination (39960086059/50000000000 : ℝ)*(base7) + (653821/1000000000000 : ℝ)*(base40) + (351151829333/500000000000 : ℝ)*(base53) + (3140293289/31250000000 : ℝ)*(base60) + (343951346867/200000000000 : ℝ)*(major_s1_0) + (343951346867/200000000000 : ℝ)*(major_s1_1) + (1017453075669/1000000000000 : ℝ)*(major_s1_2) + (1168087/500000000000 : ℝ)*(sp_s1_1) + (23745171/500000000000 : ℝ)*(sp_s1_8) + (547385792819/500000000000 : ℝ)*(sp_s1_14) + (547360879561/500000000000 : ℝ)*(sp_s1_15) + (112317202769/62500000000 : ℝ)*(sp_s1_16) + (1952050774283/1000000000000 : ℝ)*(sp_s1_20) + (17363351/500000000000 : ℝ)*(sp_s1_27) + (230576755961/200000000000 : ℝ)*(f.failure) + (112317202769/62500000000 : ℝ)*(f.sum) + (3662351866352095087/67480390750000000000000000000000 : ℝ)*base62 + (1792115569024949/2813500000000000000000000000 : ℝ)*base65 + (990668723713497/1918760000000000000000000000 : ℝ)*base66 + (80169753316801/703375000000000000000000000 : ℝ)*base69 + (25656811657595385407/33320280500000000000000000000000 : ℝ)*base71 + (1478232951283693/1894880000000000000000000000 : ℝ)*base72 + (327875857910891/479690000000000000000000000 : ℝ)*base75 + (82960261435827/118430000000000000000000000 : ℝ)*base77 + (33201861403231701017/90895498720000000000000000000000 : ℝ)*base78 + (237/2000000000000000 : ℝ)*base87 + (237/2000000000000000 : ℝ)*base89 + (237/2000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-73149/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-73149/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (72808511486656060679597268536409/6393362141218000000000000000000000000 : ℝ) := by norm_num
    linear_combination (442225114561/500000000000 : ℝ)*(base7) + (1050799/50000000000 : ℝ)*(base15) + (131011850733/1000000000000 : ℝ)*(base39) + (3541839/250000000000 : ℝ)*(base43) + (1619221488309/1000000000000 : ℝ)*(major_s1_0) + (1619207320953/1000000000000 : ℝ)*(major_s1_1) + (1619221488309/1000000000000 : ℝ)*(major_s1_2) + (918383/250000000000 : ℝ)*(sp_s1_6) + (12239711/1000000000000 : ℝ)*(sp_s1_9) + (160496303/1000000000000 : ℝ)*(sp_s1_20) + (1611167669789/1000000000000 : ℝ)*(sp_s1_21) + (322232164233/200000000000 : ℝ)*(sp_s1_22) + (805577715039/500000000000 : ℝ)*(sp_s1_23) + (1969773414861/1000000000000 : ℝ)*(sp_s1_27) + (542743677787/500000000000 : ℝ)*(f.failure) + (322236367429/200000000000 : ℝ)*(f.sum) + (26517363056607246207/67480390750000000000000000000000 : ℝ)*base62 + (179326409513261/2813500000000000000000000000 : ℝ)*base64 + (3123644496850117/9593800000000000000000000000 : ℝ)*base67 + (485757044888753/1406750000000000000000000000 : ℝ)*base68 + (2954229775988786993/33320280500000000000000000000000 : ℝ)*base70 + (852951936853563/9474400000000000000000000000 : ℝ)*base72 + (327494259151303/479690000000000000000000000 : ℝ)*base74 + (61205126628381/592150000000000000000000000 : ℝ)*base76 + (176622506321879508383/454477493600000000000000000000000 : ℝ)*base78 + (3679/5000000000000000 : ℝ)*base87 + (3679/5000000000000000 : ℝ)*base89 + (3679/5000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((11843/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11843/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(47969/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(47969/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-16881/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-16881/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((43367/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(43367/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(44881/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(44881/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-73149/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-73149/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c302054_s1 p hpa hpb X hX hprev0

#print axioms solution
