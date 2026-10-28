-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c303062_s4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:59:24.756655+00:00
-- url     : https://prove2.me/submissions/34532855-bf2c-4df9-9c0e-1885496a0d99

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
theorem collision_support_c303062_s4_s4_0 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2306432293/10000000000 : ℝ)*x 0 + (4872049577/10000000000 : ℝ)*x 1 + (-5632201739/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2306432293/10000000000 : ℝ)^33 ≤ (14423867935081/100000000000000 : ℝ)^25 := by
    have hnat : (2306432293 : ℕ)^33*100000000000000^25 ≤ 14423867935081^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2306432293 10000000000 14423867935081 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4872049577/10000000000 : ℝ)^33 ≤ (38706102521477/100000000000000 : ℝ)^25 := by
    have hnat : (4872049577 : ℕ)^33*100000000000000^25 ≤ 38706102521477^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4872049577 10000000000 38706102521477 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5632201739/10000000000 : ℝ)^33 ≤ (9374005904893/20000000000000 : ℝ)^25 := by
    have hnat : (5632201739 : ℕ)^33*20000000000000^25 ≤ 9374005904893^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5632201739 10000000000 9374005904893 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2306432293/10000000000 : ℝ), (4872049577/10000000000 : ℝ), (-5632201739/10000000000 : ℝ)] ![(14423867935081/100000000000000 : ℝ), (38706102521477/100000000000000 : ℝ), (9374005904893/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2306432293/10000000000 : ℝ)|^33 ≤ (14423867935081/100000000000000 : ℝ)^25
        have hw : |(-2306432293/10000000000 : ℝ)|=(2306432293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4872049577/10000000000 : ℝ)|^33 ≤ (38706102521477/100000000000000 : ℝ)^25
        have hw : |(4872049577/10000000000 : ℝ)|=(4872049577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5632201739/10000000000 : ℝ)|^33 ≤ (9374005904893/20000000000000 : ℝ)^25
        have hw : |(-5632201739/10000000000 : ℝ)|=(5632201739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303062_s4_s4_1 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (487008447/1000000000 : ℝ)*x 0 + (-2310340309/10000000000 : ℝ)*x 1 + (-43993281/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (487008447/1000000000 : ℝ)^33 ≤ (38685496229607/100000000000000 : ℝ)^25 := by
    have hnat : (487008447 : ℕ)^33*100000000000000^25 ≤ 38685496229607^25*1000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      487008447 1000000000 38685496229607 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2310340309/10000000000 : ℝ)^33 ≤ (2891227438467/20000000000000 : ℝ)^25 := by
    have hnat : (2310340309 : ℕ)^33*20000000000000^25 ≤ 2891227438467^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2310340309 10000000000 2891227438467 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (43993281/78125000 : ℝ)^33 ≤ (5857295820797/12500000000000 : ℝ)^25 := by
    have hnat : (43993281 : ℕ)^33*12500000000000^25 ≤ 5857295820797^25*78125000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43993281 78125000 5857295820797 12500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(487008447/1000000000 : ℝ), (-2310340309/10000000000 : ℝ), (-43993281/78125000 : ℝ)] ![(38685496229607/100000000000000 : ℝ), (2891227438467/20000000000000 : ℝ), (5857295820797/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(487008447/1000000000 : ℝ)|^33 ≤ (38685496229607/100000000000000 : ℝ)^25
        have hw : |(487008447/1000000000 : ℝ)|=(487008447/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2310340309/10000000000 : ℝ)|^33 ≤ (2891227438467/20000000000000 : ℝ)^25
        have hw : |(-2310340309/10000000000 : ℝ)|=(2310340309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-43993281/78125000 : ℝ)|^33 ≤ (5857295820797/12500000000000 : ℝ)^25
        have hw : |(-43993281/78125000 : ℝ)|=(43993281/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303062_s4_s4_2 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (253567591/500000000 : ℝ)*x 0 + (5068913239/10000000000 : ℝ)*x 1 + (2774343607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (253567591/500000000 : ℝ)^33 ≤ (1020242347417/2500000000000 : ℝ)^25 := by
    have hnat : (253567591 : ℕ)^33*2500000000000^25 ≤ 1020242347417^25*500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      253567591 500000000 1020242347417 2500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5068913239/10000000000 : ℝ)^33 ≤ (326270342809/800000000000 : ℝ)^25 := by
    have hnat : (5068913239 : ℕ)^33*800000000000^25 ≤ 326270342809^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5068913239 10000000000 326270342809 800000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2774343607/10000000000 : ℝ)^33 ≤ (18406513240141/100000000000000 : ℝ)^25 := by
    have hnat : (2774343607 : ℕ)^33*100000000000000^25 ≤ 18406513240141^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2774343607 10000000000 18406513240141 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(253567591/500000000 : ℝ), (5068913239/10000000000 : ℝ), (2774343607/10000000000 : ℝ)] ![(1020242347417/2500000000000 : ℝ), (326270342809/800000000000 : ℝ), (18406513240141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(253567591/500000000 : ℝ)|^33 ≤ (1020242347417/2500000000000 : ℝ)^25
        have hw : |(253567591/500000000 : ℝ)|=(253567591/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5068913239/10000000000 : ℝ)|^33 ≤ (326270342809/800000000000 : ℝ)^25
        have hw : |(5068913239/10000000000 : ℝ)|=(5068913239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2774343607/10000000000 : ℝ)|^33 ≤ (18406513240141/100000000000000 : ℝ)^25
        have hw : |(2774343607/10000000000 : ℝ)|=(2774343607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303062_s4_s4_6 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (108694761/200000000 : ℝ)*x 0 + (339241321/625000000 : ℝ)*x 1 + (-1832694207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (108694761/200000000 : ℝ)^33 ≤ (22356601094317/50000000000000 : ℝ)^25 := by
    have hnat : (108694761 : ℕ)^33*50000000000000^25 ≤ 22356601094317^25*200000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108694761 200000000 22356601094317 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (339241321/625000000 : ℝ)^33 ≤ (22319266904993/50000000000000 : ℝ)^25 := by
    have hnat : (339241321 : ℕ)^33*50000000000000^25 ≤ 22319266904993^25*625000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339241321 625000000 22319266904993 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1832694207/10000000000 : ℝ)^33 ≤ (2129652796987/20000000000000 : ℝ)^25 := by
    have hnat : (1832694207 : ℕ)^33*20000000000000^25 ≤ 2129652796987^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1832694207 10000000000 2129652796987 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(108694761/200000000 : ℝ), (339241321/625000000 : ℝ), (-1832694207/10000000000 : ℝ)] ![(22356601094317/50000000000000 : ℝ), (22319266904993/50000000000000 : ℝ), (2129652796987/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(108694761/200000000 : ℝ)|^33 ≤ (22356601094317/50000000000000 : ℝ)^25
        have hw : |(108694761/200000000 : ℝ)|=(108694761/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(339241321/625000000 : ℝ)|^33 ≤ (22319266904993/50000000000000 : ℝ)^25
        have hw : |(339241321/625000000 : ℝ)|=(339241321/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1832694207/10000000000 : ℝ)|^33 ≤ (2129652796987/20000000000000 : ℝ)^25
        have hw : |(-1832694207/10000000000 : ℝ)|=(1832694207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303062_s4_s4_7 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-209925243/1000000000 : ℝ)*x 0 + (141616847/312500000 : ℝ)*x 1 + (-6100681561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (209925243/1000000000 : ℝ)^33 ≤ (2547741450571/20000000000000 : ℝ)^25 := by
    have hnat : (209925243 : ℕ)^33*20000000000000^25 ≤ 2547741450571^25*1000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209925243 1000000000 2547741450571 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (141616847/312500000 : ℝ)^33 ≤ (35177880313781/100000000000000 : ℝ)^25 := by
    have hnat : (141616847 : ℕ)^33*100000000000000^25 ≤ 35177880313781^25*312500000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141616847 312500000 35177880313781 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6100681561/10000000000 : ℝ)^33 ≤ (3255213275839/6250000000000 : ℝ)^25 := by
    have hnat : (6100681561 : ℕ)^33*6250000000000^25 ≤ 3255213275839^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6100681561 10000000000 3255213275839 6250000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-209925243/1000000000 : ℝ), (141616847/312500000 : ℝ), (-6100681561/10000000000 : ℝ)] ![(2547741450571/20000000000000 : ℝ), (35177880313781/100000000000000 : ℝ), (3255213275839/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-209925243/1000000000 : ℝ)|^33 ≤ (2547741450571/20000000000000 : ℝ)^25
        have hw : |(-209925243/1000000000 : ℝ)|=(209925243/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(141616847/312500000 : ℝ)|^33 ≤ (35177880313781/100000000000000 : ℝ)^25
        have hw : |(141616847/312500000 : ℝ)|=(141616847/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6100681561/10000000000 : ℝ)|^33 ≤ (3255213275839/6250000000000 : ℝ)^25
        have hw : |(-6100681561/10000000000 : ℝ)|=(6100681561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303062_s4_s4_8 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (242239507/500000000 : ℝ)*x 0 + (-1842939253/10000000000 : ℝ)*x 1 + (-748893333/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (242239507/500000000 : ℝ)^33 ≤ (38420495353397/100000000000000 : ℝ)^25 := by
    have hnat : (242239507 : ℕ)^33*100000000000000^25 ≤ 38420495353397^25*500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      242239507 500000000 38420495353397 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1842939253/10000000000 : ℝ)^33 ≤ (2681726943323/25000000000000 : ℝ)^25 := by
    have hnat : (1842939253 : ℕ)^33*25000000000000^25 ≤ 2681726943323^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1842939253 10000000000 2681726943323 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (748893333/1250000000 : ℝ)^33 ≤ (50852596863533/100000000000000 : ℝ)^25 := by
    have hnat : (748893333 : ℕ)^33*100000000000000^25 ≤ 50852596863533^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      748893333 1250000000 50852596863533 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(242239507/500000000 : ℝ), (-1842939253/10000000000 : ℝ), (-748893333/1250000000 : ℝ)] ![(38420495353397/100000000000000 : ℝ), (2681726943323/25000000000000 : ℝ), (50852596863533/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(242239507/500000000 : ℝ)|^33 ≤ (38420495353397/100000000000000 : ℝ)^25
        have hw : |(242239507/500000000 : ℝ)|=(242239507/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1842939253/10000000000 : ℝ)|^33 ≤ (2681726943323/25000000000000 : ℝ)^25
        have hw : |(-1842939253/10000000000 : ℝ)|=(1842939253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-748893333/1250000000 : ℝ)|^33 ≤ (50852596863533/100000000000000 : ℝ)^25
        have hw : |(-748893333/1250000000 : ℝ)|=(748893333/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303062_s4_s4_9 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4931662403/10000000000 : ℝ)*x 0 + (2833152531/5000000000 : ℝ)*x 1 + (2184078661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4931662403/10000000000 : ℝ)^33 ≤ (7866493779029/20000000000000 : ℝ)^25 := by
    have hnat : (4931662403 : ℕ)^33*20000000000000^25 ≤ 7866493779029^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4931662403 10000000000 7866493779029 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2833152531/5000000000 : ℝ)^33 ≤ (47245009109287/100000000000000 : ℝ)^25 := by
    have hnat : (2833152531 : ℕ)^33*100000000000000^25 ≤ 47245009109287^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2833152531 5000000000 47245009109287 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2184078661/10000000000 : ℝ)^33 ≤ (13422521983831/100000000000000 : ℝ)^25 := by
    have hnat : (2184078661 : ℕ)^33*100000000000000^25 ≤ 13422521983831^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184078661 10000000000 13422521983831 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4931662403/10000000000 : ℝ), (2833152531/5000000000 : ℝ), (2184078661/10000000000 : ℝ)] ![(7866493779029/20000000000000 : ℝ), (47245009109287/100000000000000 : ℝ), (13422521983831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4931662403/10000000000 : ℝ)|^33 ≤ (7866493779029/20000000000000 : ℝ)^25
        have hw : |(4931662403/10000000000 : ℝ)|=(4931662403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2833152531/5000000000 : ℝ)|^33 ≤ (47245009109287/100000000000000 : ℝ)^25
        have hw : |(2833152531/5000000000 : ℝ)|=(2833152531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2184078661/10000000000 : ℝ)|^33 ≤ (13422521983831/100000000000000 : ℝ)^25
        have hw : |(2184078661/10000000000 : ℝ)|=(2184078661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303062_s4_s4_13 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5239684803/10000000000 : ℝ)*x 0 + (2950444829/5000000000 : ℝ)*x 1 + (-4413339/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5239684803/10000000000 : ℝ)^33 ≤ (21303591154699/50000000000000 : ℝ)^25 := by
    have hnat : (5239684803 : ℕ)^33*50000000000000^25 ≤ 21303591154699^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239684803 10000000000 21303591154699 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2950444829/5000000000 : ℝ)^33 ≤ (6230474239941/12500000000000 : ℝ)^25 := by
    have hnat : (2950444829 : ℕ)^33*12500000000000^25 ≤ 6230474239941^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2950444829 5000000000 6230474239941 12500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4413339/31250000 : ℝ)^33 ≤ (37745118737/500000000000 : ℝ)^25 := by
    have hnat : (4413339 : ℕ)^33*500000000000^25 ≤ 37745118737^25*31250000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4413339 31250000 37745118737 500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5239684803/10000000000 : ℝ), (2950444829/5000000000 : ℝ), (-4413339/31250000 : ℝ)] ![(21303591154699/50000000000000 : ℝ), (6230474239941/12500000000000 : ℝ), (37745118737/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5239684803/10000000000 : ℝ)|^33 ≤ (21303591154699/50000000000000 : ℝ)^25
        have hw : |(5239684803/10000000000 : ℝ)|=(5239684803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2950444829/5000000000 : ℝ)|^33 ≤ (6230474239941/12500000000000 : ℝ)^25
        have hw : |(2950444829/5000000000 : ℝ)|=(2950444829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4413339/31250000 : ℝ)|^33 ≤ (37745118737/500000000000 : ℝ)^25
        have hw : |(-4413339/31250000 : ℝ)|=(4413339/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303062_s4_s4_14 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-448213281/2500000000 : ℝ)*x 0 + (4795982443/10000000000 : ℝ)*x 1 + (-1517675299/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (448213281/2500000000 : ℝ)^33 ≤ (10343773930929/100000000000000 : ℝ)^25 := by
    have hnat : (448213281 : ℕ)^33*100000000000000^25 ≤ 10343773930929^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448213281 2500000000 10343773930929 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4795982443/10000000000 : ℝ)^33 ≤ (37910403916339/100000000000000 : ℝ)^25 := by
    have hnat : (4795982443 : ℕ)^33*100000000000000^25 ≤ 37910403916339^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4795982443 10000000000 37910403916339 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1517675299/2500000000 : ℝ)^33 ≤ (12936455534607/25000000000000 : ℝ)^25 := by
    have hnat : (1517675299 : ℕ)^33*25000000000000^25 ≤ 12936455534607^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1517675299 2500000000 12936455534607 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-448213281/2500000000 : ℝ), (4795982443/10000000000 : ℝ), (-1517675299/2500000000 : ℝ)] ![(10343773930929/100000000000000 : ℝ), (37910403916339/100000000000000 : ℝ), (12936455534607/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-448213281/2500000000 : ℝ)|^33 ≤ (10343773930929/100000000000000 : ℝ)^25
        have hw : |(-448213281/2500000000 : ℝ)|=(448213281/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4795982443/10000000000 : ℝ)|^33 ≤ (37910403916339/100000000000000 : ℝ)^25
        have hw : |(4795982443/10000000000 : ℝ)|=(4795982443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1517675299/2500000000 : ℝ)|^33 ≤ (12936455534607/25000000000000 : ℝ)^25
        have hw : |(-1517675299/2500000000 : ℝ)|=(1517675299/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303062_s4_s4_15 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4586147311/10000000000 : ℝ)*x 0 + (-2155910053/10000000000 : ℝ)*x 1 + (-3005228749/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4586147311/10000000000 : ℝ)^33 ≤ (17868223045111/50000000000000 : ℝ)^25 := by
    have hnat : (4586147311 : ℕ)^33*50000000000000^25 ≤ 17868223045111^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4586147311 10000000000 17868223045111 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2155910053/10000000000 : ℝ)^33 ≤ (6597242468723/50000000000000 : ℝ)^25 := by
    have hnat : (2155910053 : ℕ)^33*50000000000000^25 ≤ 6597242468723^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155910053 10000000000 6597242468723 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3005228749/5000000000 : ℝ)^33 ≤ (12767267236861/25000000000000 : ℝ)^25 := by
    have hnat : (3005228749 : ℕ)^33*25000000000000^25 ≤ 12767267236861^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3005228749 5000000000 12767267236861 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4586147311/10000000000 : ℝ), (-2155910053/10000000000 : ℝ), (-3005228749/5000000000 : ℝ)] ![(17868223045111/50000000000000 : ℝ), (6597242468723/50000000000000 : ℝ), (12767267236861/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4586147311/10000000000 : ℝ)|^33 ≤ (17868223045111/50000000000000 : ℝ)^25
        have hw : |(4586147311/10000000000 : ℝ)|=(4586147311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2155910053/10000000000 : ℝ)|^33 ≤ (6597242468723/50000000000000 : ℝ)^25
        have hw : |(-2155910053/10000000000 : ℝ)|=(2155910053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3005228749/5000000000 : ℝ)|^33 ≤ (12767267236861/25000000000000 : ℝ)^25
        have hw : |(-3005228749/5000000000 : ℝ)|=(3005228749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303062_s4_s4_16 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5600119413/10000000000 : ℝ)*x 0 + (1248312939/2500000000 : ℝ)*x 1 + (34275189/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5600119413/10000000000 : ℝ)^33 ≤ (23258967084799/50000000000000 : ℝ)^25 := by
    have hnat : (5600119413 : ℕ)^33*50000000000000^25 ≤ 23258967084799^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5600119413 10000000000 23258967084799 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1248312939/2500000000 : ℝ)^33 ≤ (19991076267657/50000000000000 : ℝ)^25 := by
    have hnat : (1248312939 : ℕ)^33*50000000000000^25 ≤ 19991076267657^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1248312939 2500000000 19991076267657 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (34275189/156250000 : ℝ)^33 ≤ (13499913275149/100000000000000 : ℝ)^25 := by
    have hnat : (34275189 : ℕ)^33*100000000000000^25 ≤ 13499913275149^25*156250000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34275189 156250000 13499913275149 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5600119413/10000000000 : ℝ), (1248312939/2500000000 : ℝ), (34275189/156250000 : ℝ)] ![(23258967084799/50000000000000 : ℝ), (19991076267657/50000000000000 : ℝ), (13499913275149/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5600119413/10000000000 : ℝ)|^33 ≤ (23258967084799/50000000000000 : ℝ)^25
        have hw : |(5600119413/10000000000 : ℝ)|=(5600119413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1248312939/2500000000 : ℝ)|^33 ≤ (19991076267657/50000000000000 : ℝ)^25
        have hw : |(1248312939/2500000000 : ℝ)|=(1248312939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(34275189/156250000 : ℝ)|^33 ≤ (13499913275149/100000000000000 : ℝ)^25
        have hw : |(34275189/156250000 : ℝ)|=(34275189/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303062_s4_s4_20 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1506283941/2500000000 : ℝ)*x 0 + (2554079173/5000000000 : ℝ)*x 1 + (-353637571/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1506283941/2500000000 : ℝ)^33 ≤ (10246751898259/20000000000000 : ℝ)^25 := by
    have hnat : (1506283941 : ℕ)^33*20000000000000^25 ≤ 10246751898259^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1506283941 2500000000 10246751898259 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2554079173/5000000000 : ℝ)^33 ≤ (41201112584527/100000000000000 : ℝ)^25 := by
    have hnat : (2554079173 : ℕ)^33*100000000000000^25 ≤ 41201112584527^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2554079173 5000000000 41201112584527 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (353637571/2500000000 : ℝ)^33 ≤ (236410247027/3125000000000 : ℝ)^25 := by
    have hnat : (353637571 : ℕ)^33*3125000000000^25 ≤ 236410247027^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      353637571 2500000000 236410247027 3125000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1506283941/2500000000 : ℝ), (2554079173/5000000000 : ℝ), (-353637571/2500000000 : ℝ)] ![(10246751898259/20000000000000 : ℝ), (41201112584527/100000000000000 : ℝ), (236410247027/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1506283941/2500000000 : ℝ)|^33 ≤ (10246751898259/20000000000000 : ℝ)^25
        have hw : |(1506283941/2500000000 : ℝ)|=(1506283941/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2554079173/5000000000 : ℝ)|^33 ≤ (41201112584527/100000000000000 : ℝ)^25
        have hw : |(2554079173/5000000000 : ℝ)|=(2554079173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-353637571/2500000000 : ℝ)|^33 ≤ (236410247027/3125000000000 : ℝ)^25
        have hw : |(-353637571/2500000000 : ℝ)|=(353637571/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303062_s4_s4_21 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-65429579/400000000 : ℝ)*x 0 + (5137406251/10000000000 : ℝ)*x 1 + (-5854106681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (65429579/400000000 : ℝ)^33 ≤ (916437089987/10000000000000 : ℝ)^25 := by
    have hnat : (65429579 : ℕ)^33*10000000000000^25 ≤ 916437089987^25*400000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65429579 400000000 916437089987 10000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5137406251/10000000000 : ℝ)^33 ≤ (20756396837383/50000000000000 : ℝ)^25 := by
    have hnat : (5137406251 : ℕ)^33*50000000000000^25 ≤ 20756396837383^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5137406251 10000000000 20756396837383 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5854106681/10000000000 : ℝ)^33 ≤ (9864567081867/20000000000000 : ℝ)^25 := by
    have hnat : (5854106681 : ℕ)^33*20000000000000^25 ≤ 9864567081867^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5854106681 10000000000 9864567081867 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-65429579/400000000 : ℝ), (5137406251/10000000000 : ℝ), (-5854106681/10000000000 : ℝ)] ![(916437089987/10000000000000 : ℝ), (20756396837383/50000000000000 : ℝ), (9864567081867/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-65429579/400000000 : ℝ)|^33 ≤ (916437089987/10000000000000 : ℝ)^25
        have hw : |(-65429579/400000000 : ℝ)|=(65429579/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5137406251/10000000000 : ℝ)|^33 ≤ (20756396837383/50000000000000 : ℝ)^25
        have hw : |(5137406251/10000000000 : ℝ)|=(5137406251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5854106681/10000000000 : ℝ)|^33 ≤ (9864567081867/20000000000000 : ℝ)^25
        have hw : |(-5854106681/10000000000 : ℝ)|=(5854106681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303062_s4_s4_22 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (43402757/78125000 : ℝ)*x 0 + (-2059758699/10000000000 : ℝ)*x 1 + (-321287041/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (43402757/78125000 : ℝ)^33 ≤ (46029898668639/100000000000000 : ℝ)^25 := by
    have hnat : (43402757 : ℕ)^33*100000000000000^25 ≤ 46029898668639^25*78125000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43402757 78125000 46029898668639 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2059758699/10000000000 : ℝ)^33 ≤ (3105829316239/25000000000000 : ℝ)^25 := by
    have hnat : (2059758699 : ℕ)^33*25000000000000^25 ≤ 3105829316239^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2059758699 10000000000 3105829316239 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (321287041/625000000 : ℝ)^33 ≤ (1661871362277/4000000000000 : ℝ)^25 := by
    have hnat : (321287041 : ℕ)^33*4000000000000^25 ≤ 1661871362277^25*625000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      321287041 625000000 1661871362277 4000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(43402757/78125000 : ℝ), (-2059758699/10000000000 : ℝ), (-321287041/625000000 : ℝ)] ![(46029898668639/100000000000000 : ℝ), (3105829316239/25000000000000 : ℝ), (1661871362277/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(43402757/78125000 : ℝ)|^33 ≤ (46029898668639/100000000000000 : ℝ)^25
        have hw : |(43402757/78125000 : ℝ)|=(43402757/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2059758699/10000000000 : ℝ)|^33 ≤ (3105829316239/25000000000000 : ℝ)^25
        have hw : |(-2059758699/10000000000 : ℝ)|=(2059758699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-321287041/625000000 : ℝ)|^33 ≤ (1661871362277/4000000000000 : ℝ)^25
        have hw : |(-321287041/625000000 : ℝ)|=(321287041/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303062_s4_s4_23 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (47508051/100000000 : ℝ)*x 0 + (53346757/100000000 : ℝ)*x 1 + (2833975411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (47508051/100000000 : ℝ)^33 ≤ (37439731239497/100000000000000 : ℝ)^25 := by
    have hnat : (47508051 : ℕ)^33*100000000000000^25 ≤ 37439731239497^25*100000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47508051 100000000 37439731239497 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (53346757/100000000 : ℝ)^33 ≤ (5453717072327/12500000000000 : ℝ)^25 := by
    have hnat : (53346757 : ℕ)^33*12500000000000^25 ≤ 5453717072327^25*100000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53346757 100000000 5453717072327 12500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2833975411/10000000000 : ℝ)^33 ≤ (946526607959/5000000000000 : ℝ)^25 := by
    have hnat : (2833975411 : ℕ)^33*5000000000000^25 ≤ 946526607959^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2833975411 10000000000 946526607959 5000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(47508051/100000000 : ℝ), (53346757/100000000 : ℝ), (2833975411/10000000000 : ℝ)] ![(37439731239497/100000000000000 : ℝ), (5453717072327/12500000000000 : ℝ), (946526607959/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(47508051/100000000 : ℝ)|^33 ≤ (37439731239497/100000000000000 : ℝ)^25
        have hw : |(47508051/100000000 : ℝ)|=(47508051/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(53346757/100000000 : ℝ)|^33 ≤ (5453717072327/12500000000000 : ℝ)^25
        have hw : |(53346757/100000000 : ℝ)|=(53346757/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2833975411/10000000000 : ℝ)|^33 ≤ (946526607959/5000000000000 : ℝ)^25
        have hw : |(2833975411/10000000000 : ℝ)|=(2833975411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303062_s4_s4_27 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6099494437/10000000000 : ℝ)*x 0 + (2457524173/5000000000 : ℝ)*x 1 + (-1582445381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6099494437/10000000000 : ℝ)^33 ≤ (52070034833071/100000000000000 : ℝ)^25 := by
    have hnat : (6099494437 : ℕ)^33*100000000000000^25 ≤ 52070034833071^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6099494437 10000000000 52070034833071 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2457524173/5000000000 : ℝ)^33 ≤ (39157656122263/100000000000000 : ℝ)^25 := by
    have hnat : (2457524173 : ℕ)^33*100000000000000^25 ≤ 39157656122263^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2457524173 5000000000 39157656122263 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1582445381/10000000000 : ℝ)^33 ≤ (8772309025157/100000000000000 : ℝ)^25 := by
    have hnat : (1582445381 : ℕ)^33*100000000000000^25 ≤ 8772309025157^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1582445381 10000000000 8772309025157 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6099494437/10000000000 : ℝ), (2457524173/5000000000 : ℝ), (-1582445381/10000000000 : ℝ)] ![(52070034833071/100000000000000 : ℝ), (39157656122263/100000000000000 : ℝ), (8772309025157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6099494437/10000000000 : ℝ)|^33 ≤ (52070034833071/100000000000000 : ℝ)^25
        have hw : |(6099494437/10000000000 : ℝ)|=(6099494437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2457524173/5000000000 : ℝ)|^33 ≤ (39157656122263/100000000000000 : ℝ)^25
        have hw : |(2457524173/5000000000 : ℝ)|=(2457524173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1582445381/10000000000 : ℝ)|^33 ≤ (8772309025157/100000000000000 : ℝ)^25
        have hw : |(-1582445381/10000000000 : ℝ)|=(1582445381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c303062_s4 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev3 : (0 : ℝ) ≤ ((55887/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(55887/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7033/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(7033/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-1937/5000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-1937/5000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((15031/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15031/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7549/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(7549/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-1801/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-1801/10000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76461/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76461/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76461/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76461/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76461/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76461/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  rcases hprev3 with ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩
  have s4_pow0 : (55887/100000 : ℝ) ^ (131/32 : ℝ) ≤ (9237481400374525113/100000000000000000000 : ℝ) := by
    have hpowers : (55887/100000 : ℝ)^131 ≤ (9237481400374525113/100000000000000000000 : ℝ)^32 := by
      have hnat : (55887 : ℕ)^131*100000000000000000000^32 ≤ 9237481400374525113^32*100000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        55887 100000 9237481400374525113 100000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (55887/100000 : ℝ)) (X := (9237481400374525113/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s4_corner0a : (109237481400374525113/100000000000000000000 : ℝ) ≤ (2043634520650499/2000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (109237481400374525113/100000000000000000000 : ℝ)^32 ≤ (2043634520650499/2000000000000000 : ℝ)^131 := by
      have hnat : (109237481400374525113 : ℕ)^32*2000000000000000^131 ≤ 2043634520650499^131*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        109237481400374525113 100000000000000000000 2043634520650499 2000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2043634520650499/2000000000000000 : ℝ)) (X := (109237481400374525113/100000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s4_corner0b : (59237481400374525113/50000000000000000000 : ℝ) ≤ (5211408576501227/5000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (59237481400374525113/50000000000000000000 : ℝ)^32 ≤ (5211408576501227/5000000000000000 : ℝ)^131 := by
      have hnat : (59237481400374525113 : ℕ)^32*5000000000000000^131 ≤ 5211408576501227^131*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59237481400374525113 50000000000000000000 5211408576501227 5000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5211408576501227/5000000000000000 : ℝ)) (X := (59237481400374525113/50000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s4_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(14544840216833/372580000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(68214849916653/1862900000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (55887/100000 : ℝ)) (alpha := (14544840216833/372580000000000 : ℝ)) (beta := (68214849916653/1862900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow0,s4_corner0a]) (by linarith only [s4_pow0,s4_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (55887/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(14544840216833/372580000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(68214849916653/1862900000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow1 : (7033/12500 : ℝ) ^ (131/32 : ℝ) ≤ (1899050581753516471/20000000000000000000 : ℝ) := by
    have hpowers : (7033/12500 : ℝ)^131 ≤ (1899050581753516471/20000000000000000000 : ℝ)^32 := by
      have hnat : (7033 : ℕ)^131*20000000000000000000^32 ≤ 1899050581753516471^32*12500^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7033 12500 1899050581753516471 20000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7033/12500 : ℝ)) (X := (1899050581753516471/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s4_corner1a : (21899050581753516471/20000000000000000000 : ℝ) ≤ (10224057356701573/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (21899050581753516471/20000000000000000000 : ℝ)^32 ≤ (10224057356701573/10000000000000000 : ℝ)^131 := by
      have hnat : (21899050581753516471 : ℕ)^32*10000000000000000^131 ≤ 10224057356701573^131*20000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21899050581753516471 20000000000000000000 10224057356701573 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10224057356701573/10000000000000000 : ℝ)) (X := (21899050581753516471/20000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s4_corner1b : (11899050581753516471/10000000000000000000 : ℝ) ≤ (1304234752791569/1250000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (11899050581753516471/10000000000000000000 : ℝ)^32 ≤ (1304234752791569/1250000000000000 : ℝ)^131 := by
      have hnat : (11899050581753516471 : ℕ)^32*1250000000000000^131 ≤ 1304234752791569^131*10000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11899050581753516471 10000000000000000000 1304234752791569 1250000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1304234752791569/1250000000000000 : ℝ)) (X := (11899050581753516471/10000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s4_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(224057356701573/5626400000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(16140051202383/432800000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (7033/12500 : ℝ)) (alpha := (224057356701573/5626400000000000 : ℝ)) (beta := (16140051202383/432800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow1,s4_corner1a]) (by linarith only [s4_pow1,s4_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (7033/12500 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(224057356701573/5626400000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(16140051202383/432800000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow2 : (1937/5000 : ℝ) ^ (131/32 : ℝ) ≤ (2060764809610542673/100000000000000000000 : ℝ) := by
    have hpowers : (1937/5000 : ℝ)^131 ≤ (2060764809610542673/100000000000000000000 : ℝ)^32 := by
      have hnat : (1937 : ℕ)^131*100000000000000000000^32 ≤ 2060764809610542673^32*5000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1937 5000 2060764809610542673 100000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1937/5000 : ℝ)) (X := (2060764809610542673/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s4_corner2a : (102060764809610542673/100000000000000000000 : ℝ) ≤ (10049951969484237/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (102060764809610542673/100000000000000000000 : ℝ)^32 ≤ (10049951969484237/10000000000000000 : ℝ)^131 := by
      have hnat : (102060764809610542673 : ℕ)^32*10000000000000000^131 ≤ 10049951969484237^131*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102060764809610542673 100000000000000000000 10049951969484237 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10049951969484237/10000000000000000 : ℝ)) (X := (102060764809610542673/100000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s4_corner2b : (52060764809610542673/50000000000000000000 : ℝ) ≤ (10099147424582517/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (52060764809610542673/50000000000000000000 : ℝ)^32 ≤ (10099147424582517/10000000000000000 : ℝ)^131 := by
      have hnat : (52060764809610542673 : ℕ)^32*10000000000000000^131 ≤ 10099147424582517^131*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52060764809610542673 50000000000000000000 10099147424582517 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10099147424582517/10000000000000000 : ℝ)) (X := (52060764809610542673/50000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s4_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(49951969484237/3874000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1229886377457/96850000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (1937/5000 : ℝ)) (alpha := (49951969484237/3874000000000000 : ℝ)) (beta := (1229886377457/96850000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow2,s4_corner2a]) (by linarith only [s4_pow2,s4_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1937/5000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(49951969484237/3874000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1229886377457/96850000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s4_0 : ((-2306432293/10000000000 : ℝ)*X 0 0+(4872049577/10000000000 : ℝ)*X 0 1+(-5632201739/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303062_s4_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_1 : ((487008447/1000000000 : ℝ)*X 1 0+(-2310340309/10000000000 : ℝ)*X 1 1+(-43993281/78125000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303062_s4_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_2 : ((253567591/500000000 : ℝ)*X 2 0+(5068913239/10000000000 : ℝ)*X 2 1+(2774343607/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303062_s4_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_6 : ((108694761/200000000 : ℝ)*X 0 0+(339241321/625000000 : ℝ)*X 0 1+(-1832694207/10000000000 : ℝ)*X 0 2+(108694761/200000000 : ℝ)*X 1 0+(339241321/625000000 : ℝ)*X 1 1+(-1832694207/10000000000 : ℝ)*X 1 2+(108694761/200000000 : ℝ)*X 2 0+(339241321/625000000 : ℝ)*X 2 1+(-1832694207/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303062_s4_s4_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_7 : ((-209925243/1000000000 : ℝ)*X 0 0+(141616847/312500000 : ℝ)*X 0 1+(-6100681561/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303062_s4_s4_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_8 : ((242239507/500000000 : ℝ)*X 1 0+(-1842939253/10000000000 : ℝ)*X 1 1+(-748893333/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303062_s4_s4_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_9 : ((4931662403/10000000000 : ℝ)*X 2 0+(2833152531/5000000000 : ℝ)*X 2 1+(2184078661/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303062_s4_s4_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_13 : ((5239684803/10000000000 : ℝ)*X 0 0+(2950444829/5000000000 : ℝ)*X 0 1+(-4413339/31250000 : ℝ)*X 0 2+(5239684803/10000000000 : ℝ)*X 1 0+(2950444829/5000000000 : ℝ)*X 1 1+(-4413339/31250000 : ℝ)*X 1 2+(5239684803/10000000000 : ℝ)*X 2 0+(2950444829/5000000000 : ℝ)*X 2 1+(-4413339/31250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303062_s4_s4_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_14 : ((-448213281/2500000000 : ℝ)*X 0 0+(4795982443/10000000000 : ℝ)*X 0 1+(-1517675299/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303062_s4_s4_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_15 : ((4586147311/10000000000 : ℝ)*X 1 0+(-2155910053/10000000000 : ℝ)*X 1 1+(-3005228749/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303062_s4_s4_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_16 : ((5600119413/10000000000 : ℝ)*X 2 0+(1248312939/2500000000 : ℝ)*X 2 1+(34275189/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303062_s4_s4_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_20 : ((1506283941/2500000000 : ℝ)*X 0 0+(2554079173/5000000000 : ℝ)*X 0 1+(-353637571/2500000000 : ℝ)*X 0 2+(1506283941/2500000000 : ℝ)*X 1 0+(2554079173/5000000000 : ℝ)*X 1 1+(-353637571/2500000000 : ℝ)*X 1 2+(1506283941/2500000000 : ℝ)*X 2 0+(2554079173/5000000000 : ℝ)*X 2 1+(-353637571/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303062_s4_s4_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_21 : ((-65429579/400000000 : ℝ)*X 0 0+(5137406251/10000000000 : ℝ)*X 0 1+(-5854106681/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303062_s4_s4_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_22 : ((43402757/78125000 : ℝ)*X 1 0+(-2059758699/10000000000 : ℝ)*X 1 1+(-321287041/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303062_s4_s4_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_23 : ((47508051/100000000 : ℝ)*X 2 0+(53346757/100000000 : ℝ)*X 2 1+(2833975411/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303062_s4_s4_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_27 : ((6099494437/10000000000 : ℝ)*X 0 0+(2457524173/5000000000 : ℝ)*X 0 1+(-1582445381/10000000000 : ℝ)*X 0 2+(6099494437/10000000000 : ℝ)*X 1 0+(2457524173/5000000000 : ℝ)*X 1 1+(-1582445381/10000000000 : ℝ)*X 1 2+(6099494437/10000000000 : ℝ)*X 2 0+(2457524173/5000000000 : ℝ)*X 2 1+(-1582445381/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303062_s4_s4_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s4_0 : (0 : ℝ) ≤ ((15031/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15031/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (5869390950492533855752341/403131560000000000000000000000 : ℝ) := by norm_num
    linear_combination (316708059439/500000000000 : ℝ)*(base39) + (494098191151/1000000000000 : ℝ)*(base49) + (5583516553/40000000000 : ℝ)*(base60) + (910605071289/100000000000 : ℝ)*(major_s4_0) + (910605071289/100000000000 : ℝ)*(major_s4_1) + (910605071289/100000000000 : ℝ)*(major_s4_2) + (42557383/500000000000 : ℝ)*(sp_s4_0) + (80357117/1000000000000 : ℝ)*(sp_s4_1) + (12158261482517/1000000000000 : ℝ)*(sp_s4_7) + (6079042983549/500000000000 : ℝ)*(sp_s4_8) + (12158138266123/1000000000000 : ℝ)*(sp_s4_9) + (6053749975329/1000000000000 : ℝ)*(sp_s4_13) + (180273069/1000000000000 : ℝ)*(sp_s4_15) + (5208279/25000000000 : ℝ)*(sp_s4_23) + (6053749975329/1000000000000 : ℝ)*(f.failure) + (12158346597283/1000000000000 : ℝ)*(f.sum) + (3572456358518667/32243600000000000000000000000 : ℝ)*base63 + (430162443619/9685000000000000000000000 : ℝ)*base64 + (2521986105629/8656000000000000000000000 : ℝ)*base66 + (173364885479947/387400000000000000000000000 : ℝ)*base68 + (1352235723081049/5551442000000000000000000000 : ℝ)*base71 + (147112401695407/186290000000000000000000000 : ℝ)*base73 + (17252117993987/562640000000000000000000000 : ℝ)*base74 + (2697827480753/186290000000000000000000000 : ℝ)*base77 + (200117185986848317/806263120000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (591/5000000000000000 : ℝ)*base86 + (591/5000000000000000 : ℝ)*base88 + (591/5000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s4_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7549/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(7549/25000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (18476121812521622076102296883/1501665061000000000000000000000000 : ℝ) := by norm_num
    linear_combination (616181353407/1000000000000 : ℝ)*(base39) + (13394891907/25000000000 : ℝ)*(base49) + (175609/125000000000 : ℝ)*(base60) + (9220283492899/1000000000000 : ℝ)*(major_s4_0) + (9220283492899/1000000000000 : ℝ)*(major_s4_1) + (9220283492899/1000000000000 : ℝ)*(major_s4_2) + (4349283/200000000000 : ℝ)*(sp_s4_6) + (53639471/1000000000000 : ℝ)*(sp_s4_7) + (44477977/500000000000 : ℝ)*(sp_s4_8) + (6155408361101/500000000000 : ℝ)*(sp_s4_14) + (12310781405719/1000000000000 : ℝ)*(sp_s4_15) + (12310870361673/1000000000000 : ℝ)*(sp_s4_16) + (1532343336389/250000000000 : ℝ)*(sp_s4_20) + (297430897/1000000000000 : ℝ)*(sp_s4_27) + (6129692522869/1000000000000 : ℝ)*(f.failure) + (12310870361673/1000000000000 : ℝ)*(f.sum) + (131765735670507137/322436000000000000000000000000 : ℝ)*base63 + (26420202856963/96850000000000000000000000 : ℝ)*base65 + (32646252414237/432800000000000000000000000 : ℝ)*base67 + (1486670757852263/3874000000000000000000000000 : ℝ)*base69 + (82819702434762063/277572100000000000000000000000 : ℝ)*base71 + (57931747314593/1862900000000000000000000000 : ℝ)*base72 + (1973509294944047/5626400000000000000000000000 : ℝ)*base75 + (106845024179639/372580000000000000000000000 : ℝ)*base77 + (420564389602155769/8062631200000000000000000000000 : ℝ)*base79 + (2749/5000000000000000 : ℝ)*base87 + (2749/5000000000000000 : ℝ)*base89 + (2749/5000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s4_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-1801/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-1801/10000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (7797930550848164943705539481/750832530500000000000000000000000 : ℝ) := by norm_num
    linear_combination (274620256963/250000000000 : ℝ)*(base39) + (1006803/250000000000 : ℝ)*(base40) + (96124868651/250000000000 : ℝ)*(base49) + (1860430271811/250000000000 : ℝ)*(major_s4_0) + (1860430271811/250000000000 : ℝ)*(major_s4_1) + (1860430271811/250000000000 : ℝ)*(major_s4_2) + (3019791/125000000000 : ℝ)*(sp_s4_0) + (248293/25000000000 : ℝ)*(sp_s4_2) + (13298227/125000000000 : ℝ)*(sp_s4_9) + (162931649/1000000000000 : ℝ)*(sp_s4_20) + (9936119588659/1000000000000 : ℝ)*(sp_s4_21) + (9936143746987/1000000000000 : ℝ)*(sp_s4_22) + (9936027429451/1000000000000 : ℝ)*(sp_s4_23) + (618391504243/125000000000 : ℝ)*(sp_s4_27) + (4947294965593/1000000000000 : ℝ)*(f.failure) + (9936143746987/1000000000000 : ℝ)*(f.sum) + (27199120130658907/80609000000000000000000000000 : ℝ)*base62 + (44150391160947/96850000000000000000000000 : ℝ)*base64 + (543978039433/108200000000000000000000000 : ℝ)*base67 + (457592462201393/968500000000000000000000000 : ℝ)*base68 + (39130578824384491/138786050000000000000000000000 : ℝ)*base70 + (115913979574353/465725000000000000000000000 : ℝ)*base73 + (714587219091217/1406600000000000000000000000 : ℝ)*base74 + (5090035797239/11643125000000000000000000 : ℝ)*base76 + (413973570343374859/2015657800000000000000000000000 : ℝ)*base78 + (4953/5000000000000000 : ℝ)*base87 + (4953/5000000000000000 : ℝ)*base89 + (4953/5000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s4_0,ratio_s4_1,ratio_s4_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev3 : (0 : ℝ) ≤ ((55887/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(55887/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7033/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(7033/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-1937/5000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-1937/5000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((15031/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15031/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7549/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(7549/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-1801/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-1801/10000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c303062_s4 p hpa hpb X hX hprev3

#print axioms solution
