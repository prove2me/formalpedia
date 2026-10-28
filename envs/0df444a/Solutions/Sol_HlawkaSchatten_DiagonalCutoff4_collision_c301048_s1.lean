-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c301048_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:27:41.551723+00:00
-- url     : https://prove2.me/submissions/c535e149-b8ba-40e0-8157-fc433b157dae

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
theorem collision_support_c301048_s1_s1_0 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2673218913/10000000000 : ℝ)*x 0 + (1334631169/5000000000 : ℝ)*x 1 + (-362539827/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673218913/10000000000 : ℝ)^65 ≤ (4343939484387/25000000000000 : ℝ)^49 := by
    have hnat : (2673218913 : ℕ)^65*25000000000000^49 ≤ 4343939484387^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673218913 10000000000 4343939484387 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1334631169/5000000000 : ℝ)^65 ≤ (3468330228383/20000000000000 : ℝ)^49 := by
    have hnat : (1334631169 : ℕ)^65*20000000000000^49 ≤ 3468330228383^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1334631169 5000000000 3468330228383 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (362539827/500000000 : ℝ)^65 ≤ (32641295449903/50000000000000 : ℝ)^49 := by
    have hnat : (362539827 : ℕ)^65*50000000000000^49 ≤ 32641295449903^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      362539827 500000000 32641295449903 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2673218913/10000000000 : ℝ), (1334631169/5000000000 : ℝ), (-362539827/500000000 : ℝ)] ![(4343939484387/25000000000000 : ℝ), (3468330228383/20000000000000 : ℝ), (32641295449903/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2673218913/10000000000 : ℝ)|^65 ≤ (4343939484387/25000000000000 : ℝ)^49
        have hw : |(-2673218913/10000000000 : ℝ)|=(2673218913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1334631169/5000000000 : ℝ)|^65 ≤ (3468330228383/20000000000000 : ℝ)^49
        have hw : |(1334631169/5000000000 : ℝ)|=(1334631169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-362539827/500000000 : ℝ)|^65 ≤ (32641295449903/50000000000000 : ℝ)^49
        have hw : |(-362539827/500000000 : ℝ)|=(362539827/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301048_s1_s1_2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5696258361/10000000000 : ℝ)*x 0 + (712832341/1250000000 : ℝ)*x 1 + (532721789/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5696258361/10000000000 : ℝ)^65 ≤ (23700212045151/50000000000000 : ℝ)^49 := by
    have hnat : (5696258361 : ℕ)^65*50000000000000^49 ≤ 23700212045151^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5696258361 10000000000 23700212045151 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (712832341/1250000000 : ℝ)^65 ≤ (47471087460153/100000000000000 : ℝ)^49 := by
    have hnat : (712832341 : ℕ)^65*100000000000000^49 ≤ 47471087460153^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      712832341 1250000000 47471087460153 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (532721789/5000000000 : ℝ)^65 ≤ (51284884341/1000000000000 : ℝ)^49 := by
    have hnat : (532721789 : ℕ)^65*1000000000000^49 ≤ 51284884341^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      532721789 5000000000 51284884341 1000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5696258361/10000000000 : ℝ), (712832341/1250000000 : ℝ), (532721789/5000000000 : ℝ)] ![(23700212045151/50000000000000 : ℝ), (47471087460153/100000000000000 : ℝ), (51284884341/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5696258361/10000000000 : ℝ)|^65 ≤ (23700212045151/50000000000000 : ℝ)^49
        have hw : |(5696258361/10000000000 : ℝ)|=(5696258361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(712832341/1250000000 : ℝ)|^65 ≤ (47471087460153/100000000000000 : ℝ)^49
        have hw : |(712832341/1250000000 : ℝ)|=(712832341/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(532721789/5000000000 : ℝ)|^65 ≤ (51284884341/1000000000000 : ℝ)^49
        have hw : |(532721789/5000000000 : ℝ)|=(532721789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301048_s1_s1_7 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2117149713/10000000000 : ℝ)*x 0 + (378677231/2000000000 : ℝ)*x 1 + (-8151435981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2117149713/10000000000 : ℝ)^65 ≤ (3188077175113/25000000000000 : ℝ)^49 := by
    have hnat : (2117149713 : ℕ)^65*25000000000000^49 ≤ 3188077175113^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117149713 10000000000 3188077175113 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (378677231/2000000000 : ℝ)^65 ≤ (5498011880493/50000000000000 : ℝ)^49 := by
    have hnat : (378677231 : ℕ)^65*50000000000000^49 ≤ 5498011880493^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      378677231 2000000000 5498011880493 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8151435981/10000000000 : ℝ)^65 ≤ (76251667530613/100000000000000 : ℝ)^49 := by
    have hnat : (8151435981 : ℕ)^65*100000000000000^49 ≤ 76251667530613^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8151435981 10000000000 76251667530613 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2117149713/10000000000 : ℝ), (378677231/2000000000 : ℝ), (-8151435981/10000000000 : ℝ)] ![(3188077175113/25000000000000 : ℝ), (5498011880493/50000000000000 : ℝ), (76251667530613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2117149713/10000000000 : ℝ)|^65 ≤ (3188077175113/25000000000000 : ℝ)^49
        have hw : |(-2117149713/10000000000 : ℝ)|=(2117149713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(378677231/2000000000 : ℝ)|^65 ≤ (5498011880493/50000000000000 : ℝ)^49
        have hw : |(378677231/2000000000 : ℝ)|=(378677231/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8151435981/10000000000 : ℝ)|^65 ≤ (76251667530613/100000000000000 : ℝ)^49
        have hw : |(-8151435981/10000000000 : ℝ)|=(8151435981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301048_s1_s1_8 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (656588337/2000000000 : ℝ)*x 0 + (-293596447/1000000000 : ℝ)*x 1 + (-3294706871/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (656588337/2000000000 : ℝ)^65 ≤ (570490337773/2500000000000 : ℝ)^49 := by
    have hnat : (656588337 : ℕ)^65*2500000000000^49 ≤ 570490337773^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656588337 2000000000 570490337773 2500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (293596447/1000000000 : ℝ)^65 ≤ (19676830159119/100000000000000 : ℝ)^49 := by
    have hnat : (293596447 : ℕ)^65*100000000000000^49 ≤ 19676830159119^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      293596447 1000000000 19676830159119 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3294706871/5000000000 : ℝ)^65 ≤ (28751778159309/50000000000000 : ℝ)^49 := by
    have hnat : (3294706871 : ℕ)^65*50000000000000^49 ≤ 28751778159309^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3294706871 5000000000 28751778159309 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(656588337/2000000000 : ℝ), (-293596447/1000000000 : ℝ), (-3294706871/5000000000 : ℝ)] ![(570490337773/2500000000000 : ℝ), (19676830159119/100000000000000 : ℝ), (28751778159309/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(656588337/2000000000 : ℝ)|^65 ≤ (570490337773/2500000000000 : ℝ)^49
        have hw : |(656588337/2000000000 : ℝ)|=(656588337/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-293596447/1000000000 : ℝ)|^65 ≤ (19676830159119/100000000000000 : ℝ)^49
        have hw : |(-293596447/1000000000 : ℝ)|=(293596447/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3294706871/5000000000 : ℝ)|^65 ≤ (28751778159309/50000000000000 : ℝ)^49
        have hw : |(-3294706871/5000000000 : ℝ)|=(3294706871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301048_s1_s1_9 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1238071877/2500000000 : ℝ)*x 0 + (340745677/500000000 : ℝ)*x 1 + (18503797/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1238071877/2500000000 : ℝ)^65 ≤ (1230270580931/3125000000000 : ℝ)^49 := by
    have hnat : (1238071877 : ℕ)^65*3125000000000^49 ≤ 1230270580931^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1238071877 2500000000 1230270580931 3125000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (340745677/500000000 : ℝ)^65 ≤ (15032114158679/25000000000000 : ℝ)^49 := by
    have hnat : (340745677 : ℕ)^65*25000000000000^49 ≤ 15032114158679^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340745677 500000000 15032114158679 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (18503797/1000000000 : ℝ)^65 ≤ (502884768123/100000000000000 : ℝ)^49 := by
    have hnat : (18503797 : ℕ)^65*100000000000000^49 ≤ 502884768123^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18503797 1000000000 502884768123 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1238071877/2500000000 : ℝ), (340745677/500000000 : ℝ), (18503797/1000000000 : ℝ)] ![(1230270580931/3125000000000 : ℝ), (15032114158679/25000000000000 : ℝ), (502884768123/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1238071877/2500000000 : ℝ)|^65 ≤ (1230270580931/3125000000000 : ℝ)^49
        have hw : |(1238071877/2500000000 : ℝ)|=(1238071877/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(340745677/500000000 : ℝ)|^65 ≤ (15032114158679/25000000000000 : ℝ)^49
        have hw : |(340745677/500000000 : ℝ)|=(340745677/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(18503797/1000000000 : ℝ)|^65 ≤ (502884768123/100000000000000 : ℝ)^49
        have hw : |(18503797/1000000000 : ℝ)|=(18503797/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301048_s1_s1_12 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4926728561/10000000000 : ℝ)*x 0 + (6779741509/10000000000 : ℝ)*x 1 + (-176373717/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4926728561/10000000000 : ℝ)^65 ≤ (1563974290913/4000000000000 : ℝ)^49 := by
    have hnat : (4926728561 : ℕ)^65*4000000000000^49 ≤ 1563974290913^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4926728561 10000000000 1563974290913 4000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6779741509/10000000000 : ℝ)^65 ≤ (59717147925037/100000000000000 : ℝ)^49 := by
    have hnat : (6779741509 : ℕ)^65*100000000000000^49 ≤ 59717147925037^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6779741509 10000000000 59717147925037 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (176373717/5000000000 : ℝ)^65 ≤ (591747393341/50000000000000 : ℝ)^49 := by
    have hnat : (176373717 : ℕ)^65*50000000000000^49 ≤ 591747393341^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      176373717 5000000000 591747393341 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4926728561/10000000000 : ℝ), (6779741509/10000000000 : ℝ), (-176373717/5000000000 : ℝ)] ![(1563974290913/4000000000000 : ℝ), (59717147925037/100000000000000 : ℝ), (591747393341/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4926728561/10000000000 : ℝ)|^65 ≤ (1563974290913/4000000000000 : ℝ)^49
        have hw : |(4926728561/10000000000 : ℝ)|=(4926728561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6779741509/10000000000 : ℝ)|^65 ≤ (59717147925037/100000000000000 : ℝ)^49
        have hw : |(6779741509/10000000000 : ℝ)|=(6779741509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-176373717/5000000000 : ℝ)|^65 ≤ (591747393341/50000000000000 : ℝ)^49
        have hw : |(-176373717/5000000000 : ℝ)|=(176373717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301048_s1_s1_13 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1897022603/10000000000 : ℝ)*x 0 + (1056811267/5000000000 : ℝ)*x 1 + (-2037862041/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1897022603/10000000000 : ℝ)^65 ≤ (11024047574339/100000000000000 : ℝ)^49 := by
    have hnat : (1897022603 : ℕ)^65*100000000000000^49 ≤ 11024047574339^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1897022603 10000000000 11024047574339 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1056811267/5000000000 : ℝ)^65 ≤ (3181033426561/25000000000000 : ℝ)^49 := by
    have hnat : (1056811267 : ℕ)^65*25000000000000^49 ≤ 3181033426561^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056811267 5000000000 3181033426561 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2037862041/2500000000 : ℝ)^65 ≤ (38125909354003/50000000000000 : ℝ)^49 := by
    have hnat : (2037862041 : ℕ)^65*50000000000000^49 ≤ 38125909354003^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2037862041 2500000000 38125909354003 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1897022603/10000000000 : ℝ), (1056811267/5000000000 : ℝ), (-2037862041/2500000000 : ℝ)] ![(11024047574339/100000000000000 : ℝ), (3181033426561/25000000000000 : ℝ), (38125909354003/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1897022603/10000000000 : ℝ)|^65 ≤ (11024047574339/100000000000000 : ℝ)^49
        have hw : |(-1897022603/10000000000 : ℝ)|=(1897022603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1056811267/5000000000 : ℝ)|^65 ≤ (3181033426561/25000000000000 : ℝ)^49
        have hw : |(1056811267/5000000000 : ℝ)|=(1056811267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2037862041/2500000000 : ℝ)|^65 ≤ (38125909354003/50000000000000 : ℝ)^49
        have hw : |(-2037862041/2500000000 : ℝ)|=(2037862041/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301048_s1_s1_14 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (367701309/1250000000 : ℝ)*x 0 + (-655496057/2000000000 : ℝ)*x 1 + (-6589425237/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (367701309/1250000000 : ℝ)^65 ≤ (19727041164763/100000000000000 : ℝ)^49 := by
    have hnat : (367701309 : ℕ)^65*100000000000000^49 ≤ 19727041164763^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      367701309 1250000000 19727041164763 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655496057/2000000000 : ℝ)^65 ≤ (22769269436239/100000000000000 : ℝ)^49 := by
    have hnat : (655496057 : ℕ)^65*100000000000000^49 ≤ 22769269436239^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655496057 2000000000 22769269436239 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6589425237/10000000000 : ℝ)^65 ≤ (7187961173353/12500000000000 : ℝ)^49 := by
    have hnat : (6589425237 : ℕ)^65*12500000000000^49 ≤ 7187961173353^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6589425237 10000000000 7187961173353 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(367701309/1250000000 : ℝ), (-655496057/2000000000 : ℝ), (-6589425237/10000000000 : ℝ)] ![(19727041164763/100000000000000 : ℝ), (22769269436239/100000000000000 : ℝ), (7187961173353/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(367701309/1250000000 : ℝ)|^65 ≤ (19727041164763/100000000000000 : ℝ)^49
        have hw : |(367701309/1250000000 : ℝ)|=(367701309/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-655496057/2000000000 : ℝ)|^65 ≤ (22769269436239/100000000000000 : ℝ)^49
        have hw : |(-655496057/2000000000 : ℝ)|=(655496057/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6589425237/10000000000 : ℝ)|^65 ≤ (7187961173353/12500000000000 : ℝ)^49
        have hw : |(-6589425237/10000000000 : ℝ)|=(6589425237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301048_s1_s1_15 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1702189119/2500000000 : ℝ)*x 0 + (4959122509/10000000000 : ℝ)*x 1 + (185026373/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1702189119/2500000000 : ℝ)^65 ≤ (1201128090929/2000000000000 : ℝ)^49 := by
    have hnat : (1702189119 : ℕ)^65*2000000000000^49 ≤ 1201128090929^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1702189119 2500000000 1201128090929 2000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4959122509/10000000000 : ℝ)^65 ≤ (39440752477601/100000000000000 : ℝ)^49 := by
    have hnat : (4959122509 : ℕ)^65*100000000000000^49 ≤ 39440752477601^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4959122509 10000000000 39440752477601 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (185026373/10000000000 : ℝ)^65 ≤ (125710739869/25000000000000 : ℝ)^49 := by
    have hnat : (185026373 : ℕ)^65*25000000000000^49 ≤ 125710739869^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      185026373 10000000000 125710739869 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1702189119/2500000000 : ℝ), (4959122509/10000000000 : ℝ), (185026373/10000000000 : ℝ)] ![(1201128090929/2000000000000 : ℝ), (39440752477601/100000000000000 : ℝ), (125710739869/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1702189119/2500000000 : ℝ)|^65 ≤ (1201128090929/2000000000000 : ℝ)^49
        have hw : |(1702189119/2500000000 : ℝ)|=(1702189119/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4959122509/10000000000 : ℝ)|^65 ≤ (39440752477601/100000000000000 : ℝ)^49
        have hw : |(4959122509/10000000000 : ℝ)|=(4959122509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(185026373/10000000000 : ℝ)|^65 ≤ (125710739869/25000000000000 : ℝ)^49
        have hw : |(185026373/10000000000 : ℝ)|=(185026373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301048_s1_s1_18 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6773619449/10000000000 : ℝ)*x 0 + (2466765319/5000000000 : ℝ)*x 1 + (-352724073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6773619449/10000000000 : ℝ)^65 ≤ (59645626405059/100000000000000 : ℝ)^49 := by
    have hnat : (6773619449 : ℕ)^65*100000000000000^49 ≤ 59645626405059^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6773619449 10000000000 59645626405059 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2466765319/5000000000 : ℝ)^65 ≤ (3917098277127/10000000000000 : ℝ)^49 := by
    have hnat : (2466765319 : ℕ)^65*10000000000000^49 ≤ 3917098277127^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2466765319 5000000000 3917098277127 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (352724073/10000000000 : ℝ)^65 ≤ (295847704263/25000000000000 : ℝ)^49 := by
    have hnat : (352724073 : ℕ)^65*25000000000000^49 ≤ 295847704263^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      352724073 10000000000 295847704263 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6773619449/10000000000 : ℝ), (2466765319/5000000000 : ℝ), (-352724073/10000000000 : ℝ)] ![(59645626405059/100000000000000 : ℝ), (3917098277127/10000000000000 : ℝ), (295847704263/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6773619449/10000000000 : ℝ)|^65 ≤ (59645626405059/100000000000000 : ℝ)^49
        have hw : |(6773619449/10000000000 : ℝ)|=(6773619449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2466765319/5000000000 : ℝ)|^65 ≤ (3917098277127/10000000000000 : ℝ)^49
        have hw : |(2466765319/5000000000 : ℝ)|=(2466765319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-352724073/10000000000 : ℝ)|^65 ≤ (295847704263/25000000000000 : ℝ)^49
        have hw : |(-352724073/10000000000 : ℝ)|=(352724073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301048_s1_s1_19 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-633673101/2000000000 : ℝ)*x 0 + (832276267/5000000000 : ℝ)*x 1 + (-3778385071/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (633673101/2000000000 : ℝ)^65 ≤ (21769212237697/100000000000000 : ℝ)^49 := by
    have hnat : (633673101 : ℕ)^65*100000000000000^49 ≤ 21769212237697^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      633673101 2000000000 21769212237697 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (832276267/5000000000 : ℝ)^65 ≤ (4634440475973/50000000000000 : ℝ)^49 := by
    have hnat : (832276267 : ℕ)^65*50000000000000^49 ≤ 4634440475973^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      832276267 5000000000 4634440475973 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3778385071/5000000000 : ℝ)^65 ≤ (68961906788579/100000000000000 : ℝ)^49 := by
    have hnat : (3778385071 : ℕ)^65*100000000000000^49 ≤ 68961906788579^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3778385071 5000000000 68961906788579 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-633673101/2000000000 : ℝ), (832276267/5000000000 : ℝ), (-3778385071/5000000000 : ℝ)] ![(21769212237697/100000000000000 : ℝ), (4634440475973/50000000000000 : ℝ), (68961906788579/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-633673101/2000000000 : ℝ)|^65 ≤ (21769212237697/100000000000000 : ℝ)^49
        have hw : |(-633673101/2000000000 : ℝ)|=(633673101/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(832276267/5000000000 : ℝ)|^65 ≤ (4634440475973/50000000000000 : ℝ)^49
        have hw : |(832276267/5000000000 : ℝ)|=(832276267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3778385071/5000000000 : ℝ)|^65 ≤ (68961906788579/100000000000000 : ℝ)^49
        have hw : |(-3778385071/5000000000 : ℝ)|=(3778385071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301048_s1_s1_20 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (396270739/1250000000 : ℝ)*x 0 + (-968981587/2000000000 : ℝ)*x 1 + (-5009587569/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (396270739/1250000000 : ℝ)^65 ≤ (10892811631047/50000000000000 : ℝ)^49 := by
    have hnat : (396270739 : ℕ)^65*50000000000000^49 ≤ 10892811631047^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      396270739 1250000000 10892811631047 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (968981587/2000000000 : ℝ)^65 ≤ (1912016449093/5000000000000 : ℝ)^49 := by
    have hnat : (968981587 : ℕ)^65*5000000000000^49 ≤ 1912016449093^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      968981587 2000000000 1912016449093 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5009587569/10000000000 : ℝ)^65 ≤ (19987023875421/50000000000000 : ℝ)^49 := by
    have hnat : (5009587569 : ℕ)^65*50000000000000^49 ≤ 19987023875421^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5009587569 10000000000 19987023875421 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(396270739/1250000000 : ℝ), (-968981587/2000000000 : ℝ), (-5009587569/10000000000 : ℝ)] ![(10892811631047/50000000000000 : ℝ), (1912016449093/5000000000000 : ℝ), (19987023875421/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(396270739/1250000000 : ℝ)|^65 ≤ (10892811631047/50000000000000 : ℝ)^49
        have hw : |(396270739/1250000000 : ℝ)|=(396270739/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-968981587/2000000000 : ℝ)|^65 ≤ (1912016449093/5000000000000 : ℝ)^49
        have hw : |(-968981587/2000000000 : ℝ)|=(968981587/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5009587569/10000000000 : ℝ)|^65 ≤ (19987023875421/50000000000000 : ℝ)^49
        have hw : |(-5009587569/10000000000 : ℝ)|=(5009587569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301048_s1_s1_21 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5803963997/10000000000 : ℝ)*x 0 + (5690812143/10000000000 : ℝ)*x 1 + (223626031/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5803963997/10000000000 : ℝ)^65 ≤ (24296493428651/50000000000000 : ℝ)^49 := by
    have hnat : (5803963997 : ℕ)^65*50000000000000^49 ≤ 24296493428651^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5803963997 10000000000 24296493428651 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5690812143/10000000000 : ℝ)^65 ≤ (23670157716047/50000000000000 : ℝ)^49 := by
    have hnat : (5690812143 : ℕ)^65*50000000000000^49 ≤ 23670157716047^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5690812143 10000000000 23670157716047 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (223626031/2500000000 : ℝ)^65 ≤ (4066697690577/100000000000000 : ℝ)^49 := by
    have hnat : (223626031 : ℕ)^65*100000000000000^49 ≤ 4066697690577^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223626031 2500000000 4066697690577 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5803963997/10000000000 : ℝ), (5690812143/10000000000 : ℝ), (223626031/2500000000 : ℝ)] ![(24296493428651/50000000000000 : ℝ), (23670157716047/50000000000000 : ℝ), (4066697690577/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5803963997/10000000000 : ℝ)|^65 ≤ (24296493428651/50000000000000 : ℝ)^49
        have hw : |(5803963997/10000000000 : ℝ)|=(5803963997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5690812143/10000000000 : ℝ)|^65 ≤ (23670157716047/50000000000000 : ℝ)^49
        have hw : |(5690812143/10000000000 : ℝ)|=(5690812143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(223626031/2500000000 : ℝ)|^65 ≤ (4066697690577/100000000000000 : ℝ)^49
        have hw : |(223626031/2500000000 : ℝ)|=(223626031/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301048_s1_s1_25 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (767340107/2500000000 : ℝ)*x 0 + (29250023/50000000 : ℝ)*x 1 + (-4037258593/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (767340107/2500000000 : ℝ)^65 ≤ (10435741848801/50000000000000 : ℝ)^49 := by
    have hnat : (767340107 : ℕ)^65*50000000000000^49 ≤ 10435741848801^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      767340107 2500000000 10435741848801 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (29250023/50000000 : ℝ)^65 ≤ (49104984860493/100000000000000 : ℝ)^49 := by
    have hnat : (29250023 : ℕ)^65*100000000000000^49 ≤ 49104984860493^49*50000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      29250023 50000000 49104984860493 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4037258593/10000000000 : ℝ)^65 ≤ (30023531414797/100000000000000 : ℝ)^49 := by
    have hnat : (4037258593 : ℕ)^65*100000000000000^49 ≤ 30023531414797^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4037258593 10000000000 30023531414797 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(767340107/2500000000 : ℝ), (29250023/50000000 : ℝ), (-4037258593/10000000000 : ℝ)] ![(10435741848801/50000000000000 : ℝ), (49104984860493/100000000000000 : ℝ), (30023531414797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(767340107/2500000000 : ℝ)|^65 ≤ (10435741848801/50000000000000 : ℝ)^49
        have hw : |(767340107/2500000000 : ℝ)|=(767340107/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(29250023/50000000 : ℝ)|^65 ≤ (49104984860493/100000000000000 : ℝ)^49
        have hw : |(29250023/50000000 : ℝ)|=(29250023/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4037258593/10000000000 : ℝ)|^65 ≤ (30023531414797/100000000000000 : ℝ)^49
        have hw : |(-4037258593/10000000000 : ℝ)|=(4037258593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c301048_s1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, false]])
    (hprev0 : (0 : ℝ) ≤ ((87523/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(87523/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(21797/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(21797/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-14937/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-14937/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((13321/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(13321/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(66551/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(66551/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-3427/25000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-3427/25000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4759/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4759/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4759/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4759/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4759/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4759/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base12 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).1]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s1_pow0 : (87523/100000 : ℝ) ^ (129/32 : ℝ) ≤ (58435948857677416153/100000000000000000000 : ℝ) := by
    have hpowers : (87523/100000 : ℝ)^129 ≤ (58435948857677416153/100000000000000000000 : ℝ)^32 := by
      have hnat : (87523 : ℕ)^129*100000000000000000000^32 ≤ 58435948857677416153^32*100000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        87523 100000 58435948857677416153 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (87523/100000 : ℝ)) (X := (58435948857677416153/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner0a : (158435948857677416153/100000000000000000000 : ℝ) ≤ (2241847746821439/2000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (158435948857677416153/100000000000000000000 : ℝ)^32 ≤ (2241847746821439/2000000000000000 : ℝ)^129 := by
      have hnat : (158435948857677416153 : ℕ)^32*2000000000000000^129 ≤ 2241847746821439^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        158435948857677416153 100000000000000000000 2241847746821439 2000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2241847746821439/2000000000000000 : ℝ)) (X := (158435948857677416153/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner0b : (108435948857677416153/50000000000000000000 : ℝ) ≤ (6058557967590323/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (108435948857677416153/50000000000000000000 : ℝ)^32 ≤ (6058557967590323/5000000000000000 : ℝ)^129 := by
      have hnat : (108435948857677416153 : ℕ)^32*5000000000000000^129 ≤ 6058557967590323^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        108435948857677416153 50000000000000000000 6058557967590323 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6058557967590323/5000000000000000 : ℝ)) (X := (108435948857677416153/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(241847746821439/1750460000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(907877201073451/8752300000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (87523/100000 : ℝ)) (alpha := (241847746821439/1750460000000000 : ℝ)) (beta := (907877201073451/8752300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (87523/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(241847746821439/1750460000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(907877201073451/8752300000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (21797/25000 : ℝ) ^ (129/32 : ℝ) ≤ (7192438340772194411/12500000000000000000 : ℝ) := by
    have hpowers : (21797/25000 : ℝ)^129 ≤ (7192438340772194411/12500000000000000000 : ℝ)^32 := by
      have hnat : (21797 : ℕ)^129*12500000000000000000^32 ≤ 7192438340772194411^32*25000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21797 25000 7192438340772194411 12500000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (21797/25000 : ℝ)) (X := (7192438340772194411/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner1a : (19692438340772194411/12500000000000000000 : ℝ) ≤ (2238694479086731/2000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (19692438340772194411/12500000000000000000 : ℝ)^32 ≤ (2238694479086731/2000000000000000 : ℝ)^129 := by
      have hnat : (19692438340772194411 : ℕ)^32*2000000000000000^129 ≤ 2238694479086731^129*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19692438340772194411 12500000000000000000 2238694479086731 2000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2238694479086731/2000000000000000 : ℝ)) (X := (19692438340772194411/12500000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner1b : (13442438340772194411/6250000000000000000 : ℝ) ≤ (12092189349426317/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (13442438340772194411/6250000000000000000 : ℝ)^32 ≤ (12092189349426317/10000000000000000 : ℝ)^129 := by
      have hnat : (13442438340772194411 : ℕ)^32*10000000000000000^129 ≤ 12092189349426317^129*6250000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13442438340772194411 6250000000000000000 12092189349426317 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12092189349426317/10000000000000000 : ℝ)) (X := (13442438340772194411/6250000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(238694479086731/1743760000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(449358476996331/4359400000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (21797/25000 : ℝ)) (alpha := (238694479086731/1743760000000000 : ℝ)) (beta := (449358476996331/4359400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (21797/25000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(238694479086731/1743760000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(449358476996331/4359400000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (14937/50000 : ℝ) ^ (129/32 : ℝ) ≤ (383483276186081249/50000000000000000000 : ℝ) := by
    have hpowers : (14937/50000 : ℝ)^129 ≤ (383483276186081249/50000000000000000000 : ℝ)^32 := by
      have hnat : (14937 : ℕ)^129*50000000000000000000^32 ≤ 383483276186081249^32*50000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14937 50000 383483276186081249 50000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14937/50000 : ℝ)) (X := (383483276186081249/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner2a : (50383483276186081249/50000000000000000000 : ℝ) ≤ (2504742727532609/2500000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (50383483276186081249/50000000000000000000 : ℝ)^32 ≤ (2504742727532609/2500000000000000 : ℝ)^129 := by
      have hnat : (50383483276186081249 : ℕ)^32*2500000000000000^129 ≤ 2504742727532609^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50383483276186081249 50000000000000000000 2504742727532609 2500000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2504742727532609/2500000000000000 : ℝ)) (X := (50383483276186081249/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner2b : (25383483276186081249/25000000000000000000 : ℝ) ≤ (10037833554284813/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (25383483276186081249/25000000000000000000 : ℝ)^32 ≤ (10037833554284813/10000000000000000 : ℝ)^129 := by
      have hnat : (25383483276186081249 : ℕ)^32*10000000000000000^129 ≤ 10037833554284813^129*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25383483276186081249 25000000000000000000 10037833554284813 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10037833554284813/10000000000000000 : ℝ)) (X := (25383483276186081249/25000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(4742727532609/746850000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(6287548051459/995800000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (14937/50000 : ℝ)) (alpha := (4742727532609/746850000000000 : ℝ)) (beta := (6287548051459/995800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (14937/50000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(4742727532609/746850000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(6287548051459/995800000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-2673218913/10000000000 : ℝ)*X 0 0+(1334631169/5000000000 : ℝ)*X 0 1+(-362539827/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301048_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((5696258361/10000000000 : ℝ)*X 2 0+(712832341/1250000000 : ℝ)*X 2 1+(532721789/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301048_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-2117149713/10000000000 : ℝ)*X 0 0+(378677231/2000000000 : ℝ)*X 0 1+(-8151435981/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301048_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((656588337/2000000000 : ℝ)*X 1 0+(-293596447/1000000000 : ℝ)*X 1 1+(-3294706871/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301048_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((1238071877/2500000000 : ℝ)*X 2 0+(340745677/500000000 : ℝ)*X 2 1+(18503797/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301048_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_12 : ((4926728561/10000000000 : ℝ)*X 0 0+(6779741509/10000000000 : ℝ)*X 0 1+(-176373717/5000000000 : ℝ)*X 0 2+(4926728561/10000000000 : ℝ)*X 1 0+(6779741509/10000000000 : ℝ)*X 1 1+(-176373717/5000000000 : ℝ)*X 1 2+(4926728561/10000000000 : ℝ)*X 2 0+(6779741509/10000000000 : ℝ)*X 2 1+(-176373717/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301048_s1_s1_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((-1897022603/10000000000 : ℝ)*X 0 0+(1056811267/5000000000 : ℝ)*X 0 1+(-2037862041/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301048_s1_s1_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((367701309/1250000000 : ℝ)*X 1 0+(-655496057/2000000000 : ℝ)*X 1 1+(-6589425237/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301048_s1_s1_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((1702189119/2500000000 : ℝ)*X 2 0+(4959122509/10000000000 : ℝ)*X 2 1+(185026373/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301048_s1_s1_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_18 : ((6773619449/10000000000 : ℝ)*X 0 0+(2466765319/5000000000 : ℝ)*X 0 1+(-352724073/10000000000 : ℝ)*X 0 2+(6773619449/10000000000 : ℝ)*X 1 0+(2466765319/5000000000 : ℝ)*X 1 1+(-352724073/10000000000 : ℝ)*X 1 2+(6773619449/10000000000 : ℝ)*X 2 0+(2466765319/5000000000 : ℝ)*X 2 1+(-352724073/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301048_s1_s1_18 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_19 : ((-633673101/2000000000 : ℝ)*X 0 0+(832276267/5000000000 : ℝ)*X 0 1+(-3778385071/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301048_s1_s1_19 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((396270739/1250000000 : ℝ)*X 1 0+(-968981587/2000000000 : ℝ)*X 1 1+(-5009587569/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301048_s1_s1_20 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((5803963997/10000000000 : ℝ)*X 2 0+(5690812143/10000000000 : ℝ)*X 2 1+(223626031/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301048_s1_s1_21 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_25 : ((767340107/2500000000 : ℝ)*X 0 0+(29250023/50000000 : ℝ)*X 0 1+(-4037258593/10000000000 : ℝ)*X 0 2+(767340107/2500000000 : ℝ)*X 1 0+(29250023/50000000 : ℝ)*X 1 1+(-4037258593/10000000000 : ℝ)*X 1 2+(767340107/2500000000 : ℝ)*X 2 0+(29250023/50000000 : ℝ)*X 2 1+(-4037258593/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301048_s1_s1_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((13321/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(13321/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (5539188834431332384825286441229/379945265581960000000000000000000000 : ℝ) := by norm_num
    linear_combination (4216717/1000000000000 : ℝ)*(base12) + (1770367/100000000000 : ℝ)*(base23) + (407364743591/250000000000 : ℝ)*(base59) + (349668253643/1000000000000 : ℝ)*(base60) + (4495555398363/1000000000000 : ℝ)*(major_s1_0) + (4495555398363/1000000000000 : ℝ)*(major_s1_1) + (4495555398363/1000000000000 : ℝ)*(major_s1_2) + (10258411/250000000000 : ℝ)*(sp_s1_2) + (1487930623873/250000000000 : ℝ)*(sp_s1_7) + (5952007887837/1000000000000 : ℝ)*(sp_s1_8) + (1487987287631/250000000000 : ℝ)*(sp_s1_9) + (1519544682349/500000000000 : ℝ)*(sp_s1_12) + (70293907/250000000000 : ℝ)*(sp_s1_13) + (1736909/200000000000 : ℝ)*(sp_s1_25) + (3039098049243/1000000000000 : ℝ)*(f.failure) + (5952007887837/1000000000000 : ℝ)*(f.sum) + (14922339597271447711/43410905200000000000000000000000 : ℝ)*base63 + (565425768013863/995800000000000000000000000 : ℝ)*base65 + (2963788907095813/4359400000000000000000000000 : ℝ)*base66 + (94689942877263/124475000000000000000000000 : ℝ)*base69 + (14627654883616787059/87155403400000000000000000000000 : ℝ)*base71 + (5097440344394957/8752300000000000000000000000 : ℝ)*base72 + (349474366216089/1743760000000000000000000000 : ℝ)*base75 + (70845683065047/1750460000000000000000000000 : ℝ)*base76 + (71379845208152851397/381547766200000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + (19617/25000000000000000 : ℝ)*base86 + (19617/25000000000000000 : ℝ)*base88 + (19617/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(66551/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(66551/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (37231481179487616266097037/3352130900000000000000000000000 : ℝ) := by norm_num
    linear_combination (3851197/500000000000 : ℝ)*(base12) + (19826451/1000000000000 : ℝ)*(base21) + (7902087/1000000000000 : ℝ)*(base53) + (340268329261/200000000000 : ℝ)*(base59) + (657439751769/1000000000000 : ℝ)*(base60) + (112363693921/25000000000 : ℝ)*(major_s1_0) + (112363693921/25000000000 : ℝ)*(major_s1_1) + (4494539854753/1000000000000 : ℝ)*(major_s1_2) + (663289/250000000000 : ℝ)*(sp_s1_2) + (28476471/250000000000 : ℝ)*(sp_s1_8) + (119013186927/20000000000 : ℝ)*(sp_s1_13) + (297527657143/50000000000 : ℝ)*(sp_s1_14) + (743831558903/125000000000 : ℝ)*(sp_s1_15) + (3038416860577/1000000000000 : ℝ)*(sp_s1_18) + (3038416860577/1000000000000 : ℝ)*(f.failure) + (5950674950831/1000000000000 : ℝ)*(f.sum) + (453692484030902467/1252237650000000000000000000000 : ℝ)*base63 + (21968741426439/76600000000000000000000000 : ℝ)*base64 + (2278465872893/43594000000000000000000000 : ℝ)*base66 + (9362637436243/28725000000000000000000000 : ℝ)*base69 + (1569319728681123397/6704261800000000000000000000000 : ℝ)*base70 + (39047121577971/875230000000000000000000000 : ℝ)*base73 + (8506815017053/108985000000000000000000000 : ℝ)*base74 + (2858344361461/17504600000000000000000000 : ℝ)*base77 + (807869625165780833/19077388310000000000000000000000 : ℝ)*base79 + (1963/25000000000000000 : ℝ)*base86 + (1963/25000000000000000 : ℝ)*base88 + (1963/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-3427/25000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-3427/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (27502423792915983/5000000000000000000000 : ℝ) := by norm_num
    linear_combination (1177889306957/1000000000000 : ℝ)*(base5) + (918407/250000000000 : ℝ)*(base8) + (53783287929/200000000000 : ℝ)*(base39) + (833124831/20000000000 : ℝ)*(base50) + (21052932683/15625000000 : ℝ)*(base59) + (1742380978423/1000000000000 : ℝ)*(major_s1_0) + (1742380978423/1000000000000 : ℝ)*(major_s1_1) + (1742380978423/1000000000000 : ℝ)*(major_s1_2) + (16138323/1000000000000 : ℝ)*(sp_s1_0) + (5942311/200000000000 : ℝ)*(sp_s1_9) + (8043533/250000000000 : ℝ)*(sp_s1_15) + (2306851004439/1000000000000 : ℝ)*(sp_s1_19) + (230687081639/100000000000 : ℝ)*(sp_s1_20) + (174234911883/50000000000 : ℝ)*(sp_s1_21) + (1177889306957/1000000000000 : ℝ)*(f.failure) + (230687081639/100000000000 : ℝ)*(f.sum) + (4966510534708513313/130232715600000000000000000000000 : ℝ)*base63 + (470258000077157/995800000000000000000000000 : ℝ)*base64 + (409124933556507/4359400000000000000000000000 : ℝ)*base67 + (447822881126407/746850000000000000000000000 : ℝ)*base68 + (10284957041861556519/87155403400000000000000000000000 : ℝ)*base71 + (3269665045257073/8752300000000000000000000000 : ℝ)*base73 + (1827900930460579/1743760000000000000000000000 : ℝ)*base74 + (1050668856563631/1750460000000000000000000000 : ℝ)*base76 + (253305285936382099757/381547766200000000000000000000000 : ℝ)*base78 + (1817/25000000000000000 : ℝ)*base87 + (1817/25000000000000000 : ℝ)*base89 + (1817/25000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, false]])
    (hprev0 : (0 : ℝ) ≤ ((87523/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(87523/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(21797/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(21797/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-14937/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-14937/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((13321/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(13321/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(66551/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(66551/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-3427/25000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-3427/25000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c301048_s1 p hpa hpb X hX hprev0

#print axioms solution
