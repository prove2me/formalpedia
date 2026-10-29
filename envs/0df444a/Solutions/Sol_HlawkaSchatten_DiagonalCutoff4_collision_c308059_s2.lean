-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c308059_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:37:59.640241+00:00
-- url     : https://prove2.me/submissions/ad96f5eb-5da7-43ef-8b41-04470b345bac

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
theorem collision_support_c308059_s2_s2_1 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (395012821/1250000000 : ℝ)*x 0 + (-3157945521/10000000000 : ℝ)*x 1 + (198486419/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (395012821/1250000000 : ℝ)^69 ≤ (174364312911/781250000000 : ℝ)^53 := by
    have hnat : (395012821 : ℕ)^69*781250000000^53 ≤ 174364312911^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      395012821 1250000000 174364312911 781250000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3157945521/10000000000 : ℝ)^69 ≤ (5574700150677/25000000000000 : ℝ)^53 := by
    have hnat : (3157945521 : ℕ)^69*25000000000000^53 ≤ 5574700150677^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3157945521 10000000000 5574700150677 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (198486419/312500000 : ℝ)^69 ≤ (55382567329723/100000000000000 : ℝ)^53 := by
    have hnat : (198486419 : ℕ)^69*100000000000000^53 ≤ 55382567329723^53*312500000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      198486419 312500000 55382567329723 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(395012821/1250000000 : ℝ), (-3157945521/10000000000 : ℝ), (198486419/312500000 : ℝ)] ![(174364312911/781250000000 : ℝ), (5574700150677/25000000000000 : ℝ), (55382567329723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(395012821/1250000000 : ℝ)|^69 ≤ (174364312911/781250000000 : ℝ)^53
        have hw : |(395012821/1250000000 : ℝ)|=(395012821/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3157945521/10000000000 : ℝ)|^69 ≤ (5574700150677/25000000000000 : ℝ)^53
        have hw : |(-3157945521/10000000000 : ℝ)|=(3157945521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(198486419/312500000 : ℝ)|^69 ≤ (55382567329723/100000000000000 : ℝ)^53
        have hw : |(198486419/312500000 : ℝ)|=(198486419/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308059_s2_s2_6 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3781121749/10000000000 : ℝ)*x 0 + (1441295449/2500000000 : ℝ)*x 1 + (808167069/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3781121749/10000000000 : ℝ)^69 ≤ (1761935212829/6250000000000 : ℝ)^53 := by
    have hnat : (3781121749 : ℕ)^69*6250000000000^53 ≤ 1761935212829^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3781121749 10000000000 1761935212829 6250000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1441295449/2500000000 : ℝ)^69 ≤ (24410440510469/50000000000000 : ℝ)^53 := by
    have hnat : (1441295449 : ℕ)^69*50000000000000^53 ≤ 24410440510469^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1441295449 2500000000 24410440510469 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (808167069/2500000000 : ℝ)^69 ≤ (11494077779551/50000000000000 : ℝ)^53 := by
    have hnat : (808167069 : ℕ)^69*50000000000000^53 ≤ 11494077779551^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      808167069 2500000000 11494077779551 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3781121749/10000000000 : ℝ), (1441295449/2500000000 : ℝ), (808167069/2500000000 : ℝ)] ![(1761935212829/6250000000000 : ℝ), (24410440510469/50000000000000 : ℝ), (11494077779551/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3781121749/10000000000 : ℝ)|^69 ≤ (1761935212829/6250000000000 : ℝ)^53
        have hw : |(3781121749/10000000000 : ℝ)|=(3781121749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1441295449/2500000000 : ℝ)|^69 ≤ (24410440510469/50000000000000 : ℝ)^53
        have hw : |(1441295449/2500000000 : ℝ)|=(1441295449/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(808167069/2500000000 : ℝ)|^69 ≤ (11494077779551/50000000000000 : ℝ)^53
        have hw : |(808167069/2500000000 : ℝ)|=(808167069/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308059_s2_s2_7 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2257465923/10000000000 : ℝ)*x 0 + (113761817/625000000 : ℝ)*x 1 + (999222289/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2257465923/10000000000 : ℝ)^69 ≤ (14404161484803/100000000000000 : ℝ)^53 := by
    have hnat : (2257465923 : ℕ)^69*100000000000000^53 ≤ 14404161484803^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2257465923 10000000000 14404161484803 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (113761817/625000000 : ℝ)^69 ≤ (2720792711287/25000000000000 : ℝ)^53 := by
    have hnat : (113761817 : ℕ)^69*25000000000000^53 ≤ 2720792711287^53*625000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113761817 625000000 2720792711287 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (999222289/1250000000 : ℝ)^69 ≤ (7471266765237/10000000000000 : ℝ)^53 := by
    have hnat : (999222289 : ℕ)^69*10000000000000^53 ≤ 7471266765237^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      999222289 1250000000 7471266765237 10000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2257465923/10000000000 : ℝ), (113761817/625000000 : ℝ), (999222289/1250000000 : ℝ)] ![(14404161484803/100000000000000 : ℝ), (2720792711287/25000000000000 : ℝ), (7471266765237/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2257465923/10000000000 : ℝ)|^69 ≤ (14404161484803/100000000000000 : ℝ)^53
        have hw : |(-2257465923/10000000000 : ℝ)|=(2257465923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(113761817/625000000 : ℝ)|^69 ≤ (2720792711287/25000000000000 : ℝ)^53
        have hw : |(113761817/625000000 : ℝ)|=(113761817/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(999222289/1250000000 : ℝ)|^69 ≤ (7471266765237/10000000000000 : ℝ)^53
        have hw : |(999222289/1250000000 : ℝ)|=(999222289/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308059_s2_s2_8 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1178339581/5000000000 : ℝ)*x 0 + (-854234041/5000000000 : ℝ)*x 1 + (319856029/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1178339581/5000000000 : ℝ)^69 ≤ (15233730265277/100000000000000 : ℝ)^53 := by
    have hnat : (1178339581 : ℕ)^69*100000000000000^53 ≤ 15233730265277^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1178339581 5000000000 15233730265277 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (854234041/5000000000 : ℝ)^69 ≤ (2505422813341/25000000000000 : ℝ)^53 := by
    have hnat : (854234041 : ℕ)^69*25000000000000^53 ≤ 2505422813341^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      854234041 5000000000 2505422813341 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (319856029/400000000 : ℝ)^69 ≤ (7474457847183/10000000000000 : ℝ)^53 := by
    have hnat : (319856029 : ℕ)^69*10000000000000^53 ≤ 7474457847183^53*400000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      319856029 400000000 7474457847183 10000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1178339581/5000000000 : ℝ), (-854234041/5000000000 : ℝ), (319856029/400000000 : ℝ)] ![(15233730265277/100000000000000 : ℝ), (2505422813341/25000000000000 : ℝ), (7474457847183/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1178339581/5000000000 : ℝ)|^69 ≤ (15233730265277/100000000000000 : ℝ)^53
        have hw : |(1178339581/5000000000 : ℝ)|=(1178339581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-854234041/5000000000 : ℝ)|^69 ≤ (2505422813341/25000000000000 : ℝ)^53
        have hw : |(-854234041/5000000000 : ℝ)|=(854234041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(319856029/400000000 : ℝ)|^69 ≤ (7474457847183/10000000000000 : ℝ)^53
        have hw : |(319856029/400000000 : ℝ)|=(319856029/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308059_s2_s2_9 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4541131193/10000000000 : ℝ)*x 0 + (444770459/625000000 : ℝ)*x 1 + (-266419/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4541131193/10000000000 : ℝ)^69 ≤ (447276845367/1250000000000 : ℝ)^53 := by
    have hnat : (4541131193 : ℕ)^69*1250000000000^53 ≤ 447276845367^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4541131193 10000000000 447276845367 1250000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (444770459/625000000 : ℝ)^69 ≤ (32108789574413/50000000000000 : ℝ)^53 := by
    have hnat : (444770459 : ℕ)^69*50000000000000^53 ≤ 32108789574413^53*625000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      444770459 625000000 32108789574413 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (266419/5000000000 : ℝ)^69 ≤ (34152361/12500000000000 : ℝ)^53 := by
    have hnat : (266419 : ℕ)^69*12500000000000^53 ≤ 34152361^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266419 5000000000 34152361 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4541131193/10000000000 : ℝ), (444770459/625000000 : ℝ), (-266419/5000000000 : ℝ)] ![(447276845367/1250000000000 : ℝ), (32108789574413/50000000000000 : ℝ), (34152361/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4541131193/10000000000 : ℝ)|^69 ≤ (447276845367/1250000000000 : ℝ)^53
        have hw : |(4541131193/10000000000 : ℝ)|=(4541131193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(444770459/625000000 : ℝ)|^69 ≤ (32108789574413/50000000000000 : ℝ)^53
        have hw : |(444770459/625000000 : ℝ)|=(444770459/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-266419/5000000000 : ℝ)|^69 ≤ (34152361/12500000000000 : ℝ)^53
        have hw : |(-266419/5000000000 : ℝ)|=(266419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308059_s2_s2_13 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (61208611/250000000 : ℝ)*x 0 + (3930974619/5000000000 : ℝ)*x 1 + (1819496419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (61208611/250000000 : ℝ)^69 ≤ (16009626478259/100000000000000 : ℝ)^53 := by
    have hnat : (61208611 : ℕ)^69*100000000000000^53 ≤ 16009626478259^53*250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      61208611 250000000 16009626478259 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3930974619/5000000000 : ℝ)^69 ≤ (73112594086611/100000000000000 : ℝ)^53 := by
    have hnat : (3930974619 : ℕ)^69*100000000000000^53 ≤ 73112594086611^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3930974619 5000000000 73112594086611 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1819496419/10000000000 : ℝ)^69 ≤ (10877779427993/100000000000000 : ℝ)^53 := by
    have hnat : (1819496419 : ℕ)^69*100000000000000^53 ≤ 10877779427993^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1819496419 10000000000 10877779427993 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(61208611/250000000 : ℝ), (3930974619/5000000000 : ℝ), (1819496419/10000000000 : ℝ)] ![(16009626478259/100000000000000 : ℝ), (73112594086611/100000000000000 : ℝ), (10877779427993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(61208611/250000000 : ℝ)|^69 ≤ (16009626478259/100000000000000 : ℝ)^53
        have hw : |(61208611/250000000 : ℝ)|=(61208611/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3930974619/5000000000 : ℝ)|^69 ≤ (73112594086611/100000000000000 : ℝ)^53
        have hw : |(3930974619/5000000000 : ℝ)|=(3930974619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1819496419/10000000000 : ℝ)|^69 ≤ (10877779427993/100000000000000 : ℝ)^53
        have hw : |(1819496419/10000000000 : ℝ)|=(1819496419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308059_s2_s2_14 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-125960847/625000000 : ℝ)*x 0 + (2451114201/10000000000 : ℝ)*x 1 + (3865876387/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (125960847/625000000 : ℝ)^69 ≤ (12426524624531/100000000000000 : ℝ)^53 := by
    have hnat : (125960847 : ℕ)^69*100000000000000^53 ≤ 12426524624531^53*625000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125960847 625000000 12426524624531 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2451114201/10000000000 : ℝ)^69 ≤ (2004151179921/12500000000000 : ℝ)^53 := by
    have hnat : (2451114201 : ℕ)^69*12500000000000^53 ≤ 2004151179921^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2451114201 10000000000 2004151179921 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3865876387/5000000000 : ℝ)^69 ≤ (71540265929919/100000000000000 : ℝ)^53 := by
    have hnat : (3865876387 : ℕ)^69*100000000000000^53 ≤ 71540265929919^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3865876387 5000000000 71540265929919 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-125960847/625000000 : ℝ), (2451114201/10000000000 : ℝ), (3865876387/5000000000 : ℝ)] ![(12426524624531/100000000000000 : ℝ), (2004151179921/12500000000000 : ℝ), (71540265929919/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-125960847/625000000 : ℝ)|^69 ≤ (12426524624531/100000000000000 : ℝ)^53
        have hw : |(-125960847/625000000 : ℝ)|=(125960847/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2451114201/10000000000 : ℝ)|^69 ≤ (2004151179921/12500000000000 : ℝ)^53
        have hw : |(2451114201/10000000000 : ℝ)|=(2451114201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3865876387/5000000000 : ℝ)|^69 ≤ (71540265929919/100000000000000 : ℝ)^53
        have hw : |(3865876387/5000000000 : ℝ)|=(3865876387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308059_s2_s2_15 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1973753107/10000000000 : ℝ)*x 0 + (-2486559803/10000000000 : ℝ)*x 1 + (7734288249/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1973753107/10000000000 : ℝ)^69 ≤ (12093472976469/100000000000000 : ℝ)^53 := by
    have hnat : (1973753107 : ℕ)^69*100000000000000^53 ≤ 12093472976469^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1973753107 10000000000 12093472976469 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2486559803/10000000000 : ℝ)^69 ≤ (16335717029823/100000000000000 : ℝ)^53 := by
    have hnat : (2486559803 : ℕ)^69*100000000000000^53 ≤ 16335717029823^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2486559803 10000000000 16335717029823 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7734288249/10000000000 : ℝ)^69 ≤ (14314161996239/20000000000000 : ℝ)^53 := by
    have hnat : (7734288249 : ℕ)^69*20000000000000^53 ≤ 14314161996239^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7734288249 10000000000 14314161996239 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1973753107/10000000000 : ℝ), (-2486559803/10000000000 : ℝ), (7734288249/10000000000 : ℝ)] ![(12093472976469/100000000000000 : ℝ), (16335717029823/100000000000000 : ℝ), (14314161996239/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1973753107/10000000000 : ℝ)|^69 ≤ (12093472976469/100000000000000 : ℝ)^53
        have hw : |(1973753107/10000000000 : ℝ)|=(1973753107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2486559803/10000000000 : ℝ)|^69 ≤ (16335717029823/100000000000000 : ℝ)^53
        have hw : |(-2486559803/10000000000 : ℝ)|=(2486559803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7734288249/10000000000 : ℝ)|^69 ≤ (14314161996239/20000000000000 : ℝ)^53
        have hw : |(7734288249/10000000000 : ℝ)|=(7734288249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308059_s2_s2_16 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7812656783/10000000000 : ℝ)*x 0 + (741606899/2000000000 : ℝ)*x 1 + (5213/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7812656783/10000000000 : ℝ)^69 ≤ (72516377814519/100000000000000 : ℝ)^53 := by
    have hnat : (7812656783 : ℕ)^69*100000000000000^53 ≤ 72516377814519^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7812656783 10000000000 72516377814519 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (741606899/2000000000 : ℝ)^69 ≤ (27483621509887/100000000000000 : ℝ)^53 := by
    have hnat : (741606899 : ℕ)^69*100000000000000^53 ≤ 27483621509887^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      741606899 2000000000 27483621509887 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5213/10000000000 : ℝ)^69 ≤ (661241/100000000000000 : ℝ)^53 := by
    have hnat : (5213 : ℕ)^69*100000000000000^53 ≤ 661241^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5213 10000000000 661241 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7812656783/10000000000 : ℝ), (741606899/2000000000 : ℝ), (5213/10000000000 : ℝ)] ![(72516377814519/100000000000000 : ℝ), (27483621509887/100000000000000 : ℝ), (661241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7812656783/10000000000 : ℝ)|^69 ≤ (72516377814519/100000000000000 : ℝ)^53
        have hw : |(7812656783/10000000000 : ℝ)|=(7812656783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(741606899/2000000000 : ℝ)|^69 ≤ (27483621509887/100000000000000 : ℝ)^53
        have hw : |(741606899/2000000000 : ℝ)|=(741606899/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5213/10000000000 : ℝ)|^69 ≤ (661241/100000000000000 : ℝ)^53
        have hw : |(5213/10000000000 : ℝ)|=(5213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308059_s2_s2_20 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3254034631/5000000000 : ℝ)*x 0 + (508517761/1250000000 : ℝ)*x 1 + (1940129969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3254034631/5000000000 : ℝ)^69 ≤ (57165741232923/100000000000000 : ℝ)^53 := by
    have hnat : (3254034631 : ℕ)^69*100000000000000^53 ≤ 57165741232923^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3254034631 5000000000 57165741232923 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (508517761/1250000000 : ℝ)^69 ≤ (15504150052593/50000000000000 : ℝ)^53 := by
    have hnat : (508517761 : ℕ)^69*50000000000000^53 ≤ 15504150052593^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508517761 1250000000 15504150052593 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1940129969/10000000000 : ℝ)^69 ≤ (11825958648069/100000000000000 : ℝ)^53 := by
    have hnat : (1940129969 : ℕ)^69*100000000000000^53 ≤ 11825958648069^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1940129969 10000000000 11825958648069 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3254034631/5000000000 : ℝ), (508517761/1250000000 : ℝ), (1940129969/10000000000 : ℝ)] ![(57165741232923/100000000000000 : ℝ), (15504150052593/50000000000000 : ℝ), (11825958648069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3254034631/5000000000 : ℝ)|^69 ≤ (57165741232923/100000000000000 : ℝ)^53
        have hw : |(3254034631/5000000000 : ℝ)|=(3254034631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(508517761/1250000000 : ℝ)|^69 ≤ (15504150052593/50000000000000 : ℝ)^53
        have hw : |(508517761/1250000000 : ℝ)|=(508517761/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1940129969/10000000000 : ℝ)|^69 ≤ (11825958648069/100000000000000 : ℝ)^53
        have hw : |(1940129969/10000000000 : ℝ)|=(1940129969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308059_s2_s2_21 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-96193741/250000000 : ℝ)*x 0 + (398235763/1250000000 : ℝ)*x 1 + (2872777063/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (96193741/250000000 : ℝ)^69 ≤ (5767879982941/20000000000000 : ℝ)^53 := by
    have hnat : (96193741 : ℕ)^69*20000000000000^53 ≤ 5767879982941^53*250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      96193741 250000000 5767879982941 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (398235763/1250000000 : ℝ)^69 ≤ (902239858707/4000000000000 : ℝ)^53 := by
    have hnat : (398235763 : ℕ)^69*4000000000000^53 ≤ 902239858707^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      398235763 1250000000 902239858707 4000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2872777063/5000000000 : ℝ)^69 ≤ (24302301805361/50000000000000 : ℝ)^53 := by
    have hnat : (2872777063 : ℕ)^69*50000000000000^53 ≤ 24302301805361^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2872777063 5000000000 24302301805361 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-96193741/250000000 : ℝ), (398235763/1250000000 : ℝ), (2872777063/5000000000 : ℝ)] ![(5767879982941/20000000000000 : ℝ), (902239858707/4000000000000 : ℝ), (24302301805361/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-96193741/250000000 : ℝ)|^69 ≤ (5767879982941/20000000000000 : ℝ)^53
        have hw : |(-96193741/250000000 : ℝ)|=(96193741/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(398235763/1250000000 : ℝ)|^69 ≤ (902239858707/4000000000000 : ℝ)^53
        have hw : |(398235763/1250000000 : ℝ)|=(398235763/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2872777063/5000000000 : ℝ)|^69 ≤ (24302301805361/50000000000000 : ℝ)^53
        have hw : |(2872777063/5000000000 : ℝ)|=(2872777063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308059_s2_s2_22 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3071786089/10000000000 : ℝ)*x 0 + (-479231331/1250000000 : ℝ)*x 1 + (5852535039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3071786089/10000000000 : ℝ)^69 ≤ (10755016415139/50000000000000 : ℝ)^53 := by
    have hnat : (3071786089 : ℕ)^69*50000000000000^53 ≤ 10755016415139^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3071786089 10000000000 10755016415139 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (479231331/1250000000 : ℝ)^69 ≤ (28703850115389/100000000000000 : ℝ)^53 := by
    have hnat : (479231331 : ℕ)^69*100000000000000^53 ≤ 28703850115389^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      479231331 1250000000 28703850115389 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5852535039/10000000000 : ℝ)^69 ≤ (4978611703427/10000000000000 : ℝ)^53 := by
    have hnat : (5852535039 : ℕ)^69*10000000000000^53 ≤ 4978611703427^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5852535039 10000000000 4978611703427 10000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3071786089/10000000000 : ℝ), (-479231331/1250000000 : ℝ), (5852535039/10000000000 : ℝ)] ![(10755016415139/50000000000000 : ℝ), (28703850115389/100000000000000 : ℝ), (4978611703427/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3071786089/10000000000 : ℝ)|^69 ≤ (10755016415139/50000000000000 : ℝ)^53
        have hw : |(3071786089/10000000000 : ℝ)|=(3071786089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-479231331/1250000000 : ℝ)|^69 ≤ (28703850115389/100000000000000 : ℝ)^53
        have hw : |(-479231331/1250000000 : ℝ)|=(479231331/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5852535039/10000000000 : ℝ)|^69 ≤ (4978611703427/10000000000000 : ℝ)^53
        have hw : |(5852535039/10000000000 : ℝ)|=(5852535039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308059_s2_s2_23 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (49025821/62500000 : ℝ)*x 0 + (1834259687/5000000000 : ℝ)*x 1 + (137967/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (49025821/62500000 : ℝ)^69 ≤ (72896947549547/100000000000000 : ℝ)^53 := by
    have hnat : (49025821 : ℕ)^69*100000000000000^53 ≤ 72896947549547^53*62500000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49025821 62500000 72896947549547 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1834259687/5000000000 : ℝ)^69 ≤ (27102936442031/100000000000000 : ℝ)^53 := by
    have hnat : (1834259687 : ℕ)^69*100000000000000^53 ≤ 27102936442031^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1834259687 5000000000 27102936442031 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (137967/5000000000 : ℝ)^69 ≤ (23199281/20000000000000 : ℝ)^53 := by
    have hnat : (137967 : ℕ)^69*20000000000000^53 ≤ 23199281^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137967 5000000000 23199281 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(49025821/62500000 : ℝ), (1834259687/5000000000 : ℝ), (137967/5000000000 : ℝ)] ![(72896947549547/100000000000000 : ℝ), (27102936442031/100000000000000 : ℝ), (23199281/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(49025821/62500000 : ℝ)|^69 ≤ (72896947549547/100000000000000 : ℝ)^53
        have hw : |(49025821/62500000 : ℝ)|=(49025821/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1834259687/5000000000 : ℝ)|^69 ≤ (27102936442031/100000000000000 : ℝ)^53
        have hw : |(1834259687/5000000000 : ℝ)|=(1834259687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(137967/5000000000 : ℝ)|^69 ≤ (23199281/20000000000000 : ℝ)^53
        have hw : |(137967/5000000000 : ℝ)|=(137967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308059_s2_s2_27 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1821319813/10000000000 : ℝ)*x 0 + (4053951589/5000000000 : ℝ)*x 1 + (2086897561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1821319813/10000000000 : ℝ)^69 ≤ (2722993386893/25000000000000 : ℝ)^53 := by
    have hnat : (1821319813 : ℕ)^69*25000000000000^53 ≤ 2722993386893^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1821319813 10000000000 2722993386893 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4053951589/5000000000 : ℝ)^69 ≤ (1189129834351/1562500000000 : ℝ)^53 := by
    have hnat : (4053951589 : ℕ)^69*1562500000000^53 ≤ 1189129834351^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4053951589 5000000000 1189129834351 1562500000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2086897561/10000000000 : ℝ)^69 ≤ (3250929260723/25000000000000 : ℝ)^53 := by
    have hnat : (2086897561 : ℕ)^69*25000000000000^53 ≤ 3250929260723^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086897561 10000000000 3250929260723 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1821319813/10000000000 : ℝ), (4053951589/5000000000 : ℝ), (2086897561/10000000000 : ℝ)] ![(2722993386893/25000000000000 : ℝ), (1189129834351/1562500000000 : ℝ), (3250929260723/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1821319813/10000000000 : ℝ)|^69 ≤ (2722993386893/25000000000000 : ℝ)^53
        have hw : |(1821319813/10000000000 : ℝ)|=(1821319813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4053951589/5000000000 : ℝ)|^69 ≤ (1189129834351/1562500000000 : ℝ)^53
        have hw : |(4053951589/5000000000 : ℝ)|=(4053951589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2086897561/10000000000 : ℝ)|^69 ≤ (3250929260723/25000000000000 : ℝ)^53
        have hw : |(2086897561/10000000000 : ℝ)|=(2086897561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c308059_s2 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((85393/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(85393/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(21311/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(21311/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(69743/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(69743/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((14879/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(14879/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(36421/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(36421/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(23529/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(23529/50000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (3861/5000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (3861/5000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (3861/5000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (3861/5000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (3861/5000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (3861/5000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (11517/6250 : ℝ) := by
    linarith only [f.Tcap]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (85393/100000 : ℝ) ^ (17/4 : ℝ) ≤ (51114563110351811279/100000000000000000000 : ℝ) := by
    have hpowers : (85393/100000 : ℝ)^17 ≤ (51114563110351811279/100000000000000000000 : ℝ)^4 := by
      have hnat : (85393 : ℕ)^17*100000000000000000000^4 ≤ 51114563110351811279^4*100000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        85393 100000 51114563110351811279 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (85393/100000 : ℝ)) (X := (51114563110351811279/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s2_corner0a : (151114563110351811279/100000000000000000000 : ℝ) ≤ (11020206240975563/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (151114563110351811279/100000000000000000000 : ℝ)^4 ≤ (11020206240975563/10000000000000000 : ℝ)^17 := by
      have hnat : (151114563110351811279 : ℕ)^4*10000000000000000^17 ≤ 11020206240975563^17*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        151114563110351811279 100000000000000000000 11020206240975563 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11020206240975563/10000000000000000 : ℝ)) (X := (151114563110351811279/100000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s2_corner0b : (101114563110351811279/50000000000000000000 : ℝ) ≤ (2360441385306891/2000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (101114563110351811279/50000000000000000000 : ℝ)^4 ≤ (2360441385306891/2000000000000000 : ℝ)^17 := by
      have hnat : (101114563110351811279 : ℕ)^4*2000000000000000^17 ≤ 2360441385306891^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101114563110351811279 50000000000000000000 2360441385306891 2000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2360441385306891/2000000000000000 : ℝ)) (X := (101114563110351811279/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1020206240975563/8539300000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(195500171389723/2134825000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (85393/100000 : ℝ)) (alpha := (1020206240975563/8539300000000000 : ℝ)) (beta := (195500171389723/2134825000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (85393/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1020206240975563/8539300000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(195500171389723/2134825000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (21311/25000 : ℝ) ^ (17/4 : ℝ) ≤ (50736585531156804581/100000000000000000000 : ℝ) := by
    have hpowers : (21311/25000 : ℝ)^17 ≤ (50736585531156804581/100000000000000000000 : ℝ)^4 := by
      have hnat : (21311 : ℕ)^17*100000000000000000000^4 ≤ 50736585531156804581^4*25000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21311 25000 50736585531156804581 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (21311/25000 : ℝ)) (X := (50736585531156804581/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s2_corner1a : (150736585531156804581/100000000000000000000 : ℝ) ≤ (11013714274489241/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (150736585531156804581/100000000000000000000 : ℝ)^4 ≤ (11013714274489241/10000000000000000 : ℝ)^17 := by
      have hnat : (150736585531156804581 : ℕ)^4*10000000000000000^17 ≤ 11013714274489241^17*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        150736585531156804581 100000000000000000000 11013714274489241 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11013714274489241/10000000000000000 : ℝ)) (X := (150736585531156804581/100000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s2_corner1b : (100736585531156804581/50000000000000000000 : ℝ) ≤ (184247052457809/156250000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (100736585531156804581/50000000000000000000 : ℝ)^4 ≤ (184247052457809/156250000000000 : ℝ)^17 := by
      have hnat : (100736585531156804581 : ℕ)^4*156250000000000^17 ≤ 184247052457809^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100736585531156804581 50000000000000000000 184247052457809 156250000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (184247052457809/156250000000000 : ℝ)) (X := (100736585531156804581/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1013714274489241/8524400000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(155619416562107/1704880000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (21311/25000 : ℝ)) (alpha := (1013714274489241/8524400000000000 : ℝ)) (beta := (155619416562107/1704880000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (21311/25000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1013714274489241/8524400000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(155619416562107/1704880000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (69743/100000 : ℝ) ^ (17/4 : ℝ) ≤ (10810546746952005121/50000000000000000000 : ℝ) := by
    have hpowers : (69743/100000 : ℝ)^17 ≤ (10810546746952005121/50000000000000000000 : ℝ)^4 := by
      have hnat : (69743 : ℕ)^17*50000000000000000000^4 ≤ 10810546746952005121^4*100000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        69743 100000 10810546746952005121 50000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (69743/100000 : ℝ)) (X := (10810546746952005121/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s2_corner2a : (60810546746952005121/50000000000000000000 : ℝ) ≤ (10471335993689979/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (60810546746952005121/50000000000000000000 : ℝ)^4 ≤ (10471335993689979/10000000000000000 : ℝ)^17 := by
      have hnat : (60810546746952005121 : ℕ)^4*10000000000000000^17 ≤ 10471335993689979^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        60810546746952005121 50000000000000000000 10471335993689979 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10471335993689979/10000000000000000 : ℝ)) (X := (60810546746952005121/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s2_corner2b : (35810546746952005121/25000000000000000000 : ℝ) ≤ (10882347123351141/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (35810546746952005121/25000000000000000000 : ℝ)^4 ≤ (10882347123351141/10000000000000000 : ℝ)^17 := by
      have hnat : (35810546746952005121 : ℕ)^4*10000000000000000^17 ≤ 10882347123351141^17*25000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        35810546746952005121 25000000000000000000 10882347123351141 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10882347123351141/10000000000000000 : ℝ)) (X := (35810546746952005121/25000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(471335993689979/6974300000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(205505564830581/3487150000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (69743/100000 : ℝ)) (alpha := (471335993689979/6974300000000000 : ℝ)) (beta := (205505564830581/3487150000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (69743/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(471335993689979/6974300000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(205505564830581/3487150000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_1 : ((395012821/1250000000 : ℝ)*X 1 0+(-3157945521/10000000000 : ℝ)*X 1 1+(198486419/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308059_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((3781121749/10000000000 : ℝ)*X 0 0+(1441295449/2500000000 : ℝ)*X 0 1+(808167069/2500000000 : ℝ)*X 0 2+(3781121749/10000000000 : ℝ)*X 1 0+(1441295449/2500000000 : ℝ)*X 1 1+(808167069/2500000000 : ℝ)*X 1 2+(3781121749/10000000000 : ℝ)*X 2 0+(1441295449/2500000000 : ℝ)*X 2 1+(808167069/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308059_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-2257465923/10000000000 : ℝ)*X 0 0+(113761817/625000000 : ℝ)*X 0 1+(999222289/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308059_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((1178339581/5000000000 : ℝ)*X 1 0+(-854234041/5000000000 : ℝ)*X 1 1+(319856029/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308059_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((4541131193/10000000000 : ℝ)*X 2 0+(444770459/625000000 : ℝ)*X 2 1+(-266419/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308059_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((61208611/250000000 : ℝ)*X 0 0+(3930974619/5000000000 : ℝ)*X 0 1+(1819496419/10000000000 : ℝ)*X 0 2+(61208611/250000000 : ℝ)*X 1 0+(3930974619/5000000000 : ℝ)*X 1 1+(1819496419/10000000000 : ℝ)*X 1 2+(61208611/250000000 : ℝ)*X 2 0+(3930974619/5000000000 : ℝ)*X 2 1+(1819496419/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308059_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-125960847/625000000 : ℝ)*X 0 0+(2451114201/10000000000 : ℝ)*X 0 1+(3865876387/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308059_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((1973753107/10000000000 : ℝ)*X 1 0+(-2486559803/10000000000 : ℝ)*X 1 1+(7734288249/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308059_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((7812656783/10000000000 : ℝ)*X 2 0+(741606899/2000000000 : ℝ)*X 2 1+(5213/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308059_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((3254034631/5000000000 : ℝ)*X 0 0+(508517761/1250000000 : ℝ)*X 0 1+(1940129969/10000000000 : ℝ)*X 0 2+(3254034631/5000000000 : ℝ)*X 1 0+(508517761/1250000000 : ℝ)*X 1 1+(1940129969/10000000000 : ℝ)*X 1 2+(3254034631/5000000000 : ℝ)*X 2 0+(508517761/1250000000 : ℝ)*X 2 1+(1940129969/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308059_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-96193741/250000000 : ℝ)*X 0 0+(398235763/1250000000 : ℝ)*X 0 1+(2872777063/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308059_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((3071786089/10000000000 : ℝ)*X 1 0+(-479231331/1250000000 : ℝ)*X 1 1+(5852535039/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308059_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((49025821/62500000 : ℝ)*X 2 0+(1834259687/5000000000 : ℝ)*X 2 1+(137967/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308059_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((1821319813/10000000000 : ℝ)*X 0 0+(4053951589/5000000000 : ℝ)*X 0 1+(2086897561/10000000000 : ℝ)*X 0 2+(1821319813/10000000000 : ℝ)*X 1 0+(4053951589/5000000000 : ℝ)*X 1 1+(2086897561/10000000000 : ℝ)*X 1 2+(1821319813/10000000000 : ℝ)*X 2 0+(4053951589/5000000000 : ℝ)*X 2 1+(2086897561/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308059_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((14879/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(14879/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (17335063092450338200747923725343/906564459876350000000000000000000000 : ℝ) := by norm_num
    linear_combination (382847323203/500000000000 : ℝ)*(base7) + (5579689/500000000000 : ℝ)*(base19) + (32180983763/250000000000 : ℝ)*(base60) + (521321557827/250000000000 : ℝ)*(major_s2_0) + (521321557827/250000000000 : ℝ)*(major_s2_1) + (521321557827/250000000000 : ℝ)*(major_s2_2) + (1077383/1000000000000 : ℝ)*(sp_s2_6) + (1184790580101/500000000000 : ℝ)*(sp_s2_7) + (14809214359/6250000000 : ℝ)*(sp_s2_8) + (1184794296057/500000000000 : ℝ)*(sp_s2_9) + (2096288789563/1000000000000 : ℝ)*(sp_s2_13) + (928989/125000000000 : ℝ)*(sp_s2_14) + (1611489/15625000000 : ℝ)*(sp_s2_15) + (61996443/1000000000000 : ℝ)*(sp_s2_27) + (166332152123/125000000000 : ℝ)*(f.failure) + (1184794296057/500000000000 : ℝ)*(f.sum) + (15751105734891620831/148629307300000000000000000000000 : ℝ)*base62 + (121469567516873/217946875000000000000000000 : ℝ)*base65 + (216249252626609/426220000000000000000000000 : ℝ)*base67 + (13944983013833/435893750000000000000000000 : ℝ)*base69 + (1916946099884421377/4253974285000000000000000000000 : ℝ)*base71 + (43314543178223/76243750000000000000000000 : ℝ)*base73 + (1183103112343027/2131100000000000000000000000 : ℝ)*base75 + (306027018909773/304975000000000000000000000 : ℝ)*base77 + (7835713127911105243/25997288900000000000000000000000 : ℝ)*base79 + (2547/12500000000000000 : ℝ)*base86 + (2547/12500000000000000 : ℝ)*base88 + (2547/12500000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(36421/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(36421/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (103702399770493661345383737/6767686362500000000000000000000 : ℝ) := by norm_num
    linear_combination (738063725327/1000000000000 : ℝ)*(base7) + (1268397/1000000000000 : ℝ)*(base40) + (547319/250000000000 : ℝ)*(base59) + (211307841017/1000000000000 : ℝ)*(base60) + (1212454091981/500000000000 : ℝ)*(major_s2_0) + (1212454091981/500000000000 : ℝ)*(major_s2_1) + (1212454091981/500000000000 : ℝ)*(major_s2_2) + (41881209/500000000000 : ℝ)*(sp_s2_7) + (8010661/250000000000 : ℝ)*(sp_s2_8) + (89031355473/31250000000 : ℝ)*(sp_s2_14) + (284905509491/100000000000 : ℝ)*(sp_s2_15) + (2848368753941/1000000000000 : ℝ)*(sp_s2_16) + (91417583413/40000000000 : ℝ)*(sp_s2_20) + (718383613/1000000000000 : ℝ)*(sp_s2_23) + (773687929999/500000000000 : ℝ)*(f.failure) + (1424543568777/500000000000 : ℝ)*(f.sum) + (119030897673395659993/297258614600000000000000000000000 : ℝ)*base62 + (295758368784021/1743575000000000000000000000 : ℝ)*base65 + (150569061951347/852440000000000000000000000 : ℝ)*base67 + (1062474676203719/3487150000000000000000000000 : ℝ)*base68 + (534814787892173687/5414149090000000000000000000000 : ℝ)*base71 + (50065002449507/388150000000000000000000000 : ℝ)*base73 + (611314709779161/4262200000000000000000000000 : ℝ)*base75 + (19047845874059/194075000000000000000000000 : ℝ)*base77 + (1826285741869828287/33087458600000000000000000000000 : ℝ)*base78 + (26711/50000000000000000 : ℝ)*base86 + (26711/50000000000000000 : ℝ)*base88 + (26711/50000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(23529/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(23529/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (217841075264337227311454494064133/25383804876537800000000000000000000000 : ℝ) := by norm_num
    linear_combination (219361183317/500000000000 : ℝ)*(base7) + (5686693/1000000000000 : ℝ)*(base11) + (6578084819/200000000000 : ℝ)*(base50) + (705617/1000000000000 : ℝ)*(base60) + (2506281118823/1000000000000 : ℝ)*(major_s2_0) + (2506281118823/1000000000000 : ℝ)*(major_s2_1) + (2506281118823/1000000000000 : ℝ)*(major_s2_2) + (3185129/125000000000 : ℝ)*(sp_s2_1) + (85357819/500000000000 : ℝ)*(sp_s2_13) + (12125431/10000000000 : ℝ)*(sp_s2_16) + (3143771526457/1000000000000 : ℝ)*(sp_s2_21) + (3143751732117/1000000000000 : ℝ)*(sp_s2_22) + (3142564670049/1000000000000 : ℝ)*(sp_s2_23) + (2037852988377/1000000000000 : ℝ)*(sp_s2_27) + (1599301337381/1000000000000 : ℝ)*(f.failure) + (3143777213149/1000000000000 : ℝ)*(f.sum) + (57865245131985268819/594517229200000000000000000000000 : ℝ)*base62 + (2530270084844607/3487150000000000000000000000 : ℝ)*base64 + (747106386605627/1704880000000000000000000000 : ℝ)*base66 + (1474007693973017/6974300000000000000000000000 : ℝ)*base68 + (80148670457999390991/119111279980000000000000000000000 : ℝ)*base70 + (210597136849097/1067412500000000000000000000 : ℝ)*base73 + (2505051532840503/8524400000000000000000000000 : ℝ)*base75 + (1167911437697331/8539300000000000000000000000 : ℝ)*base76 + (80124605322272385031/727924089200000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (13891/100000000000000000 : ℝ)*base87 + (13891/100000000000000000 : ℝ)*base89 + (13891/100000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((85393/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(85393/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(21311/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(21311/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(69743/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(69743/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((14879/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(14879/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(36421/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(36421/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(23529/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(23529/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c308059_s2 p hpa hpb X hX hprev1

#print axioms solution
