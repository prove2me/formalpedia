-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c310083_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:49:10.837265+00:00
-- url     : https://prove2.me/submissions/c1f0f1a6-2665-4533-8735-8cd27af5daa8

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
theorem collision_support_c310083_s1_s1_0 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-405923209/2000000000 : ℝ)*x 0 + (4971549119/10000000000 : ℝ)*x 1 + (5541247589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (405923209/2000000000 : ℝ)^71 ≤ (255249139593/2000000000000 : ℝ)^55 := by
    have hnat : (405923209 : ℕ)^71*2000000000000^55 ≤ 255249139593^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      405923209 2000000000 255249139593 2000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4971549119/10000000000 : ℝ)^71 ≤ (4056938470579/10000000000000 : ℝ)^55 := by
    have hnat : (4971549119 : ℕ)^71*10000000000000^55 ≤ 4056938470579^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4971549119 10000000000 4056938470579 10000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5541247589/10000000000 : ℝ)^71 ≤ (46668158301707/100000000000000 : ℝ)^55 := by
    have hnat : (5541247589 : ℕ)^71*100000000000000^55 ≤ 46668158301707^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5541247589 10000000000 46668158301707 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-405923209/2000000000 : ℝ), (4971549119/10000000000 : ℝ), (5541247589/10000000000 : ℝ)] ![(255249139593/2000000000000 : ℝ), (4056938470579/10000000000000 : ℝ), (46668158301707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-405923209/2000000000 : ℝ)|^71 ≤ (255249139593/2000000000000 : ℝ)^55
        have hw : |(-405923209/2000000000 : ℝ)|=(405923209/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4971549119/10000000000 : ℝ)|^71 ≤ (4056938470579/10000000000000 : ℝ)^55
        have hw : |(4971549119/10000000000 : ℝ)|=(4971549119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5541247589/10000000000 : ℝ)|^71 ≤ (46668158301707/100000000000000 : ℝ)^55
        have hw : |(5541247589/10000000000 : ℝ)|=(5541247589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310083_s1_s1_2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1772305597/5000000000 : ℝ)*x 0 + (6750118127/10000000000 : ℝ)*x 1 + (-2129335583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1772305597/5000000000 : ℝ)^71 ≤ (26214043570083/100000000000000 : ℝ)^55 := by
    have hnat : (1772305597 : ℕ)^71*100000000000000^55 ≤ 26214043570083^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1772305597 5000000000 26214043570083 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6750118127/10000000000 : ℝ)^71 ≤ (60208318689361/100000000000000 : ℝ)^55 := by
    have hnat : (6750118127 : ℕ)^71*100000000000000^55 ≤ 60208318689361^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6750118127 10000000000 60208318689361 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2129335583/10000000000 : ℝ)^71 ≤ (13577637725361/100000000000000 : ℝ)^55 := by
    have hnat : (2129335583 : ℕ)^71*100000000000000^55 ≤ 13577637725361^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2129335583 10000000000 13577637725361 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1772305597/5000000000 : ℝ), (6750118127/10000000000 : ℝ), (-2129335583/10000000000 : ℝ)] ![(26214043570083/100000000000000 : ℝ), (60208318689361/100000000000000 : ℝ), (13577637725361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1772305597/5000000000 : ℝ)|^71 ≤ (26214043570083/100000000000000 : ℝ)^55
        have hw : |(1772305597/5000000000 : ℝ)|=(1772305597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6750118127/10000000000 : ℝ)|^71 ≤ (60208318689361/100000000000000 : ℝ)^55
        have hw : |(6750118127/10000000000 : ℝ)|=(6750118127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2129335583/10000000000 : ℝ)|^71 ≤ (13577637725361/100000000000000 : ℝ)^55
        have hw : |(-2129335583/10000000000 : ℝ)|=(2129335583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310083_s1_s1_6 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1537065549/5000000000 : ℝ)*x 0 + (4642651053/10000000000 : ℝ)*x 1 + (5017054879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1537065549/5000000000 : ℝ)^71 ≤ (4362406828341/20000000000000 : ℝ)^55 := by
    have hnat : (1537065549 : ℕ)^71*20000000000000^55 ≤ 4362406828341^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1537065549 5000000000 4362406828341 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4642651053/10000000000 : ℝ)^71 ≤ (1856928832729/5000000000000 : ℝ)^55 := by
    have hnat : (4642651053 : ℕ)^71*5000000000000^55 ≤ 1856928832729^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4642651053 10000000000 1856928832729 5000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5017054879/10000000000 : ℝ)^71 ≤ (20524694597727/50000000000000 : ℝ)^55 := by
    have hnat : (5017054879 : ℕ)^71*50000000000000^55 ≤ 20524694597727^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5017054879 10000000000 20524694597727 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1537065549/5000000000 : ℝ), (4642651053/10000000000 : ℝ), (5017054879/10000000000 : ℝ)] ![(4362406828341/20000000000000 : ℝ), (1856928832729/5000000000000 : ℝ), (20524694597727/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1537065549/5000000000 : ℝ)|^71 ≤ (4362406828341/20000000000000 : ℝ)^55
        have hw : |(1537065549/5000000000 : ℝ)|=(1537065549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4642651053/10000000000 : ℝ)|^71 ≤ (1856928832729/5000000000000 : ℝ)^55
        have hw : |(4642651053/10000000000 : ℝ)|=(4642651053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5017054879/10000000000 : ℝ)|^71 ≤ (20524694597727/50000000000000 : ℝ)^55
        have hw : |(5017054879/10000000000 : ℝ)|=(5017054879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310083_s1_s1_7 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2614011843/10000000000 : ℝ)*x 0 + (2036037659/5000000000 : ℝ)*x 1 + (118627083/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2614011843/10000000000 : ℝ)^71 ≤ (8846409205797/50000000000000 : ℝ)^55 := by
    have hnat : (2614011843 : ℕ)^71*50000000000000^55 ≤ 8846409205797^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614011843 10000000000 8846409205797 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2036037659/5000000000 : ℝ)^71 ≤ (3135506258317/10000000000000 : ℝ)^55 := by
    have hnat : (2036037659 : ℕ)^71*10000000000000^55 ≤ 3135506258317^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2036037659 5000000000 3135506258317 10000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (118627083/200000000 : ℝ)^71 ≤ (50952118990483/100000000000000 : ℝ)^55 := by
    have hnat : (118627083 : ℕ)^71*100000000000000^55 ≤ 50952118990483^55*200000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      118627083 200000000 50952118990483 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2614011843/10000000000 : ℝ), (2036037659/5000000000 : ℝ), (118627083/200000000 : ℝ)] ![(8846409205797/50000000000000 : ℝ), (3135506258317/10000000000000 : ℝ), (50952118990483/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2614011843/10000000000 : ℝ)|^71 ≤ (8846409205797/50000000000000 : ℝ)^55
        have hw : |(-2614011843/10000000000 : ℝ)|=(2614011843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2036037659/5000000000 : ℝ)|^71 ≤ (3135506258317/10000000000000 : ℝ)^55
        have hw : |(2036037659/5000000000 : ℝ)|=(2036037659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(118627083/200000000 : ℝ)|^71 ≤ (50952118990483/100000000000000 : ℝ)^55
        have hw : |(118627083/200000000 : ℝ)|=(118627083/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310083_s1_s1_8 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1191457573/2000000000 : ℝ)*x 0 + (2477109/2000000000 : ℝ)*x 1 + (1146220139/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1191457573/2000000000 : ℝ)^71 ≤ (25619944196197/50000000000000 : ℝ)^55 := by
    have hnat : (1191457573 : ℕ)^71*50000000000000^55 ≤ 25619944196197^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1191457573 2000000000 25619944196197 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2477109/2000000000 : ℝ)^71 ≤ (1766923319/10000000000000 : ℝ)^55 := by
    have hnat : (2477109 : ℕ)^71*10000000000000^55 ≤ 1766923319^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2477109 2000000000 1766923319 10000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1146220139/2000000000 : ℝ)^71 ≤ (24371221178901/50000000000000 : ℝ)^55 := by
    have hnat : (1146220139 : ℕ)^71*50000000000000^55 ≤ 24371221178901^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1146220139 2000000000 24371221178901 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1191457573/2000000000 : ℝ), (2477109/2000000000 : ℝ), (1146220139/2000000000 : ℝ)] ![(25619944196197/50000000000000 : ℝ), (1766923319/10000000000000 : ℝ), (24371221178901/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1191457573/2000000000 : ℝ)|^71 ≤ (25619944196197/50000000000000 : ℝ)^55
        have hw : |(1191457573/2000000000 : ℝ)|=(1191457573/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2477109/2000000000 : ℝ)|^71 ≤ (1766923319/10000000000000 : ℝ)^55
        have hw : |(2477109/2000000000 : ℝ)|=(2477109/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1146220139/2000000000 : ℝ)|^71 ≤ (24371221178901/50000000000000 : ℝ)^55
        have hw : |(1146220139/2000000000 : ℝ)|=(1146220139/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310083_s1_s1_9 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (963728447/5000000000 : ℝ)*x 0 + (517214879/625000000 : ℝ)*x 1 + (-41156057/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (963728447/5000000000 : ℝ)^71 ≤ (5969668568669/50000000000000 : ℝ)^55 := by
    have hnat : (963728447 : ℕ)^71*50000000000000^55 ≤ 5969668568669^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      963728447 5000000000 5969668568669 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (517214879/625000000 : ℝ)^71 ≤ (78320534927899/100000000000000 : ℝ)^55 := by
    have hnat : (517214879 : ℕ)^71*100000000000000^55 ≤ 78320534927899^55*625000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517214879 625000000 78320534927899 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41156057/250000000 : ℝ)^71 ≤ (2435031981221/25000000000000 : ℝ)^55 := by
    have hnat : (41156057 : ℕ)^71*25000000000000^55 ≤ 2435031981221^55*250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41156057 250000000 2435031981221 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(963728447/5000000000 : ℝ), (517214879/625000000 : ℝ), (-41156057/250000000 : ℝ)] ![(5969668568669/50000000000000 : ℝ), (78320534927899/100000000000000 : ℝ), (2435031981221/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(963728447/5000000000 : ℝ)|^71 ≤ (5969668568669/50000000000000 : ℝ)^55
        have hw : |(963728447/5000000000 : ℝ)|=(963728447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(517214879/625000000 : ℝ)|^71 ≤ (78320534927899/100000000000000 : ℝ)^55
        have hw : |(517214879/625000000 : ℝ)|=(517214879/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-41156057/250000000 : ℝ)|^71 ≤ (2435031981221/25000000000000 : ℝ)^55
        have hw : |(-41156057/250000000 : ℝ)|=(41156057/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310083_s1_s1_13 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1461382463/5000000000 : ℝ)*x 0 + (2782142807/5000000000 : ℝ)*x 1 + (840262513/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1461382463/5000000000 : ℝ)^71 ≤ (20435650773127/100000000000000 : ℝ)^55 := by
    have hnat : (1461382463 : ℕ)^71*100000000000000^55 ≤ 20435650773127^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1461382463 5000000000 20435650773127 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2782142807/5000000000 : ℝ)^71 ≤ (23459389318769/50000000000000 : ℝ)^55 := by
    have hnat : (2782142807 : ℕ)^71*50000000000000^55 ≤ 23459389318769^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2782142807 5000000000 23459389318769 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (840262513/2000000000 : ℝ)^71 ≤ (16322785289991/50000000000000 : ℝ)^55 := by
    have hnat : (840262513 : ℕ)^71*50000000000000^55 ≤ 16322785289991^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      840262513 2000000000 16322785289991 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1461382463/5000000000 : ℝ), (2782142807/5000000000 : ℝ), (840262513/2000000000 : ℝ)] ![(20435650773127/100000000000000 : ℝ), (23459389318769/50000000000000 : ℝ), (16322785289991/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1461382463/5000000000 : ℝ)|^71 ≤ (20435650773127/100000000000000 : ℝ)^55
        have hw : |(1461382463/5000000000 : ℝ)|=(1461382463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2782142807/5000000000 : ℝ)|^71 ≤ (23459389318769/50000000000000 : ℝ)^55
        have hw : |(2782142807/5000000000 : ℝ)|=(2782142807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(840262513/2000000000 : ℝ)|^71 ≤ (16322785289991/50000000000000 : ℝ)^55
        have hw : |(840262513/2000000000 : ℝ)|=(840262513/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310083_s1_s1_14 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-683998151/10000000000 : ℝ)*x 0 + (1569287451/5000000000 : ℝ)*x 1 + (3978890707/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (683998151/10000000000 : ℝ)^71 ≤ (125378135491/4000000000000 : ℝ)^55 := by
    have hnat : (683998151 : ℕ)^71*4000000000000^55 ≤ 125378135491^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683998151 10000000000 125378135491 4000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1569287451/5000000000 : ℝ)^71 ≤ (22404095019187/100000000000000 : ℝ)^55 := by
    have hnat : (1569287451 : ℕ)^71*100000000000000^55 ≤ 22404095019187^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1569287451 5000000000 22404095019187 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3978890707/5000000000 : ℝ)^71 ≤ (74461451576143/100000000000000 : ℝ)^55 := by
    have hnat : (3978890707 : ℕ)^71*100000000000000^55 ≤ 74461451576143^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3978890707 5000000000 74461451576143 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-683998151/10000000000 : ℝ), (1569287451/5000000000 : ℝ), (3978890707/5000000000 : ℝ)] ![(125378135491/4000000000000 : ℝ), (22404095019187/100000000000000 : ℝ), (74461451576143/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-683998151/10000000000 : ℝ)|^71 ≤ (125378135491/4000000000000 : ℝ)^55
        have hw : |(-683998151/10000000000 : ℝ)|=(683998151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1569287451/5000000000 : ℝ)|^71 ≤ (22404095019187/100000000000000 : ℝ)^55
        have hw : |(1569287451/5000000000 : ℝ)|=(1569287451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3978890707/5000000000 : ℝ)|^71 ≤ (74461451576143/100000000000000 : ℝ)^55
        have hw : |(3978890707/5000000000 : ℝ)|=(3978890707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310083_s1_s1_15 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4248964707/5000000000 : ℝ)*x 0 + (963/625000000 : ℝ)*x 1 + (1378423191/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4248964707/5000000000 : ℝ)^71 ≤ (81049373699647/100000000000000 : ℝ)^55 := by
    have hnat : (4248964707 : ℕ)^71*100000000000000^55 ≤ 81049373699647^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4248964707 5000000000 81049373699647 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (963/625000000 : ℝ)^71 ≤ (62797/2000000000000 : ℝ)^55 := by
    have hnat : (963 : ℕ)^71*2000000000000^55 ≤ 62797^55*625000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      963 625000000 62797 2000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1378423191/5000000000 : ℝ)^71 ≤ (9475311575851/50000000000000 : ℝ)^55 := by
    have hnat : (1378423191 : ℕ)^71*50000000000000^55 ≤ 9475311575851^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1378423191 5000000000 9475311575851 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4248964707/5000000000 : ℝ), (963/625000000 : ℝ), (1378423191/5000000000 : ℝ)] ![(81049373699647/100000000000000 : ℝ), (62797/2000000000000 : ℝ), (9475311575851/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4248964707/5000000000 : ℝ)|^71 ≤ (81049373699647/100000000000000 : ℝ)^55
        have hw : |(4248964707/5000000000 : ℝ)|=(4248964707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(963/625000000 : ℝ)|^71 ≤ (62797/2000000000000 : ℝ)^55
        have hw : |(963/625000000 : ℝ)|=(963/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1378423191/5000000000 : ℝ)|^71 ≤ (9475311575851/50000000000000 : ℝ)^55
        have hw : |(1378423191/5000000000 : ℝ)|=(1378423191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310083_s1_s1_16 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1037562727/2500000000 : ℝ)*x 0 + (3477686883/5000000000 : ℝ)*x 1 + (-1024994683/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1037562727/2500000000 : ℝ)^71 ≤ (32134290137421/100000000000000 : ℝ)^55 := by
    have hnat : (1037562727 : ℕ)^71*100000000000000^55 ≤ 32134290137421^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037562727 2500000000 32134290137421 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3477686883/5000000000 : ℝ)^71 ≤ (62582090328151/100000000000000 : ℝ)^55 := by
    have hnat : (3477686883 : ℕ)^71*100000000000000^55 ≤ 62582090328151^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3477686883 5000000000 62582090328151 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1024994683/10000000000 : ℝ)^71 ≤ (5283619522843/100000000000000 : ℝ)^55 := by
    have hnat : (1024994683 : ℕ)^71*100000000000000^55 ≤ 5283619522843^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1024994683 10000000000 5283619522843 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1037562727/2500000000 : ℝ), (3477686883/5000000000 : ℝ), (-1024994683/10000000000 : ℝ)] ![(32134290137421/100000000000000 : ℝ), (62582090328151/100000000000000 : ℝ), (5283619522843/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1037562727/2500000000 : ℝ)|^71 ≤ (32134290137421/100000000000000 : ℝ)^55
        have hw : |(1037562727/2500000000 : ℝ)|=(1037562727/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3477686883/5000000000 : ℝ)|^71 ≤ (62582090328151/100000000000000 : ℝ)^55
        have hw : |(3477686883/5000000000 : ℝ)|=(3477686883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1024994683/10000000000 : ℝ)|^71 ≤ (5283619522843/100000000000000 : ℝ)^55
        have hw : |(-1024994683/10000000000 : ℝ)|=(1024994683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310083_s1_s1_20 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1443498663/5000000000 : ℝ)*x 0 + (3550336191/10000000000 : ℝ)*x 1 + (6170358237/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1443498663/5000000000 : ℝ)^71 ≤ (5028348128991/25000000000000 : ℝ)^55 := by
    have hnat : (1443498663 : ℕ)^71*25000000000000^55 ≤ 5028348128991^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1443498663 5000000000 5028348128991 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3550336191/10000000000 : ℝ)^71 ≤ (26268712215339/100000000000000 : ℝ)^55 := by
    have hnat : (3550336191 : ℕ)^71*100000000000000^55 ≤ 26268712215339^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3550336191 10000000000 26268712215339 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6170358237/10000000000 : ℝ)^71 ≤ (53617895244801/100000000000000 : ℝ)^55 := by
    have hnat : (6170358237 : ℕ)^71*100000000000000^55 ≤ 53617895244801^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6170358237 10000000000 53617895244801 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1443498663/5000000000 : ℝ), (3550336191/10000000000 : ℝ), (6170358237/10000000000 : ℝ)] ![(5028348128991/25000000000000 : ℝ), (26268712215339/100000000000000 : ℝ), (53617895244801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1443498663/5000000000 : ℝ)|^71 ≤ (5028348128991/25000000000000 : ℝ)^55
        have hw : |(1443498663/5000000000 : ℝ)|=(1443498663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3550336191/10000000000 : ℝ)|^71 ≤ (26268712215339/100000000000000 : ℝ)^55
        have hw : |(3550336191/10000000000 : ℝ)|=(3550336191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6170358237/10000000000 : ℝ)|^71 ≤ (53617895244801/100000000000000 : ℝ)^55
        have hw : |(6170358237/10000000000 : ℝ)|=(6170358237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310083_s1_s1_21 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3264501/20000000 : ℝ)*x 0 + (3048867691/5000000000 : ℝ)*x 1 + (2341798929/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3264501/20000000 : ℝ)^71 ≤ (1926678861739/20000000000000 : ℝ)^55 := by
    have hnat : (3264501 : ℕ)^71*20000000000000^55 ≤ 1926678861739^55*20000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3264501 20000000 1926678861739 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3048867691/5000000000 : ℝ)^71 ≤ (52804648840269/100000000000000 : ℝ)^55 := by
    have hnat : (3048867691 : ℕ)^71*100000000000000^55 ≤ 52804648840269^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3048867691 5000000000 52804648840269 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2341798929/5000000000 : ℝ)^71 ≤ (37561956832283/100000000000000 : ℝ)^55 := by
    have hnat : (2341798929 : ℕ)^71*100000000000000^55 ≤ 37561956832283^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2341798929 5000000000 37561956832283 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3264501/20000000 : ℝ), (3048867691/5000000000 : ℝ), (2341798929/5000000000 : ℝ)] ![(1926678861739/20000000000000 : ℝ), (52804648840269/100000000000000 : ℝ), (37561956832283/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3264501/20000000 : ℝ)|^71 ≤ (1926678861739/20000000000000 : ℝ)^55
        have hw : |(-3264501/20000000 : ℝ)|=(3264501/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3048867691/5000000000 : ℝ)|^71 ≤ (52804648840269/100000000000000 : ℝ)^55
        have hw : |(3048867691/5000000000 : ℝ)|=(3048867691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2341798929/5000000000 : ℝ)|^71 ≤ (37561956832283/100000000000000 : ℝ)^55
        have hw : |(2341798929/5000000000 : ℝ)|=(2341798929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310083_s1_s1_22 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (31883253/39062500 : ℝ)*x 0 + (536273/2500000000 : ℝ)*x 1 + (3209457577/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (31883253/39062500 : ℝ)^71 ≤ (38469378221219/50000000000000 : ℝ)^55 := by
    have hnat : (31883253 : ℕ)^71*50000000000000^55 ≤ 38469378221219^55*39062500^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31883253 39062500 38469378221219 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (536273/2500000000 : ℝ)^71 ≤ (918756017/50000000000000 : ℝ)^55 := by
    have hnat : (536273 : ℕ)^71*50000000000000^55 ≤ 918756017^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536273 2500000000 918756017 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3209457577/10000000000 : ℝ)^71 ≤ (1152970301529/5000000000000 : ℝ)^55 := by
    have hnat : (3209457577 : ℕ)^71*5000000000000^55 ≤ 1152970301529^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3209457577 10000000000 1152970301529 5000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(31883253/39062500 : ℝ), (536273/2500000000 : ℝ), (3209457577/10000000000 : ℝ)] ![(38469378221219/50000000000000 : ℝ), (918756017/50000000000000 : ℝ), (1152970301529/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(31883253/39062500 : ℝ)|^71 ≤ (38469378221219/50000000000000 : ℝ)^55
        have hw : |(31883253/39062500 : ℝ)|=(31883253/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(536273/2500000000 : ℝ)|^71 ≤ (918756017/50000000000000 : ℝ)^55
        have hw : |(536273/2500000000 : ℝ)|=(536273/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3209457577/10000000000 : ℝ)|^71 ≤ (1152970301529/5000000000000 : ℝ)^55
        have hw : |(3209457577/10000000000 : ℝ)|=(3209457577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310083_s1_s1_23 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (522090787/2000000000 : ℝ)*x 0 + (7359510517/10000000000 : ℝ)*x 1 + (-230289667/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (522090787/2000000000 : ℝ)^71 ≤ (1103858593401/6250000000000 : ℝ)^55 := by
    have hnat : (522090787 : ℕ)^71*6250000000000^55 ≤ 1103858593401^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522090787 2000000000 1103858593401 6250000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7359510517/10000000000 : ℝ)^71 ≤ (420720903977/625000000000 : ℝ)^55 := by
    have hnat : (7359510517 : ℕ)^71*625000000000^55 ≤ 420720903977^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7359510517 10000000000 420720903977 625000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (230289667/1000000000 : ℝ)^71 ≤ (3755729461797/25000000000000 : ℝ)^55 := by
    have hnat : (230289667 : ℕ)^71*25000000000000^55 ≤ 3755729461797^55*1000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      230289667 1000000000 3755729461797 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(522090787/2000000000 : ℝ), (7359510517/10000000000 : ℝ), (-230289667/1000000000 : ℝ)] ![(1103858593401/6250000000000 : ℝ), (420720903977/625000000000 : ℝ), (3755729461797/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(522090787/2000000000 : ℝ)|^71 ≤ (1103858593401/6250000000000 : ℝ)^55
        have hw : |(522090787/2000000000 : ℝ)|=(522090787/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7359510517/10000000000 : ℝ)|^71 ≤ (420720903977/625000000000 : ℝ)^55
        have hw : |(7359510517/10000000000 : ℝ)|=(7359510517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-230289667/1000000000 : ℝ)|^71 ≤ (3755729461797/25000000000000 : ℝ)^55
        have hw : |(-230289667/1000000000 : ℝ)|=(230289667/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310083_s1_s1_27 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (270590859/500000000 : ℝ)*x 0 + (3884303041/10000000000 : ℝ)*x 1 + (3441404047/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (270590859/500000000 : ℝ)^71 ≤ (9053160111543/20000000000000 : ℝ)^55 := by
    have hnat : (270590859 : ℕ)^71*20000000000000^55 ≤ 9053160111543^55*500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270590859 500000000 9053160111543 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3884303041/10000000000 : ℝ)^71 ≤ (29501259212409/100000000000000 : ℝ)^55 := by
    have hnat : (3884303041 : ℕ)^71*100000000000000^55 ≤ 29501259212409^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3884303041 10000000000 29501259212409 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3441404047/10000000000 : ℝ)^71 ≤ (6308235051667/25000000000000 : ℝ)^55 := by
    have hnat : (3441404047 : ℕ)^71*25000000000000^55 ≤ 6308235051667^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3441404047 10000000000 6308235051667 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(270590859/500000000 : ℝ), (3884303041/10000000000 : ℝ), (3441404047/10000000000 : ℝ)] ![(9053160111543/20000000000000 : ℝ), (29501259212409/100000000000000 : ℝ), (6308235051667/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(270590859/500000000 : ℝ)|^71 ≤ (9053160111543/20000000000000 : ℝ)^55
        have hw : |(270590859/500000000 : ℝ)|=(270590859/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3884303041/10000000000 : ℝ)|^71 ≤ (29501259212409/100000000000000 : ℝ)^55
        have hw : |(3884303041/10000000000 : ℝ)|=(3884303041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3441404047/10000000000 : ℝ)|^71 ≤ (6308235051667/25000000000000 : ℝ)^55
        have hw : |(3441404047/10000000000 : ℝ)|=(3441404047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c310083_s1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((19323/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(19323/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((80169/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(80169/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(42709/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(42709/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((54817/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(54817/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((25299/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(25299/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(61427/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(61427/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (2431/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (2431/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (18111/10000 : ℝ) := by
    linarith only [f.Tcap]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  have s1_pow0 : (19323/25000 : ℝ) ^ (35/8 : ℝ) ≤ (32403254756758782403/100000000000000000000 : ℝ) := by
    have hpowers : (19323/25000 : ℝ)^35 ≤ (32403254756758782403/100000000000000000000 : ℝ)^8 := by
      have hnat : (19323 : ℕ)^35*100000000000000000000^8 ≤ 32403254756758782403^8*25000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19323 25000 32403254756758782403 100000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19323/25000 : ℝ)) (X := (32403254756758782403/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (132403254756758782403/100000000000000000000 : ℝ) ≤ (106625861003123/100000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (132403254756758782403/100000000000000000000 : ℝ)^8 ≤ (106625861003123/100000000000000 : ℝ)^35 := by
      have hnat : (132403254756758782403 : ℕ)^8*100000000000000^35 ≤ 106625861003123^35*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        132403254756758782403 100000000000000000000 106625861003123 100000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (106625861003123/100000000000000 : ℝ)) (X := (132403254756758782403/100000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (82403254756758782403/50000000000000000000 : ℝ) ≤ (5604851933599177/5000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (82403254756758782403/50000000000000000000 : ℝ)^8 ≤ (5604851933599177/5000000000000000 : ℝ)^35 := by
      have hnat : (82403254756758782403 : ℕ)^8*5000000000000000^35 ≤ 5604851933599177^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        82403254756758782403 50000000000000000000 5604851933599177 5000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5604851933599177/5000000000000000 : ℝ)) (X := (82403254756758782403/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(6625861003123/77292000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(91186294481009/1288200000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (19323/25000 : ℝ)) (alpha := (6625861003123/77292000000000 : ℝ)) (beta := (91186294481009/1288200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (19323/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(6625861003123/77292000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(91186294481009/1288200000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (80169/100000 : ℝ) ^ (35/8 : ℝ) ≤ (38021416312976489773/100000000000000000000 : ℝ) := by
    have hpowers : (80169/100000 : ℝ)^35 ≤ (38021416312976489773/100000000000000000000 : ℝ)^8 := by
      have hnat : (80169 : ℕ)^35*100000000000000000000^8 ≤ 38021416312976489773^8*100000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        80169 100000 38021416312976489773 100000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (80169/100000 : ℝ)) (X := (38021416312976489773/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (138021416312976489773/100000000000000000000 : ℝ) ≤ (10764348921313217/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (138021416312976489773/100000000000000000000 : ℝ)^8 ≤ (10764348921313217/10000000000000000 : ℝ)^35 := by
      have hnat : (138021416312976489773 : ℕ)^8*10000000000000000^35 ≤ 10764348921313217^35*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        138021416312976489773 100000000000000000000 10764348921313217 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10764348921313217/10000000000000000 : ℝ)) (X := (138021416312976489773/100000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (88021416312976489773/50000000000000000000 : ℝ) ≤ (2844993937996453/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (88021416312976489773/50000000000000000000 : ℝ)^8 ≤ (2844993937996453/2500000000000000 : ℝ)^35 := by
      have hnat : (88021416312976489773 : ℕ)^8*2500000000000000^35 ≤ 2844993937996453^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        88021416312976489773 50000000000000000000 2844993937996453 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2844993937996453/2500000000000000 : ℝ)) (X := (88021416312976489773/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(764348921313217/8016900000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(123125366134519/1603380000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (80169/100000 : ℝ)) (alpha := (764348921313217/8016900000000000 : ℝ)) (beta := (123125366134519/1603380000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (80169/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(764348921313217/8016900000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(123125366134519/1603380000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (42709/50000 : ℝ) ^ (35/8 : ℝ) ≤ (12544941117785286057/25000000000000000000 : ℝ) := by
    have hpowers : (42709/50000 : ℝ)^35 ≤ (12544941117785286057/25000000000000000000 : ℝ)^8 := by
      have hnat : (42709 : ℕ)^35*25000000000000000000^8 ≤ 12544941117785286057^8*50000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        42709 50000 12544941117785286057 25000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (42709/50000 : ℝ)) (X := (12544941117785286057/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (37544941117785286057/25000000000000000000 : ℝ) ≤ (10974085116392349/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (37544941117785286057/25000000000000000000 : ℝ)^8 ≤ (10974085116392349/10000000000000000 : ℝ)^35 := by
      have hnat : (37544941117785286057 : ℕ)^8*10000000000000000^35 ≤ 10974085116392349^35*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        37544941117785286057 25000000000000000000 10974085116392349 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10974085116392349/10000000000000000 : ℝ)) (X := (37544941117785286057/25000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (25044941117785286057/12500000000000000000 : ℝ) ≤ (11721552668356499/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (25044941117785286057/12500000000000000000 : ℝ)^8 ≤ (11721552668356499/10000000000000000 : ℝ)^35 := by
      have hnat : (25044941117785286057 : ℕ)^8*10000000000000000^35 ≤ 11721552668356499^35*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25044941117785286057 12500000000000000000 11721552668356499 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11721552668356499/10000000000000000 : ℝ)) (X := (25044941117785286057/12500000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(974085116392349/8541800000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(14949351039283/170836000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (42709/50000 : ℝ)) (alpha := (974085116392349/8541800000000000 : ℝ)) (beta := (14949351039283/170836000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (42709/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(974085116392349/8541800000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(14949351039283/170836000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-405923209/2000000000 : ℝ)*X 0 0+(4971549119/10000000000 : ℝ)*X 0 1+(5541247589/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310083_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((1772305597/5000000000 : ℝ)*X 2 0+(6750118127/10000000000 : ℝ)*X 2 1+(-2129335583/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310083_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((1537065549/5000000000 : ℝ)*X 0 0+(4642651053/10000000000 : ℝ)*X 0 1+(5017054879/10000000000 : ℝ)*X 0 2+(1537065549/5000000000 : ℝ)*X 1 0+(4642651053/10000000000 : ℝ)*X 1 1+(5017054879/10000000000 : ℝ)*X 1 2+(1537065549/5000000000 : ℝ)*X 2 0+(4642651053/10000000000 : ℝ)*X 2 1+(5017054879/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310083_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-2614011843/10000000000 : ℝ)*X 0 0+(2036037659/5000000000 : ℝ)*X 0 1+(118627083/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310083_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((1191457573/2000000000 : ℝ)*X 1 0+(2477109/2000000000 : ℝ)*X 1 1+(1146220139/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310083_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((963728447/5000000000 : ℝ)*X 2 0+(517214879/625000000 : ℝ)*X 2 1+(-41156057/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310083_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((1461382463/5000000000 : ℝ)*X 0 0+(2782142807/5000000000 : ℝ)*X 0 1+(840262513/2000000000 : ℝ)*X 0 2+(1461382463/5000000000 : ℝ)*X 1 0+(2782142807/5000000000 : ℝ)*X 1 1+(840262513/2000000000 : ℝ)*X 1 2+(1461382463/5000000000 : ℝ)*X 2 0+(2782142807/5000000000 : ℝ)*X 2 1+(840262513/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310083_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-683998151/10000000000 : ℝ)*X 0 0+(1569287451/5000000000 : ℝ)*X 0 1+(3978890707/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310083_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((4248964707/5000000000 : ℝ)*X 1 0+(963/625000000 : ℝ)*X 1 1+(1378423191/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310083_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((1037562727/2500000000 : ℝ)*X 2 0+(3477686883/5000000000 : ℝ)*X 2 1+(-1024994683/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310083_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((1443498663/5000000000 : ℝ)*X 0 0+(3550336191/10000000000 : ℝ)*X 0 1+(6170358237/10000000000 : ℝ)*X 0 2+(1443498663/5000000000 : ℝ)*X 1 0+(3550336191/10000000000 : ℝ)*X 1 1+(6170358237/10000000000 : ℝ)*X 1 2+(1443498663/5000000000 : ℝ)*X 2 0+(3550336191/10000000000 : ℝ)*X 2 1+(6170358237/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310083_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-3264501/20000000 : ℝ)*X 0 0+(3048867691/5000000000 : ℝ)*X 0 1+(2341798929/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310083_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((31883253/39062500 : ℝ)*X 1 0+(536273/2500000000 : ℝ)*X 1 1+(3209457577/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310083_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((522090787/2000000000 : ℝ)*X 2 0+(7359510517/10000000000 : ℝ)*X 2 1+(-230289667/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310083_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((270590859/500000000 : ℝ)*X 0 0+(3884303041/10000000000 : ℝ)*X 0 1+(3441404047/10000000000 : ℝ)*X 0 2+(270590859/500000000 : ℝ)*X 1 0+(3884303041/10000000000 : ℝ)*X 1 1+(3441404047/10000000000 : ℝ)*X 1 2+(270590859/500000000 : ℝ)*X 2 0+(3884303041/10000000000 : ℝ)*X 2 1+(3441404047/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310083_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((54817/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(54817/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (308759901889897811995149101757/24503981672290000000000000000000000 : ℝ) := by norm_num
    linear_combination (309572548621/500000000000 : ℝ)*(base7) + (9143093/1000000000000 : ℝ)*(base23) + (121599511273/250000000000 : ℝ)*(base49) + (241994031083/1000000000000 : ℝ)*(base60) + (96050673063/40000000000 : ℝ)*(major_s1_0) + (96050673063/40000000000 : ℝ)*(major_s1_1) + (96050673063/40000000000 : ℝ)*(major_s1_2) + (2263709/31250000000 : ℝ)*(sp_s1_0) + (7769853/200000000000 : ℝ)*(sp_s1_6) + (2944505448791/1000000000000 : ℝ)*(sp_s1_7) + (736147914519/250000000000 : ℝ)*(sp_s1_8) + (2944582514983/1000000000000 : ℝ)*(sp_s1_9) + (2103266147709/1000000000000 : ℝ)*(sp_s1_13) + (13770597/1000000000000 : ℝ)*(sp_s1_14) + (1484159899733/1000000000000 : ℝ)*(f.failure) + (736147914519/250000000000 : ℝ)*(f.sum) + (25631796757035118503/45652504280000000000000000000000 : ℝ)*base63 + (3955265620293/34167200000000000000000000 : ℝ)*base64 + (3955732588441/21378400000000000000000000 : ℝ)*base67 + (1102755124270951/1708360000000000000000000000 : ℝ)*base69 + (189901263057240393/916962230000000000000000000000 : ℝ)*base70 + (772604718441/3435200000000000000000000 : ℝ)*base73 + (119112816458049/534460000000000000000000000 : ℝ)*base75 + (9502791574423/42940000000000000000000000 : ℝ)*base77 + (96475295470398661/458994248000000000000000000000 : ℝ)*base79 + (1269/100000000000000000 : ℝ)*base87 + (1269/100000000000000000 : ℝ)*base89 + (1269/100000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((25299/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(25299/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (7641650226646443498355546914761/735119450168700000000000000000000000 : ℝ) := by norm_num
    linear_combination (51613357181/500000000000 : ℝ)*(base7) + (18083201/1000000000000 : ℝ)*(base33) + (185451579229/250000000000 : ℝ)*(base40) + (433714745559/1000000000000 : ℝ)*(base49) + (587056459567/1000000000000 : ℝ)*(base60) + (1277929700159/500000000000 : ℝ)*(major_s1_0) + (2555877483519/1000000000000 : ℝ)*(major_s1_1) + (2555877483519/1000000000000 : ℝ)*(major_s1_2) + (1522133/100000000000 : ℝ)*(sp_s1_2) + (3469712852231/1000000000000 : ℝ)*(sp_s1_14) + (3469487258801/1000000000000 : ℝ)*(sp_s1_15) + (34696795477/10000000000 : ℝ)*(sp_s1_16) + (336589479333/200000000000 : ℝ)*(sp_s1_20) + (207510229/1000000000000 : ℝ)*(sp_s1_22) + (1579720682303/1000000000000 : ℝ)*(f.failure) + (3469712852231/1000000000000 : ℝ)*(f.sum) + (67213779328965313623/228262521400000000000000000000000 : ℝ)*base63 + (373620466419799/854180000000000000000000000 : ℝ)*base65 + (1135245074035571/2672300000000000000000000000 : ℝ)*base67 + (212785776522451/8541800000000000000000000000 : ℝ)*base69 + (10661572991677620011/16505320140000000000000000000000 : ℝ)*base71 + (56611772185231/644100000000000000000000000 : ℝ)*base73 + (252226233394353/534460000000000000000000000 : ℝ)*base75 + (14283575209741/19323000000000000000000000 : ℝ)*base77 + (125384513025595891/1075767768750000000000000000000 : ℝ)*base78 + (50721/100000000000000000 : ℝ)*base86 + (50721/100000000000000000 : ℝ)*base88 + (50721/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(61427/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(61427/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (702935079694887264120517520371/183779862542175000000000000000000000 : ℝ) := by norm_num
    linear_combination (326171307737/500000000000 : ℝ)*(base7) + (58171/62500000000 : ℝ)*(base11) + (439935934209/1000000000000 : ℝ)*(base40) + (38344363687/100000000000 : ℝ)*(base49) + (25531/500000000000 : ℝ)*(base50) + (2779605069661/1000000000000 : ℝ)*(major_s1_0) + (2779605069661/1000000000000 : ℝ)*(major_s1_1) + (2779605069661/1000000000000 : ℝ)*(major_s1_2) + (5651539/1000000000000 : ℝ)*(sp_s1_9) + (875127/100000000000 : ℝ)*(sp_s1_16) + (3447387874831/1000000000000 : ℝ)*(sp_s1_21) + (3447388805567/1000000000000 : ℝ)*(sp_s1_22) + (3447374402759/1000000000000 : ℝ)*(sp_s1_23) + (2370343437303/1000000000000 : ℝ)*(sp_s1_27) + (1718000821829/1000000000000 : ℝ)*(f.failure) + (3447388805567/1000000000000 : ℝ)*(f.sum) + (187927561367505748331/684787564200000000000000000000000 : ℝ)*base63 + (79184787073051/170836000000000000000000000 : ℝ)*base64 + (2446452129275527/8016900000000000000000000000 : ℝ)*base67 + (2966632394259591/8541800000000000000000000000 : ℝ)*base68 + (3953581601560460669/8252660070000000000000000000000 : ℝ)*base70 + (3516227680051/1288200000000000000000000000 : ℝ)*base72 + (81056416496137/1603380000000000000000000000 : ℝ)*base74 + (535177621359217/386460000000000000000000000 : ℝ)*base76 + (5300839800368759989/6884913720000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (79397/100000000000000000 : ℝ)*base87 + (79397/100000000000000000 : ℝ)*base89 + (79397/100000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((19323/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(19323/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((80169/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(80169/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(42709/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(42709/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((54817/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(54817/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((25299/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(25299/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(61427/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(61427/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c310083_s1 p hpa hpb X hX hprev0

#print axioms solution
