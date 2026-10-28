-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c301063_s5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:40:29.628695+00:00
-- url     : https://prove2.me/submissions/16c13c76-52d0-4c1d-9f47-c1f62c7d8c5b

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
theorem collision_support_c301063_s5_s5_0 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-66122553/625000000 : ℝ)*x 0 + (5620278603/10000000000 : ℝ)*x 1 + (722823031/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66122553/625000000 : ℝ)^65 ≤ (5080764391307/100000000000000 : ℝ)^49 := by
    have hnat : (66122553 : ℕ)^65*100000000000000^49 ≤ 5080764391307^49*625000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66122553 625000000 5080764391307 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5620278603/10000000000 : ℝ)^65 ≤ (23281776974037/50000000000000 : ℝ)^49 := by
    have hnat : (5620278603 : ℕ)^65*50000000000000^49 ≤ 23281776974037^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5620278603 10000000000 23281776974037 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (722823031/1250000000 : ℝ)^65 ≤ (4835568164417/10000000000000 : ℝ)^49 := by
    have hnat : (722823031 : ℕ)^65*10000000000000^49 ≤ 4835568164417^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      722823031 1250000000 4835568164417 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-66122553/625000000 : ℝ), (5620278603/10000000000 : ℝ), (722823031/1250000000 : ℝ)] ![(5080764391307/100000000000000 : ℝ), (23281776974037/50000000000000 : ℝ), (4835568164417/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-66122553/625000000 : ℝ)|^65 ≤ (5080764391307/100000000000000 : ℝ)^49
        have hw : |(-66122553/625000000 : ℝ)|=(66122553/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5620278603/10000000000 : ℝ)|^65 ≤ (23281776974037/50000000000000 : ℝ)^49
        have hw : |(5620278603/10000000000 : ℝ)|=(5620278603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(722823031/1250000000 : ℝ)|^65 ≤ (4835568164417/10000000000000 : ℝ)^49
        have hw : |(722823031/1250000000 : ℝ)|=(722823031/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s5_s5_1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2810427829/5000000000 : ℝ)*x 0 + (-1066945261/10000000000 : ℝ)*x 1 + (5776844763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2810427829/5000000000 : ℝ)^65 ≤ (46569896003609/100000000000000 : ℝ)^49 := by
    have hnat : (2810427829 : ℕ)^65*100000000000000^49 ≤ 46569896003609^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2810427829 5000000000 46569896003609 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1066945261/10000000000 : ℝ)^65 ≤ (5138079223601/100000000000000 : ℝ)^49 := by
    have hnat : (1066945261 : ℕ)^65*100000000000000^49 ≤ 5138079223601^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1066945261 10000000000 5138079223601 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5776844763/10000000000 : ℝ)^65 ≤ (48292024764801/100000000000000 : ℝ)^49 := by
    have hnat : (5776844763 : ℕ)^65*100000000000000^49 ≤ 48292024764801^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5776844763 10000000000 48292024764801 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2810427829/5000000000 : ℝ), (-1066945261/10000000000 : ℝ), (5776844763/10000000000 : ℝ)] ![(46569896003609/100000000000000 : ℝ), (5138079223601/100000000000000 : ℝ), (48292024764801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2810427829/5000000000 : ℝ)|^65 ≤ (46569896003609/100000000000000 : ℝ)^49
        have hw : |(2810427829/5000000000 : ℝ)|=(2810427829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1066945261/10000000000 : ℝ)|^65 ≤ (5138079223601/100000000000000 : ℝ)^49
        have hw : |(-1066945261/10000000000 : ℝ)|=(1066945261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5776844763/10000000000 : ℝ)|^65 ≤ (48292024764801/100000000000000 : ℝ)^49
        have hw : |(5776844763/10000000000 : ℝ)|=(5776844763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s5_s5_2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (22210501/39062500 : ℝ)*x 0 + (5752163147/10000000000 : ℝ)*x 1 + (-249225373/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (22210501/39062500 : ℝ)^65 ≤ (47285987786279/100000000000000 : ℝ)^49 := by
    have hnat : (22210501 : ℕ)^65*100000000000000^49 ≤ 47285987786279^49*39062500^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22210501 39062500 47285987786279 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5752163147/10000000000 : ℝ)^65 ≤ (24009257686067/50000000000000 : ℝ)^49 := by
    have hnat : (5752163147 : ℕ)^65*50000000000000^49 ≤ 24009257686067^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5752163147 10000000000 24009257686067 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (249225373/2500000000 : ℝ)^65 ≤ (469549682033/10000000000000 : ℝ)^49 := by
    have hnat : (249225373 : ℕ)^65*10000000000000^49 ≤ 469549682033^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249225373 2500000000 469549682033 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(22210501/39062500 : ℝ), (5752163147/10000000000 : ℝ), (-249225373/2500000000 : ℝ)] ![(47285987786279/100000000000000 : ℝ), (24009257686067/50000000000000 : ℝ), (469549682033/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(22210501/39062500 : ℝ)|^65 ≤ (47285987786279/100000000000000 : ℝ)^49
        have hw : |(22210501/39062500 : ℝ)|=(22210501/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5752163147/10000000000 : ℝ)|^65 ≤ (24009257686067/50000000000000 : ℝ)^49
        have hw : |(5752163147/10000000000 : ℝ)|=(5752163147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-249225373/2500000000 : ℝ)|^65 ≤ (469549682033/10000000000000 : ℝ)^49
        have hw : |(-249225373/2500000000 : ℝ)|=(249225373/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s5_s5_6 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4547205971/10000000000 : ℝ)*x 0 + (4395990809/10000000000 : ℝ)*x 1 + (4159184473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4547205971/10000000000 : ℝ)^65 ≤ (35155054041319/100000000000000 : ℝ)^49 := by
    have hnat : (4547205971 : ℕ)^65*100000000000000^49 ≤ 35155054041319^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4547205971 10000000000 35155054041319 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4395990809/10000000000 : ℝ)^65 ≤ (840318441991/2500000000000 : ℝ)^49 := by
    have hnat : (4395990809 : ℕ)^65*2500000000000^49 ≤ 840318441991^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4395990809 10000000000 840318441991 2500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4159184473/10000000000 : ℝ)^65 ≤ (15616104129329/50000000000000 : ℝ)^49 := by
    have hnat : (4159184473 : ℕ)^65*50000000000000^49 ≤ 15616104129329^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4159184473 10000000000 15616104129329 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4547205971/10000000000 : ℝ), (4395990809/10000000000 : ℝ), (4159184473/10000000000 : ℝ)] ![(35155054041319/100000000000000 : ℝ), (840318441991/2500000000000 : ℝ), (15616104129329/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4547205971/10000000000 : ℝ)|^65 ≤ (35155054041319/100000000000000 : ℝ)^49
        have hw : |(4547205971/10000000000 : ℝ)|=(4547205971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4395990809/10000000000 : ℝ)|^65 ≤ (840318441991/2500000000000 : ℝ)^49
        have hw : |(4395990809/10000000000 : ℝ)|=(4395990809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4159184473/10000000000 : ℝ)|^65 ≤ (15616104129329/50000000000000 : ℝ)^49
        have hw : |(4159184473/10000000000 : ℝ)|=(4159184473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s5_s5_7 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-981212527/10000000000 : ℝ)*x 0 + (3893952037/10000000000 : ℝ)*x 1 + (3688084981/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (981212527/10000000000 : ℝ)^65 ≤ (459772367791/10000000000000 : ℝ)^49 := by
    have hnat : (981212527 : ℕ)^65*10000000000000^49 ≤ 459772367791^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      981212527 10000000000 459772367791 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3893952037/10000000000 : ℝ)^65 ≤ (3577260787749/12500000000000 : ℝ)^49 := by
    have hnat : (3893952037 : ℕ)^65*12500000000000^49 ≤ 3577260787749^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3893952037 10000000000 3577260787749 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3688084981/5000000000 : ℝ)^65 ≤ (66784190009357/100000000000000 : ℝ)^49 := by
    have hnat : (3688084981 : ℕ)^65*100000000000000^49 ≤ 66784190009357^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3688084981 5000000000 66784190009357 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-981212527/10000000000 : ℝ), (3893952037/10000000000 : ℝ), (3688084981/5000000000 : ℝ)] ![(459772367791/10000000000000 : ℝ), (3577260787749/12500000000000 : ℝ), (66784190009357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-981212527/10000000000 : ℝ)|^65 ≤ (459772367791/10000000000000 : ℝ)^49
        have hw : |(-981212527/10000000000 : ℝ)|=(981212527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3893952037/10000000000 : ℝ)|^65 ≤ (3577260787749/12500000000000 : ℝ)^49
        have hw : |(3893952037/10000000000 : ℝ)|=(3893952037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3688084981/5000000000 : ℝ)|^65 ≤ (66784190009357/100000000000000 : ℝ)^49
        have hw : |(3688084981/5000000000 : ℝ)|=(3688084981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s5_s5_8 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4300054993/10000000000 : ℝ)*x 0 + (-224178277/10000000000 : ℝ)*x 1 + (1842460491/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4300054993/10000000000 : ℝ)^65 ≤ (16321574740743/50000000000000 : ℝ)^49 := by
    have hnat : (4300054993 : ℕ)^65*50000000000000^49 ≤ 16321574740743^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4300054993 10000000000 16321574740743 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (224178277/10000000000 : ℝ)^65 ≤ (648652089513/100000000000000 : ℝ)^49 := by
    have hnat : (224178277 : ℕ)^65*100000000000000^49 ≤ 648652089513^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224178277 10000000000 648652089513 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1842460491/2500000000 : ℝ)^65 ≤ (16677049605681/25000000000000 : ℝ)^49 := by
    have hnat : (1842460491 : ℕ)^65*25000000000000^49 ≤ 16677049605681^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1842460491 2500000000 16677049605681 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4300054993/10000000000 : ℝ), (-224178277/10000000000 : ℝ), (1842460491/2500000000 : ℝ)] ![(16321574740743/50000000000000 : ℝ), (648652089513/100000000000000 : ℝ), (16677049605681/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4300054993/10000000000 : ℝ)|^65 ≤ (16321574740743/50000000000000 : ℝ)^49
        have hw : |(4300054993/10000000000 : ℝ)|=(4300054993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-224178277/10000000000 : ℝ)|^65 ≤ (648652089513/100000000000000 : ℝ)^49
        have hw : |(-224178277/10000000000 : ℝ)|=(224178277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1842460491/2500000000 : ℝ)|^65 ≤ (16677049605681/25000000000000 : ℝ)^49
        have hw : |(1842460491/2500000000 : ℝ)|=(1842460491/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s5_s5_9 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2021468137/5000000000 : ℝ)*x 0 + (1904712839/2500000000 : ℝ)*x 1 + (-94419653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2021468137/5000000000 : ℝ)^65 ≤ (7519888499911/25000000000000 : ℝ)^49 := by
    have hnat : (2021468137 : ℕ)^65*25000000000000^49 ≤ 7519888499911^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2021468137 5000000000 7519888499911 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1904712839/2500000000 : ℝ)^65 ≤ (69714450230513/100000000000000 : ℝ)^49 := by
    have hnat : (1904712839 : ℕ)^65*100000000000000^49 ≤ 69714450230513^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1904712839 2500000000 69714450230513 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (94419653/10000000000 : ℝ)^65 ≤ (102997881033/50000000000000 : ℝ)^49 := by
    have hnat : (94419653 : ℕ)^65*50000000000000^49 ≤ 102997881033^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94419653 10000000000 102997881033 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2021468137/5000000000 : ℝ), (1904712839/2500000000 : ℝ), (-94419653/10000000000 : ℝ)] ![(7519888499911/25000000000000 : ℝ), (69714450230513/100000000000000 : ℝ), (102997881033/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2021468137/5000000000 : ℝ)|^65 ≤ (7519888499911/25000000000000 : ℝ)^49
        have hw : |(2021468137/5000000000 : ℝ)|=(2021468137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1904712839/2500000000 : ℝ)|^65 ≤ (69714450230513/100000000000000 : ℝ)^49
        have hw : |(1904712839/2500000000 : ℝ)|=(1904712839/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-94419653/10000000000 : ℝ)|^65 ≤ (102997881033/50000000000000 : ℝ)^49
        have hw : |(-94419653/10000000000 : ℝ)|=(94419653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s5_s5_13 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1005673323/2500000000 : ℝ)*x 0 + (3350848387/5000000000 : ℝ)*x 1 + (1934399653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1005673323/2500000000 : ℝ)^65 ≤ (7469982736547/25000000000000 : ℝ)^49 := by
    have hnat : (1005673323 : ℕ)^65*25000000000000^49 ≤ 7469982736547^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005673323 2500000000 7469982736547 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3350848387/5000000000 : ℝ)^65 ≤ (11761393414671/20000000000000 : ℝ)^49 := by
    have hnat : (3350848387 : ℕ)^65*20000000000000^49 ≤ 11761393414671^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3350848387 5000000000 11761393414671 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1934399653/10000000000 : ℝ)^65 ≤ (2262620392383/20000000000000 : ℝ)^49 := by
    have hnat : (1934399653 : ℕ)^65*20000000000000^49 ≤ 2262620392383^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1934399653 10000000000 2262620392383 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1005673323/2500000000 : ℝ), (3350848387/5000000000 : ℝ), (1934399653/10000000000 : ℝ)] ![(7469982736547/25000000000000 : ℝ), (11761393414671/20000000000000 : ℝ), (2262620392383/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1005673323/2500000000 : ℝ)|^65 ≤ (7469982736547/25000000000000 : ℝ)^49
        have hw : |(1005673323/2500000000 : ℝ)|=(1005673323/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3350848387/5000000000 : ℝ)|^65 ≤ (11761393414671/20000000000000 : ℝ)^49
        have hw : |(3350848387/5000000000 : ℝ)|=(3350848387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1934399653/10000000000 : ℝ)|^65 ≤ (2262620392383/20000000000000 : ℝ)^49
        have hw : |(1934399653/10000000000 : ℝ)|=(1934399653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s5_s5_14 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-197675093/10000000000 : ℝ)*x 0 + (845522653/2000000000 : ℝ)*x 1 + (7438629231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (197675093/10000000000 : ℝ)^65 ≤ (21957762869/4000000000000 : ℝ)^49 := by
    have hnat : (197675093 : ℕ)^65*4000000000000^49 ≤ 21957762869^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197675093 10000000000 21957762869 4000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (845522653/2000000000 : ℝ)^65 ≤ (3191566556701/10000000000000 : ℝ)^49 := by
    have hnat : (845522653 : ℕ)^65*10000000000000^49 ≤ 3191566556701^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      845522653 2000000000 3191566556701 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7438629231/10000000000 : ℝ)^65 ≤ (67535390349713/100000000000000 : ℝ)^49 := by
    have hnat : (7438629231 : ℕ)^65*100000000000000^49 ≤ 67535390349713^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7438629231 10000000000 67535390349713 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-197675093/10000000000 : ℝ), (845522653/2000000000 : ℝ), (7438629231/10000000000 : ℝ)] ![(21957762869/4000000000000 : ℝ), (3191566556701/10000000000000 : ℝ), (67535390349713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-197675093/10000000000 : ℝ)|^65 ≤ (21957762869/4000000000000 : ℝ)^49
        have hw : |(-197675093/10000000000 : ℝ)|=(197675093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(845522653/2000000000 : ℝ)|^65 ≤ (3191566556701/10000000000000 : ℝ)^49
        have hw : |(845522653/2000000000 : ℝ)|=(845522653/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7438629231/10000000000 : ℝ)|^65 ≤ (67535390349713/100000000000000 : ℝ)^49
        have hw : |(7438629231/10000000000 : ℝ)|=(7438629231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s5_s5_15 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3807735673/10000000000 : ℝ)*x 0 + (-100739983/1000000000 : ℝ)*x 1 + (7432218537/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3807735673/10000000000 : ℝ)^65 ≤ (27780602718823/100000000000000 : ℝ)^49 := by
    have hnat : (3807735673 : ℕ)^65*100000000000000^49 ≤ 27780602718823^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3807735673 10000000000 27780602718823 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (100739983/1000000000 : ℝ)^65 ≤ (4761203789831/100000000000000 : ℝ)^49 := by
    have hnat : (100739983 : ℕ)^65*100000000000000^49 ≤ 4761203789831^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100739983 1000000000 4761203789831 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7432218537/10000000000 : ℝ)^65 ≤ (16864548369441/25000000000000 : ℝ)^49 := by
    have hnat : (7432218537 : ℕ)^65*25000000000000^49 ≤ 16864548369441^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7432218537 10000000000 16864548369441 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3807735673/10000000000 : ℝ), (-100739983/1000000000 : ℝ), (7432218537/10000000000 : ℝ)] ![(27780602718823/100000000000000 : ℝ), (4761203789831/100000000000000 : ℝ), (16864548369441/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3807735673/10000000000 : ℝ)|^65 ≤ (27780602718823/100000000000000 : ℝ)^49
        have hw : |(3807735673/10000000000 : ℝ)|=(3807735673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-100739983/1000000000 : ℝ)|^65 ≤ (4761203789831/100000000000000 : ℝ)^49
        have hw : |(-100739983/1000000000 : ℝ)|=(100739983/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7432218537/10000000000 : ℝ)|^65 ≤ (16864548369441/25000000000000 : ℝ)^49
        have hw : |(7432218537/10000000000 : ℝ)|=(7432218537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s5_s5_16 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (733392451/1000000000 : ℝ)*x 0 + (136715587/312500000 : ℝ)*x 1 + (-4148909/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (733392451/1000000000 : ℝ)^65 ≤ (66277277303429/100000000000000 : ℝ)^49 := by
    have hnat : (733392451 : ℕ)^65*100000000000000^49 ≤ 66277277303429^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      733392451 1000000000 66277277303429 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (136715587/312500000 : ℝ)^65 ≤ (16699485020603/50000000000000 : ℝ)^49 := by
    have hnat : (136715587 : ℕ)^65*50000000000000^49 ≤ 16699485020603^49*312500000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136715587 312500000 16699485020603 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4148909/312500000 : ℝ)^65 ≤ (161876320697/50000000000000 : ℝ)^49 := by
    have hnat : (4148909 : ℕ)^65*50000000000000^49 ≤ 161876320697^49*312500000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4148909 312500000 161876320697 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(733392451/1000000000 : ℝ), (136715587/312500000 : ℝ), (-4148909/312500000 : ℝ)] ![(66277277303429/100000000000000 : ℝ), (16699485020603/50000000000000 : ℝ), (161876320697/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(733392451/1000000000 : ℝ)|^65 ≤ (66277277303429/100000000000000 : ℝ)^49
        have hw : |(733392451/1000000000 : ℝ)|=(733392451/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(136715587/312500000 : ℝ)|^65 ≤ (16699485020603/50000000000000 : ℝ)^49
        have hw : |(136715587/312500000 : ℝ)|=(136715587/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4148909/312500000 : ℝ)|^65 ≤ (161876320697/50000000000000 : ℝ)^49
        have hw : |(-4148909/312500000 : ℝ)|=(4148909/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s5_s5_20 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7301985489/10000000000 : ℝ)*x 0 + (821628373/2500000000 : ℝ)*x 1 + (963309587/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7301985489/10000000000 : ℝ)^65 ≤ (32947332955259/50000000000000 : ℝ)^49 := by
    have hnat : (7301985489 : ℕ)^65*50000000000000^49 ≤ 32947332955259^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7301985489 10000000000 32947332955259 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (821628373/2500000000 : ℝ)^65 ≤ (11426276903383/50000000000000 : ℝ)^49 := by
    have hnat : (821628373 : ℕ)^65*50000000000000^49 ≤ 11426276903383^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      821628373 2500000000 11426276903383 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (963309587/5000000000 : ℝ)^65 ≤ (5626390131631/50000000000000 : ℝ)^49 := by
    have hnat : (963309587 : ℕ)^65*50000000000000^49 ≤ 5626390131631^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      963309587 5000000000 5626390131631 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7301985489/10000000000 : ℝ), (821628373/2500000000 : ℝ), (963309587/5000000000 : ℝ)] ![(32947332955259/50000000000000 : ℝ), (11426276903383/50000000000000 : ℝ), (5626390131631/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7301985489/10000000000 : ℝ)|^65 ≤ (32947332955259/50000000000000 : ℝ)^49
        have hw : |(7301985489/10000000000 : ℝ)|=(7301985489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(821628373/2500000000 : ℝ)|^65 ≤ (11426276903383/50000000000000 : ℝ)^49
        have hw : |(821628373/2500000000 : ℝ)|=(821628373/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(963309587/5000000000 : ℝ)|^65 ≤ (5626390131631/50000000000000 : ℝ)^49
        have hw : |(963309587/5000000000 : ℝ)|=(963309587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s5_s5_21 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-41285759/2500000000 : ℝ)*x 0 + (6833395697/10000000000 : ℝ)*x 1 + (197537531/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41285759/2500000000 : ℝ)^65 ≤ (432451178999/100000000000000 : ℝ)^49 := by
    have hnat : (41285759 : ℕ)^65*100000000000000^49 ≤ 432451178999^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41285759 2500000000 432451178999 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6833395697/10000000000 : ℝ)^65 ≤ (3017243442599/5000000000000 : ℝ)^49 := by
    have hnat : (6833395697 : ℕ)^65*5000000000000^49 ≤ 3017243442599^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6833395697 10000000000 3017243442599 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (197537531/400000000 : ℝ)^65 ≤ (4902834993981/12500000000000 : ℝ)^49 := by
    have hnat : (197537531 : ℕ)^65*12500000000000^49 ≤ 4902834993981^49*400000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197537531 400000000 4902834993981 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-41285759/2500000000 : ℝ), (6833395697/10000000000 : ℝ), (197537531/400000000 : ℝ)] ![(432451178999/100000000000000 : ℝ), (3017243442599/5000000000000 : ℝ), (4902834993981/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-41285759/2500000000 : ℝ)|^65 ≤ (432451178999/100000000000000 : ℝ)^49
        have hw : |(-41285759/2500000000 : ℝ)|=(41285759/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6833395697/10000000000 : ℝ)|^65 ≤ (3017243442599/5000000000000 : ℝ)^49
        have hw : |(6833395697/10000000000 : ℝ)|=(6833395697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(197537531/400000000 : ℝ)|^65 ≤ (4902834993981/12500000000000 : ℝ)^49
        have hw : |(197537531/400000000 : ℝ)|=(197537531/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s5_s5_22 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (730823167/1000000000 : ℝ)*x 0 + (-31265441/2500000000 : ℝ)*x 1 + (4407692417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (730823167/1000000000 : ℝ)^65 ≤ (13193889743881/20000000000000 : ℝ)^49 := by
    have hnat : (730823167 : ℕ)^65*20000000000000^49 ≤ 13193889743881^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      730823167 1000000000 13193889743881 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (31265441/2500000000 : ℝ)^65 ≤ (299073177191/100000000000000 : ℝ)^49 := by
    have hnat : (31265441 : ℕ)^65*100000000000000^49 ≤ 299073177191^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31265441 2500000000 299073177191 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4407692417/10000000000 : ℝ)^65 ≤ (33731478083049/100000000000000 : ℝ)^49 := by
    have hnat : (4407692417 : ℕ)^65*100000000000000^49 ≤ 33731478083049^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4407692417 10000000000 33731478083049 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(730823167/1000000000 : ℝ), (-31265441/2500000000 : ℝ), (4407692417/10000000000 : ℝ)] ![(13193889743881/20000000000000 : ℝ), (299073177191/100000000000000 : ℝ), (33731478083049/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(730823167/1000000000 : ℝ)|^65 ≤ (13193889743881/20000000000000 : ℝ)^49
        have hw : |(730823167/1000000000 : ℝ)|=(730823167/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-31265441/2500000000 : ℝ)|^65 ≤ (299073177191/100000000000000 : ℝ)^49
        have hw : |(-31265441/2500000000 : ℝ)|=(31265441/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4407692417/10000000000 : ℝ)|^65 ≤ (33731478083049/100000000000000 : ℝ)^49
        have hw : |(4407692417/10000000000 : ℝ)|=(4407692417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s5_s5_23 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7532051/20000000 : ℝ)*x 0 + (7505291333/10000000000 : ℝ)*x 1 + (-58133139/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7532051/20000000 : ℝ)^65 ≤ (427775770657/1562500000000 : ℝ)^49 := by
    have hnat : (7532051 : ℕ)^65*1562500000000^49 ≤ 427775770657^49*20000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7532051 20000000 427775770657 1562500000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7505291333/10000000000 : ℝ)^65 ≤ (3416970667383/5000000000000 : ℝ)^49 := by
    have hnat : (7505291333 : ℕ)^65*5000000000000^49 ≤ 3416970667383^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7505291333 10000000000 3416970667383 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (58133139/625000000 : ℝ)^65 ≤ (2141468657487/50000000000000 : ℝ)^49 := by
    have hnat : (58133139 : ℕ)^65*50000000000000^49 ≤ 2141468657487^49*625000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58133139 625000000 2141468657487 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7532051/20000000 : ℝ), (7505291333/10000000000 : ℝ), (-58133139/625000000 : ℝ)] ![(427775770657/1562500000000 : ℝ), (3416970667383/5000000000000 : ℝ), (2141468657487/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7532051/20000000 : ℝ)|^65 ≤ (427775770657/1562500000000 : ℝ)^49
        have hw : |(7532051/20000000 : ℝ)|=(7532051/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7505291333/10000000000 : ℝ)|^65 ≤ (3416970667383/5000000000000 : ℝ)^49
        have hw : |(7505291333/10000000000 : ℝ)|=(7505291333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-58133139/625000000 : ℝ)|^65 ≤ (2141468657487/50000000000000 : ℝ)^49
        have hw : |(-58133139/625000000 : ℝ)|=(58133139/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s5_s5_27 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1489236457/2000000000 : ℝ)*x 0 + (343359287/1250000000 : ℝ)*x 1 + (2315383433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1489236457/2000000000 : ℝ)^65 ≤ (67626371273427/100000000000000 : ℝ)^49 := by
    have hnat : (1489236457 : ℕ)^65*100000000000000^49 ≤ 67626371273427^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1489236457 2000000000 67626371273427 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (343359287/1250000000 : ℝ)^65 ≤ (450342027939/2500000000000 : ℝ)^49 := by
    have hnat : (343359287 : ℕ)^65*2500000000000^49 ≤ 450342027939^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343359287 1250000000 450342027939 2500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2315383433/10000000000 : ℝ)^65 ≤ (14359947597023/100000000000000 : ℝ)^49 := by
    have hnat : (2315383433 : ℕ)^65*100000000000000^49 ≤ 14359947597023^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2315383433 10000000000 14359947597023 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1489236457/2000000000 : ℝ), (343359287/1250000000 : ℝ), (2315383433/10000000000 : ℝ)] ![(67626371273427/100000000000000 : ℝ), (450342027939/2500000000000 : ℝ), (14359947597023/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1489236457/2000000000 : ℝ)|^65 ≤ (67626371273427/100000000000000 : ℝ)^49
        have hw : |(1489236457/2000000000 : ℝ)|=(1489236457/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(343359287/1250000000 : ℝ)|^65 ≤ (450342027939/2500000000000 : ℝ)^49
        have hw : |(343359287/1250000000 : ℝ)|=(343359287/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2315383433/10000000000 : ℝ)|^65 ≤ (14359947597023/100000000000000 : ℝ)^49
        have hw : |(2315383433/10000000000 : ℝ)|=(2315383433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c301063_s5 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev4 : (0 : ℝ) ≤ ((2259/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2259/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18163/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(18163/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(69771/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(69771/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((1998/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1998/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(64669/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(64669/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(31007/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(31007/50000 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (92391/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
  rcases hprev4 with ⟨ratio_s4_0,ratio_s4_1,ratio_s4_2⟩
  have s5_pow0 : (2259/3125 : ℝ) ^ (129/32 : ℝ) ≤ (1081236373760044283/4000000000000000000 : ℝ) := by
    have hpowers : (2259/3125 : ℝ)^129 ≤ (1081236373760044283/4000000000000000000 : ℝ)^32 := by
      have hnat : (2259 : ℕ)^129*4000000000000000000^32 ≤ 1081236373760044283^32*3125^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2259 3125 1081236373760044283 4000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2259/3125 : ℝ)) (X := (1081236373760044283/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s5_corner0a : (5081236373760044283/4000000000000000000 : ℝ) ≤ (10611480416732703/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (5081236373760044283/4000000000000000000 : ℝ)^32 ≤ (10611480416732703/10000000000000000 : ℝ)^129 := by
      have hnat : (5081236373760044283 : ℕ)^32*10000000000000000^129 ≤ 10611480416732703^129*4000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5081236373760044283 4000000000000000000 10611480416732703 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10611480416732703/10000000000000000 : ℝ)) (X := (5081236373760044283/4000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s5_corner0b : (3081236373760044283/2000000000000000000 : ℝ) ≤ (11131661847196971/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (3081236373760044283/2000000000000000000 : ℝ)^32 ≤ (11131661847196971/10000000000000000 : ℝ)^129 := by
      have hnat : (3081236373760044283 : ℕ)^32*10000000000000000^129 ≤ 11131661847196971^129*2000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3081236373760044283 2000000000000000000 11131661847196971 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11131661847196971/10000000000000000 : ℝ)) (X := (3081236373760044283/2000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s5_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(611480416732703/7228800000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(14449484179563/200800000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (2259/3125 : ℝ)) (alpha := (611480416732703/7228800000000000 : ℝ)) (beta := (14449484179563/200800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow0,s5_corner0a]) (by linarith only [s5_pow0,s5_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (2259/3125 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(611480416732703/7228800000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(14449484179563/200800000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s5_pow1 : (18163/25000 : ℝ) ^ (129/32 : ℝ) ≤ (27583811974479400421/100000000000000000000 : ℝ) := by
    have hpowers : (18163/25000 : ℝ)^129 ≤ (27583811974479400421/100000000000000000000 : ℝ)^32 := by
      have hnat : (18163 : ℕ)^129*100000000000000000000^32 ≤ 27583811974479400421^32*25000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18163 25000 27583811974479400421 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18163/25000 : ℝ)) (X := (27583811974479400421/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s5_corner1a : (127583811974479400421/100000000000000000000 : ℝ) ≤ (5311459418292693/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (127583811974479400421/100000000000000000000 : ℝ)^32 ≤ (5311459418292693/5000000000000000 : ℝ)^129 := by
      have hnat : (127583811974479400421 : ℕ)^32*5000000000000000^129 ≤ 5311459418292693^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        127583811974479400421 100000000000000000000 5311459418292693 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5311459418292693/5000000000000000 : ℝ)) (X := (127583811974479400421/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s5_corner1b : (77583811974479400421/50000000000000000000 : ℝ) ≤ (2230285719192909/2000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (77583811974479400421/50000000000000000000 : ℝ)^32 ≤ (2230285719192909/2000000000000000 : ℝ)^129 := by
      have hnat : (77583811974479400421 : ℕ)^32*2000000000000000^129 ≤ 2230285719192909^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        77583811974479400421 50000000000000000000 2230285719192909 2000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2230285719192909/2000000000000000 : ℝ)) (X := (77583811974479400421/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s5_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(311459418292693/3632600000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(528509759379159/7265200000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (18163/25000 : ℝ)) (alpha := (311459418292693/3632600000000000 : ℝ)) (beta := (528509759379159/7265200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow1,s5_corner1a]) (by linarith only [s5_pow1,s5_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (18163/25000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(311459418292693/3632600000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(528509759379159/7265200000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s5_pow2 : (69771/100000 : ℝ) ^ (129/32 : ℝ) ≤ (23432284546019105297/100000000000000000000 : ℝ) := by
    have hpowers : (69771/100000 : ℝ)^129 ≤ (23432284546019105297/100000000000000000000 : ℝ)^32 := by
      have hnat : (69771 : ℕ)^129*100000000000000000000^32 ≤ 23432284546019105297^32*100000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        69771 100000 23432284546019105297 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (69771/100000 : ℝ)) (X := (23432284546019105297/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s5_corner2a : (123432284546019105297/100000000000000000000 : ℝ) ≤ (10536102919195961/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (123432284546019105297/100000000000000000000 : ℝ)^32 ≤ (10536102919195961/10000000000000000 : ℝ)^129 := by
      have hnat : (123432284546019105297 : ℕ)^32*10000000000000000^129 ≤ 10536102919195961^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        123432284546019105297 100000000000000000000 10536102919195961 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10536102919195961/10000000000000000 : ℝ)) (X := (123432284546019105297/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s5_corner2b : (73432284546019105297/50000000000000000000 : ℝ) ≤ (11000331581096159/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (73432284546019105297/50000000000000000000 : ℝ)^32 ≤ (11000331581096159/10000000000000000 : ℝ)^129 := by
      have hnat : (73432284546019105297 : ℕ)^32*10000000000000000^129 ≤ 11000331581096159^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        73432284546019105297 50000000000000000000 11000331581096159 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11000331581096159/10000000000000000 : ℝ)) (X := (73432284546019105297/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s5_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(41238686091997/536700000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(5951649511541/89450000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (69771/100000 : ℝ)) (alpha := (41238686091997/536700000000000 : ℝ)) (beta := (5951649511541/89450000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow2,s5_corner2a]) (by linarith only [s5_pow2,s5_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (69771/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(41238686091997/536700000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(5951649511541/89450000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s5_0 : ((-66122553/625000000 : ℝ)*X 0 0+(5620278603/10000000000 : ℝ)*X 0 1+(722823031/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s5_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_1 : ((2810427829/5000000000 : ℝ)*X 1 0+(-1066945261/10000000000 : ℝ)*X 1 1+(5776844763/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s5_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_2 : ((22210501/39062500 : ℝ)*X 2 0+(5752163147/10000000000 : ℝ)*X 2 1+(-249225373/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s5_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_6 : ((4547205971/10000000000 : ℝ)*X 0 0+(4395990809/10000000000 : ℝ)*X 0 1+(4159184473/10000000000 : ℝ)*X 0 2+(4547205971/10000000000 : ℝ)*X 1 0+(4395990809/10000000000 : ℝ)*X 1 1+(4159184473/10000000000 : ℝ)*X 1 2+(4547205971/10000000000 : ℝ)*X 2 0+(4395990809/10000000000 : ℝ)*X 2 1+(4159184473/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s5_s5_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_7 : ((-981212527/10000000000 : ℝ)*X 0 0+(3893952037/10000000000 : ℝ)*X 0 1+(3688084981/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s5_s5_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_8 : ((4300054993/10000000000 : ℝ)*X 1 0+(-224178277/10000000000 : ℝ)*X 1 1+(1842460491/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s5_s5_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_9 : ((2021468137/5000000000 : ℝ)*X 2 0+(1904712839/2500000000 : ℝ)*X 2 1+(-94419653/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s5_s5_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_13 : ((1005673323/2500000000 : ℝ)*X 0 0+(3350848387/5000000000 : ℝ)*X 0 1+(1934399653/10000000000 : ℝ)*X 0 2+(1005673323/2500000000 : ℝ)*X 1 0+(3350848387/5000000000 : ℝ)*X 1 1+(1934399653/10000000000 : ℝ)*X 1 2+(1005673323/2500000000 : ℝ)*X 2 0+(3350848387/5000000000 : ℝ)*X 2 1+(1934399653/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s5_s5_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_14 : ((-197675093/10000000000 : ℝ)*X 0 0+(845522653/2000000000 : ℝ)*X 0 1+(7438629231/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s5_s5_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_15 : ((3807735673/10000000000 : ℝ)*X 1 0+(-100739983/1000000000 : ℝ)*X 1 1+(7432218537/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s5_s5_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_16 : ((733392451/1000000000 : ℝ)*X 2 0+(136715587/312500000 : ℝ)*X 2 1+(-4148909/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s5_s5_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_20 : ((7301985489/10000000000 : ℝ)*X 0 0+(821628373/2500000000 : ℝ)*X 0 1+(963309587/5000000000 : ℝ)*X 0 2+(7301985489/10000000000 : ℝ)*X 1 0+(821628373/2500000000 : ℝ)*X 1 1+(963309587/5000000000 : ℝ)*X 1 2+(7301985489/10000000000 : ℝ)*X 2 0+(821628373/2500000000 : ℝ)*X 2 1+(963309587/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s5_s5_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_21 : ((-41285759/2500000000 : ℝ)*X 0 0+(6833395697/10000000000 : ℝ)*X 0 1+(197537531/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s5_s5_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_22 : ((730823167/1000000000 : ℝ)*X 1 0+(-31265441/2500000000 : ℝ)*X 1 1+(4407692417/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s5_s5_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_23 : ((7532051/20000000 : ℝ)*X 2 0+(7505291333/10000000000 : ℝ)*X 2 1+(-58133139/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s5_s5_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_27 : ((1489236457/2000000000 : ℝ)*X 0 0+(343359287/1250000000 : ℝ)*X 0 1+(2315383433/10000000000 : ℝ)*X 0 2+(1489236457/2000000000 : ℝ)*X 1 0+(343359287/1250000000 : ℝ)*X 1 1+(2315383433/10000000000 : ℝ)*X 1 2+(1489236457/2000000000 : ℝ)*X 2 0+(343359287/1250000000 : ℝ)*X 2 1+(2315383433/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s5_s5_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s5_0 : (0 : ℝ) ≤ ((1998/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1998/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (222018267494915300622165387047/13049432571200000000000000000000000 : ℝ) := by norm_num
    linear_combination (164261440013/500000000000 : ℝ)*(base7) + (202207/100000000000 : ℝ)*(base50) + (1264281629/12500000000 : ℝ)*(base60) + (2476297997733/1000000000000 : ℝ)*(major_s5_0) + (2476297997733/1000000000000 : ℝ)*(major_s5_1) + (2476297997733/1000000000000 : ℝ)*(major_s5_2) + (21796651/1000000000000 : ℝ)*(sp_s5_0) + (185419/25000000000 : ℝ)*(sp_s5_6) + (1538035584379/500000000000 : ℝ)*(sp_s5_7) + (384525747459/125000000000 : ℝ)*(sp_s5_8) + (769051044479/250000000000 : ℝ)*(sp_s5_9) + (12515933907/6250000000 : ℝ)*(sp_s5_13) + (56507131/500000000000 : ℝ)*(sp_s5_14) + (450439/250000000000 : ℝ)*(sp_s5_23) + (837016980927/500000000000 : ℝ)*(f.failure) + (384525747459/125000000000 : ℝ)*(f.sum) + (2387789951114495783/6498721400000000000000000000000 : ℝ)*base63 + (13979475372063/22362500000000000000000000 : ℝ)*base64 + (381238014207427/7265200000000000000000000000 : ℝ)*base67 + (20341205671173/178900000000000000000000000 : ℝ)*base68 + (1905063581092765627/4310774400000000000000000000000 : ℝ)*base70 + (156798674561161/200800000000000000000000000 : ℝ)*base72 + (2637573100442871/3632600000000000000000000000 : ℝ)*base74 + (1841066986674007/2409600000000000000000000000 : ℝ)*base76 + (696675853674191351/3647130400000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1113/12500000000000000 : ℝ)*base86 + (1113/12500000000000000 : ℝ)*base88 + (1113/12500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s5_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(64669/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(64669/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (302537023513855298170870130063/19574148856800000000000000000000000 : ℝ) := by norm_num
    linear_combination (376846506181/1000000000000 : ℝ)*(base7) + (425519/500000000000 : ℝ)*(base49) + (589607/1000000000000 : ℝ)*(base59) + (1181176446391/500000000000 : ℝ)*(major_s5_0) + (1181176446391/500000000000 : ℝ)*(major_s5_1) + (1181176446391/500000000000 : ℝ)*(major_s5_2) + (1749761/1000000000000 : ℝ)*(sp_s5_1) + (1902771/1000000000000 : ℝ)*(sp_s5_2) + (50631283/500000000000 : ℝ)*(sp_s5_8) + (361947665771/125000000000 : ℝ)*(sp_s5_14) + (2895478313841/1000000000000 : ℝ)*(sp_s5_15) + (2895579423397/1000000000000 : ℝ)*(sp_s5_16) + (1973786476451/1000000000000 : ℝ)*(sp_s5_20) + (32250061/500000000000 : ℝ)*(sp_s5_27) + (199625558799/125000000000 : ℝ)*(f.failure) + (361947665771/125000000000 : ℝ)*(f.sum) + (3477657403107581827/9748082100000000000000000000000 : ℝ)*base62 + (25475546922559/44725000000000000000000000 : ℝ)*base64 + (881082409486911/3632600000000000000000000000 : ℝ)*base66 + (150440239790303/268350000000000000000000000 : ℝ)*base68 + (1914320287282031707/6466161600000000000000000000000 : ℝ)*base70 + (46152182220227/100400000000000000000000000 : ℝ)*base72 + (1047325632511687/1816300000000000000000000000 : ℝ)*base74 + (1815341825663287/3614400000000000000000000000 : ℝ)*base76 + (71518286219922877/1823565200000000000000000000000 : ℝ)*base79 + (2069/3125000000000000 : ℝ)*base87 + (2069/3125000000000000 : ℝ)*base89 + (2069/3125000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s5_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(31007/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(31007/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (18468278857798782224647792097/2609886514240000000000000000000000 : ℝ) := by norm_num
    linear_combination (184695483273/500000000000 : ℝ)*(base7) + (72520337703/500000000000 : ℝ)*(base40) + (877949/1000000000000 : ℝ)*(base49) + (90448962459/40000000000 : ℝ)*(major_s5_0) + (90448962459/40000000000 : ℝ)*(major_s5_1) + (90448962459/40000000000 : ℝ)*(major_s5_2) + (174101/25000000000 : ℝ)*(sp_s5_1) + (14528937/1000000000000 : ℝ)*(sp_s5_2) + (902207/15625000000 : ℝ)*(sp_s5_9) + (6023761/500000000000 : ℝ)*(sp_s5_20) + (2766284019839/1000000000000 : ℝ)*(sp_s5_21) + (13831385279/5000000000 : ℝ)*(sp_s5_22) + (1383105874827/500000000000 : ℝ)*(sp_s5_23) + (1898017991437/1000000000000 : ℝ)*(sp_s5_27) + (382159768103/250000000000 : ℝ)*(f.failure) + (2766284019839/1000000000000 : ℝ)*(f.sum) + (325092722473792327/1299744280000000000000000000000 : ℝ)*base62 + (43004084467/559062500000000000000000 : ℝ)*base65 + (497482941553391/1453040000000000000000000000 : ℝ)*base66 + (24957919500389/35780000000000000000000000 : ℝ)*base68 + (417188503634082073/862154880000000000000000000000 : ℝ)*base70 + (2032742407619/40160000000000000000000000 : ℝ)*base72 + (54896625036369/726520000000000000000000000 : ℝ)*base74 + (7354362586453/19276800000000000000000000 : ℝ)*base76 + (1967575536849947/29177043200000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (1707/6250000000000000 : ℝ)*base86 + (1707/6250000000000000 : ℝ)*base88 + (1707/6250000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s5_0,ratio_s5_1,ratio_s5_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev4 : (0 : ℝ) ≤ ((2259/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2259/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18163/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(18163/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(69771/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(69771/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((1998/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1998/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(64669/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(64669/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(31007/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(31007/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c301063_s5 p hpa hpb X hX hprev4

#print axioms solution
