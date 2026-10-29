-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c309060_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:04:02.949245+00:00
-- url     : https://prove2.me/submissions/de5e0efd-d125-4017-b2dc-a5247b5ff1f9

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
theorem collision_support_c309060_s2_s2_0 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-497980713/2500000000 : ℝ)*x 0 + (4251712381/10000000000 : ℝ)*x 1 + (-627444067/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (497980713/2500000000 : ℝ)^35 ≤ (6174752569569/50000000000000 : ℝ)^27 := by
    have hnat : (497980713 : ℕ)^35*50000000000000^27 ≤ 6174752569569^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      497980713 2500000000 6174752569569 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4251712381/10000000000 : ℝ)^35 ≤ (32999604162571/100000000000000 : ℝ)^27 := by
    have hnat : (4251712381 : ℕ)^35*100000000000000^27 ≤ 32999604162571^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4251712381 10000000000 32999604162571 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (627444067/1000000000 : ℝ)^35 ≤ (54650890680263/100000000000000 : ℝ)^27 := by
    have hnat : (627444067 : ℕ)^35*100000000000000^27 ≤ 54650890680263^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      627444067 1000000000 54650890680263 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-497980713/2500000000 : ℝ), (4251712381/10000000000 : ℝ), (-627444067/1000000000 : ℝ)] ![(6174752569569/50000000000000 : ℝ), (32999604162571/100000000000000 : ℝ), (54650890680263/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-497980713/2500000000 : ℝ)|^35 ≤ (6174752569569/50000000000000 : ℝ)^27
        have hw : |(-497980713/2500000000 : ℝ)|=(497980713/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4251712381/10000000000 : ℝ)|^35 ≤ (32999604162571/100000000000000 : ℝ)^27
        have hw : |(4251712381/10000000000 : ℝ)|=(4251712381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-627444067/1000000000 : ℝ)|^35 ≤ (54650890680263/100000000000000 : ℝ)^27
        have hw : |(-627444067/1000000000 : ℝ)|=(627444067/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309060_s2_s2_2 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4714348141/10000000000 : ℝ)*x 0 + (238286793/400000000 : ℝ)*x 1 + (922174131/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4714348141/10000000000 : ℝ)^35 ≤ (3772747112937/10000000000000 : ℝ)^27 := by
    have hnat : (4714348141 : ℕ)^35*10000000000000^27 ≤ 3772747112937^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4714348141 10000000000 3772747112937 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (238286793/400000000 : ℝ)^35 ≤ (51095794978663/100000000000000 : ℝ)^27 := by
    have hnat : (238286793 : ℕ)^35*100000000000000^27 ≤ 51095794978663^27*400000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      238286793 400000000 51095794978663 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (922174131/5000000000 : ℝ)^35 ≤ (11176733876947/100000000000000 : ℝ)^27 := by
    have hnat : (922174131 : ℕ)^35*100000000000000^27 ≤ 11176733876947^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      922174131 5000000000 11176733876947 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4714348141/10000000000 : ℝ), (238286793/400000000 : ℝ), (922174131/5000000000 : ℝ)] ![(3772747112937/10000000000000 : ℝ), (51095794978663/100000000000000 : ℝ), (11176733876947/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4714348141/10000000000 : ℝ)|^35 ≤ (3772747112937/10000000000000 : ℝ)^27
        have hw : |(4714348141/10000000000 : ℝ)|=(4714348141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(238286793/400000000 : ℝ)|^35 ≤ (51095794978663/100000000000000 : ℝ)^27
        have hw : |(238286793/400000000 : ℝ)|=(238286793/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(922174131/5000000000 : ℝ)|^35 ≤ (11176733876947/100000000000000 : ℝ)^27
        have hw : |(922174131/5000000000 : ℝ)|=(922174131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309060_s2_s2_7 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-361422033/2000000000 : ℝ)*x 0 + (3687694283/10000000000 : ℝ)*x 1 + (-344392027/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (361422033/2000000000 : ℝ)^35 ≤ (5442543772143/50000000000000 : ℝ)^27 := by
    have hnat : (361422033 : ℕ)^35*50000000000000^27 ≤ 5442543772143^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      361422033 2000000000 5442543772143 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3687694283/10000000000 : ℝ)^35 ≤ (13720059626993/50000000000000 : ℝ)^27 := by
    have hnat : (3687694283 : ℕ)^35*50000000000000^27 ≤ 13720059626993^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3687694283 10000000000 13720059626993 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (344392027/500000000 : ℝ)^35 ≤ (30837396588849/50000000000000 : ℝ)^27 := by
    have hnat : (344392027 : ℕ)^35*50000000000000^27 ≤ 30837396588849^27*500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      344392027 500000000 30837396588849 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-361422033/2000000000 : ℝ), (3687694283/10000000000 : ℝ), (-344392027/500000000 : ℝ)] ![(5442543772143/50000000000000 : ℝ), (13720059626993/50000000000000 : ℝ), (30837396588849/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-361422033/2000000000 : ℝ)|^35 ≤ (5442543772143/50000000000000 : ℝ)^27
        have hw : |(-361422033/2000000000 : ℝ)|=(361422033/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3687694283/10000000000 : ℝ)|^35 ≤ (13720059626993/50000000000000 : ℝ)^27
        have hw : |(3687694283/10000000000 : ℝ)|=(3687694283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-344392027/500000000 : ℝ)|^35 ≤ (30837396588849/50000000000000 : ℝ)^27
        have hw : |(-344392027/500000000 : ℝ)|=(344392027/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309060_s2_s2_8 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1975895419/5000000000 : ℝ)*x 0 + (-1453295237/10000000000 : ℝ)*x 1 + (-3448421407/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1975895419/5000000000 : ℝ)^35 ≤ (6002822288619/20000000000000 : ℝ)^27 := by
    have hnat : (1975895419 : ℕ)^35*20000000000000^27 ≤ 6002822288619^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1975895419 5000000000 6002822288619 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1453295237/10000000000 : ℝ)^35 ≤ (8206583608071/100000000000000 : ℝ)^27 := by
    have hnat : (1453295237 : ℕ)^35*100000000000000^27 ≤ 8206583608071^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1453295237 10000000000 8206583608071 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3448421407/5000000000 : ℝ)^35 ≤ (30889652471349/50000000000000 : ℝ)^27 := by
    have hnat : (3448421407 : ℕ)^35*50000000000000^27 ≤ 30889652471349^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3448421407 5000000000 30889652471349 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1975895419/5000000000 : ℝ), (-1453295237/10000000000 : ℝ), (-3448421407/5000000000 : ℝ)] ![(6002822288619/20000000000000 : ℝ), (8206583608071/100000000000000 : ℝ), (30889652471349/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1975895419/5000000000 : ℝ)|^35 ≤ (6002822288619/20000000000000 : ℝ)^27
        have hw : |(1975895419/5000000000 : ℝ)|=(1975895419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1453295237/10000000000 : ℝ)|^35 ≤ (8206583608071/100000000000000 : ℝ)^27
        have hw : |(-1453295237/10000000000 : ℝ)|=(1453295237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3448421407/5000000000 : ℝ)|^35 ≤ (30889652471349/50000000000000 : ℝ)^27
        have hw : |(-3448421407/5000000000 : ℝ)|=(3448421407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309060_s2_s2_9 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4205412451/10000000000 : ℝ)*x 0 + (171059653/250000000 : ℝ)*x 1 + (237547457/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4205412451/10000000000 : ℝ)^35 ≤ (8133631363673/25000000000000 : ℝ)^27 := by
    have hnat : (4205412451 : ℕ)^35*25000000000000^27 ≤ 8133631363673^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4205412451 10000000000 8133631363673 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (171059653/250000000 : ℝ)^35 ≤ (15286927378171/25000000000000 : ℝ)^27 := by
    have hnat : (171059653 : ℕ)^35*25000000000000^27 ≤ 15286927378171^27*250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171059653 250000000 15286927378171 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (237547457/2000000000 : ℝ)^35 ≤ (394860313257/6250000000000 : ℝ)^27 := by
    have hnat : (237547457 : ℕ)^35*6250000000000^27 ≤ 394860313257^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      237547457 2000000000 394860313257 6250000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4205412451/10000000000 : ℝ), (171059653/250000000 : ℝ), (237547457/2000000000 : ℝ)] ![(8133631363673/25000000000000 : ℝ), (15286927378171/25000000000000 : ℝ), (394860313257/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4205412451/10000000000 : ℝ)|^35 ≤ (8133631363673/25000000000000 : ℝ)^27
        have hw : |(4205412451/10000000000 : ℝ)|=(4205412451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(171059653/250000000 : ℝ)|^35 ≤ (15286927378171/25000000000000 : ℝ)^27
        have hw : |(171059653/250000000 : ℝ)|=(171059653/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(237547457/2000000000 : ℝ)|^35 ≤ (394860313257/6250000000000 : ℝ)^27
        have hw : |(237547457/2000000000 : ℝ)|=(237547457/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309060_s2_s2_13 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5907453143/10000000000 : ℝ)*x 0 + (5808559271/10000000000 : ℝ)*x 1 + (-1506861/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5907453143/10000000000 : ℝ)^35 ≤ (50543700699121/100000000000000 : ℝ)^27 := by
    have hnat : (5907453143 : ℕ)^35*100000000000000^27 ≤ 50543700699121^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5907453143 10000000000 50543700699121 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5808559271/10000000000 : ℝ)^35 ≤ (49449598930317/100000000000000 : ℝ)^27 := by
    have hnat : (5808559271 : ℕ)^35*100000000000000^27 ≤ 49449598930317^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5808559271 10000000000 49449598930317 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1506861/2500000000 : ℝ)^35 ≤ (6700366707/100000000000000 : ℝ)^27 := by
    have hnat : (1506861 : ℕ)^35*100000000000000^27 ≤ 6700366707^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1506861 2500000000 6700366707 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5907453143/10000000000 : ℝ), (5808559271/10000000000 : ℝ), (-1506861/2500000000 : ℝ)] ![(50543700699121/100000000000000 : ℝ), (49449598930317/100000000000000 : ℝ), (6700366707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5907453143/10000000000 : ℝ)|^35 ≤ (50543700699121/100000000000000 : ℝ)^27
        have hw : |(5907453143/10000000000 : ℝ)|=(5907453143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5808559271/10000000000 : ℝ)|^35 ≤ (49449598930317/100000000000000 : ℝ)^27
        have hw : |(5808559271/10000000000 : ℝ)|=(5808559271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1506861/2500000000 : ℝ)|^35 ≤ (6700366707/100000000000000 : ℝ)^27
        have hw : |(-1506861/2500000000 : ℝ)|=(1506861/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309060_s2_s2_14 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-24175173/200000000 : ℝ)*x 0 + (3885371717/10000000000 : ℝ)*x 1 + (-7102267157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (24175173/200000000 : ℝ)^35 ≤ (100985784057/1562500000000 : ℝ)^27 := by
    have hnat : (24175173 : ℕ)^35*1562500000000^27 ≤ 100985784057^27*200000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24175173 200000000 100985784057 1562500000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3885371717/10000000000 : ℝ)^35 ≤ (3670227457477/12500000000000 : ℝ)^27 := by
    have hnat : (3885371717 : ℕ)^35*12500000000000^27 ≤ 3670227457477^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3885371717 10000000000 3670227457477 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7102267157/10000000000 : ℝ)^35 ≤ (16043772537423/25000000000000 : ℝ)^27 := by
    have hnat : (7102267157 : ℕ)^35*25000000000000^27 ≤ 16043772537423^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7102267157 10000000000 16043772537423 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-24175173/200000000 : ℝ), (3885371717/10000000000 : ℝ), (-7102267157/10000000000 : ℝ)] ![(100985784057/1562500000000 : ℝ), (3670227457477/12500000000000 : ℝ), (16043772537423/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-24175173/200000000 : ℝ)|^35 ≤ (100985784057/1562500000000 : ℝ)^27
        have hw : |(-24175173/200000000 : ℝ)|=(24175173/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3885371717/10000000000 : ℝ)|^35 ≤ (3670227457477/12500000000000 : ℝ)^27
        have hw : |(3885371717/10000000000 : ℝ)|=(3885371717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7102267157/10000000000 : ℝ)|^35 ≤ (16043772537423/25000000000000 : ℝ)^27
        have hw : |(-7102267157/10000000000 : ℝ)|=(7102267157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309060_s2_s2_15 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (176354393/500000000 : ℝ)*x 0 + (-1668452223/10000000000 : ℝ)*x 1 + (-7111563037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (176354393/500000000 : ℝ)^35 ≤ (2529399573/9765625000 : ℝ)^27 := by
    have hnat : (176354393 : ℕ)^35*9765625000^27 ≤ 2529399573^27*500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      176354393 500000000 2529399573 9765625000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1668452223/10000000000 : ℝ)^35 ≤ (2453738263981/25000000000000 : ℝ)^27 := by
    have hnat : (1668452223 : ℕ)^35*25000000000000^27 ≤ 2453738263981^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1668452223 10000000000 2453738263981 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7111563037/10000000000 : ℝ)^35 ≤ (32141997653897/50000000000000 : ℝ)^27 := by
    have hnat : (7111563037 : ℕ)^35*50000000000000^27 ≤ 32141997653897^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7111563037 10000000000 32141997653897 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(176354393/500000000 : ℝ), (-1668452223/10000000000 : ℝ), (-7111563037/10000000000 : ℝ)] ![(2529399573/9765625000 : ℝ), (2453738263981/25000000000000 : ℝ), (32141997653897/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(176354393/500000000 : ℝ)|^35 ≤ (2529399573/9765625000 : ℝ)^27
        have hw : |(176354393/500000000 : ℝ)|=(176354393/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1668452223/10000000000 : ℝ)|^35 ≤ (2453738263981/25000000000000 : ℝ)^27
        have hw : |(-1668452223/10000000000 : ℝ)|=(1668452223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7111563037/10000000000 : ℝ)|^35 ≤ (32141997653897/50000000000000 : ℝ)^27
        have hw : |(-7111563037/10000000000 : ℝ)|=(7111563037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309060_s2_s2_16 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6016470917/10000000000 : ℝ)*x 0 + (1270455497/2500000000 : ℝ)*x 1 + (123722159/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6016470917/10000000000 : ℝ)^35 ≤ (10351221845279/20000000000000 : ℝ)^27 := by
    have hnat : (6016470917 : ℕ)^35*20000000000000^27 ≤ 10351221845279^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6016470917 10000000000 10351221845279 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1270455497/2500000000 : ℝ)^35 ≤ (41582835411117/100000000000000 : ℝ)^27 := by
    have hnat : (1270455497 : ℕ)^35*100000000000000^27 ≤ 41582835411117^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1270455497 2500000000 41582835411117 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (123722159/1000000000 : ℝ)^35 ≤ (416315959529/6250000000000 : ℝ)^27 := by
    have hnat : (123722159 : ℕ)^35*6250000000000^27 ≤ 416315959529^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      123722159 1000000000 416315959529 6250000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6016470917/10000000000 : ℝ), (1270455497/2500000000 : ℝ), (123722159/1000000000 : ℝ)] ![(10351221845279/20000000000000 : ℝ), (41582835411117/100000000000000 : ℝ), (416315959529/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6016470917/10000000000 : ℝ)|^35 ≤ (10351221845279/20000000000000 : ℝ)^27
        have hw : |(6016470917/10000000000 : ℝ)|=(6016470917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1270455497/2500000000 : ℝ)|^35 ≤ (41582835411117/100000000000000 : ℝ)^27
        have hw : |(1270455497/2500000000 : ℝ)|=(1270455497/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(123722159/1000000000 : ℝ)|^35 ≤ (416315959529/6250000000000 : ℝ)^27
        have hw : |(123722159/1000000000 : ℝ)|=(123722159/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309060_s2_s2_20 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1609386407/2000000000 : ℝ)*x 0 + (211244597/625000000 : ℝ)*x 1 + (-5923329/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1609386407/2000000000 : ℝ)^35 ≤ (75451686313599/100000000000000 : ℝ)^27 := by
    have hnat : (1609386407 : ℕ)^35*100000000000000^27 ≤ 75451686313599^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1609386407 2000000000 75451686313599 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (211244597/625000000 : ℝ)^35 ≤ (4901760185971/20000000000000 : ℝ)^27 := by
    have hnat : (211244597 : ℕ)^35*20000000000000^27 ≤ 4901760185971^27*625000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211244597 625000000 4901760185971 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5923329/2500000000 : ℝ)^35 ≤ (7902549127/20000000000000 : ℝ)^27 := by
    have hnat : (5923329 : ℕ)^35*20000000000000^27 ≤ 7902549127^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5923329 2500000000 7902549127 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1609386407/2000000000 : ℝ), (211244597/625000000 : ℝ), (-5923329/2500000000 : ℝ)] ![(75451686313599/100000000000000 : ℝ), (4901760185971/20000000000000 : ℝ), (7902549127/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1609386407/2000000000 : ℝ)|^35 ≤ (75451686313599/100000000000000 : ℝ)^27
        have hw : |(1609386407/2000000000 : ℝ)|=(1609386407/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(211244597/625000000 : ℝ)|^35 ≤ (4901760185971/20000000000000 : ℝ)^27
        have hw : |(211244597/625000000 : ℝ)|=(211244597/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5923329/2500000000 : ℝ)|^35 ≤ (7902549127/20000000000000 : ℝ)^27
        have hw : |(-5923329/2500000000 : ℝ)|=(5923329/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309060_s2_s2_21 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-197401959/2500000000 : ℝ)*x 0 + (1401958793/2500000000 : ℝ)*x 1 + (-2885367561/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (197401959/2500000000 : ℝ)^35 ≤ (1860752238367/50000000000000 : ℝ)^27 := by
    have hnat : (197401959 : ℕ)^35*50000000000000^27 ≤ 1860752238367^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197401959 2500000000 1860752238367 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1401958793/2500000000 : ℝ)^35 ≤ (47245908030757/100000000000000 : ℝ)^27 := by
    have hnat : (1401958793 : ℕ)^35*100000000000000^27 ≤ 47245908030757^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1401958793 2500000000 47245908030757 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2885367561/5000000000 : ℝ)^35 ≤ (49032587478943/100000000000000 : ℝ)^27 := by
    have hnat : (2885367561 : ℕ)^35*100000000000000^27 ≤ 49032587478943^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2885367561 5000000000 49032587478943 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-197401959/2500000000 : ℝ), (1401958793/2500000000 : ℝ), (-2885367561/5000000000 : ℝ)] ![(1860752238367/50000000000000 : ℝ), (47245908030757/100000000000000 : ℝ), (49032587478943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-197401959/2500000000 : ℝ)|^35 ≤ (1860752238367/50000000000000 : ℝ)^27
        have hw : |(-197401959/2500000000 : ℝ)|=(197401959/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1401958793/2500000000 : ℝ)|^35 ≤ (47245908030757/100000000000000 : ℝ)^27
        have hw : |(1401958793/2500000000 : ℝ)|=(1401958793/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2885367561/5000000000 : ℝ)|^35 ≤ (49032587478943/100000000000000 : ℝ)^27
        have hw : |(-2885367561/5000000000 : ℝ)|=(2885367561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309060_s2_s2_22 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1446254303/2500000000 : ℝ)*x 0 + (-981369621/10000000000 : ℝ)*x 1 + (-17131471/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1446254303/2500000000 : ℝ)^35 ≤ (49189952727277/100000000000000 : ℝ)^27 := by
    have hnat : (1446254303 : ℕ)^35*100000000000000^27 ≤ 49189952727277^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1446254303 2500000000 49189952727277 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (981369621/10000000000 : ℝ)^35 ≤ (4933059414937/100000000000000 : ℝ)^27 := by
    have hnat : (981369621 : ℕ)^35*100000000000000^27 ≤ 4933059414937^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      981369621 10000000000 4933059414937 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (17131471/31250000 : ℝ)^35 ≤ (45876987843727/100000000000000 : ℝ)^27 := by
    have hnat : (17131471 : ℕ)^35*100000000000000^27 ≤ 45876987843727^27*31250000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17131471 31250000 45876987843727 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1446254303/2500000000 : ℝ), (-981369621/10000000000 : ℝ), (-17131471/31250000 : ℝ)] ![(49189952727277/100000000000000 : ℝ), (4933059414937/100000000000000 : ℝ), (45876987843727/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1446254303/2500000000 : ℝ)|^35 ≤ (49189952727277/100000000000000 : ℝ)^27
        have hw : |(1446254303/2500000000 : ℝ)|=(1446254303/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-981369621/10000000000 : ℝ)|^35 ≤ (4933059414937/100000000000000 : ℝ)^27
        have hw : |(-981369621/10000000000 : ℝ)|=(981369621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-17131471/31250000 : ℝ)|^35 ≤ (45876987843727/100000000000000 : ℝ)^27
        have hw : |(-17131471/31250000 : ℝ)|=(17131471/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309060_s2_s2_23 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2054869551/5000000000 : ℝ)*x 0 + (842187387/1250000000 : ℝ)*x 1 + (1491357707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2054869551/5000000000 : ℝ)^35 ≤ (3157830723653/10000000000000 : ℝ)^27 := by
    have hnat : (2054869551 : ℕ)^35*10000000000000^27 ≤ 3157830723653^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2054869551 5000000000 3157830723653 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (842187387/1250000000 : ℝ)^35 ≤ (59935416248283/100000000000000 : ℝ)^27 := by
    have hnat : (842187387 : ℕ)^35*100000000000000^27 ≤ 59935416248283^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      842187387 1250000000 59935416248283 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1491357707/10000000000 : ℝ)^35 ≤ (8486276499461/100000000000000 : ℝ)^27 := by
    have hnat : (1491357707 : ℕ)^35*100000000000000^27 ≤ 8486276499461^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1491357707 10000000000 8486276499461 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2054869551/5000000000 : ℝ), (842187387/1250000000 : ℝ), (1491357707/10000000000 : ℝ)] ![(3157830723653/10000000000000 : ℝ), (59935416248283/100000000000000 : ℝ), (8486276499461/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2054869551/5000000000 : ℝ)|^35 ≤ (3157830723653/10000000000000 : ℝ)^27
        have hw : |(2054869551/5000000000 : ℝ)|=(2054869551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(842187387/1250000000 : ℝ)|^35 ≤ (59935416248283/100000000000000 : ℝ)^27
        have hw : |(842187387/1250000000 : ℝ)|=(842187387/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1491357707/10000000000 : ℝ)|^35 ≤ (8486276499461/100000000000000 : ℝ)^27
        have hw : |(1491357707/10000000000 : ℝ)|=(1491357707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309060_s2_s2_27 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (8492544643/10000000000 : ℝ)*x 0 + (1382041241/5000000000 : ℝ)*x 1 + (-42120323/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8492544643/10000000000 : ℝ)^35 ≤ (1618236559301/2000000000000 : ℝ)^27 := by
    have hnat : (8492544643 : ℕ)^35*2000000000000^27 ≤ 1618236559301^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8492544643 10000000000 1618236559301 2000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1382041241/5000000000 : ℝ)^35 ≤ (2360449104603/12500000000000 : ℝ)^27 := by
    have hnat : (1382041241 : ℕ)^35*12500000000000^27 ≤ 2360449104603^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1382041241 5000000000 2360449104603 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42120323/5000000000 : ℝ)^35 ≤ (40915837379/20000000000000 : ℝ)^27 := by
    have hnat : (42120323 : ℕ)^35*20000000000000^27 ≤ 40915837379^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42120323 5000000000 40915837379 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8492544643/10000000000 : ℝ), (1382041241/5000000000 : ℝ), (-42120323/5000000000 : ℝ)] ![(1618236559301/2000000000000 : ℝ), (2360449104603/12500000000000 : ℝ), (40915837379/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8492544643/10000000000 : ℝ)|^35 ≤ (1618236559301/2000000000000 : ℝ)^27
        have hw : |(8492544643/10000000000 : ℝ)|=(8492544643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1382041241/5000000000 : ℝ)|^35 ≤ (2360449104603/12500000000000 : ℝ)^27
        have hw : |(1382041241/5000000000 : ℝ)|=(1382041241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-42120323/5000000000 : ℝ)|^35 ≤ (40915837379/20000000000000 : ℝ)^27
        have hw : |(-42120323/5000000000 : ℝ)|=(42120323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c309060_s2 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev1 : (0 : ℝ) ≤ ((3201/4000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3201/4000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(80603/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(80603/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-17471/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-17471/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((60861/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(60861/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15993/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(15993/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-23649/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-23649/50000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (77509/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (77509/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (77509/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (77509/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (77509/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (77509/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (91323/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
  have s2_pow0 : (3201/4000 : ℝ) ^ (69/16 : ℝ) ≤ (9563145551696986099/25000000000000000000 : ℝ) := by
    have hpowers : (3201/4000 : ℝ)^69 ≤ (9563145551696986099/25000000000000000000 : ℝ)^16 := by
      have hnat : (3201 : ℕ)^69*25000000000000000000^16 ≤ 9563145551696986099^16*4000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3201 4000 9563145551696986099 25000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3201/4000 : ℝ)) (X := (9563145551696986099/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s2_corner0a : (34563145551696986099/25000000000000000000 : ℝ) ≤ (10780027889170581/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (34563145551696986099/25000000000000000000 : ℝ)^16 ≤ (10780027889170581/10000000000000000 : ℝ)^69 := by
      have hnat : (34563145551696986099 : ℕ)^16*10000000000000000^69 ≤ 10780027889170581^69*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        34563145551696986099 25000000000000000000 10780027889170581 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10780027889170581/10000000000000000 : ℝ)) (X := (34563145551696986099/25000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s2_corner0b : (22063145551696986099/12500000000000000000 : ℝ) ≤ (5704126070099859/5000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (22063145551696986099/12500000000000000000 : ℝ)^16 ≤ (5704126070099859/5000000000000000 : ℝ)^69 := by
      have hnat : (22063145551696986099 : ℕ)^16*5000000000000000^69 ≤ 5704126070099859^69*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22063145551696986099 12500000000000000000 5704126070099859 5000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5704126070099859/5000000000000000 : ℝ)) (X := (22063145551696986099/12500000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(780027889170581/8002500000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(209408083676379/2667500000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (3201/4000 : ℝ)) (alpha := (780027889170581/8002500000000000 : ℝ)) (beta := (209408083676379/2667500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (3201/4000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(780027889170581/8002500000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(209408083676379/2667500000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (80603/100000 : ℝ) ^ (69/16 : ℝ) ≤ (39458409645843090211/100000000000000000000 : ℝ) := by
    have hpowers : (80603/100000 : ℝ)^69 ≤ (39458409645843090211/100000000000000000000 : ℝ)^16 := by
      have hnat : (80603 : ℕ)^69*100000000000000000000^16 ≤ 39458409645843090211^16*100000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        80603 100000 39458409645843090211 100000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (80603/100000 : ℝ)) (X := (39458409645843090211/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s2_corner1a : (139458409645843090211/100000000000000000000 : ℝ) ≤ (10801757549501073/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (139458409645843090211/100000000000000000000 : ℝ)^16 ≤ (10801757549501073/10000000000000000 : ℝ)^69 := by
      have hnat : (139458409645843090211 : ℕ)^16*10000000000000000^69 ≤ 10801757549501073^69*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        139458409645843090211 100000000000000000000 10801757549501073 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10801757549501073/10000000000000000 : ℝ)) (X := (139458409645843090211/100000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s2_corner1b : (89458409645843090211/50000000000000000000 : ℝ) ≤ (11444208941330769/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (89458409645843090211/50000000000000000000 : ℝ)^16 ≤ (11444208941330769/10000000000000000 : ℝ)^69 := by
      have hnat : (89458409645843090211 : ℕ)^16*10000000000000000^69 ≤ 11444208941330769^69*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        89458409645843090211 50000000000000000000 11444208941330769 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11444208941330769/10000000000000000 : ℝ)) (X := (89458409645843090211/50000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(801757549501073/8060300000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(10038302997339/125942187500000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (80603/100000 : ℝ)) (alpha := (801757549501073/8060300000000000 : ℝ)) (beta := (10038302997339/125942187500000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (80603/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(801757549501073/8060300000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(10038302997339/125942187500000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (17471/25000 : ℝ) ^ (69/16 : ℝ) ≤ (21324510392722307751/100000000000000000000 : ℝ) := by
    have hpowers : (17471/25000 : ℝ)^69 ≤ (21324510392722307751/100000000000000000000 : ℝ)^16 := by
      have hnat : (17471 : ℕ)^69*100000000000000000000^16 ≤ 21324510392722307751^16*25000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17471 25000 21324510392722307751 100000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17471/25000 : ℝ)) (X := (21324510392722307751/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s2_corner2a : (121324510392722307751/100000000000000000000 : ℝ) ≤ (1307303255976003/1250000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (121324510392722307751/100000000000000000000 : ℝ)^16 ≤ (1307303255976003/1250000000000000 : ℝ)^69 := by
      have hnat : (121324510392722307751 : ℕ)^16*1250000000000000^69 ≤ 1307303255976003^69*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        121324510392722307751 100000000000000000000 1307303255976003 1250000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1307303255976003/1250000000000000 : ℝ)) (X := (121324510392722307751/100000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s2_corner2b : (71324510392722307751/50000000000000000000 : ℝ) ≤ (10858565968852783/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (71324510392722307751/50000000000000000000 : ℝ)^16 ≤ (10858565968852783/10000000000000000 : ℝ)^69 := by
      have hnat : (71324510392722307751 : ℕ)^16*10000000000000000^69 ≤ 10858565968852783^69*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        71324510392722307751 50000000000000000000 10858565968852783 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10858565968852783/10000000000000000 : ℝ)) (X := (71324510392722307751/50000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(57303255976003/873550000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(400139921044759/6988400000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (17471/25000 : ℝ)) (alpha := (57303255976003/873550000000000 : ℝ)) (beta := (400139921044759/6988400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (17471/25000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(57303255976003/873550000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(400139921044759/6988400000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-497980713/2500000000 : ℝ)*X 0 0+(4251712381/10000000000 : ℝ)*X 0 1+(-627444067/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309060_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((4714348141/10000000000 : ℝ)*X 2 0+(238286793/400000000 : ℝ)*X 2 1+(922174131/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309060_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-361422033/2000000000 : ℝ)*X 0 0+(3687694283/10000000000 : ℝ)*X 0 1+(-344392027/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309060_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((1975895419/5000000000 : ℝ)*X 1 0+(-1453295237/10000000000 : ℝ)*X 1 1+(-3448421407/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309060_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((4205412451/10000000000 : ℝ)*X 2 0+(171059653/250000000 : ℝ)*X 2 1+(237547457/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309060_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((5907453143/10000000000 : ℝ)*X 0 0+(5808559271/10000000000 : ℝ)*X 0 1+(-1506861/2500000000 : ℝ)*X 0 2+(5907453143/10000000000 : ℝ)*X 1 0+(5808559271/10000000000 : ℝ)*X 1 1+(-1506861/2500000000 : ℝ)*X 1 2+(5907453143/10000000000 : ℝ)*X 2 0+(5808559271/10000000000 : ℝ)*X 2 1+(-1506861/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309060_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-24175173/200000000 : ℝ)*X 0 0+(3885371717/10000000000 : ℝ)*X 0 1+(-7102267157/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309060_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((176354393/500000000 : ℝ)*X 1 0+(-1668452223/10000000000 : ℝ)*X 1 1+(-7111563037/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309060_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((6016470917/10000000000 : ℝ)*X 2 0+(1270455497/2500000000 : ℝ)*X 2 1+(123722159/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309060_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((1609386407/2000000000 : ℝ)*X 0 0+(211244597/625000000 : ℝ)*X 0 1+(-5923329/2500000000 : ℝ)*X 0 2+(1609386407/2000000000 : ℝ)*X 1 0+(211244597/625000000 : ℝ)*X 1 1+(-5923329/2500000000 : ℝ)*X 1 2+(1609386407/2000000000 : ℝ)*X 2 0+(211244597/625000000 : ℝ)*X 2 1+(-5923329/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309060_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-197401959/2500000000 : ℝ)*X 0 0+(1401958793/2500000000 : ℝ)*X 0 1+(-2885367561/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309060_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((1446254303/2500000000 : ℝ)*X 1 0+(-981369621/10000000000 : ℝ)*X 1 1+(-17131471/31250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309060_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((2054869551/5000000000 : ℝ)*X 2 0+(842187387/1250000000 : ℝ)*X 2 1+(1491357707/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309060_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((8492544643/10000000000 : ℝ)*X 0 0+(1382041241/5000000000 : ℝ)*X 0 1+(-42120323/5000000000 : ℝ)*X 0 2+(8492544643/10000000000 : ℝ)*X 1 0+(1382041241/5000000000 : ℝ)*X 1 1+(-42120323/5000000000 : ℝ)*X 1 2+(8492544643/10000000000 : ℝ)*X 2 0+(1382041241/5000000000 : ℝ)*X 2 1+(-42120323/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309060_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((60861/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(60861/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (72755552730021429030489686004561/3756413547177500000000000000000000000 : ℝ) := by norm_num
    linear_combination (277869653801/1000000000000 : ℝ)*(base7) + (9851/500000000000 : ℝ)*(base39) + (3664246959/15625000000 : ℝ)*(base59) + (2315450098989/500000000000 : ℝ)*(major_s2_0) + (2315450098989/500000000000 : ℝ)*(major_s2_1) + (2315450098989/500000000000 : ℝ)*(major_s2_2) + (9166237/500000000000 : ℝ)*(sp_s2_0) + (309224362499/50000000000 : ℝ)*(sp_s2_7) + (6184585098747/1000000000000 : ℝ)*(sp_s2_8) + (1236922593779/200000000000 : ℝ)*(sp_s2_9) + (637173608993/200000000000 : ℝ)*(sp_s2_13) + (117363587/1000000000000 : ℝ)*(sp_s2_14) + (18923647/500000000000 : ℝ)*(sp_s2_15) + (4988573/500000000000 : ℝ)*(sp_s2_23) + (581599678233/200000000000 : ℝ)*(f.failure) + (6184622946041/1000000000000 : ℝ)*(f.sum) + (3077285294134777421/17602687662500000000000000000000 : ℝ)*base63 + (277090378138411/3494200000000000000000000000 : ℝ)*base64 + (1108823605349671/4030150000000000000000000000 : ℝ)*base66 + (353468035128479/873550000000000000000000000 : ℝ)*base69 + (28343362985166451973/93207785000000000000000000000000 : ℝ)*base70 + (714458179227669/1333750000000000000000000000 : ℝ)*base72 + (1710899462576217/4030150000000000000000000000 : ℝ)*base75 + (300694417833539/666875000000000000000000000 : ℝ)*base77 + (5948645398392176833/26876062812500000000000000000000 : ℝ)*base78 + (10551/20000000000000000 : ℝ)*base87 + (10551/20000000000000000 : ℝ)*base89 + (10551/20000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15993/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(15993/25000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (66273510017070257321722626942971/3756413547177500000000000000000000000 : ℝ) := by norm_num
    linear_combination (22463733017/50000000000 : ℝ)*(base7) + (1138589/500000000000 : ℝ)*(base39) + (2795297/1000000000000 : ℝ)*(base59) + (1735728992233/500000000000 : ℝ)*(major_s2_0) + (1735728992233/500000000000 : ℝ)*(major_s2_1) + (1735728992233/500000000000 : ℝ)*(major_s2_2) + (583633/20000000000 : ℝ)*(sp_s2_0) + (7667991/200000000000 : ℝ)*(sp_s2_2) + (28245391/125000000000 : ℝ)*(sp_s2_8) + (4489433016543/1000000000000 : ℝ)*(sp_s2_14) + (2244618117533/500000000000 : ℝ)*(sp_s2_15) + (4489423858239/1000000000000 : ℝ)*(sp_s2_16) + (2629164924493/1000000000000 : ℝ)*(sp_s2_20) + (604539/20000000000 : ℝ)*(sp_s2_27) + (2179920491103/1000000000000 : ℝ)*(f.failure) + (4489462198193/1000000000000 : ℝ)*(f.sum) + (20922556672691101421/35205375325000000000000000000000 : ℝ)*base62 + (1495269137936987/3494200000000000000000000000 : ℝ)*base64 + (1121721699698247/4030150000000000000000000000 : ℝ)*base66 + (631272919609397/873550000000000000000000000 : ℝ)*base68 + (144172990032838827443/279623355000000000000000000000000 : ℝ)*base70 + (577041026836057/1333750000000000000000000000 : ℝ)*base73 + (839800769341709/1007537500000000000000000000 : ℝ)*base74 + (1002916136554001/2000625000000000000000000000 : ℝ)*base76 + (5254349259559572979/107504251250000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (79441/100000000000000000 : ℝ)*base87 + (79441/100000000000000000 : ℝ)*base89 + (79441/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-23649/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-23649/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (10113727648713955077611937811857/1878206773588750000000000000000000000 : ℝ) := by norm_num
    linear_combination (14589562879/1000000000000 : ℝ)*(base7) + (1292059/200000000000 : ℝ)*(base11) + (30941413331/200000000000 : ℝ)*(base39) + (3797442120497/1000000000000 : ℝ)*(major_s2_0) + (3797442120497/1000000000000 : ℝ)*(major_s2_1) + (3797442120497/1000000000000 : ℝ)*(major_s2_2) + (162501/10000000000 : ℝ)*(sp_s2_0) + (1081323/500000000000 : ℝ)*(sp_s2_8) + (98572341/1000000000000 : ℝ)*(sp_s2_9) + (1610991/500000000000 : ℝ)*(sp_s2_20) + (2600676678083/500000000000 : ℝ)*(sp_s2_21) + (1300343475979/250000000000 : ℝ)*(sp_s2_22) + (260063874711/50000000000 : ℝ)*(sp_s2_23) + (299901287841/125000000000 : ℝ)*(sp_s2_27) + (2384623961831/1000000000000 : ℝ)*(f.failure) + (5201376066561/1000000000000 : ℝ)*(f.sum) + (48897863084002012243/140821501300000000000000000000000 : ℝ)*base62 + (1515176024024697/6988400000000000000000000000 : ℝ)*base65 + (658335223861691/1007537500000000000000000000 : ℝ)*base66 + (233746317034479/873550000000000000000000000 : ℝ)*base68 + (2064914284755598387/559246710000000000000000000000000 : ℝ)*base70 + (794908303962637/2667500000000000000000000000 : ℝ)*base72 + (1463397547932131/8060300000000000000000000000 : ℝ)*base75 + (3801901478748757/8002500000000000000000000000 : ℝ)*base77 + (75225310465444374761/215008502500000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (1257/100000000000000000 : ℝ)*base87 + (1257/100000000000000000 : ℝ)*base89 + (1257/100000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev1 : (0 : ℝ) ≤ ((3201/4000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3201/4000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(80603/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(80603/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-17471/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-17471/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((60861/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(60861/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15993/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(15993/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-23649/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-23649/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c309060_s2 p hpa hpb X hX hprev1

#print axioms solution
