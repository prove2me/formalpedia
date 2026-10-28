-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1096_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:58:51.103003+00:00
-- url     : https://prove2.me/submissions/bb802e46-15c1-43c5-912d-f5466b9e297d

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_majorant
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
theorem frame_box_of_interval_base {p k A d ell u v w rho lo : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      (∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) →
      -u ≤ X 0 0 ∧ X 0 0 ≤ -ell ∧ v ≤ X 0 1 ∧ X 0 1 ≤ w)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) :
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
    · intro i j hij
      rw [pair_relabel]
      exact hlower (e i) (e j) (e.injective.ne hij)
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

theorem frame_interval_of_base {p k A d rho lo R L : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      (∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) →
      L*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ R*pair X 0 0)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → L*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ R*pair X i i := by
  have permuted (e : Equiv.Perm (Fin 3)) :
      L*pair X (e 0) (e 0) ≤ pair X (e 0) (e 1) ∧
        pair X (e 0) (e 1) ≤ R*pair X (e 0) (e 0) := by
    have hh := base (relabel e X) (frame_relabel hX e)
      (fun i j hij => by rw [pair_relabel];exact hsign (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hratio (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hlower (e i) (e j) (e.injective.ne hij))
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


theorem rectangle_pair_majorant {p a lo hi c alpha : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hlo : 0 ≤ lo) (hlohi : lo < hi) (hhi : hi ≤ 1) (halpha : 0 ≤ alpha)
    (hc : 1 ≤ c+2*alpha*lo)
    (hcorner00 : 1+2*lo^a ≤ (c+2*alpha*lo)^a)
    (hcorner10 : 1+hi^a+lo^a ≤ (c+alpha*(hi+lo))^a)
    (hcorner11 : 1+2*hi^a ≤ (c+2*alpha*hi)^a)
    (X : Fin 3 → Fin 3 → ℝ)
    (hmain : ∀ i, 0 ≤ pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h)
    (hupper : ∀ i h, i ≠ h → |pair X i h| ≤ hi*pair X i i)
    (i j l : Fin 3) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    lpNorm p (pair X i) ≤ c*pair X i i+alpha*(pair X i j+pair X i l) := by
  have hh := rectangle_majorant hp ha hap hlo hlohi hhi halpha hc hcorner00 hcorner10 hcorner11
    (hmain i) (hlower i j hij) ((le_abs_self _).trans (hupper i j hij))
    (hlower i l hil) ((le_abs_self _).trans (hupper i l hil))
  have he : lpNorm p (pair X i) =
      (|pair X i i|^p+|pair X i j|^p+|pair X i l|^p)^(1/p) := by
    simp only [lpNorm,Real.norm_eq_abs]
    congr 1
    fin_cases i <;> fin_cases j <;> fin_cases l <;> try contradiction
    all_goals simp [Fin.sum_univ_three] <;> ring
  rw [he]
  exact hh

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
theorem support_rectangle_w1096_s3_0 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1092367159/5000000000 : ℝ)*x 0 + (543411113/1000000000 : ℝ)*x 1 + (2613776741/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1092367159/5000000000 : ℝ)^8289 ≤ (13262353928623/100000000000000 : ℝ)^6241 := by
    have hnat : (1092367159 : ℕ)^8289*100000000000000^6241 ≤ 13262353928623^6241*5000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092367159 5000000000 13262353928623 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (543411113/1000000000 : ℝ)^8289 ≤ (347536398137/781250000000 : ℝ)^6241 := by
    have hnat : (543411113 : ℕ)^8289*781250000000^6241 ≤ 347536398137^6241*1000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543411113 1000000000 347536398137 781250000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2613776741/5000000000 : ℝ)^8289 ≤ (42252987093757/100000000000000 : ℝ)^6241 := by
    have hnat : (2613776741 : ℕ)^8289*100000000000000^6241 ≤ 42252987093757^6241*5000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613776741 5000000000 42252987093757 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1092367159/5000000000 : ℝ), (543411113/1000000000 : ℝ), (2613776741/5000000000 : ℝ)] ![(13262353928623/100000000000000 : ℝ), (347536398137/781250000000 : ℝ), (42252987093757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1092367159/5000000000 : ℝ)|^8289 ≤ (13262353928623/100000000000000 : ℝ)^6241
        have hw : |(-1092367159/5000000000 : ℝ)|=(1092367159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(543411113/1000000000 : ℝ)|^8289 ≤ (347536398137/781250000000 : ℝ)^6241
        have hw : |(543411113/1000000000 : ℝ)|=(543411113/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2613776741/5000000000 : ℝ)|^8289 ≤ (42252987093757/100000000000000 : ℝ)^6241
        have hw : |(2613776741/5000000000 : ℝ)|=(2613776741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s3_1 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (669365809/1250000000 : ℝ)*x 0 + (-286303809/1250000000 : ℝ)*x 1 + (5227553697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669365809/1250000000 : ℝ)^8289 ≤ (10906447086677/25000000000000 : ℝ)^6241 := by
    have hnat : (669365809 : ℕ)^8289*25000000000000^6241 ≤ 10906447086677^6241*1250000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669365809 1250000000 10906447086677 25000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (286303809/1250000000 : ℝ)^8289 ≤ (7060611118867/50000000000000 : ℝ)^6241 := by
    have hnat : (286303809 : ℕ)^8289*50000000000000^6241 ≤ 7060611118867^6241*1250000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      286303809 1250000000 7060611118867 50000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5227553697/10000000000 : ℝ)^8289 ≤ (2640811837613/6250000000000 : ℝ)^6241 := by
    have hnat : (5227553697 : ℕ)^8289*6250000000000^6241 ≤ 2640811837613^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227553697 10000000000 2640811837613 6250000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669365809/1250000000 : ℝ), (-286303809/1250000000 : ℝ), (5227553697/10000000000 : ℝ)] ![(10906447086677/25000000000000 : ℝ), (7060611118867/50000000000000 : ℝ), (2640811837613/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669365809/1250000000 : ℝ)|^8289 ≤ (10906447086677/25000000000000 : ℝ)^6241
        have hw : |(669365809/1250000000 : ℝ)|=(669365809/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-286303809/1250000000 : ℝ)|^8289 ≤ (7060611118867/50000000000000 : ℝ)^6241
        have hw : |(-286303809/1250000000 : ℝ)|=(286303809/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5227553697/10000000000 : ℝ)|^8289 ≤ (2640811837613/6250000000000 : ℝ)^6241
        have hw : |(5227553697/10000000000 : ℝ)|=(5227553697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s3_2 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1338731657/2500000000 : ℝ)*x 0 + (5227553793/10000000000 : ℝ)*x 1 + (-114521507/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338731657/2500000000 : ℝ)^8289 ≤ (43625790034669/100000000000000 : ℝ)^6241 := by
    have hnat : (1338731657 : ℕ)^8289*100000000000000^6241 ≤ 43625790034669^6241*2500000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338731657 2500000000 43625790034669 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5227553793/10000000000 : ℝ)^8289 ≤ (42252990432379/100000000000000 : ℝ)^6241 := by
    have hnat : (5227553793 : ℕ)^8289*100000000000000^6241 ≤ 42252990432379^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227553793 10000000000 42252990432379 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (114521507/500000000 : ℝ)^8289 ≤ (353030487979/2500000000000 : ℝ)^6241 := by
    have hnat : (114521507 : ℕ)^8289*2500000000000^6241 ≤ 353030487979^6241*500000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114521507 500000000 353030487979 2500000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338731657/2500000000 : ℝ), (5227553793/10000000000 : ℝ), (-114521507/500000000 : ℝ)] ![(43625790034669/100000000000000 : ℝ), (42252990432379/100000000000000 : ℝ), (353030487979/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338731657/2500000000 : ℝ)|^8289 ≤ (43625790034669/100000000000000 : ℝ)^6241
        have hw : |(1338731657/2500000000 : ℝ)|=(1338731657/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5227553793/10000000000 : ℝ)|^8289 ≤ (42252990432379/100000000000000 : ℝ)^6241
        have hw : |(5227553793/10000000000 : ℝ)|=(5227553793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-114521507/500000000 : ℝ)|^8289 ≤ (353030487979/2500000000000 : ℝ)^6241
        have hw : |(-114521507/500000000 : ℝ)|=(114521507/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s3_3 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4368621521/10000000000 : ℝ)*x 0 + (2084884829/5000000000 : ℝ)*x 1 + (2288502533/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4368621521/10000000000 : ℝ)^8289 ≤ (33290669498257/100000000000000 : ℝ)^6241 := by
    have hnat : (4368621521 : ℕ)^8289*100000000000000^6241 ≤ 33290669498257^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4368621521 10000000000 33290669498257 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2084884829/5000000000 : ℝ)^8289 ≤ (15646632363673/50000000000000 : ℝ)^6241 := by
    have hnat : (2084884829 : ℕ)^8289*50000000000000^6241 ≤ 15646632363673^6241*5000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084884829 5000000000 15646632363673 50000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2288502533/5000000000 : ℝ)^8289 ≤ (35416065752161/100000000000000 : ℝ)^6241 := by
    have hnat : (2288502533 : ℕ)^8289*100000000000000^6241 ≤ 35416065752161^6241*5000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2288502533 5000000000 35416065752161 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4368621521/10000000000 : ℝ), (2084884829/5000000000 : ℝ), (2288502533/5000000000 : ℝ)] ![(33290669498257/100000000000000 : ℝ), (15646632363673/50000000000000 : ℝ), (35416065752161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4368621521/10000000000 : ℝ)|^8289 ≤ (33290669498257/100000000000000 : ℝ)^6241
        have hw : |(4368621521/10000000000 : ℝ)|=(4368621521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2084884829/5000000000 : ℝ)|^8289 ≤ (15646632363673/50000000000000 : ℝ)^6241
        have hw : |(2084884829/5000000000 : ℝ)|=(2084884829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2288502533/5000000000 : ℝ)|^8289 ≤ (35416065752161/100000000000000 : ℝ)^6241
        have hw : |(2288502533/5000000000 : ℝ)|=(2288502533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s3_4 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-436951049/2000000000 : ℝ)*x 0 + (2614190877/5000000000 : ℝ)*x 1 + (1358319441/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (436951049/2000000000 : ℝ)^8289 ≤ (3315630663227/25000000000000 : ℝ)^6241 := by
    have hnat : (436951049 : ℕ)^8289*25000000000000^6241 ≤ 3315630663227^6241*2000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436951049 2000000000 3315630663227 25000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2614190877/5000000000 : ℝ)^8289 ≤ (21130939461963/50000000000000 : ℝ)^6241 := by
    have hnat : (2614190877 : ℕ)^8289*50000000000000^6241 ≤ 21130939461963^6241*5000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614190877 5000000000 21130939461963 50000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1358319441/2500000000 : ℝ)^8289 ≤ (44475598411641/100000000000000 : ℝ)^6241 := by
    have hnat : (1358319441 : ℕ)^8289*100000000000000^6241 ≤ 44475598411641^6241*2500000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358319441 2500000000 44475598411641 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-436951049/2000000000 : ℝ), (2614190877/5000000000 : ℝ), (1358319441/2500000000 : ℝ)] ![(3315630663227/25000000000000 : ℝ), (21130939461963/50000000000000 : ℝ), (44475598411641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-436951049/2000000000 : ℝ)|^8289 ≤ (3315630663227/25000000000000 : ℝ)^6241
        have hw : |(-436951049/2000000000 : ℝ)|=(436951049/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2614190877/5000000000 : ℝ)|^8289 ≤ (21130939461963/50000000000000 : ℝ)^6241
        have hw : |(2614190877/5000000000 : ℝ)|=(2614190877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1358319441/2500000000 : ℝ)|^8289 ≤ (44475598411641/100000000000000 : ℝ)^6241
        have hw : |(1358319441/2500000000 : ℝ)|=(1358319441/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s3_5 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5302774973/10000000000 : ℝ)*x 0 + (-521176653/2500000000 : ℝ)*x 1 + (339579863/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302774973/10000000000 : ℝ)^8289 ≤ (43062399198463/100000000000000 : ℝ)^6241 := by
    have hnat : (5302774973 : ℕ)^8289*100000000000000^6241 ≤ 43062399198463^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302774973 10000000000 43062399198463 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (521176653/2500000000 : ℝ)^8289 ≤ (6231000944773/50000000000000 : ℝ)^6241 := by
    have hnat : (521176653 : ℕ)^8289*50000000000000^6241 ≤ 6231000944773^6241*2500000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521176653 2500000000 6231000944773 50000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (339579863/625000000 : ℝ)^8289 ≤ (44475598890007/100000000000000 : ℝ)^6241 := by
    have hnat : (339579863 : ℕ)^8289*100000000000000^6241 ≤ 44475598890007^6241*625000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339579863 625000000 44475598890007 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302774973/10000000000 : ℝ), (-521176653/2500000000 : ℝ), (339579863/625000000 : ℝ)] ![(43062399198463/100000000000000 : ℝ), (6231000944773/50000000000000 : ℝ), (44475598890007/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302774973/10000000000 : ℝ)|^8289 ≤ (43062399198463/100000000000000 : ℝ)^6241
        have hw : |(5302774973/10000000000 : ℝ)|=(5302774973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-521176653/2500000000 : ℝ)|^8289 ≤ (6231000944773/50000000000000 : ℝ)^6241
        have hw : |(-521176653/2500000000 : ℝ)|=(521176653/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(339579863/625000000 : ℝ)|^8289 ≤ (44475598890007/100000000000000 : ℝ)^6241
        have hw : |(339579863/625000000 : ℝ)|=(339579863/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s3_6 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2651387733/5000000000 : ℝ)*x 0 + (5433278121/10000000000 : ℝ)*x 1 + (-1042352757/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651387733/5000000000 : ℝ)^8289 ≤ (10765601128937/25000000000000 : ℝ)^6241 := by
    have hnat : (2651387733 : ℕ)^8289*25000000000000^6241 ≤ 10765601128937^6241*5000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651387733 5000000000 10765601128937 25000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5433278121/10000000000 : ℝ)^8289 ≤ (44475602292931/100000000000000 : ℝ)^6241 := by
    have hnat : (5433278121 : ℕ)^8289*100000000000000^6241 ≤ 44475602292931^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433278121 10000000000 44475602292931 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1042352757/5000000000 : ℝ)^8289 ≤ (12461993172023/100000000000000 : ℝ)^6241 := by
    have hnat : (1042352757 : ℕ)^8289*100000000000000^6241 ≤ 12461993172023^6241*5000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042352757 5000000000 12461993172023 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651387733/5000000000 : ℝ), (5433278121/10000000000 : ℝ), (-1042352757/5000000000 : ℝ)] ![(10765601128937/25000000000000 : ℝ), (44475602292931/100000000000000 : ℝ), (12461993172023/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651387733/5000000000 : ℝ)|^8289 ≤ (10765601128937/25000000000000 : ℝ)^6241
        have hw : |(2651387733/5000000000 : ℝ)|=(2651387733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5433278121/10000000000 : ℝ)|^8289 ≤ (44475602292931/100000000000000 : ℝ)^6241
        have hw : |(5433278121/10000000000 : ℝ)|=(5433278121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1042352757/5000000000 : ℝ)|^8289 ≤ (12461993172023/100000000000000 : ℝ)^6241
        have hw : |(-1042352757/5000000000 : ℝ)|=(1042352757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s3_7 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1092165349/2500000000 : ℝ)*x 0 + (571921617/1250000000 : ℝ)*x 1 + (2085705887/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1092165349/2500000000 : ℝ)^8289 ≤ (3329107307619/10000000000000 : ℝ)^6241 := by
    have hnat : (1092165349 : ℕ)^8289*10000000000000^6241 ≤ 3329107307619^6241*2500000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092165349 2500000000 3329107307619 10000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (571921617/1250000000 : ℝ)^8289 ≤ (35399293313431/100000000000000 : ℝ)^6241 := by
    have hnat : (571921617 : ℕ)^8289*100000000000000^6241 ≤ 35399293313431^6241*1250000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      571921617 1250000000 35399293313431 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2085705887/5000000000 : ℝ)^8289 ≤ (7827408398943/25000000000000 : ℝ)^6241 := by
    have hnat : (2085705887 : ℕ)^8289*25000000000000^6241 ≤ 7827408398943^6241*5000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085705887 5000000000 7827408398943 25000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1092165349/2500000000 : ℝ), (571921617/1250000000 : ℝ), (2085705887/5000000000 : ℝ)] ![(3329107307619/10000000000000 : ℝ), (35399293313431/100000000000000 : ℝ), (7827408398943/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1092165349/2500000000 : ℝ)|^8289 ≤ (3329107307619/10000000000000 : ℝ)^6241
        have hw : |(1092165349/2500000000 : ℝ)|=(1092165349/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(571921617/1250000000 : ℝ)|^8289 ≤ (35399293313431/100000000000000 : ℝ)^6241
        have hw : |(571921617/1250000000 : ℝ)|=(571921617/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2085705887/5000000000 : ℝ)|^8289 ≤ (7827408398943/25000000000000 : ℝ)^6241
        have hw : |(2085705887/5000000000 : ℝ)|=(2085705887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1096_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37144247/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4161/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8857/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5247/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (929/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4161/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8857/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4161/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8857/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4161/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8857/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4161/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8857/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4161/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8857/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4161/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8857/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (8857/100000 : ℝ) ^ (259/64 : ℝ) ≤ (5492886688853973/100000000000000000000 : ℝ) := by
    have hpowers : (8857/100000 : ℝ)^259 ≤ (5492886688853973/100000000000000000000 : ℝ)^64 := by
      have hnat : (8857 : ℕ)^259*100000000000000000000^64 ≤ 5492886688853973^64*100000^259 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8857 100000 5492886688853973 100000000000000000000 259 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8857/100000 : ℝ)) (X := (5492886688853973/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 259 64 (by norm_num) hpowers
    exact h
  have hpowhi : (4161/25000 : ℝ) ^ (259/64 : ℝ) ≤ (6890128584821/9765625000000000 : ℝ) := by
    have hpowers : (4161/25000 : ℝ)^259 ≤ (6890128584821/9765625000000000 : ℝ)^64 := by
      have hnat : (4161 : ℕ)^259*9765625000000000^64 ≤ 6890128584821^64*25000^259 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4161 25000 6890128584821 9765625000000000 259 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4161/25000 : ℝ)) (X := (6890128584821/9765625000000000 : ℝ)) (by norm_num) (by norm_num) 259 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005492886688853973/50000000000000000000 : ℝ) ≤ (5000135725950053/5000000000000000 : ℝ) ^ (259/64 : ℝ) := by
    have hpowers : (50005492886688853973/50000000000000000000 : ℝ)^64 ≤ (5000135725950053/5000000000000000 : ℝ)^259 := by
      have hnat : (50005492886688853973 : ℕ)^64*5000000000000000^259 ≤ 5000135725950053^259*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005492886688853973 50000000000000000000 5000135725950053 5000000000000000 64 259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000135725950053/5000000000000000 : ℝ)) (X := (50005492886688853973/50000000000000000000 : ℝ)) (by norm_num) 259 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (100076047803397421013/100000000000000000000 : ℝ) ≤ (1000187863578873/1000000000000000 : ℝ) ^ (259/64 : ℝ) := by
    have hpowers : (100076047803397421013/100000000000000000000 : ℝ)^64 ≤ (1000187863578873/1000000000000000 : ℝ)^259 := by
      have hnat : (100076047803397421013 : ℕ)^64*1000000000000000^259 ≤ 1000187863578873^259*100000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100076047803397421013 100000000000000000000 1000187863578873 1000000000000000 64 259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000187863578873/1000000000000000 : ℝ)) (X := (100076047803397421013/100000000000000000000 : ℝ)) (by norm_num) 259 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (4889702628584821/4882812500000000 : ℝ) ≤ (5001742909838677/5000000000000000 : ℝ) ^ (259/64 : ℝ) := by
    have hpowers : (4889702628584821/4882812500000000 : ℝ)^64 ≤ (5001742909838677/5000000000000000 : ℝ)^259 := by
      have hnat : (4889702628584821 : ℕ)^64*5000000000000000^259 ≤ 5001742909838677^259*4882812500000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4889702628584821 4882812500000000 5001742909838677 5000000000000000 64 259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001742909838677/5000000000000000 : ℝ)) (X := (4889702628584821/4882812500000000 : ℝ)) (by norm_num) 259 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5492886688853973/100000000000000000000 : ℝ) ≤ ((38921822070271519943/38935000000000000000 : ℝ)+2*(100448993039/48668750000000 : ℝ)*(8857/100000 : ℝ))^(259/64 : ℝ) := by
    rw [show (38921822070271519943/38935000000000000000 : ℝ)+2*(100448993039/48668750000000 : ℝ)*(8857/100000 : ℝ)=(5000135725950053/5000000000000000 : ℝ) by norm_num, show 1+2*(5492886688853973/100000000000000000000 : ℝ)=(50005492886688853973/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6890128584821/9765625000000000 : ℝ)+(5492886688853973/100000000000000000000 : ℝ) ≤ ((38921822070271519943/38935000000000000000 : ℝ)+(100448993039/48668750000000 : ℝ)*((4161/25000 : ℝ)+(8857/100000 : ℝ)))^(259/64 : ℝ) := by
    rw [show (38921822070271519943/38935000000000000000 : ℝ)+(100448993039/48668750000000 : ℝ)*((4161/25000 : ℝ)+(8857/100000 : ℝ))=(1000187863578873/1000000000000000 : ℝ) by norm_num, show 1+(6890128584821/9765625000000000 : ℝ)+(5492886688853973/100000000000000000000 : ℝ)=(100076047803397421013/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6890128584821/9765625000000000 : ℝ) ≤ ((38921822070271519943/38935000000000000000 : ℝ)+2*(100448993039/48668750000000 : ℝ)*(4161/25000 : ℝ))^(259/64 : ℝ) := by
    rw [show (38921822070271519943/38935000000000000000 : ℝ)+2*(100448993039/48668750000000 : ℝ)*(4161/25000 : ℝ)=(5001742909838677/5000000000000000 : ℝ) by norm_num, show 1+2*(6890128584821/9765625000000000 : ℝ)=(4889702628584821/4882812500000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (38921822070271519943/38935000000000000000 : ℝ)*(X 1 0+X 2 0)+(100448993039/48668750000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (259/64 : ℝ)) (lo := (8857/100000 : ℝ)) (hi := (4161/25000 : ℝ)) (c := (38921822070271519943/38935000000000000000 : ℝ)) (alpha := (100448993039/48668750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (38921822070271519943/38935000000000000000 : ℝ)*(X 0 1+X 2 1)+(100448993039/48668750000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (259/64 : ℝ)) (lo := (8857/100000 : ℝ)) (hi := (4161/25000 : ℝ)) (c := (38921822070271519943/38935000000000000000 : ℝ)) (alpha := (100448993039/48668750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (38921822070271519943/38935000000000000000 : ℝ)*(X 0 2+X 1 2)+(100448993039/48668750000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (259/64 : ℝ)) (lo := (8857/100000 : ℝ)) (hi := (4161/25000 : ℝ)) (c := (38921822070271519943/38935000000000000000 : ℝ)) (alpha := (100448993039/48668750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1092367159/5000000000 : ℝ)*X 0 0+(543411113/1000000000 : ℝ)*X 0 1+(2613776741/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((669365809/1250000000 : ℝ)*X 1 0+(-286303809/1250000000 : ℝ)*X 1 1+(5227553697/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338731657/2500000000 : ℝ)*X 2 0+(5227553793/10000000000 : ℝ)*X 2 1+(-114521507/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4368621521/10000000000 : ℝ)*X 0 0+(2084884829/5000000000 : ℝ)*X 0 1+(2288502533/5000000000 : ℝ)*X 0 2+(4368621521/10000000000 : ℝ)*X 1 0+(2084884829/5000000000 : ℝ)*X 1 1+(2288502533/5000000000 : ℝ)*X 1 2+(4368621521/10000000000 : ℝ)*X 2 0+(2084884829/5000000000 : ℝ)*X 2 1+(2288502533/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-436951049/2000000000 : ℝ)*X 0 0+(2614190877/5000000000 : ℝ)*X 0 1+(1358319441/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5302774973/10000000000 : ℝ)*X 1 0+(-521176653/2500000000 : ℝ)*X 1 1+(339579863/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2651387733/5000000000 : ℝ)*X 2 0+(5433278121/10000000000 : ℝ)*X 2 1+(-1042352757/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1092165349/2500000000 : ℝ)*X 0 0+(571921617/1250000000 : ℝ)*X 0 1+(2085705887/5000000000 : ℝ)*X 0 2+(1092165349/2500000000 : ℝ)*X 1 0+(571921617/1250000000 : ℝ)*X 1 1+(2085705887/5000000000 : ℝ)*X 1 2+(1092165349/2500000000 : ℝ)*X 2 0+(571921617/1250000000 : ℝ)*X 2 1+(2085705887/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (34609614744861038735115813/37437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (660681203/100000000000000 : ℝ)*(base19) + (159296919/25000000000000 : ℝ)*(base23) + (10161619/10000000000000 : ℝ)*(lower2) + (111591143/100000000000000 : ℝ)*(upper5) + (912112241657813/25000000000000 : ℝ)*(major0) + (912112241657813/25000000000000 : ℝ)*(major1) + (912112241657813/25000000000000 : ℝ)*(major2) + (2420640003720671/50000000000000 : ℝ)*(sp0) + (2420649866501721/50000000000000 : ℝ)*(sp1) + (2420651173634459/50000000000000 : ℝ)*(sp2) + (61389715684623/2500000000000 : ℝ)*(sp3) + (22977015253/100000000000000 : ℝ)*(sp4) + (51815439/2000000000000 : ℝ)*(sp5) + (629060551/10000000000000 : ℝ)*(sp7) + (245559491799043/10000000000000 : ℝ)*(f.failure) + (968260596891319/20000000000000 : ℝ)*(f.sum) + (111741593511283/38935000000000000000000000000 : ℝ)*base65 + (13560097074657614659/973375000000000000000000000000000 : ℝ)*base67 + (14123484914695364659/973375000000000000000000000000000 : ℝ)*base69 + (19919531368714614659/973375000000000000000000000000000 : ℝ)*base71 + (13803256452311/4866875000000000000000000000 : ℝ)*base73 + (16879962665894614659/973375000000000000000000000000000 : ℝ)*base75 + (8986948841825864659/973375000000000000000000000000000 : ℝ)*base77 + (36986628814554614659/973375000000000000000000000000000 : ℝ)*base79 + (9302446732087/9733750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (2444379/250000000000000000000 : ℝ)*base90 + (2444379/250000000000000000000 : ℝ)*base92 + (2444379/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (298523882165544532863312249/60835937500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1144016807/100000000000000 : ℝ)*(base19) + (2362785013/100000000000000 : ℝ)*(base23) + (211050909/100000000000000 : ℝ)*(upper2) + (218754347/100000000000000 : ℝ)*(upper3) + (133172629/100000000000000 : ℝ)*(upper5) + (459750720247413/12500000000000 : ℝ)*(major0) + (459750720247413/12500000000000 : ℝ)*(major1) + (459750720247413/12500000000000 : ℝ)*(major2) + (7902832787/50000000000000 : ℝ)*(sp1) + (53125121521/100000000000000 : ℝ)*(sp2) + (4880523189921761/100000000000000 : ℝ)*(sp4) + (4880506240239379/100000000000000 : ℝ)*(sp5) + (1220116925503807/25000000000000 : ℝ)*(sp6) + (1237744085234553/50000000000000 : ℝ)*(sp7) + (1237744085234553/50000000000000 : ℝ)*(f.failure) + (4880523189921761/100000000000000 : ℝ)*(f.sum) + (47518597711789/38935000000000000000000000000 : ℝ)*base66 + (7321202225142382459/486687500000000000000000000000000 : ℝ)*base67 + (1833794609223257459/486687500000000000000000000000000 : ℝ)*base69 + (2919257525441944959/486687500000000000000000000000000 : ℝ)*base71 + (35688945337449/9733750000000000000000000000 : ℝ)*base73 + (8405679053596882459/486687500000000000000000000000000 : ℝ)*base75 + (5813285981056507459/486687500000000000000000000000000 : ℝ)*base77 + (4695480546500680041/486687500000000000000000000000000 : ℝ)*base80 + (2924709290497/4866875000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (10433409/1250000000000000000000 : ℝ)*base90 + (10433409/1250000000000000000000 : ℝ)*base92 + (10433409/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1096_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37144247/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4161/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8857/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5247/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (929/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1096_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1096_s4_0 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-547032221/2500000000 : ℝ)*x 0 + (1080839103/2000000000 : ℝ)*x 1 + (5255250401/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (547032221/2500000000 : ℝ)^8289 ≤ (6644864802613/50000000000000 : ℝ)^6241 := by
    have hnat : (547032221 : ℕ)^8289*50000000000000^6241 ≤ 6644864802613^6241*2500000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547032221 2500000000 6644864802613 50000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1080839103/2000000000 : ℝ)^8289 ≤ (5519961922113/12500000000000 : ℝ)^6241 := by
    have hnat : (1080839103 : ℕ)^8289*12500000000000^6241 ≤ 5519961922113^6241*2000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080839103 2000000000 5519961922113 12500000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255250401/10000000000 : ℝ)^8289 ≤ (42550575001343/100000000000000 : ℝ)^6241 := by
    have hnat : (5255250401 : ℕ)^8289*100000000000000^6241 ≤ 42550575001343^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255250401 10000000000 42550575001343 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-547032221/2500000000 : ℝ), (1080839103/2000000000 : ℝ), (5255250401/10000000000 : ℝ)] ![(6644864802613/50000000000000 : ℝ), (5519961922113/12500000000000 : ℝ), (42550575001343/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-547032221/2500000000 : ℝ)|^8289 ≤ (6644864802613/50000000000000 : ℝ)^6241
        have hw : |(-547032221/2500000000 : ℝ)|=(547032221/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1080839103/2000000000 : ℝ)|^8289 ≤ (5519961922113/12500000000000 : ℝ)^6241
        have hw : |(1080839103/2000000000 : ℝ)|=(1080839103/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255250401/10000000000 : ℝ)|^8289 ≤ (42550575001343/100000000000000 : ℝ)^6241
        have hw : |(5255250401/10000000000 : ℝ)|=(5255250401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s4_1 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5347491513/10000000000 : ℝ)*x 0 + (-2263860307/10000000000 : ℝ)*x 1 + (5255250239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347491513/10000000000 : ℝ)^8289 ≤ (43545358482987/100000000000000 : ℝ)^6241 := by
    have hnat : (5347491513 : ℕ)^8289*100000000000000^6241 ≤ 43545358482987^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347491513 10000000000 43545358482987 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2263860307/10000000000 : ℝ)^8289 ≤ (3476017062229/25000000000000 : ℝ)^6241 := by
    have hnat : (2263860307 : ℕ)^8289*25000000000000^6241 ≤ 3476017062229^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2263860307 10000000000 3476017062229 25000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255250239/10000000000 : ℝ)^8289 ≤ (8510114651847/20000000000000 : ℝ)^6241 := by
    have hnat : (5255250239 : ℕ)^8289*20000000000000^6241 ≤ 8510114651847^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255250239 10000000000 8510114651847 20000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347491513/10000000000 : ℝ), (-2263860307/10000000000 : ℝ), (5255250239/10000000000 : ℝ)] ![(43545358482987/100000000000000 : ℝ), (3476017062229/25000000000000 : ℝ), (8510114651847/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347491513/10000000000 : ℝ)|^8289 ≤ (43545358482987/100000000000000 : ℝ)^6241
        have hw : |(5347491513/10000000000 : ℝ)|=(5347491513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2263860307/10000000000 : ℝ)|^8289 ≤ (3476017062229/25000000000000 : ℝ)^6241
        have hw : |(-2263860307/10000000000 : ℝ)|=(2263860307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255250239/10000000000 : ℝ)|^8289 ≤ (8510114651847/20000000000000 : ℝ)^6241
        have hw : |(5255250239/10000000000 : ℝ)|=(5255250239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s4_2 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2673745953/5000000000 : ℝ)*x 0 + (328453133/625000000 : ℝ)*x 1 + (-565964983/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673745953/5000000000 : ℝ)^8289 ≤ (10886340683353/25000000000000 : ℝ)^6241 := by
    have hnat : (2673745953 : ℕ)^8289*25000000000000^6241 ≤ 10886340683353^6241*5000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673745953 5000000000 10886340683353 25000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (328453133/625000000 : ℝ)^8289 ≤ (42550572065569/100000000000000 : ℝ)^6241 := by
    have hnat : (328453133 : ℕ)^8289*100000000000000^6241 ≤ 42550572065569^6241*625000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328453133 625000000 42550572065569 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (565964983/2500000000 : ℝ)^8289 ≤ (13904065189973/100000000000000 : ℝ)^6241 := by
    have hnat : (565964983 : ℕ)^8289*100000000000000^6241 ≤ 13904065189973^6241*2500000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565964983 2500000000 13904065189973 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673745953/5000000000 : ℝ), (328453133/625000000 : ℝ), (-565964983/2500000000 : ℝ)] ![(10886340683353/25000000000000 : ℝ), (42550572065569/100000000000000 : ℝ), (13904065189973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673745953/5000000000 : ℝ)|^8289 ≤ (10886340683353/25000000000000 : ℝ)^6241
        have hw : |(2673745953/5000000000 : ℝ)|=(2673745953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(328453133/625000000 : ℝ)|^8289 ≤ (42550572065569/100000000000000 : ℝ)^6241
        have hw : |(328453133/625000000 : ℝ)|=(328453133/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-565964983/2500000000 : ℝ)|^8289 ≤ (13904065189973/100000000000000 : ℝ)^6241
        have hw : |(-565964983/2500000000 : ℝ)|=(565964983/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s4_3 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4370643701/10000000000 : ℝ)*x 0 + (4226297713/10000000000 : ℝ)*x 1 + (2259974573/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4370643701/10000000000 : ℝ)^8289 ≤ (4163892207591/12500000000000 : ℝ)^6241 := by
    have hnat : (4370643701 : ℕ)^8289*12500000000000^6241 ≤ 4163892207591^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4370643701 10000000000 4163892207591 12500000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4226297713/10000000000 : ℝ)^8289 ≤ (31857958290539/100000000000000 : ℝ)^6241 := by
    have hnat : (4226297713 : ℕ)^8289*100000000000000^6241 ≤ 31857958290539^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4226297713 10000000000 31857958290539 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2259974573/5000000000 : ℝ)^8289 ≤ (6966180807143/20000000000000 : ℝ)^6241 := by
    have hnat : (2259974573 : ℕ)^8289*20000000000000^6241 ≤ 6966180807143^6241*5000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2259974573 5000000000 6966180807143 20000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4370643701/10000000000 : ℝ), (4226297713/10000000000 : ℝ), (2259974573/5000000000 : ℝ)] ![(4163892207591/12500000000000 : ℝ), (31857958290539/100000000000000 : ℝ), (6966180807143/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4370643701/10000000000 : ℝ)|^8289 ≤ (4163892207591/12500000000000 : ℝ)^6241
        have hw : |(4370643701/10000000000 : ℝ)|=(4370643701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4226297713/10000000000 : ℝ)|^8289 ≤ (31857958290539/100000000000000 : ℝ)^6241
        have hw : |(4226297713/10000000000 : ℝ)|=(4226297713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2259974573/5000000000 : ℝ)|^8289 ≤ (6966180807143/20000000000000 : ℝ)^6241
        have hw : |(2259974573/5000000000 : ℝ)|=(2259974573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s4_4 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2188136483/10000000000 : ℝ)*x 0 + (5255681797/10000000000 : ℝ)*x 1 + (2701881199/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2188136483/10000000000 : ℝ)^8289 ≤ (265795818069/2000000000000 : ℝ)^6241 := by
    have hnat : (2188136483 : ℕ)^8289*2000000000000^6241 ≤ 265795818069^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188136483 10000000000 265795818069 2000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5255681797/10000000000 : ℝ)^8289 ≤ (42555214188991/100000000000000 : ℝ)^6241 := by
    have hnat : (5255681797 : ℕ)^8289*100000000000000^6241 ≤ 42555214188991^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255681797 10000000000 42555214188991 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2701881199/5000000000 : ℝ)^8289 ≤ (44154994893837/100000000000000 : ℝ)^6241 := by
    have hnat : (2701881199 : ℕ)^8289*100000000000000^6241 ≤ 44154994893837^6241*5000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701881199 5000000000 44154994893837 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2188136483/10000000000 : ℝ), (5255681797/10000000000 : ℝ), (2701881199/5000000000 : ℝ)] ![(265795818069/2000000000000 : ℝ), (42555214188991/100000000000000 : ℝ), (44154994893837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2188136483/10000000000 : ℝ)|^8289 ≤ (265795818069/2000000000000 : ℝ)^6241
        have hw : |(-2188136483/10000000000 : ℝ)|=(2188136483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5255681797/10000000000 : ℝ)|^8289 ≤ (42555214188991/100000000000000 : ℝ)^6241
        have hw : |(5255681797/10000000000 : ℝ)|=(5255681797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2701881199/5000000000 : ℝ)|^8289 ≤ (44154994893837/100000000000000 : ℝ)^6241
        have hw : |(2701881199/5000000000 : ℝ)|=(2701881199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s4_5 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5309889189/10000000000 : ℝ)*x 0 + (-1057674021/5000000000 : ℝ)*x 1 + (168867561/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5309889189/10000000000 : ℝ)^8289 ≤ (43139146937237/100000000000000 : ℝ)^6241 := by
    have hnat : (5309889189 : ℕ)^8289*100000000000000^6241 ≤ 43139146937237^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5309889189 10000000000 43139146937237 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1057674021/5000000000 : ℝ)^8289 ≤ (12705862991469/100000000000000 : ℝ)^6241 := by
    have hnat : (1057674021 : ℕ)^8289*100000000000000^6241 ≤ 12705862991469^6241*5000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057674021 5000000000 12705862991469 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (168867561/312500000 : ℝ)^8289 ≤ (44154990053603/100000000000000 : ℝ)^6241 := by
    have hnat : (168867561 : ℕ)^8289*100000000000000^6241 ≤ 44154990053603^6241*312500000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168867561 312500000 44154990053603 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5309889189/10000000000 : ℝ), (-1057674021/5000000000 : ℝ), (168867561/312500000 : ℝ)] ![(43139146937237/100000000000000 : ℝ), (12705862991469/100000000000000 : ℝ), (44154990053603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5309889189/10000000000 : ℝ)|^8289 ≤ (43139146937237/100000000000000 : ℝ)^6241
        have hw : |(5309889189/10000000000 : ℝ)|=(5309889189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1057674021/5000000000 : ℝ)|^8289 ≤ (12705862991469/100000000000000 : ℝ)^6241
        have hw : |(-1057674021/5000000000 : ℝ)|=(1057674021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(168867561/312500000 : ℝ)|^8289 ≤ (44154990053603/100000000000000 : ℝ)^6241
        have hw : |(168867561/312500000 : ℝ)|=(168867561/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s4_6 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2654944567/5000000000 : ℝ)*x 0 + (5403762197/10000000000 : ℝ)*x 1 + (-2115347783/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2654944567/5000000000 : ℝ)^8289 ≤ (4313914634377/10000000000000 : ℝ)^6241 := by
    have hnat : (2654944567 : ℕ)^8289*10000000000000^6241 ≤ 4313914634377^6241*5000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2654944567 5000000000 4313914634377 10000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5403762197/10000000000 : ℝ)^8289 ≤ (11038748178119/25000000000000 : ℝ)^6241 := by
    have hnat : (5403762197 : ℕ)^8289*25000000000000^6241 ≤ 11038748178119^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403762197 10000000000 11038748178119 25000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2115347783/10000000000 : ℝ)^8289 ≤ (79411630783/625000000000 : ℝ)^6241 := by
    have hnat : (2115347783 : ℕ)^8289*625000000000^6241 ≤ 79411630783^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115347783 10000000000 79411630783 625000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2654944567/5000000000 : ℝ), (5403762197/10000000000 : ℝ), (-2115347783/10000000000 : ℝ)] ![(4313914634377/10000000000000 : ℝ), (11038748178119/25000000000000 : ℝ), (79411630783/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2654944567/5000000000 : ℝ)|^8289 ≤ (4313914634377/10000000000000 : ℝ)^6241
        have hw : |(2654944567/5000000000 : ℝ)|=(2654944567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5403762197/10000000000 : ℝ)|^8289 ≤ (11038748178119/25000000000000 : ℝ)^6241
        have hw : |(5403762197/10000000000 : ℝ)|=(5403762197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2115347783/10000000000 : ℝ)|^8289 ≤ (79411630783/625000000000 : ℝ)^6241
        have hw : |(-2115347783/10000000000 : ℝ)|=(2115347783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s4_7 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2185329603/5000000000 : ℝ)*x 0 + (4519098683/10000000000 : ℝ)*x 1 + (4227151399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2185329603/5000000000 : ℝ)^8289 ≤ (33311294611711/100000000000000 : ℝ)^6241 := by
    have hnat : (2185329603 : ℕ)^8289*100000000000000^6241 ≤ 33311294611711^6241*5000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185329603 5000000000 33311294611711 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4519098683/10000000000 : ℝ)^8289 ≤ (34822199989849/100000000000000 : ℝ)^6241 := by
    have hnat : (4519098683 : ℕ)^8289*100000000000000^6241 ≤ 34822199989849^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4519098683 10000000000 34822199989849 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4227151399/10000000000 : ℝ)^8289 ≤ (15933252691101/50000000000000 : ℝ)^6241 := by
    have hnat : (4227151399 : ℕ)^8289*50000000000000^6241 ≤ 15933252691101^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227151399 10000000000 15933252691101 50000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2185329603/5000000000 : ℝ), (4519098683/10000000000 : ℝ), (4227151399/10000000000 : ℝ)] ![(33311294611711/100000000000000 : ℝ), (34822199989849/100000000000000 : ℝ), (15933252691101/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2185329603/5000000000 : ℝ)|^8289 ≤ (33311294611711/100000000000000 : ℝ)^6241
        have hw : |(2185329603/5000000000 : ℝ)|=(2185329603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4519098683/10000000000 : ℝ)|^8289 ≤ (34822199989849/100000000000000 : ℝ)^6241
        have hw : |(4519098683/10000000000 : ℝ)|=(4519098683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4227151399/10000000000 : ℝ)|^8289 ≤ (15933252691101/50000000000000 : ℝ)^6241
        have hw : |(4227151399/10000000000 : ℝ)|=(4227151399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1096_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37144247/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (929/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5247/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2217/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14239/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (929/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5247/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (929/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5247/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (929/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5247/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (929/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5247/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (929/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5247/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (929/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5247/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (5247/50000 : ℝ) ^ (259/64 : ℝ) ≤ (340973692972531/3125000000000000000 : ℝ) := by
    have hpowers : (5247/50000 : ℝ)^259 ≤ (340973692972531/3125000000000000000 : ℝ)^64 := by
      have hnat : (5247 : ℕ)^259*3125000000000000000^64 ≤ 340973692972531^64*50000^259 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5247 50000 340973692972531 3125000000000000000 259 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5247/50000 : ℝ)) (X := (340973692972531/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 259 64 (by norm_num) hpowers
    exact h
  have hpowhi : (929/6250 : ℝ) ^ (259/64 : ℝ) ≤ (44641280898321323/100000000000000000000 : ℝ) := by
    have hpowers : (929/6250 : ℝ)^259 ≤ (44641280898321323/100000000000000000000 : ℝ)^64 := by
      have hnat : (929 : ℕ)^259*100000000000000000000^64 ≤ 44641280898321323^64*6250^259 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        929 6250 44641280898321323 100000000000000000000 259 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (929/6250 : ℝ)) (X := (44641280898321323/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 259 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562840973692972531/1562500000000000000 : ℝ) ≤ (10000539194412559/10000000000000000 : ℝ) ^ (259/64 : ℝ) := by
    have hpowers : (1562840973692972531/1562500000000000000 : ℝ)^64 ≤ (10000539194412559/10000000000000000 : ℝ)^259 := by
      have hnat : (1562840973692972531 : ℕ)^64*10000000000000000^259 ≤ 10000539194412559^259*1562500000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562840973692972531 1562500000000000000 10000539194412559 10000000000000000 64 259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000539194412559/10000000000000000 : ℝ)) (X := (1562840973692972531/1562500000000000000 : ℝ)) (by norm_num) 259 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (20011110487814688463/20000000000000000000 : ℝ) ≤ (10001372437384027/10000000000000000 : ℝ) ^ (259/64 : ℝ) := by
    have hpowers : (20011110487814688463/20000000000000000000 : ℝ)^64 ≤ (10001372437384027/10000000000000000 : ℝ)^259 := by
      have hnat : (20011110487814688463 : ℕ)^64*10000000000000000^259 ≤ 10001372437384027^259*20000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20011110487814688463 20000000000000000000 10001372437384027 10000000000000000 64 259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001372437384027/10000000000000000 : ℝ)) (X := (20011110487814688463/20000000000000000000 : ℝ)) (by norm_num) 259 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (50044641280898321323/50000000000000000000 : ℝ) ≤ (2000441136071099/2000000000000000 : ℝ) ^ (259/64 : ℝ) := by
    have hpowers : (50044641280898321323/50000000000000000000 : ℝ)^64 ≤ (2000441136071099/2000000000000000 : ℝ)^259 := by
      have hnat : (50044641280898321323 : ℕ)^64*2000000000000000^259 ≤ 2000441136071099^259*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50044641280898321323 50000000000000000000 2000441136071099 2000000000000000 64 259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000441136071099/2000000000000000 : ℝ)) (X := (50044641280898321323/50000000000000000000 : ℝ)) (by norm_num) 259 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(340973692972531/3125000000000000000 : ℝ) ≤ ((21842434088048856223/21850000000000000000 : ℝ)+2*(208310742867/109250000000000 : ℝ)*(5247/50000 : ℝ))^(259/64 : ℝ) := by
    rw [show (21842434088048856223/21850000000000000000 : ℝ)+2*(208310742867/109250000000000 : ℝ)*(5247/50000 : ℝ)=(10000539194412559/10000000000000000 : ℝ) by norm_num, show 1+2*(340973692972531/3125000000000000000 : ℝ)=(1562840973692972531/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(44641280898321323/100000000000000000000 : ℝ)+(340973692972531/3125000000000000000 : ℝ) ≤ ((21842434088048856223/21850000000000000000 : ℝ)+(208310742867/109250000000000 : ℝ)*((929/6250 : ℝ)+(5247/50000 : ℝ)))^(259/64 : ℝ) := by
    rw [show (21842434088048856223/21850000000000000000 : ℝ)+(208310742867/109250000000000 : ℝ)*((929/6250 : ℝ)+(5247/50000 : ℝ))=(10001372437384027/10000000000000000 : ℝ) by norm_num, show 1+(44641280898321323/100000000000000000000 : ℝ)+(340973692972531/3125000000000000000 : ℝ)=(20011110487814688463/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(44641280898321323/100000000000000000000 : ℝ) ≤ ((21842434088048856223/21850000000000000000 : ℝ)+2*(208310742867/109250000000000 : ℝ)*(929/6250 : ℝ))^(259/64 : ℝ) := by
    rw [show (21842434088048856223/21850000000000000000 : ℝ)+2*(208310742867/109250000000000 : ℝ)*(929/6250 : ℝ)=(2000441136071099/2000000000000000 : ℝ) by norm_num, show 1+2*(44641280898321323/100000000000000000000 : ℝ)=(50044641280898321323/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (21842434088048856223/21850000000000000000 : ℝ)*(X 1 0+X 2 0)+(208310742867/109250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (259/64 : ℝ)) (lo := (5247/50000 : ℝ)) (hi := (929/6250 : ℝ)) (c := (21842434088048856223/21850000000000000000 : ℝ)) (alpha := (208310742867/109250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (21842434088048856223/21850000000000000000 : ℝ)*(X 0 1+X 2 1)+(208310742867/109250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (259/64 : ℝ)) (lo := (5247/50000 : ℝ)) (hi := (929/6250 : ℝ)) (c := (21842434088048856223/21850000000000000000 : ℝ)) (alpha := (208310742867/109250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (21842434088048856223/21850000000000000000 : ℝ)*(X 0 2+X 1 2)+(208310742867/109250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (259/64 : ℝ)) (lo := (5247/50000 : ℝ)) (hi := (929/6250 : ℝ)) (c := (21842434088048856223/21850000000000000000 : ℝ)) (alpha := (208310742867/109250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-547032221/2500000000 : ℝ)*X 0 0+(1080839103/2000000000 : ℝ)*X 0 1+(5255250401/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347491513/10000000000 : ℝ)*X 1 0+(-2263860307/10000000000 : ℝ)*X 1 1+(5255250239/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673745953/5000000000 : ℝ)*X 2 0+(328453133/625000000 : ℝ)*X 2 1+(-565964983/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4370643701/10000000000 : ℝ)*X 0 0+(4226297713/10000000000 : ℝ)*X 0 1+(2259974573/5000000000 : ℝ)*X 0 2+(4370643701/10000000000 : ℝ)*X 1 0+(4226297713/10000000000 : ℝ)*X 1 1+(2259974573/5000000000 : ℝ)*X 1 2+(4370643701/10000000000 : ℝ)*X 2 0+(4226297713/10000000000 : ℝ)*X 2 1+(2259974573/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2188136483/10000000000 : ℝ)*X 0 0+(5255681797/10000000000 : ℝ)*X 0 1+(2701881199/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5309889189/10000000000 : ℝ)*X 1 0+(-1057674021/5000000000 : ℝ)*X 1 1+(168867561/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2654944567/5000000000 : ℝ)*X 2 0+(5403762197/10000000000 : ℝ)*X 2 1+(-2115347783/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2185329603/5000000000 : ℝ)*X 0 0+(4519098683/10000000000 : ℝ)*X 0 1+(4227151399/10000000000 : ℝ)*X 0 2+(2185329603/5000000000 : ℝ)*X 1 0+(4519098683/10000000000 : ℝ)*X 1 1+(4227151399/10000000000 : ℝ)*X 1 2+(2185329603/5000000000 : ℝ)*X 2 0+(4519098683/10000000000 : ℝ)*X 2 1+(4227151399/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (472565852115412771178135823/57500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11337027/100000000000000 : ℝ)*(base8) + (190124811/50000000000000 : ℝ)*(lower2) + (1169261/25000000000000 : ℝ)*(lower3) + (9063813/10000000000000 : ℝ)*(lower4) + (5059632957186273/100000000000000 : ℝ)*(major0) + (5059632957186273/100000000000000 : ℝ)*(major1) + (5059632957186273/100000000000000 : ℝ)*(major2) + (268554825259371/4000000000000 : ℝ)*(sp0) + (6713864035276511/100000000000000 : ℝ)*(sp1) + (6713870884951997/100000000000000 : ℝ)*(sp2) + (106418559237169/3125000000000 : ℝ)*(sp3) + (48426139/20000000000000 : ℝ)*(sp4) + (3424837743/50000000000000 : ℝ)*(sp5) + (859879907/100000000000000 : ℝ)*(sp7) + (1702697377734657/50000000000000 : ℝ)*(f.failure) + (6713870884951997/100000000000000 : ℝ)*(f.sum) + (98101687480743/10925000000000000000000000000 : ℝ)*base66 + (59528707822819426879/2185000000000000000000000000000000 : ℝ)*base67 + (7010363937065573121/2185000000000000000000000000000000 : ℝ)*base70 + (19198430288249426879/2185000000000000000000000000000000 : ℝ)*base71 + (7387760997209/5462500000000000000000000000 : ℝ)*base74 + (5254047643525573121/2185000000000000000000000000000000 : ℝ)*base76 + (100333227674475573121/2185000000000000000000000000000000 : ℝ)*base78 + (11600952043240573121/2185000000000000000000000000000000 : ℝ)*base80 + (9751793603343/10925000000000000000000000000 : ℝ)*base82 + (12431721/1250000000000000000000 : ℝ)*base90 + (12431721/1250000000000000000000 : ℝ)*base92 + (12431721/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1437464476568798506153805799/136562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (912589023/100000000000000 : ℝ)*(base19) + (218277939/12500000000000 : ℝ)*(base23) + (40047257/25000000000000 : ℝ)*(lower2) + (14782609/12500000000000 : ℝ)*(upper3) + (518069639/100000000000000 : ℝ)*(lower4) + (1272292795111271/25000000000000 : ℝ)*(major0) + (1272292795111271/25000000000000 : ℝ)*(major1) + (1272292795111271/25000000000000 : ℝ)*(major2) + (8105248277/25000000000000 : ℝ)*(sp2) + (2280827/100000000000000 : ℝ)*(sp3) + (211033328189081/3125000000000 : ℝ)*(sp4) + (6753065589461569/100000000000000 : ℝ)*(sp5) + (1688258083708493/25000000000000 : ℝ)*(sp6) + (1712637752845111/50000000000000 : ℝ)*(sp7) + (3425275507971049/100000000000000 : ℝ)*(f.failure) + (211033328189081/3125000000000 : ℝ)*(f.sum) + (83405583582119/10925000000000000000000000000 : ℝ)*base66 + (834795921814060567/546250000000000000000000000000000 : ℝ)*base68 + (2454348033317189433/546250000000000000000000000000000 : ℝ)*base69 + (2650138659142810567/546250000000000000000000000000000 : ℝ)*base72 + (58272313608919/10925000000000000000000000000 : ℝ)*base74 + (2890808219762810567/546250000000000000000000000000000 : ℝ)*base76 + (2412283139811560567/546250000000000000000000000000000 : ℝ)*base78 + (3741720186199060567/546250000000000000000000000000000 : ℝ)*base80 + (8790073166811/2731250000000000000000000000 : ℝ)*base82 + (12905103/2500000000000000000000 : ℝ)*base89 + (12905103/2500000000000000000000 : ℝ)*base91 + (12905103/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1096_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37144247/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (929/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5247/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2217/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14239/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1096_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1096_s5_0 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1094438511/5000000000 : ℝ)*x 0 + (5396153151/10000000000 : ℝ)*x 1 + (8420483/16000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1094438511/5000000000 : ℝ)^8289 ≤ (2659152976641/20000000000000 : ℝ)^6241 := by
    have hnat : (1094438511 : ℕ)^8289*20000000000000^6241 ≤ 2659152976641^6241*5000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094438511 5000000000 2659152976641 20000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5396153151/10000000000 : ℝ)^8289 ≤ (1377263571631/3125000000000 : ℝ)^6241 := by
    have hnat : (5396153151 : ℕ)^8289*3125000000000^6241 ≤ 1377263571631^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396153151 10000000000 1377263571631 3125000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8420483/16000000 : ℝ)^8289 ≤ (66612188769/156250000000 : ℝ)^6241 := by
    have hnat : (8420483 : ℕ)^8289*156250000000^6241 ≤ 66612188769^6241*16000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8420483 16000000 66612188769 156250000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1094438511/5000000000 : ℝ), (5396153151/10000000000 : ℝ), (8420483/16000000 : ℝ)] ![(2659152976641/20000000000000 : ℝ), (1377263571631/3125000000000 : ℝ), (66612188769/156250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1094438511/5000000000 : ℝ)|^8289 ≤ (2659152976641/20000000000000 : ℝ)^6241
        have hw : |(-1094438511/5000000000 : ℝ)|=(1094438511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5396153151/10000000000 : ℝ)|^8289 ≤ (1377263571631/3125000000000 : ℝ)^6241
        have hw : |(5396153151/10000000000 : ℝ)|=(5396153151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8420483/16000000 : ℝ)|^8289 ≤ (66612188769/156250000000 : ℝ)^6241
        have hw : |(8420483/16000000 : ℝ)|=(8420483/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s5_1 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (668185351/1250000000 : ℝ)*x 0 + (-2256560227/10000000000 : ℝ)*x 1 + (1052560607/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668185351/1250000000 : ℝ)^8289 ≤ (21761817508607/50000000000000 : ℝ)^6241 := by
    have hnat : (668185351 : ℕ)^8289*50000000000000^6241 ≤ 21761817508607^6241*1250000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668185351 1250000000 21761817508607 50000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2256560227/10000000000 : ℝ)^8289 ≤ (138445516867/1000000000000 : ℝ)^6241 := by
    have hnat : (2256560227 : ℕ)^8289*1000000000000^6241 ≤ 138445516867^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2256560227 10000000000 138445516867 1000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052560607/2000000000 : ℝ)^8289 ≤ (42631813292391/100000000000000 : ℝ)^6241 := by
    have hnat : (1052560607 : ℕ)^8289*100000000000000^6241 ≤ 42631813292391^6241*2000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052560607 2000000000 42631813292391 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668185351/1250000000 : ℝ), (-2256560227/10000000000 : ℝ), (1052560607/2000000000 : ℝ)] ![(21761817508607/50000000000000 : ℝ), (138445516867/1000000000000 : ℝ), (42631813292391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668185351/1250000000 : ℝ)|^8289 ≤ (21761817508607/50000000000000 : ℝ)^6241
        have hw : |(668185351/1250000000 : ℝ)|=(668185351/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2256560227/10000000000 : ℝ)|^8289 ≤ (138445516867/1000000000000 : ℝ)^6241
        have hw : |(-2256560227/10000000000 : ℝ)|=(2256560227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052560607/2000000000 : ℝ)|^8289 ≤ (42631813292391/100000000000000 : ℝ)^6241
        have hw : |(1052560607/2000000000 : ℝ)|=(1052560607/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s5_2 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345483181/10000000000 : ℝ)*x 0 + (5262802373/10000000000 : ℝ)*x 1 + (-564140151/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345483181/10000000000 : ℝ)^8289 ≤ (8704727810167/20000000000000 : ℝ)^6241 := by
    have hnat : (5345483181 : ℕ)^8289*20000000000000^6241 ≤ 8704727810167^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345483181 10000000000 8704727810167 20000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5262802373/10000000000 : ℝ)^8289 ≤ (42631806170053/100000000000000 : ℝ)^6241 := by
    have hnat : (5262802373 : ℕ)^8289*100000000000000^6241 ≤ 42631806170053^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262802373 10000000000 42631806170053 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (564140151/2500000000 : ℝ)^8289 ≤ (138445547587/1000000000000 : ℝ)^6241 := by
    have hnat : (564140151 : ℕ)^8289*1000000000000^6241 ≤ 138445547587^6241*2500000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      564140151 2500000000 138445547587 1000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345483181/10000000000 : ℝ), (5262802373/10000000000 : ℝ), (-564140151/2500000000 : ℝ)] ![(8704727810167/20000000000000 : ℝ), (42631806170053/100000000000000 : ℝ), (138445547587/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345483181/10000000000 : ℝ)|^8289 ≤ (8704727810167/20000000000000 : ℝ)^6241
        have hw : |(5345483181/10000000000 : ℝ)|=(5345483181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5262802373/10000000000 : ℝ)|^8289 ≤ (42631806170053/100000000000000 : ℝ)^6241
        have hw : |(5262802373/10000000000 : ℝ)|=(5262802373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-564140151/2500000000 : ℝ)|^8289 ≤ (138445547587/1000000000000 : ℝ)^6241
        have hw : |(-564140151/2500000000 : ℝ)|=(564140151/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s5_3 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4371078939/10000000000 : ℝ)*x 0 + (4241613487/10000000000 : ℝ)*x 1 + (4504519267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4371078939/10000000000 : ℝ)^8289 ≤ (8328885868077/25000000000000 : ℝ)^6241 := by
    have hnat : (4371078939 : ℕ)^8289*25000000000000^6241 ≤ 8328885868077^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4371078939 10000000000 8328885868077 25000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4241613487/10000000000 : ℝ)^8289 ≤ (6402277122481/20000000000000 : ℝ)^6241 := by
    have hnat : (4241613487 : ℕ)^8289*20000000000000^6241 ≤ 6402277122481^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4241613487 10000000000 6402277122481 20000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4504519267/10000000000 : ℝ)^8289 ≤ (1386922836251/4000000000000 : ℝ)^6241 := by
    have hnat : (4504519267 : ℕ)^8289*4000000000000^6241 ≤ 1386922836251^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4504519267 10000000000 1386922836251 4000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4371078939/10000000000 : ℝ), (4241613487/10000000000 : ℝ), (4504519267/10000000000 : ℝ)] ![(8328885868077/25000000000000 : ℝ), (6402277122481/20000000000000 : ℝ), (1386922836251/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4371078939/10000000000 : ℝ)|^8289 ≤ (8328885868077/25000000000000 : ℝ)^6241
        have hw : |(4371078939/10000000000 : ℝ)|=(4371078939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4241613487/10000000000 : ℝ)|^8289 ≤ (6402277122481/20000000000000 : ℝ)^6241
        have hw : |(4241613487/10000000000 : ℝ)|=(4241613487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4504519267/10000000000 : ℝ)|^8289 ≤ (1386922836251/4000000000000 : ℝ)^6241
        have hw : |(4504519267/10000000000 : ℝ)|=(4504519267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s5_4 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-109444111/500000000 : ℝ)*x 0 + (1052629683/2000000000 : ℝ)*x 1 + (5395805571/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (109444111/500000000 : ℝ)^8289 ≤ (6647903409089/50000000000000 : ℝ)^6241 := by
    have hnat : (109444111 : ℕ)^8289*50000000000000^6241 ≤ 6647903409089^6241*500000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109444111 500000000 6647903409089 50000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052629683/2000000000 : ℝ)^8289 ≤ (4263552921369/10000000000000 : ℝ)^6241 := by
    have hnat : (1052629683 : ℕ)^8289*10000000000000^6241 ≤ 4263552921369^6241*2000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052629683 2000000000 4263552921369 10000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5395805571/10000000000 : ℝ)^8289 ≤ (440686639487/1000000000000 : ℝ)^6241 := by
    have hnat : (5395805571 : ℕ)^8289*1000000000000^6241 ≤ 440686639487^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395805571 10000000000 440686639487 1000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-109444111/500000000 : ℝ), (1052629683/2000000000 : ℝ), (5395805571/10000000000 : ℝ)] ![(6647903409089/50000000000000 : ℝ), (4263552921369/10000000000000 : ℝ), (440686639487/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-109444111/500000000 : ℝ)|^8289 ≤ (6647903409089/50000000000000 : ℝ)^6241
        have hw : |(-109444111/500000000 : ℝ)|=(109444111/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1052629683/2000000000 : ℝ)|^8289 ≤ (4263552921369/10000000000000 : ℝ)^6241
        have hw : |(1052629683/2000000000 : ℝ)|=(1052629683/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5395805571/10000000000 : ℝ)|^8289 ≤ (440686639487/1000000000000 : ℝ)^6241
        have hw : |(5395805571/10000000000 : ℝ)|=(5395805571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s5_5 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311816249/10000000000 : ℝ)*x 0 + (-2123557417/10000000000 : ℝ)*x 1 + (5395805461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311816249/10000000000 : ℝ)^8289 ≤ (10789985439083/25000000000000 : ℝ)^6241 := by
    have hnat : (5311816249 : ℕ)^8289*25000000000000^6241 ≤ 10789985439083^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311816249 10000000000 10789985439083 25000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2123557417/10000000000 : ℝ)^8289 ≤ (6385697735393/50000000000000 : ℝ)^6241 := by
    have hnat : (2123557417 : ℕ)^8289*50000000000000^6241 ≤ 6385697735393^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123557417 10000000000 6385697735393 50000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5395805461/10000000000 : ℝ)^8289 ≤ (44068662755497/100000000000000 : ℝ)^6241 := by
    have hnat : (5395805461 : ℕ)^8289*100000000000000^6241 ≤ 44068662755497^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395805461 10000000000 44068662755497 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311816249/10000000000 : ℝ), (-2123557417/10000000000 : ℝ), (5395805461/10000000000 : ℝ)] ![(10789985439083/25000000000000 : ℝ), (6385697735393/50000000000000 : ℝ), (44068662755497/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311816249/10000000000 : ℝ)|^8289 ≤ (10789985439083/25000000000000 : ℝ)^6241
        have hw : |(5311816249/10000000000 : ℝ)|=(5311816249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2123557417/10000000000 : ℝ)|^8289 ≤ (6385697735393/50000000000000 : ℝ)^6241
        have hw : |(-2123557417/10000000000 : ℝ)|=(2123557417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5395805461/10000000000 : ℝ)|^8289 ≤ (44068662755497/100000000000000 : ℝ)^6241
        have hw : |(5395805461/10000000000 : ℝ)|=(5395805461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s5_6 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (663977033/1250000000 : ℝ)*x 0 + (5395805503/10000000000 : ℝ)*x 1 + (-106177867/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663977033/1250000000 : ℝ)^8289 ≤ (21579970959103/50000000000000 : ℝ)^6241 := by
    have hnat : (663977033 : ℕ)^8289*50000000000000^6241 ≤ 21579970959103^6241*1250000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663977033 1250000000 21579970959103 50000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5395805503/10000000000 : ℝ)^8289 ≤ (11017165802771/25000000000000 : ℝ)^6241 := by
    have hnat : (5395805503 : ℕ)^8289*25000000000000^6241 ≤ 11017165802771^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395805503 10000000000 11017165802771 25000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (106177867/500000000 : ℝ)^8289 ≤ (3192848713933/25000000000000 : ℝ)^6241 := by
    have hnat : (106177867 : ℕ)^8289*25000000000000^6241 ≤ 3192848713933^6241*500000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106177867 500000000 3192848713933 25000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663977033/1250000000 : ℝ), (5395805503/10000000000 : ℝ), (-106177867/500000000 : ℝ)] ![(21579970959103/50000000000000 : ℝ), (11017165802771/25000000000000 : ℝ), (3192848713933/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663977033/1250000000 : ℝ)|^8289 ≤ (21579970959103/50000000000000 : ℝ)^6241
        have hw : |(663977033/1250000000 : ℝ)|=(663977033/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5395805503/10000000000 : ℝ)|^8289 ≤ (11017165802771/25000000000000 : ℝ)^6241
        have hw : |(5395805503/10000000000 : ℝ)|=(5395805503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-106177867/500000000 : ℝ)|^8289 ≤ (3192848713933/25000000000000 : ℝ)^6241
        have hw : |(-106177867/500000000 : ℝ)|=(106177867/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s5_7 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2185544647/5000000000 : ℝ)*x 0 + (900767473/2000000000 : ℝ)*x 1 + (2121149243/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2185544647/5000000000 : ℝ)^8289 ≤ (8328912073821/25000000000000 : ℝ)^6241 := by
    have hnat : (2185544647 : ℕ)^8289*25000000000000^6241 ≤ 8328912073821^6241*5000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185544647 5000000000 8328912073821 25000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (900767473/2000000000 : ℝ)^8289 ≤ (3466609977931/10000000000000 : ℝ)^6241 := by
    have hnat : (900767473 : ℕ)^8289*10000000000000^6241 ≤ 3466609977931^6241*2000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900767473 2000000000 3466609977931 10000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2121149243/5000000000 : ℝ)^8289 ≤ (6403650382509/20000000000000 : ℝ)^6241 := by
    have hnat : (2121149243 : ℕ)^8289*20000000000000^6241 ≤ 6403650382509^6241*5000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121149243 5000000000 6403650382509 20000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2185544647/5000000000 : ℝ), (900767473/2000000000 : ℝ), (2121149243/5000000000 : ℝ)] ![(8328912073821/25000000000000 : ℝ), (3466609977931/10000000000000 : ℝ), (6403650382509/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2185544647/5000000000 : ℝ)|^8289 ≤ (8328912073821/25000000000000 : ℝ)^6241
        have hw : |(2185544647/5000000000 : ℝ)|=(2185544647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(900767473/2000000000 : ℝ)|^8289 ≤ (3466609977931/10000000000000 : ℝ)^6241
        have hw : |(900767473/2000000000 : ℝ)|=(900767473/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2121149243/5000000000 : ℝ)|^8289 ≤ (6403650382509/20000000000000 : ℝ)^6241
        have hw : |(2121149243/5000000000 : ℝ)|=(2121149243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1096_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37144247/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14239/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2217/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (5623/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1407/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14239/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2217/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14239/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2217/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14239/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2217/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14239/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2217/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14239/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2217/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14239/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2217/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (2217/20000 : ℝ) ^ (259/64 : ℝ) ≤ (13619613260418359/100000000000000000000 : ℝ) := by
    have hpowers : (2217/20000 : ℝ)^259 ≤ (13619613260418359/100000000000000000000 : ℝ)^64 := by
      have hnat : (2217 : ℕ)^259*100000000000000000000^64 ≤ 13619613260418359^64*20000^259 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2217 20000 13619613260418359 100000000000000000000 259 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2217/20000 : ℝ)) (X := (13619613260418359/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 259 64 (by norm_num) hpowers
    exact h
  have hpowhi : (14239/100000 : ℝ) ^ (259/64 : ℝ) ≤ (37517795443063983/100000000000000000000 : ℝ) := by
    have hpowers : (14239/100000 : ℝ)^259 ≤ (37517795443063983/100000000000000000000 : ℝ)^64 := by
      have hnat : (14239 : ℕ)^259*100000000000000000000^64 ≤ 37517795443063983^64*100000^259 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14239 100000 37517795443063983 100000000000000000000 259 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14239/100000 : ℝ)) (X := (37517795443063983/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 259 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013619613260418359/50000000000000000000 : ℝ) ≤ (10000673023847153/10000000000000000 : ℝ) ^ (259/64 : ℝ) := by
    have hpowers : (50013619613260418359/50000000000000000000 : ℝ)^64 ≤ (10000673023847153/10000000000000000 : ℝ)^259 := by
      have hnat : (50013619613260418359 : ℕ)^64*10000000000000000^259 ≤ 10000673023847153^259*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013619613260418359 50000000000000000000 10000673023847153 10000000000000000 64 259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000673023847153/10000000000000000 : ℝ)) (X := (50013619613260418359/50000000000000000000 : ℝ)) (by norm_num) 259 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025568704351741171/50000000000000000000 : ℝ) ≤ (10001263383904909/10000000000000000 : ℝ) ^ (259/64 : ℝ) := by
    have hpowers : (50025568704351741171/50000000000000000000 : ℝ)^64 ≤ (10001263383904909/10000000000000000 : ℝ)^259 := by
      have hnat : (50025568704351741171 : ℕ)^64*10000000000000000^259 ≤ 10001263383904909^259*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025568704351741171 50000000000000000000 10001263383904909 10000000000000000 64 259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001263383904909/10000000000000000 : ℝ)) (X := (50025568704351741171/50000000000000000000 : ℝ)) (by norm_num) 259 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (50037517795443063983/50000000000000000000 : ℝ) ≤ (2000370748792533/2000000000000000 : ℝ) ^ (259/64 : ℝ) := by
    have hpowers : (50037517795443063983/50000000000000000000 : ℝ)^64 ≤ (2000370748792533/2000000000000000 : ℝ)^259 := by
      have hnat : (50037517795443063983 : ℕ)^64*2000000000000000^259 ≤ 2000370748792533^259*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50037517795443063983 50000000000000000000 2000370748792533 2000000000000000 64 259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000370748792533/2000000000000000 : ℝ)) (X := (50037517795443063983/50000000000000000000 : ℝ)) (by norm_num) 259 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13619613260418359/100000000000000000000 : ℝ) ≤ ((15764517217366735021/15770000000000000000 : ℝ)+2*(147590014439/78850000000000 : ℝ)*(2217/20000 : ℝ))^(259/64 : ℝ) := by
    rw [show (15764517217366735021/15770000000000000000 : ℝ)+2*(147590014439/78850000000000 : ℝ)*(2217/20000 : ℝ)=(10000673023847153/10000000000000000 : ℝ) by norm_num, show 1+2*(13619613260418359/100000000000000000000 : ℝ)=(50013619613260418359/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(37517795443063983/100000000000000000000 : ℝ)+(13619613260418359/100000000000000000000 : ℝ) ≤ ((15764517217366735021/15770000000000000000 : ℝ)+(147590014439/78850000000000 : ℝ)*((14239/100000 : ℝ)+(2217/20000 : ℝ)))^(259/64 : ℝ) := by
    rw [show (15764517217366735021/15770000000000000000 : ℝ)+(147590014439/78850000000000 : ℝ)*((14239/100000 : ℝ)+(2217/20000 : ℝ))=(10001263383904909/10000000000000000 : ℝ) by norm_num, show 1+(37517795443063983/100000000000000000000 : ℝ)+(13619613260418359/100000000000000000000 : ℝ)=(50025568704351741171/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(37517795443063983/100000000000000000000 : ℝ) ≤ ((15764517217366735021/15770000000000000000 : ℝ)+2*(147590014439/78850000000000 : ℝ)*(14239/100000 : ℝ))^(259/64 : ℝ) := by
    rw [show (15764517217366735021/15770000000000000000 : ℝ)+2*(147590014439/78850000000000 : ℝ)*(14239/100000 : ℝ)=(2000370748792533/2000000000000000 : ℝ) by norm_num, show 1+2*(37517795443063983/100000000000000000000 : ℝ)=(50037517795443063983/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (15764517217366735021/15770000000000000000 : ℝ)*(X 1 0+X 2 0)+(147590014439/78850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (259/64 : ℝ)) (lo := (2217/20000 : ℝ)) (hi := (14239/100000 : ℝ)) (c := (15764517217366735021/15770000000000000000 : ℝ)) (alpha := (147590014439/78850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (15764517217366735021/15770000000000000000 : ℝ)*(X 0 1+X 2 1)+(147590014439/78850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (259/64 : ℝ)) (lo := (2217/20000 : ℝ)) (hi := (14239/100000 : ℝ)) (c := (15764517217366735021/15770000000000000000 : ℝ)) (alpha := (147590014439/78850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (15764517217366735021/15770000000000000000 : ℝ)*(X 0 2+X 1 2)+(147590014439/78850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (259/64 : ℝ)) (lo := (2217/20000 : ℝ)) (hi := (14239/100000 : ℝ)) (c := (15764517217366735021/15770000000000000000 : ℝ)) (alpha := (147590014439/78850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1094438511/5000000000 : ℝ)*X 0 0+(5396153151/10000000000 : ℝ)*X 0 1+(8420483/16000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668185351/1250000000 : ℝ)*X 1 0+(-2256560227/10000000000 : ℝ)*X 1 1+(1052560607/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345483181/10000000000 : ℝ)*X 2 0+(5262802373/10000000000 : ℝ)*X 2 1+(-564140151/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4371078939/10000000000 : ℝ)*X 0 0+(4241613487/10000000000 : ℝ)*X 0 1+(4504519267/10000000000 : ℝ)*X 0 2+(4371078939/10000000000 : ℝ)*X 1 0+(4241613487/10000000000 : ℝ)*X 1 1+(4504519267/10000000000 : ℝ)*X 1 2+(4371078939/10000000000 : ℝ)*X 2 0+(4241613487/10000000000 : ℝ)*X 2 1+(4504519267/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-109444111/500000000 : ℝ)*X 0 0+(1052629683/2000000000 : ℝ)*X 0 1+(5395805571/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5311816249/10000000000 : ℝ)*X 1 0+(-2123557417/10000000000 : ℝ)*X 1 1+(5395805461/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((663977033/1250000000 : ℝ)*X 2 0+(5395805503/10000000000 : ℝ)*X 2 1+(-106177867/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2185544647/5000000000 : ℝ)*X 0 0+(900767473/2000000000 : ℝ)*X 0 1+(2121149243/5000000000 : ℝ)*X 0 2+(2185544647/5000000000 : ℝ)*X 1 0+(900767473/2000000000 : ℝ)*X 1 1+(2121149243/5000000000 : ℝ)*X 1 2+(2185544647/5000000000 : ℝ)*X 2 0+(900767473/2000000000 : ℝ)*X 2 1+(2121149243/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3758713852943981891831045163/788500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (614900317/100000000000000 : ℝ)*(base19) + (135316207/12500000000000 : ℝ)*(base23) + (53681489/100000000000000 : ℝ)*(lower2) + (523327563/100000000000000 : ℝ)*(upper3) + (4787073/20000000000000 : ℝ)*(lower4) + (5651392393507299/100000000000000 : ℝ)*(major0) + (5651392393507299/100000000000000 : ℝ)*(major1) + (5651392393507299/100000000000000 : ℝ)*(major2) + (1874764299390607/25000000000000 : ℝ)*(sp0) + (7499104540654783/100000000000000 : ℝ)*(sp1) + (1874776018256361/25000000000000 : ℝ)*(sp2) + (3803655104021351/100000000000000 : ℝ)*(sp3) + (1498687271/3125000000000 : ℝ)*(sp4) + (12184270457/50000000000000 : ℝ)*(sp7) + (475459934070283/12500000000000 : ℝ)*(f.failure) + (74991051555551/1000000000000 : ℝ)*(f.sum) + (4962351094157/7885000000000000000000000000 : ℝ)*base65 + (9987338812120381721/1577000000000000000000000000000000 : ℝ)*base68 + (4390617932873618279/1577000000000000000000000000000000 : ℝ)*base69 + (16619623494498381721/1577000000000000000000000000000000 : ℝ)*base72 + (1183585616303/1971250000000000000000000000 : ℝ)*base73 + (23634846402512618279/1577000000000000000000000000000000 : ℝ)*base75 + (3727482279601618279/1577000000000000000000000000000000 : ℝ)*base77 + (8333059542871618279/1577000000000000000000000000000000 : ℝ)*base79 + (16895954638803/7885000000000000000000000000 : ℝ)*base82 + (2263099/312500000000000000000 : ℝ)*base90 + (2263099/312500000000000000000 : ℝ)*base92 + (2263099/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (105536856831781137968418951/19712500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (491704633/100000000000000 : ℝ)*(base19) + (50861113/6250000000000 : ℝ)*(base23) + (4640691/12500000000000 : ℝ)*(upper3) + (123009533/100000000000000 : ℝ)*(lower4) + (39794139/100000000000000 : ℝ)*(upper5) + (142021863709741/2500000000000 : ℝ)*(major0) + (142021863709741/2500000000000 : ℝ)*(major1) + (142021863709741/2500000000000 : ℝ)*(major2) + (799567081/10000000000000 : ℝ)*(sp1) + (2364381719/12500000000000 : ℝ)*(sp2) + (753822643017337/10000000000000 : ℝ)*(sp4) + (7538217942797927/100000000000000 : ℝ)*(sp5) + (7538206701341809/100000000000000 : ℝ)*(sp6) + (477940311018221/12500000000000 : ℝ)*(sp7) + (477940311018221/12500000000000 : ℝ)*(f.failure) + (753822643017337/10000000000000 : ℝ)*(f.sum) + (37187943423/7885000000000000000000000 : ℝ)*base65 + (761506147938589561/39425000000000000000000000000000 : ℝ)*base67 + (11350049466189561/39425000000000000000000000000000 : ℝ)*base69 + (674604450167964561/39425000000000000000000000000000 : ℝ)*base71 + (16055347255677/1577000000000000000000000000 : ℝ)*base73 + (661344369856714561/39425000000000000000000000000000 : ℝ)*base75 + (428128166189339561/39425000000000000000000000000000 : ℝ)*base77 + (1098841434445564561/39425000000000000000000000000000 : ℝ)*base79 + (1239807043831/394250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (2675413/312500000000000000000 : ℝ)*base90 + (2675413/312500000000000000000 : ℝ)*base92 + (2675413/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1096_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37144247/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14239/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2217/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5623/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1407/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1096_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1096_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37144247/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4161/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8857/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5623/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1407/10000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1096_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1096_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1096_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37144247/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4161/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8857/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5623/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1407/10000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1096_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
