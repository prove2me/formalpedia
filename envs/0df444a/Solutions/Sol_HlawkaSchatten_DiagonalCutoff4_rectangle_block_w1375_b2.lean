-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1375_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:21:30.889991+00:00
-- url     : https://prove2.me/submissions/be0235b6-e07b-440c-b736-1849af65089c

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
theorem support_rectangle_w1375_s6_0 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1007899869/5000000000 : ℝ)*x 0 + (1082201891/2000000000 : ℝ)*x 1 + (2622781289/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1007899869/5000000000 : ℝ)^4335 ≤ (12283789064291/100000000000000 : ℝ)^3311 := by
    have hnat : (1007899869 : ℕ)^4335*100000000000000^3311 ≤ 12283789064291^3311*5000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1007899869 5000000000 12283789064291 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082201891/2000000000 : ℝ)^4335 ≤ (44749553264877/100000000000000 : ℝ)^3311 := by
    have hnat : (1082201891 : ℕ)^4335*100000000000000^3311 ≤ 44749553264877^3311*2000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082201891 2000000000 44749553264877 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622781289/5000000000 : ℝ)^4335 ≤ (2148332883441/5000000000000 : ℝ)^3311 := by
    have hnat : (2622781289 : ℕ)^4335*5000000000000^3311 ≤ 2148332883441^3311*5000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622781289 5000000000 2148332883441 5000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1007899869/5000000000 : ℝ), (1082201891/2000000000 : ℝ), (2622781289/5000000000 : ℝ)] ![(12283789064291/100000000000000 : ℝ), (44749553264877/100000000000000 : ℝ), (2148332883441/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1007899869/5000000000 : ℝ)|^4335 ≤ (12283789064291/100000000000000 : ℝ)^3311
        have hw : |(-1007899869/5000000000 : ℝ)|=(1007899869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1082201891/2000000000 : ℝ)|^4335 ≤ (44749553264877/100000000000000 : ℝ)^3311
        have hw : |(1082201891/2000000000 : ℝ)|=(1082201891/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622781289/5000000000 : ℝ)|^4335 ≤ (2148332883441/5000000000000 : ℝ)^3311
        have hw : |(2622781289/5000000000 : ℝ)|=(2622781289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_s6_1 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348405071/10000000000 : ℝ)*x 0 + (-1050035383/5000000000 : ℝ)*x 1 + (2622781289/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348405071/10000000000 : ℝ)^4335 ≤ (44072901376121/100000000000000 : ℝ)^3311 := by
    have hnat : (5348405071 : ℕ)^4335*100000000000000^3311 ≤ 44072901376121^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348405071 10000000000 44072901376121 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1050035383/5000000000 : ℝ)^4335 ≤ (12960440949723/100000000000000 : ℝ)^3311 := by
    have hnat : (1050035383 : ℕ)^4335*100000000000000^3311 ≤ 12960440949723^3311*5000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050035383 5000000000 12960440949723 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622781289/5000000000 : ℝ)^4335 ≤ (2148332883441/5000000000000 : ℝ)^3311 := by
    have hnat : (2622781289 : ℕ)^4335*5000000000000^3311 ≤ 2148332883441^3311*5000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622781289 5000000000 2148332883441 5000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348405071/10000000000 : ℝ), (-1050035383/5000000000 : ℝ), (2622781289/5000000000 : ℝ)] ![(44072901376121/100000000000000 : ℝ), (12960440949723/100000000000000 : ℝ), (2148332883441/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348405071/10000000000 : ℝ)|^4335 ≤ (44072901376121/100000000000000 : ℝ)^3311
        have hw : |(5348405071/10000000000 : ℝ)|=(5348405071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1050035383/5000000000 : ℝ)|^4335 ≤ (12960440949723/100000000000000 : ℝ)^3311
        have hw : |(-1050035383/5000000000 : ℝ)|=(1050035383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622781289/5000000000 : ℝ)|^4335 ≤ (2148332883441/5000000000000 : ℝ)^3311
        have hw : |(2622781289/5000000000 : ℝ)|=(2622781289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_s6_2 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334275317/625000000 : ℝ)*x 0 + (5245562577/10000000000 : ℝ)*x 1 + (-525017691/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334275317/625000000 : ℝ)^4335 ≤ (4407290138691/10000000000000 : ℝ)^3311 := by
    have hnat : (334275317 : ℕ)^4335*10000000000000^3311 ≤ 4407290138691^3311*625000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334275317 625000000 4407290138691 10000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245562577/10000000000 : ℝ)^4335 ≤ (8593331531619/20000000000000 : ℝ)^3311 := by
    have hnat : (5245562577 : ℕ)^4335*20000000000000^3311 ≤ 8593331531619^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245562577 10000000000 8593331531619 20000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (525017691/2500000000 : ℝ)^4335 ≤ (12960440933563/100000000000000 : ℝ)^3311 := by
    have hnat : (525017691 : ℕ)^4335*100000000000000^3311 ≤ 12960440933563^3311*2500000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525017691 2500000000 12960440933563 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334275317/625000000 : ℝ), (5245562577/10000000000 : ℝ), (-525017691/2500000000 : ℝ)] ![(4407290138691/10000000000000 : ℝ), (8593331531619/20000000000000 : ℝ), (12960440933563/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334275317/625000000 : ℝ)|^4335 ≤ (4407290138691/10000000000000 : ℝ)^3311
        have hw : |(334275317/625000000 : ℝ)|=(334275317/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245562577/10000000000 : ℝ)|^4335 ≤ (8593331531619/20000000000000 : ℝ)^3311
        have hw : |(5245562577/10000000000 : ℝ)|=(5245562577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-525017691/2500000000 : ℝ)|^4335 ≤ (12960440933563/100000000000000 : ℝ)^3311
        have hw : |(-525017691/2500000000 : ℝ)|=(525017691/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_s6_3 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4318063347/10000000000 : ℝ)*x 0 + (4145921193/10000000000 : ℝ)*x 1 + (35131009/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4318063347/10000000000 : ℝ)^4335 ≤ (1332152849557/4000000000000 : ℝ)^3311 := by
    have hnat : (4318063347 : ℕ)^4335*4000000000000^3311 ≤ 1332152849557^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4318063347 10000000000 1332152849557 4000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4145921193/10000000000 : ℝ)^4335 ≤ (31576347336261/100000000000000 : ℝ)^3311 := by
    have hnat : (4145921193 : ℕ)^4335*100000000000000^3311 ≤ 31576347336261^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4145921193 10000000000 31576347336261 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (35131009/78125000 : ℝ)^4335 ≤ (17559915705381/50000000000000 : ℝ)^3311 := by
    have hnat : (35131009 : ℕ)^4335*50000000000000^3311 ≤ 17559915705381^3311*78125000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35131009 78125000 17559915705381 50000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4318063347/10000000000 : ℝ), (4145921193/10000000000 : ℝ), (35131009/78125000 : ℝ)] ![(1332152849557/4000000000000 : ℝ), (31576347336261/100000000000000 : ℝ), (17559915705381/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4318063347/10000000000 : ℝ)|^4335 ≤ (1332152849557/4000000000000 : ℝ)^3311
        have hw : |(4318063347/10000000000 : ℝ)|=(4318063347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4145921193/10000000000 : ℝ)|^4335 ≤ (31576347336261/100000000000000 : ℝ)^3311
        have hw : |(4145921193/10000000000 : ℝ)|=(4145921193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(35131009/78125000 : ℝ)|^4335 ≤ (17559915705381/50000000000000 : ℝ)^3311
        have hw : |(35131009/78125000 : ℝ)|=(35131009/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_s6_4 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-125988219/625000000 : ℝ)*x 0 + (655769589/1250000000 : ℝ)*x 1 + (1352603077/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (125988219/625000000 : ℝ)^4335 ≤ (12283882938031/100000000000000 : ℝ)^3311 := by
    have hnat : (125988219 : ℕ)^4335*100000000000000^3311 ≤ 12283882938031^3311*625000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125988219 625000000 12283882938031 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655769589/1250000000 : ℝ)^4335 ≤ (10743257364627/25000000000000 : ℝ)^3311 := by
    have hnat : (655769589 : ℕ)^4335*25000000000000^3311 ≤ 10743257364627^3311*1250000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655769589 1250000000 10743257364627 25000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1352603077/2500000000 : ℝ)^4335 ≤ (44743087585341/100000000000000 : ℝ)^3311 := by
    have hnat : (1352603077 : ℕ)^4335*100000000000000^3311 ≤ 44743087585341^3311*2500000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352603077 2500000000 44743087585341 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-125988219/625000000 : ℝ), (655769589/1250000000 : ℝ), (1352603077/2500000000 : ℝ)] ![(12283882938031/100000000000000 : ℝ), (10743257364627/25000000000000 : ℝ), (44743087585341/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-125988219/625000000 : ℝ)|^4335 ≤ (12283882938031/100000000000000 : ℝ)^3311
        have hw : |(-125988219/625000000 : ℝ)|=(125988219/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655769589/1250000000 : ℝ)|^4335 ≤ (10743257364627/25000000000000 : ℝ)^3311
        have hw : |(655769589/1250000000 : ℝ)|=(655769589/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1352603077/2500000000 : ℝ)|^4335 ≤ (44743087585341/100000000000000 : ℝ)^3311
        have hw : |(1352603077/2500000000 : ℝ)|=(1352603077/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_s6_5 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652815897/5000000000 : ℝ)*x 0 + (-1935221027/10000000000 : ℝ)*x 1 + (5410412643/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652815897/5000000000 : ℝ)^4335 ≤ (8722399282811/20000000000000 : ℝ)^3311 := by
    have hnat : (2652815897 : ℕ)^4335*20000000000000^3311 ≤ 8722399282811^3311*5000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652815897 5000000000 8722399282811 20000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1935221027/10000000000 : ℝ)^4335 ≤ (116449123613/1000000000000 : ℝ)^3311 := by
    have hnat : (1935221027 : ℕ)^4335*1000000000000^3311 ≤ 116449123613^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1935221027 10000000000 116449123613 1000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410412643/10000000000 : ℝ)^4335 ≤ (44743091212531/100000000000000 : ℝ)^3311 := by
    have hnat : (5410412643 : ℕ)^4335*100000000000000^3311 ≤ 44743091212531^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410412643 10000000000 44743091212531 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652815897/5000000000 : ℝ), (-1935221027/10000000000 : ℝ), (5410412643/10000000000 : ℝ)] ![(8722399282811/20000000000000 : ℝ), (116449123613/1000000000000 : ℝ), (44743091212531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652815897/5000000000 : ℝ)|^4335 ≤ (8722399282811/20000000000000 : ℝ)^3311
        have hw : |(2652815897/5000000000 : ℝ)|=(2652815897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1935221027/10000000000 : ℝ)|^4335 ≤ (116449123613/1000000000000 : ℝ)^3311
        have hw : |(-1935221027/10000000000 : ℝ)|=(1935221027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410412643/10000000000 : ℝ)|^4335 ≤ (44743091212531/100000000000000 : ℝ)^3311
        have hw : |(5410412643/10000000000 : ℝ)|=(5410412643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_s6_6 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326407997/2500000000 : ℝ)*x 0 + (169075397/312500000 : ℝ)*x 1 + (-1935220677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326407997/2500000000 : ℝ)^4335 ≤ (43611998501911/100000000000000 : ℝ)^3311 := by
    have hnat : (1326407997 : ℕ)^4335*100000000000000^3311 ≤ 43611998501911^3311*2500000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326407997 2500000000 43611998501911 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169075397/312500000 : ℝ)^4335 ≤ (11185772968251/25000000000000 : ℝ)^3311 := by
    have hnat : (169075397 : ℕ)^4335*25000000000000^3311 ≤ 11185772968251^3311*312500000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169075397 312500000 11185772968251 25000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1935220677/10000000000 : ℝ)^4335 ≤ (93159276831/800000000000 : ℝ)^3311 := by
    have hnat : (1935220677 : ℕ)^4335*800000000000^3311 ≤ 93159276831^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1935220677 10000000000 93159276831 800000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326407997/2500000000 : ℝ), (169075397/312500000 : ℝ), (-1935220677/10000000000 : ℝ)] ![(43611998501911/100000000000000 : ℝ), (11185772968251/25000000000000 : ℝ), (93159276831/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326407997/2500000000 : ℝ)|^4335 ≤ (43611998501911/100000000000000 : ℝ)^3311
        have hw : |(1326407997/2500000000 : ℝ)|=(1326407997/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(169075397/312500000 : ℝ)|^4335 ≤ (11185772968251/25000000000000 : ℝ)^3311
        have hw : |(169075397/312500000 : ℝ)|=(169075397/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1935220677/10000000000 : ℝ)|^4335 ≤ (93159276831/800000000000 : ℝ)^3311
        have hw : |(-1935220677/10000000000 : ℝ)|=(1935220677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_s6_7 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4318089121/10000000000 : ℝ)*x 0 + (4495509097/10000000000 : ℝ)*x 1 + (4147187089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4318089121/10000000000 : ℝ)^4335 ≤ (6660816300957/20000000000000 : ℝ)^3311 := by
    have hnat : (4318089121 : ℕ)^4335*20000000000000^3311 ≤ 6660816300957^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4318089121 10000000000 6660816300957 20000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4495509097/10000000000 : ℝ)^4335 ≤ (17553473679923/50000000000000 : ℝ)^3311 := by
    have hnat : (4495509097 : ℕ)^4335*50000000000000^3311 ≤ 17553473679923^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4495509097 10000000000 17553473679923 50000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4147187089/10000000000 : ℝ)^4335 ≤ (1579448555643/5000000000000 : ℝ)^3311 := by
    have hnat : (4147187089 : ℕ)^4335*5000000000000^3311 ≤ 1579448555643^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4147187089 10000000000 1579448555643 5000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4318089121/10000000000 : ℝ), (4495509097/10000000000 : ℝ), (4147187089/10000000000 : ℝ)] ![(6660816300957/20000000000000 : ℝ), (17553473679923/50000000000000 : ℝ), (1579448555643/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4318089121/10000000000 : ℝ)|^4335 ≤ (6660816300957/20000000000000 : ℝ)^3311
        have hw : |(4318089121/10000000000 : ℝ)|=(4318089121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4495509097/10000000000 : ℝ)|^4335 ≤ (17553473679923/50000000000000 : ℝ)^3311
        have hw : |(4495509097/10000000000 : ℝ)|=(4495509097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4147187089/10000000000 : ℝ)|^4335 ≤ (1579448555643/5000000000000 : ℝ)^3311
        have hw : |(4147187089/10000000000 : ℝ)|=(4147187089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1375_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39007599/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14733/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11219/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1403/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1841/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14733/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11219/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14733/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11219/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14733/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11219/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14733/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11219/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14733/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11219/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14733/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11219/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11219/100000 : ℝ) ^ (2167/512 : ℝ) ≤ (476403735530387/5000000000000000000 : ℝ) := by
    have hpowers : (11219/100000 : ℝ)^2167 ≤ (476403735530387/5000000000000000000 : ℝ)^512 := by
      have hnat : (11219 : ℕ)^2167*5000000000000000000^512 ≤ 476403735530387^512*100000^2167 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11219 100000 476403735530387 5000000000000000000 2167 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11219/100000 : ℝ)) (X := (476403735530387/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2167 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14733/100000 : ℝ) ^ (2167/512 : ℝ) ≤ (30189605229479727/100000000000000000000 : ℝ) := by
    have hpowers : (14733/100000 : ℝ)^2167 ≤ (30189605229479727/100000000000000000000 : ℝ)^512 := by
      have hnat : (14733 : ℕ)^2167*100000000000000000000^512 ≤ 30189605229479727^512*100000^2167 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14733 100000 30189605229479727 100000000000000000000 2167 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14733/100000 : ℝ)) (X := (30189605229479727/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2167 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500476403735530387/2500000000000000000 : ℝ) ≤ (1250056276180191/1250000000000000 : ℝ) ^ (2167/512 : ℝ) := by
    have hpowers : (2500476403735530387/2500000000000000000 : ℝ)^512 ≤ (1250056276180191/1250000000000000 : ℝ)^2167 := by
      have hnat : (2500476403735530387 : ℕ)^512*1250000000000000^2167 ≤ 1250056276180191^2167*2500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500476403735530387 2500000000000000000 1250056276180191 1250000000000000 512 2167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250056276180191/1250000000000000 : ℝ)) (X := (2500476403735530387/2500000000000000000 : ℝ)) (by norm_num) 2167 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100039717679940087467/100000000000000000000 : ℝ) ≤ (5000469136331773/5000000000000000 : ℝ) ^ (2167/512 : ℝ) := by
    have hpowers : (100039717679940087467/100000000000000000000 : ℝ)^512 ≤ (5000469136331773/5000000000000000 : ℝ)^2167 := by
      have hnat : (100039717679940087467 : ℕ)^512*5000000000000000^2167 ≤ 5000469136331773^2167*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100039717679940087467 100000000000000000000 5000469136331773 5000000000000000 512 2167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000469136331773/5000000000000000 : ℝ)) (X := (100039717679940087467/100000000000000000000 : ℝ)) (by norm_num) 2167 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50030189605229479727/50000000000000000000 : ℝ) ≤ (2500356583971391/2500000000000000 : ℝ) ^ (2167/512 : ℝ) := by
    have hpowers : (50030189605229479727/50000000000000000000 : ℝ)^512 ≤ (2500356583971391/2500000000000000 : ℝ)^2167 := by
      have hnat : (50030189605229479727 : ℕ)^512*2500000000000000^2167 ≤ 2500356583971391^2167*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030189605229479727 50000000000000000000 2500356583971391 2500000000000000 512 2167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500356583971391/2500000000000000 : ℝ)) (X := (50030189605229479727/50000000000000000000 : ℝ)) (by norm_num) 2167 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(476403735530387/5000000000000000000 : ℝ) ≤ ((8782657718350472377/8785000000000000000 : ℝ)+2*(244031611009/175700000000000 : ℝ)*(11219/100000 : ℝ))^(2167/512 : ℝ) := by
    rw [show (8782657718350472377/8785000000000000000 : ℝ)+2*(244031611009/175700000000000 : ℝ)*(11219/100000 : ℝ)=(1250056276180191/1250000000000000 : ℝ) by norm_num, show 1+2*(476403735530387/5000000000000000000 : ℝ)=(2500476403735530387/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30189605229479727/100000000000000000000 : ℝ)+(476403735530387/5000000000000000000 : ℝ) ≤ ((8782657718350472377/8785000000000000000 : ℝ)+(244031611009/175700000000000 : ℝ)*((14733/100000 : ℝ)+(11219/100000 : ℝ)))^(2167/512 : ℝ) := by
    rw [show (8782657718350472377/8785000000000000000 : ℝ)+(244031611009/175700000000000 : ℝ)*((14733/100000 : ℝ)+(11219/100000 : ℝ))=(5000469136331773/5000000000000000 : ℝ) by norm_num, show 1+(30189605229479727/100000000000000000000 : ℝ)+(476403735530387/5000000000000000000 : ℝ)=(100039717679940087467/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30189605229479727/100000000000000000000 : ℝ) ≤ ((8782657718350472377/8785000000000000000 : ℝ)+2*(244031611009/175700000000000 : ℝ)*(14733/100000 : ℝ))^(2167/512 : ℝ) := by
    rw [show (8782657718350472377/8785000000000000000 : ℝ)+2*(244031611009/175700000000000 : ℝ)*(14733/100000 : ℝ)=(2500356583971391/2500000000000000 : ℝ) by norm_num, show 1+2*(30189605229479727/100000000000000000000 : ℝ)=(50030189605229479727/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8782657718350472377/8785000000000000000 : ℝ)*(X 1 0+X 2 0)+(244031611009/175700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2167/512 : ℝ)) (lo := (11219/100000 : ℝ)) (hi := (14733/100000 : ℝ)) (c := (8782657718350472377/8785000000000000000 : ℝ)) (alpha := (244031611009/175700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8782657718350472377/8785000000000000000 : ℝ)*(X 0 1+X 2 1)+(244031611009/175700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2167/512 : ℝ)) (lo := (11219/100000 : ℝ)) (hi := (14733/100000 : ℝ)) (c := (8782657718350472377/8785000000000000000 : ℝ)) (alpha := (244031611009/175700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8782657718350472377/8785000000000000000 : ℝ)*(X 0 2+X 1 2)+(244031611009/175700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2167/512 : ℝ)) (lo := (11219/100000 : ℝ)) (hi := (14733/100000 : ℝ)) (c := (8782657718350472377/8785000000000000000 : ℝ)) (alpha := (244031611009/175700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1007899869/5000000000 : ℝ)*X 0 0+(1082201891/2000000000 : ℝ)*X 0 1+(2622781289/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348405071/10000000000 : ℝ)*X 1 0+(-1050035383/5000000000 : ℝ)*X 1 1+(2622781289/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334275317/625000000 : ℝ)*X 2 0+(5245562577/10000000000 : ℝ)*X 2 1+(-525017691/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4318063347/10000000000 : ℝ)*X 0 0+(4145921193/10000000000 : ℝ)*X 0 1+(35131009/78125000 : ℝ)*X 0 2+(4318063347/10000000000 : ℝ)*X 1 0+(4145921193/10000000000 : ℝ)*X 1 1+(35131009/78125000 : ℝ)*X 1 2+(4318063347/10000000000 : ℝ)*X 2 0+(4145921193/10000000000 : ℝ)*X 2 1+(35131009/78125000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-125988219/625000000 : ℝ)*X 0 0+(655769589/1250000000 : ℝ)*X 0 1+(1352603077/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652815897/5000000000 : ℝ)*X 1 0+(-1935221027/10000000000 : ℝ)*X 1 1+(5410412643/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326407997/2500000000 : ℝ)*X 2 0+(169075397/312500000 : ℝ)*X 2 1+(-1935220677/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4318089121/10000000000 : ℝ)*X 0 0+(4495509097/10000000000 : ℝ)*X 0 1+(4147187089/10000000000 : ℝ)*X 0 2+(4318089121/10000000000 : ℝ)*X 1 0+(4495509097/10000000000 : ℝ)*X 1 1+(4147187089/10000000000 : ℝ)*X 1 2+(4318089121/10000000000 : ℝ)*X 2 0+(4495509097/10000000000 : ℝ)*X 2 1+(4147187089/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1106043011945295269138607099/109812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (116898499/6250000000000 : ℝ)*(base19) + (348994093/20000000000000 : ℝ)*(base23) + (33838191/50000000000000 : ℝ)*(lower2) + (31489453/12500000000000 : ℝ)*(upper3) + (160717071/100000000000000 : ℝ)*(upper5) + (1111823786341329/25000000000000 : ℝ)*(major0) + (1111823786341329/25000000000000 : ℝ)*(major1) + (1111823786341329/25000000000000 : ℝ)*(major2) + (6044276436643901/100000000000000 : ℝ)*(sp0) + (1208862645664589/20000000000000 : ℝ)*(sp1) + (6044313353728463/100000000000000 : ℝ)*(sp2) + (2850255152024929/100000000000000 : ℝ)*(sp3) + (19331027513/50000000000000 : ℝ)*(sp4) + (19704269941/100000000000000 : ℝ)*(sp7) + (285027485629487/10000000000000 : ℝ)*(f.failure) + (377769693668683/6250000000000 : ℝ)*(f.sum) + (23811631122487/4392500000000000000000000000 : ℝ)*base65 + (300148372751394033/219625000000000000000000000000000 : ℝ)*base67 + (424962606675355967/219625000000000000000000000000000 : ℝ)*base70 + (425657626679355967/219625000000000000000000000000000 : ℝ)*base72 + (11432797071051/2196250000000000000000000000 : ℝ)*base73 + (2566208716671355967/219625000000000000000000000000000 : ℝ)*base76 + (811387263358980967/219625000000000000000000000000000 : ℝ)*base78 + (785473351277894033/219625000000000000000000000000000 : ℝ)*base79 + (15034829977219/8785000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base85 + (1471713/250000000000000000000 : ℝ)*base89 + (1471713/250000000000000000000 : ℝ)*base91 + (1471713/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (52501184527032849408009/4392500000000000000000000000 : ℝ) := by norm_num
    linear_combination (74095899/5000000000000 : ℝ)*(base19) + (2530914261/100000000000000 : ℝ)*(base23) + (345122449/100000000000000 : ℝ)*(upper3) + (79140239/25000000000000 : ℝ)*(lower4) + (59550647/20000000000000 : ℝ)*(upper5) + (4479486870178011/100000000000000 : ℝ)*(major0) + (4479486870178011/100000000000000 : ℝ)*(major1) + (4479486870178011/100000000000000 : ℝ)*(major2) + (8173593821/25000000000000 : ℝ)*(sp1) + (61191275501/100000000000000 : ℝ)*(sp2) + (1522016696154899/25000000000000 : ℝ)*(sp4) + (6088032608326333/100000000000000 : ℝ)*(sp5) + (3044001531214917/50000000000000 : ℝ)*(sp6) + (89715829916283/3125000000000 : ℝ)*(sp7) + (89715829916283/3125000000000 : ℝ)*(f.failure) + (1522016696154899/25000000000000 : ℝ)*(f.sum) + (17159640664379/8785000000000000000000000000 : ℝ)*base65 + (914276355660747853/878500000000000000000000000000000 : ℝ)*base68 + (1220251316651252147/878500000000000000000000000000000 : ℝ)*base69 + (2165834506363747853/878500000000000000000000000000000 : ℝ)*base72 + (12502842173523/4392500000000000000000000000 : ℝ)*base74 + (18699879117934247853/878500000000000000000000000000000 : ℝ)*base76 + (1032982097143252147/878500000000000000000000000000000 : ℝ)*base77 + (4354431759950752147/878500000000000000000000000000000 : ℝ)*base79 + (10168395259529/8785000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (259233/78125000000000000000 : ℝ)*base90 + (259233/78125000000000000000 : ℝ)*base92 + (259233/78125000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1375_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39007599/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14733/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11219/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1403/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1841/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1375_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1375_s7_0 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-503950869/2500000000 : ℝ)*x 0 + (676371283/1250000000 : ℝ)*x 1 + (1049119873/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (503950869/2500000000 : ℝ)^4335 ≤ (2456763777499/20000000000000 : ℝ)^3311 := by
    have hnat : (503950869 : ℕ)^4335*20000000000000^3311 ≤ 2456763777499^3311*2500000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      503950869 2500000000 2456763777499 20000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676371283/1250000000 : ℝ)^4335 ≤ (22374564456469/50000000000000 : ℝ)^3311 := by
    have hnat : (676371283 : ℕ)^4335*50000000000000^3311 ≤ 22374564456469^3311*1250000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676371283 1250000000 22374564456469 50000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1049119873/2000000000 : ℝ)^4335 ≤ (8593410436899/20000000000000 : ℝ)^3311 := by
    have hnat : (1049119873 : ℕ)^4335*20000000000000^3311 ≤ 8593410436899^3311*2000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049119873 2000000000 8593410436899 20000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-503950869/2500000000 : ℝ), (676371283/1250000000 : ℝ), (1049119873/2000000000 : ℝ)] ![(2456763777499/20000000000000 : ℝ), (22374564456469/50000000000000 : ℝ), (8593410436899/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-503950869/2500000000 : ℝ)|^4335 ≤ (2456763777499/20000000000000 : ℝ)^3311
        have hw : |(-503950869/2500000000 : ℝ)|=(503950869/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676371283/1250000000 : ℝ)|^4335 ≤ (22374564456469/50000000000000 : ℝ)^3311
        have hw : |(676371283/1250000000 : ℝ)|=(676371283/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1049119873/2000000000 : ℝ)|^4335 ≤ (8593410436899/20000000000000 : ℝ)^3311
        have hw : |(1049119873/2000000000 : ℝ)|=(1049119873/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_s7_1 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348395219/10000000000 : ℝ)*x 0 + (-1050017551/5000000000 : ℝ)*x 1 + (5245599359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348395219/10000000000 : ℝ)^4335 ≤ (44072795083883/100000000000000 : ℝ)^3311 := by
    have hnat : (5348395219 : ℕ)^4335*100000000000000^3311 ≤ 44072795083883^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348395219 10000000000 44072795083883 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1050017551/5000000000 : ℝ)^4335 ≤ (2592030556487/20000000000000 : ℝ)^3311 := by
    have hnat : (1050017551 : ℕ)^4335*20000000000000^3311 ≤ 2592030556487^3311*5000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050017551 5000000000 2592030556487 20000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245599359/10000000000 : ℝ)^4335 ≤ (42967052120149/100000000000000 : ℝ)^3311 := by
    have hnat : (5245599359 : ℕ)^4335*100000000000000^3311 ≤ 42967052120149^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245599359 10000000000 42967052120149 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348395219/10000000000 : ℝ), (-1050017551/5000000000 : ℝ), (5245599359/10000000000 : ℝ)] ![(44072795083883/100000000000000 : ℝ), (2592030556487/20000000000000 : ℝ), (42967052120149/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348395219/10000000000 : ℝ)|^4335 ≤ (44072795083883/100000000000000 : ℝ)^3311
        have hw : |(5348395219/10000000000 : ℝ)|=(5348395219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1050017551/5000000000 : ℝ)|^4335 ≤ (2592030556487/20000000000000 : ℝ)^3311
        have hw : |(-1050017551/5000000000 : ℝ)|=(1050017551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245599359/10000000000 : ℝ)|^4335 ≤ (42967052120149/100000000000000 : ℝ)^3311
        have hw : |(5245599359/10000000000 : ℝ)|=(5245599359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_s7_2 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674197611/5000000000 : ℝ)*x 0 + (5245599349/10000000000 : ℝ)*x 1 + (-262504389/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674197611/5000000000 : ℝ)^4335 ≤ (35258236093/80000000000 : ℝ)^3311 := by
    have hnat : (2674197611 : ℕ)^4335*80000000000^3311 ≤ 35258236093^3311*5000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674197611 5000000000 35258236093 80000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245599349/10000000000 : ℝ)^4335 ≤ (21483526006453/50000000000000 : ℝ)^3311 := by
    have hnat : (5245599349 : ℕ)^4335*50000000000000^3311 ≤ 21483526006453^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245599349 10000000000 21483526006453 50000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262504389/1250000000 : ℝ)^4335 ≤ (2592030572647/20000000000000 : ℝ)^3311 := by
    have hnat : (262504389 : ℕ)^4335*20000000000000^3311 ≤ 2592030572647^3311*1250000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262504389 1250000000 2592030572647 20000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674197611/5000000000 : ℝ), (5245599349/10000000000 : ℝ), (-262504389/1250000000 : ℝ)] ![(35258236093/80000000000 : ℝ), (21483526006453/50000000000000 : ℝ), (2592030572647/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674197611/5000000000 : ℝ)|^4335 ≤ (35258236093/80000000000 : ℝ)^3311
        have hw : |(2674197611/5000000000 : ℝ)|=(2674197611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245599349/10000000000 : ℝ)|^4335 ≤ (21483526006453/50000000000000 : ℝ)^3311
        have hw : |(5245599349/10000000000 : ℝ)|=(5245599349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-262504389/1250000000 : ℝ)|^4335 ≤ (2592030572647/20000000000000 : ℝ)^3311
        have hw : |(-262504389/1250000000 : ℝ)|=(262504389/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_s7_3 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4318065983/10000000000 : ℝ)*x 0 + (4146001421/10000000000 : ℝ)*x 1 + (4496688311/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4318065983/10000000000 : ℝ)^4335 ≤ (2081490491077/6250000000000 : ℝ)^3311 := by
    have hnat : (4318065983 : ℕ)^4335*6250000000000^3311 ≤ 2081490491077^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4318065983 10000000000 2081490491077 6250000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4146001421/10000000000 : ℝ)^4335 ≤ (6315429470217/20000000000000 : ℝ)^3311 := by
    have hnat : (4146001421 : ℕ)^4335*20000000000000^3311 ≤ 6315429470217^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4146001421 10000000000 6315429470217 20000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4496688311/10000000000 : ℝ)^4335 ≤ (8779751194687/25000000000000 : ℝ)^3311 := by
    have hnat : (4496688311 : ℕ)^4335*25000000000000^3311 ≤ 8779751194687^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4496688311 10000000000 8779751194687 25000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4318065983/10000000000 : ℝ), (4146001421/10000000000 : ℝ), (4496688311/10000000000 : ℝ)] ![(2081490491077/6250000000000 : ℝ), (6315429470217/20000000000000 : ℝ), (8779751194687/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4318065983/10000000000 : ℝ)|^4335 ≤ (2081490491077/6250000000000 : ℝ)^3311
        have hw : |(4318065983/10000000000 : ℝ)|=(4318065983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4146001421/10000000000 : ℝ)|^4335 ≤ (6315429470217/20000000000000 : ℝ)^3311
        have hw : |(4146001421/10000000000 : ℝ)|=(4146001421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4496688311/10000000000 : ℝ)|^4335 ≤ (8779751194687/25000000000000 : ℝ)^3311
        have hw : |(4496688311/10000000000 : ℝ)|=(4496688311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_s7_4 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-50395383/250000000 : ℝ)*x 0 + (1311548189/2500000000 : ℝ)*x 1 + (1082074759/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (50395383/250000000 : ℝ)^4335 ≤ (2456782676721/20000000000000 : ℝ)^3311 := by
    have hnat : (50395383 : ℕ)^4335*20000000000000^3311 ≤ 2456782676721^3311*250000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50395383 250000000 2456782676721 20000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311548189/2500000000 : ℝ)^4335 ≤ (21486708009771/50000000000000 : ℝ)^3311 := by
    have hnat : (1311548189 : ℕ)^4335*50000000000000^3311 ≤ 21486708009771^3311*2500000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311548189 2500000000 21486708009771 50000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082074759/2000000000 : ℝ)^4335 ≤ (44742670588869/100000000000000 : ℝ)^3311 := by
    have hnat : (1082074759 : ℕ)^4335*100000000000000^3311 ≤ 44742670588869^3311*2000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082074759 2000000000 44742670588869 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-50395383/250000000 : ℝ), (1311548189/2500000000 : ℝ), (1082074759/2000000000 : ℝ)] ![(2456782676721/20000000000000 : ℝ), (21486708009771/50000000000000 : ℝ), (44742670588869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-50395383/250000000 : ℝ)|^4335 ≤ (2456782676721/20000000000000 : ℝ)^3311
        have hw : |(-50395383/250000000 : ℝ)|=(50395383/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311548189/2500000000 : ℝ)|^4335 ≤ (21486708009771/50000000000000 : ℝ)^3311
        have hw : |(1311548189/2500000000 : ℝ)|=(1311548189/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082074759/2000000000 : ℝ)|^4335 ≤ (44742670588869/100000000000000 : ℝ)^3311
        have hw : |(1082074759/2000000000 : ℝ)|=(1082074759/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_s7_5 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305641863/10000000000 : ℝ)*x 0 + (-387052141/2000000000 : ℝ)*x 1 + (1352593441/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305641863/10000000000 : ℝ)^4335 ≤ (43612104778111/100000000000000 : ℝ)^3311 := by
    have hnat : (5305641863 : ℕ)^4335*100000000000000^3311 ≤ 43612104778111^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305641863 10000000000 43612104778111 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (387052141/2000000000 : ℝ)^4335 ≤ (5822612479839/50000000000000 : ℝ)^3311 := by
    have hnat : (387052141 : ℕ)^4335*50000000000000^3311 ≤ 5822612479839^3311*2000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      387052141 2000000000 5822612479839 50000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1352593441/2500000000 : ℝ)^4335 ≤ (44742670253219/100000000000000 : ℝ)^3311 := by
    have hnat : (1352593441 : ℕ)^4335*100000000000000^3311 ≤ 44742670253219^3311*2500000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352593441 2500000000 44742670253219 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305641863/10000000000 : ℝ), (-387052141/2000000000 : ℝ), (1352593441/2500000000 : ℝ)] ![(43612104778111/100000000000000 : ℝ), (5822612479839/50000000000000 : ℝ), (44742670253219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305641863/10000000000 : ℝ)|^4335 ≤ (43612104778111/100000000000000 : ℝ)^3311
        have hw : |(5305641863/10000000000 : ℝ)|=(5305641863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-387052141/2000000000 : ℝ)|^4335 ≤ (5822612479839/50000000000000 : ℝ)^3311
        have hw : |(-387052141/2000000000 : ℝ)|=(387052141/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1352593441/2500000000 : ℝ)|^4335 ≤ (44742670253219/100000000000000 : ℝ)^3311
        have hw : |(1352593441/2500000000 : ℝ)|=(1352593441/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_s7_6 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326410457/2500000000 : ℝ)*x 0 + (2705186901/5000000000 : ℝ)*x 1 + (-1935260699/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326410457/2500000000 : ℝ)^4335 ≤ (8722420880287/20000000000000 : ℝ)^3311 := by
    have hnat : (1326410457 : ℕ)^4335*20000000000000^3311 ≤ 8722420880287^3311*2500000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326410457 2500000000 8722420880287 20000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2705186901/5000000000 : ℝ)^4335 ≤ (44742670664661/100000000000000 : ℝ)^3311 := by
    have hnat : (2705186901 : ℕ)^4335*100000000000000^3311 ≤ 44742670664661^3311*5000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705186901 5000000000 44742670664661 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1935260699/10000000000 : ℝ)^4335 ≤ (1455653114051/12500000000000 : ℝ)^3311 := by
    have hnat : (1935260699 : ℕ)^4335*12500000000000^3311 ≤ 1455653114051^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1935260699 10000000000 1455653114051 12500000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326410457/2500000000 : ℝ), (2705186901/5000000000 : ℝ), (-1935260699/10000000000 : ℝ)] ![(8722420880287/20000000000000 : ℝ), (44742670664661/100000000000000 : ℝ), (1455653114051/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326410457/2500000000 : ℝ)|^4335 ≤ (8722420880287/20000000000000 : ℝ)^3311
        have hw : |(1326410457/2500000000 : ℝ)|=(1326410457/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2705186901/5000000000 : ℝ)|^4335 ≤ (44742670664661/100000000000000 : ℝ)^3311
        have hw : |(2705186901/5000000000 : ℝ)|=(2705186901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1935260699/10000000000 : ℝ)|^4335 ≤ (1455653114051/12500000000000 : ℝ)^3311
        have hw : |(-1935260699/10000000000 : ℝ)|=(1935260699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_s7_7 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (431809111/1000000000 : ℝ)*x 0 + (112385747/250000000 : ℝ)*x 1 + (4147266293/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (431809111/1000000000 : ℝ)^4335 ≤ (1040753174679/3125000000000 : ℝ)^3311 := by
    have hnat : (431809111 : ℕ)^4335*3125000000000^3311 ≤ 1040753174679^3311*1000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431809111 1000000000 1040753174679 3125000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (112385747/250000000 : ℝ)^4335 ≤ (8776534351013/25000000000000 : ℝ)^3311 := by
    have hnat : (112385747 : ℕ)^4335*25000000000000^3311 ≤ 8776534351013^3311*250000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112385747 250000000 8776534351013 25000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4147266293/10000000000 : ℝ)^4335 ≤ (31589760991139/100000000000000 : ℝ)^3311 := by
    have hnat : (4147266293 : ℕ)^4335*100000000000000^3311 ≤ 31589760991139^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4147266293 10000000000 31589760991139 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(431809111/1000000000 : ℝ), (112385747/250000000 : ℝ), (4147266293/10000000000 : ℝ)] ![(1040753174679/3125000000000 : ℝ), (8776534351013/25000000000000 : ℝ), (31589760991139/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(431809111/1000000000 : ℝ)|^4335 ≤ (1040753174679/3125000000000 : ℝ)^3311
        have hw : |(431809111/1000000000 : ℝ)|=(431809111/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(112385747/250000000 : ℝ)|^4335 ≤ (8776534351013/25000000000000 : ℝ)^3311
        have hw : |(112385747/250000000 : ℝ)|=(112385747/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4147266293/10000000000 : ℝ)|^4335 ≤ (31589760991139/100000000000000 : ℝ)^3311
        have hw : |(4147266293/10000000000 : ℝ)|=(4147266293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1375_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39007599/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1841/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1403/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (449/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14727/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1841/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1403/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1841/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1403/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1841/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1403/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1841/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1403/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1841/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1403/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1841/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1403/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1403/12500 : ℝ) ^ (2167/512 : ℝ) ≤ (9546060221310919/100000000000000000000 : ℝ) := by
    have hpowers : (1403/12500 : ℝ)^2167 ≤ (9546060221310919/100000000000000000000 : ℝ)^512 := by
      have hnat : (1403 : ℕ)^2167*100000000000000000000^512 ≤ 9546060221310919^512*12500^2167 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1403 12500 9546060221310919 100000000000000000000 2167 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1403/12500 : ℝ)) (X := (9546060221310919/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2167 512 (by norm_num) hpowers
    exact h
  have hpowhi : (1841/12500 : ℝ) ^ (2167/512 : ℝ) ≤ (753656635534347/2500000000000000000 : ℝ) := by
    have hpowers : (1841/12500 : ℝ)^2167 ≤ (753656635534347/2500000000000000000 : ℝ)^512 := by
      have hnat : (1841 : ℕ)^2167*2500000000000000000^512 ≤ 753656635534347^512*12500^2167 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1841 12500 753656635534347 2500000000000000000 2167 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1841/12500 : ℝ)) (X := (753656635534347/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2167 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009546060221310919/50000000000000000000 : ℝ) ≤ (5000225529604947/5000000000000000 : ℝ) ^ (2167/512 : ℝ) := by
    have hpowers : (50009546060221310919/50000000000000000000 : ℝ)^512 ≤ (5000225529604947/5000000000000000 : ℝ)^2167 := by
      have hnat : (50009546060221310919 : ℕ)^512*5000000000000000^2167 ≤ 5000225529604947^2167*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009546060221310919 50000000000000000000 5000225529604947 5000000000000000 512 2167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000225529604947/5000000000000000 : ℝ)) (X := (50009546060221310919/50000000000000000000 : ℝ)) (by norm_num) 2167 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100039692325642684799/100000000000000000000 : ℝ) ≤ (2500234418448937/2500000000000000 : ℝ) ^ (2167/512 : ℝ) := by
    have hpowers : (100039692325642684799/100000000000000000000 : ℝ)^512 ≤ (2500234418448937/2500000000000000 : ℝ)^2167 := by
      have hnat : (100039692325642684799 : ℕ)^512*2500000000000000^2167 ≤ 2500234418448937^2167*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100039692325642684799 100000000000000000000 2500234418448937 2500000000000000 512 2167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500234418448937/2500000000000000 : ℝ)) (X := (100039692325642684799/100000000000000000000 : ℝ)) (by norm_num) 2167 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (1250753656635534347/1250000000000000000 : ℝ) ≤ (5000712144190801/5000000000000000 : ℝ) ^ (2167/512 : ℝ) := by
    have hpowers : (1250753656635534347/1250000000000000000 : ℝ)^512 ≤ (5000712144190801/5000000000000000 : ℝ)^2167 := by
      have hnat : (1250753656635534347 : ℕ)^512*5000000000000000^2167 ≤ 5000712144190801^2167*1250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250753656635534347 1250000000000000000 5000712144190801 5000000000000000 512 2167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000712144190801/5000000000000000 : ℝ)) (X := (1250753656635534347/1250000000000000000 : ℝ)) (by norm_num) 2167 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9546060221310919/100000000000000000000 : ℝ) ≤ ((273677007712876703/273750000000000000 : ℝ)+2*(243307292927/175200000000000 : ℝ)*(1403/12500 : ℝ))^(2167/512 : ℝ) := by
    rw [show (273677007712876703/273750000000000000 : ℝ)+2*(243307292927/175200000000000 : ℝ)*(1403/12500 : ℝ)=(5000225529604947/5000000000000000 : ℝ) by norm_num, show 1+2*(9546060221310919/100000000000000000000 : ℝ)=(50009546060221310919/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(753656635534347/2500000000000000000 : ℝ)+(9546060221310919/100000000000000000000 : ℝ) ≤ ((273677007712876703/273750000000000000 : ℝ)+(243307292927/175200000000000 : ℝ)*((1841/12500 : ℝ)+(1403/12500 : ℝ)))^(2167/512 : ℝ) := by
    rw [show (273677007712876703/273750000000000000 : ℝ)+(243307292927/175200000000000 : ℝ)*((1841/12500 : ℝ)+(1403/12500 : ℝ))=(2500234418448937/2500000000000000 : ℝ) by norm_num, show 1+(753656635534347/2500000000000000000 : ℝ)+(9546060221310919/100000000000000000000 : ℝ)=(100039692325642684799/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(753656635534347/2500000000000000000 : ℝ) ≤ ((273677007712876703/273750000000000000 : ℝ)+2*(243307292927/175200000000000 : ℝ)*(1841/12500 : ℝ))^(2167/512 : ℝ) := by
    rw [show (273677007712876703/273750000000000000 : ℝ)+2*(243307292927/175200000000000 : ℝ)*(1841/12500 : ℝ)=(5000712144190801/5000000000000000 : ℝ) by norm_num, show 1+2*(753656635534347/2500000000000000000 : ℝ)=(1250753656635534347/1250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (273677007712876703/273750000000000000 : ℝ)*(X 1 0+X 2 0)+(243307292927/175200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2167/512 : ℝ)) (lo := (1403/12500 : ℝ)) (hi := (1841/12500 : ℝ)) (c := (273677007712876703/273750000000000000 : ℝ)) (alpha := (243307292927/175200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (273677007712876703/273750000000000000 : ℝ)*(X 0 1+X 2 1)+(243307292927/175200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2167/512 : ℝ)) (lo := (1403/12500 : ℝ)) (hi := (1841/12500 : ℝ)) (c := (273677007712876703/273750000000000000 : ℝ)) (alpha := (243307292927/175200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (273677007712876703/273750000000000000 : ℝ)*(X 0 2+X 1 2)+(243307292927/175200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2167/512 : ℝ)) (lo := (1403/12500 : ℝ)) (hi := (1841/12500 : ℝ)) (c := (273677007712876703/273750000000000000 : ℝ)) (alpha := (243307292927/175200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-503950869/2500000000 : ℝ)*X 0 0+(676371283/1250000000 : ℝ)*X 0 1+(1049119873/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348395219/10000000000 : ℝ)*X 1 0+(-1050017551/5000000000 : ℝ)*X 1 1+(5245599359/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674197611/5000000000 : ℝ)*X 2 0+(5245599349/10000000000 : ℝ)*X 2 1+(-262504389/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4318065983/10000000000 : ℝ)*X 0 0+(4146001421/10000000000 : ℝ)*X 0 1+(4496688311/10000000000 : ℝ)*X 0 2+(4318065983/10000000000 : ℝ)*X 1 0+(4146001421/10000000000 : ℝ)*X 1 1+(4496688311/10000000000 : ℝ)*X 1 2+(4318065983/10000000000 : ℝ)*X 2 0+(4146001421/10000000000 : ℝ)*X 2 1+(4496688311/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-50395383/250000000 : ℝ)*X 0 0+(1311548189/2500000000 : ℝ)*X 0 1+(1082074759/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305641863/10000000000 : ℝ)*X 1 0+(-387052141/2000000000 : ℝ)*X 1 1+(1352593441/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326410457/2500000000 : ℝ)*X 2 0+(2705186901/5000000000 : ℝ)*X 2 1+(-1935260699/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((431809111/1000000000 : ℝ)*X 0 0+(112385747/250000000 : ℝ)*X 0 1+(4147266293/10000000000 : ℝ)*X 0 2+(431809111/1000000000 : ℝ)*X 1 0+(112385747/250000000 : ℝ)*X 1 1+(4147266293/10000000000 : ℝ)*X 1 2+(431809111/1000000000 : ℝ)*X 2 0+(112385747/250000000 : ℝ)*X 2 1+(4147266293/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18293337706375535280223331/2281250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (183657211/12500000000000 : ℝ)*(base19) + (135686083/10000000000000 : ℝ)*(base23) + (15482101/25000000000000 : ℝ)*(lower2) + (195964083/100000000000000 : ℝ)*(upper3) + (24896063/25000000000000 : ℝ)*(upper5) + (2224663154329159/50000000000000 : ℝ)*(major0) + (2224663154329159/50000000000000 : ℝ)*(major1) + (2224663154329159/50000000000000 : ℝ)*(major2) + (302352271936271/5000000000000 : ℝ)*(sp0) + (604707425035791/10000000000000 : ℝ)*(sp1) + (377942147672173/6250000000000 : ℝ)*(sp2) + (1425780296745517/50000000000000 : ℝ)*(sp3) + (15140445089/50000000000000 : ℝ)*(sp4) + (16036910083/100000000000000 : ℝ)*(sp7) + (712894157600279/25000000000000 : ℝ)*(f.failure) + (3023537859807799/50000000000000 : ℝ)*(f.sum) + (9099983364967/4380000000000000000000000000 : ℝ)*base66 + (232645260870406321/27375000000000000000000000000000 : ℝ)*base68 + (497065283285281321/27375000000000000000000000000000 : ℝ)*base70 + (315752750715406321/27375000000000000000000000000000 : ℝ)*base72 + (1693165059473/4380000000000000000000000000 : ℝ)*base73 + (232380128000281321/27375000000000000000000000000000 : ℝ)*base76 + (344389360604656321/27375000000000000000000000000000 : ℝ)*base78 + (290991913857406321/27375000000000000000000000000000 : ℝ)*base80 + (21435597262867/4380000000000000000000000000 : ℝ)*base82 + (1979879/625000000000000000000 : ℝ)*base90 + (1979879/625000000000000000000 : ℝ)*base92 + (1979879/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11411366709415301184863227/1140625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1708948889/100000000000000 : ℝ)*(base19) + (919914769/50000000000000 : ℝ)*(base23) + (567527811/100000000000000 : ℝ)*(lower1) + (24741797/12500000000000 : ℝ)*(upper3) + (78345191/100000000000000 : ℝ)*(lower4) + (12936849/6250000000000 : ℝ)*(upper5) + (560187339934967/12500000000000 : ℝ)*(major0) + (560187339934967/12500000000000 : ℝ)*(major1) + (560187339934967/12500000000000 : ℝ)*(major2) + (725860749/25000000000000 : ℝ)*(sp2) + (121816023048021/2000000000000 : ℝ)*(sp4) + (6090799443452161/100000000000000 : ℝ)*(sp5) + (6090796409128517/100000000000000 : ℝ)*(sp6) + (1436097976537769/50000000000000 : ℝ)*(sp7) + (1436097976537769/50000000000000 : ℝ)*(f.failure) + (121816023048021/2000000000000 : ℝ)*(f.sum) + (1158710686309/1095000000000000000000000000 : ℝ)*base65 + (89291885972474273/6843750000000000000000000000000 : ℝ)*base68 + (26176470207974273/6843750000000000000000000000000 : ℝ)*base70 + (824103637765744477/6843750000000000000000000000000 : ℝ)*base71 + (95426598737/34218750000000000000000000 : ℝ)*base73 + (307709429272463227/6843750000000000000000000000000 : ℝ)*base75 + (74748726473474273/6843750000000000000000000000000 : ℝ)*base78 + (28980158126286773/6843750000000000000000000000000 : ℝ)*base80 + (35820942001/273750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (1506631/1250000000000000000000 : ℝ)*base89 + (1506631/1250000000000000000000 : ℝ)*base91 + (1506631/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1375_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39007599/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1841/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1403/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (449/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14727/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1375_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1375_box_0 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-115694993/625000000 : ℝ)*x 0 + (1077711133/2000000000 : ℝ)*x 1 + (42098091/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (115694993/625000000 : ℝ)^4335 ≤ (2746707936301/25000000000000 : ℝ)^3311 := by
    have hnat : (115694993 : ℕ)^4335*25000000000000^3311 ≤ 2746707936301^3311*625000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      115694993 625000000 2746707936301 25000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1077711133/2000000000 : ℝ)^4335 ≤ (8901316843361/20000000000000 : ℝ)^3311 := by
    have hnat : (1077711133 : ℕ)^4335*20000000000000^3311 ≤ 8901316843361^3311*2000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077711133 2000000000 8901316843361 20000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42098091/78125000 : ℝ)^4335 ≤ (5563323004121/12500000000000 : ℝ)^3311 := by
    have hnat : (42098091 : ℕ)^4335*12500000000000^3311 ≤ 5563323004121^3311*78125000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42098091 78125000 5563323004121 12500000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-115694993/625000000 : ℝ), (1077711133/2000000000 : ℝ), (42098091/78125000 : ℝ)] ![(2746707936301/25000000000000 : ℝ), (8901316843361/20000000000000 : ℝ), (5563323004121/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-115694993/625000000 : ℝ)|^4335 ≤ (2746707936301/25000000000000 : ℝ)^3311
        have hw : |(-115694993/625000000 : ℝ)|=(115694993/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1077711133/2000000000 : ℝ)|^4335 ≤ (8901316843361/20000000000000 : ℝ)^3311
        have hw : |(1077711133/2000000000 : ℝ)|=(1077711133/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(42098091/78125000 : ℝ)|^4335 ≤ (5563323004121/12500000000000 : ℝ)^3311
        have hw : |(42098091/78125000 : ℝ)|=(42098091/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_box_1 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1321393323/2500000000 : ℝ)*x 0 + (-398473201/2000000000 : ℝ)*x 1 + (67356949/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1321393323/2500000000 : ℝ)^4335 ≤ (43396250248519/100000000000000 : ℝ)^3311 := by
    have hnat : (1321393323 : ℕ)^4335*100000000000000^3311 ≤ 43396250248519^3311*2500000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321393323 2500000000 43396250248519 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (398473201/2000000000 : ℝ)^4335 ≤ (12097162763043/100000000000000 : ℝ)^3311 := by
    have hnat : (398473201 : ℕ)^4335*100000000000000^3311 ≤ 12097162763043^3311*2000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      398473201 2000000000 12097162763043 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (67356949/125000000 : ℝ)^4335 ≤ (22253293487173/50000000000000 : ℝ)^3311 := by
    have hnat : (67356949 : ℕ)^4335*50000000000000^3311 ≤ 22253293487173^3311*125000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67356949 125000000 22253293487173 50000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1321393323/2500000000 : ℝ), (-398473201/2000000000 : ℝ), (67356949/125000000 : ℝ)] ![(43396250248519/100000000000000 : ℝ), (12097162763043/100000000000000 : ℝ), (22253293487173/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1321393323/2500000000 : ℝ)|^4335 ≤ (43396250248519/100000000000000 : ℝ)^3311
        have hw : |(1321393323/2500000000 : ℝ)|=(1321393323/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-398473201/2000000000 : ℝ)|^4335 ≤ (12097162763043/100000000000000 : ℝ)^3311
        have hw : |(-398473201/2000000000 : ℝ)|=(398473201/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(67356949/125000000 : ℝ)|^4335 ≤ (22253293487173/50000000000000 : ℝ)^3311
        have hw : |(67356949/125000000 : ℝ)|=(67356949/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_box_2 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5285573027/10000000000 : ℝ)*x 0 + (5388556139/10000000000 : ℝ)*x 1 + (-996183033/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285573027/10000000000 : ℝ)^4335 ≤ (4339624739989/10000000000000 : ℝ)^3311 := by
    have hnat : (5285573027 : ℕ)^4335*10000000000000^3311 ≤ 4339624739989^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285573027 10000000000 4339624739989 10000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5388556139/10000000000 : ℝ)^4335 ≤ (44506589342587/100000000000000 : ℝ)^3311 := by
    have hnat : (5388556139 : ℕ)^4335*100000000000000^3311 ≤ 44506589342587^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5388556139 10000000000 44506589342587 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (996183033/5000000000 : ℝ)^4335 ≤ (12097163247967/100000000000000 : ℝ)^3311 := by
    have hnat : (996183033 : ℕ)^4335*100000000000000^3311 ≤ 12097163247967^3311*5000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      996183033 5000000000 12097163247967 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285573027/10000000000 : ℝ), (5388556139/10000000000 : ℝ), (-996183033/5000000000 : ℝ)] ![(4339624739989/10000000000000 : ℝ), (44506589342587/100000000000000 : ℝ), (12097163247967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285573027/10000000000 : ℝ)|^4335 ≤ (4339624739989/10000000000000 : ℝ)^3311
        have hw : |(5285573027/10000000000 : ℝ)|=(5285573027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5388556139/10000000000 : ℝ)|^4335 ≤ (44506589342587/100000000000000 : ℝ)^3311
        have hw : |(5388556139/10000000000 : ℝ)|=(5388556139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-996183033/5000000000 : ℝ)|^4335 ≤ (12097163247967/100000000000000 : ℝ)^3311
        have hw : |(-996183033/5000000000 : ℝ)|=(996183033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_box_3 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2232752661/5000000000 : ℝ)*x 0 + (849632829/2000000000 : ℝ)*x 1 + (1062041139/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2232752661/5000000000 : ℝ)^4335 ≤ (8700122357331/25000000000000 : ℝ)^3311 := by
    have hnat : (2232752661 : ℕ)^4335*25000000000000^3311 ≤ 8700122357331^3311*5000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2232752661 5000000000 8700122357331 25000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (849632829/2000000000 : ℝ)^4335 ≤ (32599753214153/100000000000000 : ℝ)^3311 := by
    have hnat : (849632829 : ℕ)^4335*100000000000000^3311 ≤ 32599753214153^3311*2000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849632829 2000000000 32599753214153 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1062041139/2500000000 : ℝ)^4335 ≤ (8149939335883/25000000000000 : ℝ)^3311 := by
    have hnat : (1062041139 : ℕ)^4335*25000000000000^3311 ≤ 8149939335883^3311*2500000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062041139 2500000000 8149939335883 25000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2232752661/5000000000 : ℝ), (849632829/2000000000 : ℝ), (1062041139/2500000000 : ℝ)] ![(8700122357331/25000000000000 : ℝ), (32599753214153/100000000000000 : ℝ), (8149939335883/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2232752661/5000000000 : ℝ)|^4335 ≤ (8700122357331/25000000000000 : ℝ)^3311
        have hw : |(2232752661/5000000000 : ℝ)|=(2232752661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(849632829/2000000000 : ℝ)|^4335 ≤ (32599753214153/100000000000000 : ℝ)^3311
        have hw : |(849632829/2000000000 : ℝ)|=(849632829/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1062041139/2500000000 : ℝ)|^4335 ≤ (8149939335883/25000000000000 : ℝ)^3311
        have hw : |(1062041139/2500000000 : ℝ)|=(1062041139/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_box_4 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-436646473/2000000000 : ℝ)*x 0 + (1316402179/2500000000 : ℝ)*x 1 + (2632804239/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (436646473/2000000000 : ℝ)^4335 ≤ (13636471290869/100000000000000 : ℝ)^3311 := by
    have hnat : (436646473 : ℕ)^4335*100000000000000^3311 ≤ 13636471290869^3311*2000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436646473 2000000000 13636471290869 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316402179/2500000000 : ℝ)^4335 ≤ (43181765628289/100000000000000 : ℝ)^3311 := by
    have hnat : (1316402179 : ℕ)^4335*100000000000000^3311 ≤ 43181765628289^3311*2500000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316402179 2500000000 43181765628289 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632804239/5000000000 : ℝ)^4335 ≤ (4318176307289/10000000000000 : ℝ)^3311 := by
    have hnat : (2632804239 : ℕ)^4335*10000000000000^3311 ≤ 4318176307289^3311*5000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632804239 5000000000 4318176307289 10000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-436646473/2000000000 : ℝ), (1316402179/2500000000 : ℝ), (2632804239/5000000000 : ℝ)] ![(13636471290869/100000000000000 : ℝ), (43181765628289/100000000000000 : ℝ), (4318176307289/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-436646473/2000000000 : ℝ)|^4335 ≤ (13636471290869/100000000000000 : ℝ)^3311
        have hw : |(-436646473/2000000000 : ℝ)|=(436646473/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316402179/2500000000 : ℝ)|^4335 ≤ (43181765628289/100000000000000 : ℝ)^3311
        have hw : |(1316402179/2500000000 : ℝ)|=(1316402179/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632804239/5000000000 : ℝ)|^4335 ≤ (4318176307289/10000000000000 : ℝ)^3311
        have hw : |(2632804239/5000000000 : ℝ)|=(2632804239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_box_5 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1342952251/2500000000 : ℝ)*x 0 + (-1020963449/5000000000 : ℝ)*x 1 + (329100553/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1342952251/2500000000 : ℝ)^4335 ≤ (44325574817361/100000000000000 : ℝ)^3311 := by
    have hnat : (1342952251 : ℕ)^4335*100000000000000^3311 ≤ 44325574817361^3311*2500000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342952251 2500000000 44325574817361 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1020963449/5000000000 : ℝ)^4335 ≤ (6246329055451/50000000000000 : ℝ)^3311 := by
    have hnat : (1020963449 : ℕ)^4335*50000000000000^3311 ≤ 6246329055451^3311*5000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1020963449 5000000000 6246329055451 50000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (329100553/625000000 : ℝ)^4335 ≤ (43181767045569/100000000000000 : ℝ)^3311 := by
    have hnat : (329100553 : ℕ)^4335*100000000000000^3311 ≤ 43181767045569^3311*625000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329100553 625000000 43181767045569 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1342952251/2500000000 : ℝ), (-1020963449/5000000000 : ℝ), (329100553/625000000 : ℝ)] ![(44325574817361/100000000000000 : ℝ), (6246329055451/50000000000000 : ℝ), (43181767045569/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1342952251/2500000000 : ℝ)|^4335 ≤ (44325574817361/100000000000000 : ℝ)^3311
        have hw : |(1342952251/2500000000 : ℝ)|=(1342952251/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1020963449/5000000000 : ℝ)|^4335 ≤ (6246329055451/50000000000000 : ℝ)^3311
        have hw : |(-1020963449/5000000000 : ℝ)|=(1020963449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(329100553/625000000 : ℝ)|^4335 ≤ (43181767045569/100000000000000 : ℝ)^3311
        have hw : |(329100553/625000000 : ℝ)|=(329100553/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_box_6 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2685904783/5000000000 : ℝ)*x 0 + (2632804223/5000000000 : ℝ)*x 1 + (-2041926679/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2685904783/5000000000 : ℝ)^4335 ≤ (22162790444459/50000000000000 : ℝ)^3311 := by
    have hnat : (2685904783 : ℕ)^4335*50000000000000^3311 ≤ 22162790444459^3311*5000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2685904783 5000000000 22162790444459 50000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632804223/5000000000 : ℝ)^4335 ≤ (43181762729307/100000000000000 : ℝ)^3311 := by
    have hnat : (2632804223 : ℕ)^4335*100000000000000^3311 ≤ 43181762729307^3311*5000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632804223 5000000000 43181762729307 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2041926679/10000000000 : ℝ)^4335 ≤ (12492656356663/100000000000000 : ℝ)^3311 := by
    have hnat : (2041926679 : ℕ)^4335*100000000000000^3311 ≤ 12492656356663^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2041926679 10000000000 12492656356663 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2685904783/5000000000 : ℝ), (2632804223/5000000000 : ℝ), (-2041926679/10000000000 : ℝ)] ![(22162790444459/50000000000000 : ℝ), (43181762729307/100000000000000 : ℝ), (12492656356663/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2685904783/5000000000 : ℝ)|^4335 ≤ (22162790444459/50000000000000 : ℝ)^3311
        have hw : |(2685904783/5000000000 : ℝ)|=(2685904783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632804223/5000000000 : ℝ)|^4335 ≤ (43181762729307/100000000000000 : ℝ)^3311
        have hw : |(2632804223/5000000000 : ℝ)|=(2632804223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2041926679/10000000000 : ℝ)|^4335 ≤ (12492656356663/100000000000000 : ℝ)^3311
        have hw : |(-2041926679/10000000000 : ℝ)|=(2041926679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_box_7 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4169652623/10000000000 : ℝ)*x 0 + (1099009527/2500000000 : ℝ)*x 1 + (2198019119/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4169652623/10000000000 : ℝ)^4335 ≤ (31813200077543/100000000000000 : ℝ)^3311 := by
    have hnat : (4169652623 : ℕ)^4335*100000000000000^3311 ≤ 31813200077543^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4169652623 10000000000 31813200077543 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1099009527/2500000000 : ℝ)^4335 ≤ (34093399294419/100000000000000 : ℝ)^3311 := by
    have hnat : (1099009527 : ℕ)^4335*100000000000000^3311 ≤ 34093399294419^3311*2500000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099009527 2500000000 34093399294419 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2198019119/5000000000 : ℝ)^4335 ≤ (8523350153611/25000000000000 : ℝ)^3311 := by
    have hnat : (2198019119 : ℕ)^4335*25000000000000^3311 ≤ 8523350153611^3311*5000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2198019119 5000000000 8523350153611 25000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4169652623/10000000000 : ℝ), (1099009527/2500000000 : ℝ), (2198019119/5000000000 : ℝ)] ![(31813200077543/100000000000000 : ℝ), (34093399294419/100000000000000 : ℝ), (8523350153611/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4169652623/10000000000 : ℝ)|^4335 ≤ (31813200077543/100000000000000 : ℝ)^3311
        have hw : |(4169652623/10000000000 : ℝ)|=(4169652623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1099009527/2500000000 : ℝ)|^4335 ≤ (34093399294419/100000000000000 : ℝ)^3311
        have hw : |(1099009527/2500000000 : ℝ)|=(1099009527/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2198019119/5000000000 : ℝ)|^4335 ≤ (8523350153611/25000000000000 : ℝ)^3311
        have hw : |(2198019119/5000000000 : ℝ)|=(2198019119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_box_8 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1056703053/5000000000 : ℝ)*x 0 + (2590407413/5000000000 : ℝ)*x 1 + (5402560429/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1056703053/5000000000 : ℝ)^4335 ≤ (13068297240121/100000000000000 : ℝ)^3311 := by
    have hnat : (1056703053 : ℕ)^4335*100000000000000^3311 ≤ 13068297240121^3311*5000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056703053 5000000000 13068297240121 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2590407413/5000000000 : ℝ)^4335 ≤ (2113680588231/5000000000000 : ℝ)^3311 := by
    have hnat : (2590407413 : ℕ)^4335*5000000000000^3311 ≤ 2113680588231^3311*5000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590407413 5000000000 2113680588231 5000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5402560429/10000000000 : ℝ)^4335 ≤ (22329045488033/50000000000000 : ℝ)^3311 := by
    have hnat : (5402560429 : ℕ)^4335*50000000000000^3311 ≤ 22329045488033^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402560429 10000000000 22329045488033 50000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1056703053/5000000000 : ℝ), (2590407413/5000000000 : ℝ), (5402560429/10000000000 : ℝ)] ![(13068297240121/100000000000000 : ℝ), (2113680588231/5000000000000 : ℝ), (22329045488033/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1056703053/5000000000 : ℝ)|^4335 ≤ (13068297240121/100000000000000 : ℝ)^3311
        have hw : |(-1056703053/5000000000 : ℝ)|=(1056703053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2590407413/5000000000 : ℝ)|^4335 ≤ (2113680588231/5000000000000 : ℝ)^3311
        have hw : |(2590407413/5000000000 : ℝ)|=(2590407413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5402560429/10000000000 : ℝ)|^4335 ≤ (22329045488033/50000000000000 : ℝ)^3311
        have hw : |(5402560429/10000000000 : ℝ)|=(5402560429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_box_9 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (131893643/250000000 : ℝ)*x 0 + (-1986590383/10000000000 : ℝ)*x 1 + (1080512099/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (131893643/250000000 : ℝ)^4335 ≤ (43290638721501/100000000000000 : ℝ)^3311 := by
    have hnat : (131893643 : ℕ)^4335*100000000000000^3311 ≤ 43290638721501^3311*250000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131893643 250000000 43290638721501 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1986590383/10000000000 : ℝ)^4335 ≤ (3012817393721/25000000000000 : ℝ)^3311 := by
    have hnat : (1986590383 : ℕ)^4335*25000000000000^3311 ≤ 3012817393721^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1986590383 10000000000 3012817393721 25000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1080512099/2000000000 : ℝ)^4335 ≤ (11164522922589/25000000000000 : ℝ)^3311 := by
    have hnat : (1080512099 : ℕ)^4335*25000000000000^3311 ≤ 11164522922589^3311*2000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080512099 2000000000 11164522922589 25000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(131893643/250000000 : ℝ), (-1986590383/10000000000 : ℝ), (1080512099/2000000000 : ℝ)] ![(43290638721501/100000000000000 : ℝ), (3012817393721/25000000000000 : ℝ), (11164522922589/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(131893643/250000000 : ℝ)|^4335 ≤ (43290638721501/100000000000000 : ℝ)^3311
        have hw : |(131893643/250000000 : ℝ)|=(131893643/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1986590383/10000000000 : ℝ)|^4335 ≤ (3012817393721/25000000000000 : ℝ)^3311
        have hw : |(-1986590383/10000000000 : ℝ)|=(1986590383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1080512099/2000000000 : ℝ)|^4335 ≤ (11164522922589/25000000000000 : ℝ)^3311
        have hw : |(1080512099/2000000000 : ℝ)|=(1080512099/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_box_10 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (329734103/625000000 : ℝ)*x 0 + (337660001/625000000 : ℝ)*x 1 + (-1986591133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (329734103/625000000 : ℝ)^4335 ≤ (43290637947979/100000000000000 : ℝ)^3311 := by
    have hnat : (329734103 : ℕ)^4335*100000000000000^3311 ≤ 43290637947979^3311*625000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329734103 625000000 43290637947979 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337660001/625000000 : ℝ)^4335 ≤ (5582260813293/12500000000000 : ℝ)^3311 := by
    have hnat : (337660001 : ℕ)^4335*12500000000000^3311 ≤ 5582260813293^3311*625000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337660001 625000000 5582260813293 12500000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1986591133/10000000000 : ℝ)^4335 ≤ (12051275531721/100000000000000 : ℝ)^3311 := by
    have hnat : (1986591133 : ℕ)^4335*100000000000000^3311 ≤ 12051275531721^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1986591133 10000000000 12051275531721 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(329734103/625000000 : ℝ), (337660001/625000000 : ℝ), (-1986591133/10000000000 : ℝ)] ![(43290637947979/100000000000000 : ℝ), (5582260813293/12500000000000 : ℝ), (12051275531721/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(329734103/625000000 : ℝ)|^4335 ≤ (43290637947979/100000000000000 : ℝ)^3311
        have hw : |(329734103/625000000 : ℝ)|=(329734103/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337660001/625000000 : ℝ)|^4335 ≤ (5582260813293/12500000000000 : ℝ)^3311
        have hw : |(337660001/625000000 : ℝ)|=(337660001/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1986591133/10000000000 : ℝ)|^4335 ≤ (12051275531721/100000000000000 : ℝ)^3311
        have hw : |(-1986591133/10000000000 : ℝ)|=(1986591133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_box_11 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (281165471/625000000 : ℝ)*x 0 + (846261061/2000000000 : ℝ)*x 1 + (4231306517/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (281165471/625000000 : ℝ)^4335 ≤ (35139039942969/100000000000000 : ℝ)^3311 := by
    have hnat : (281165471 : ℕ)^4335*100000000000000^3311 ≤ 35139039942969^3311*625000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281165471 625000000 35139039942969 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (846261061/2000000000 : ℝ)^4335 ≤ (324304739383/1000000000000 : ℝ)^3311 := by
    have hnat : (846261061 : ℕ)^4335*1000000000000^3311 ≤ 324304739383^3311*2000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      846261061 2000000000 324304739383 1000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4231306517/10000000000 : ℝ)^4335 ≤ (16215243050241/50000000000000 : ℝ)^3311 := by
    have hnat : (4231306517 : ℕ)^4335*50000000000000^3311 ≤ 16215243050241^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4231306517 10000000000 16215243050241 50000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(281165471/625000000 : ℝ), (846261061/2000000000 : ℝ), (4231306517/10000000000 : ℝ)] ![(35139039942969/100000000000000 : ℝ), (324304739383/1000000000000 : ℝ), (16215243050241/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(281165471/625000000 : ℝ)|^4335 ≤ (35139039942969/100000000000000 : ℝ)^3311
        have hw : |(281165471/625000000 : ℝ)|=(281165471/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(846261061/2000000000 : ℝ)|^4335 ≤ (324304739383/1000000000000 : ℝ)^3311
        have hw : |(846261061/2000000000 : ℝ)|=(846261061/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4231306517/10000000000 : ℝ)|^4335 ≤ (16215243050241/50000000000000 : ℝ)^3311
        have hw : |(4231306517/10000000000 : ℝ)|=(4231306517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_box_12 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-960610379/5000000000 : ℝ)*x 0 + (5471215997/10000000000 : ℝ)*x 1 + (5254514529/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (960610379/5000000000 : ℝ)^4335 ≤ (1153473686427/10000000000000 : ℝ)^3311 := by
    have hnat : (960610379 : ℕ)^4335*10000000000000^3311 ≤ 1153473686427^3311*5000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      960610379 5000000000 1153473686427 10000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5471215997/10000000000 : ℝ)^4335 ≤ (9080515323649/20000000000000 : ℝ)^3311 := by
    have hnat : (5471215997 : ℕ)^4335*20000000000000^3311 ≤ 9080515323649^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5471215997 10000000000 9080515323649 20000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5254514529/10000000000 : ℝ)^4335 ≤ (2153134325257/5000000000000 : ℝ)^3311 := by
    have hnat : (5254514529 : ℕ)^4335*5000000000000^3311 ≤ 2153134325257^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254514529 10000000000 2153134325257 5000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-960610379/5000000000 : ℝ), (5471215997/10000000000 : ℝ), (5254514529/10000000000 : ℝ)] ![(1153473686427/10000000000000 : ℝ), (9080515323649/20000000000000 : ℝ), (2153134325257/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-960610379/5000000000 : ℝ)|^4335 ≤ (1153473686427/10000000000000 : ℝ)^3311
        have hw : |(-960610379/5000000000 : ℝ)|=(960610379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5471215997/10000000000 : ℝ)|^4335 ≤ (9080515323649/20000000000000 : ℝ)^3311
        have hw : |(5471215997/10000000000 : ℝ)|=(5471215997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5254514529/10000000000 : ℝ)|^4335 ≤ (2153134325257/5000000000000 : ℝ)^3311
        have hw : |(5254514529/10000000000 : ℝ)|=(5254514529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_box_13 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (672448603/1250000000 : ℝ)*x 0 + (-2046296901/10000000000 : ℝ)*x 1 + (2627257093/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (672448603/1250000000 : ℝ)^4335 ≤ (44409642776087/100000000000000 : ℝ)^3311 := by
    have hnat : (672448603 : ℕ)^4335*100000000000000^3311 ≤ 44409642776087^3311*1250000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672448603 1250000000 44409642776087 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2046296901/10000000000 : ℝ)^4335 ≤ (6263837193289/50000000000000 : ℝ)^3311 := by
    have hnat : (2046296901 : ℕ)^4335*50000000000000^3311 ≤ 6263837193289^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2046296901 10000000000 6263837193289 50000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627257093/5000000000 : ℝ)^4335 ≤ (43062682824761/100000000000000 : ℝ)^3311 := by
    have hnat : (2627257093 : ℕ)^4335*100000000000000^3311 ≤ 43062682824761^3311*5000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627257093 5000000000 43062682824761 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(672448603/1250000000 : ℝ), (-2046296901/10000000000 : ℝ), (2627257093/5000000000 : ℝ)] ![(44409642776087/100000000000000 : ℝ), (6263837193289/50000000000000 : ℝ), (43062682824761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(672448603/1250000000 : ℝ)|^4335 ≤ (44409642776087/100000000000000 : ℝ)^3311
        have hw : |(672448603/1250000000 : ℝ)|=(672448603/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2046296901/10000000000 : ℝ)|^4335 ≤ (6263837193289/50000000000000 : ℝ)^3311
        have hw : |(-2046296901/10000000000 : ℝ)|=(2046296901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2627257093/5000000000 : ℝ)|^4335 ≤ (43062682824761/100000000000000 : ℝ)^3311
        have hw : |(2627257093/5000000000 : ℝ)|=(2627257093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_box_14 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1344897533/2500000000 : ℝ)*x 0 + (2627256581/5000000000 : ℝ)*x 1 + (-511574127/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1344897533/2500000000 : ℝ)^4335 ≤ (5551207114171/12500000000000 : ℝ)^3311 := by
    have hnat : (1344897533 : ℕ)^4335*12500000000000^3311 ≤ 5551207114171^3311*2500000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344897533 2500000000 5551207114171 12500000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2627256581/5000000000 : ℝ)^4335 ≤ (21531335918637/50000000000000 : ℝ)^3311 := by
    have hnat : (2627256581 : ℕ)^4335*50000000000000^3311 ≤ 21531335918637^3311*5000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627256581 5000000000 21531335918637 50000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (511574127/2500000000 : ℝ)^4335 ≤ (6263835618239/50000000000000 : ℝ)^3311 := by
    have hnat : (511574127 : ℕ)^4335*50000000000000^3311 ≤ 6263835618239^3311*2500000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      511574127 2500000000 6263835618239 50000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1344897533/2500000000 : ℝ), (2627256581/5000000000 : ℝ), (-511574127/2500000000 : ℝ)] ![(5551207114171/12500000000000 : ℝ), (21531335918637/50000000000000 : ℝ), (6263835618239/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1344897533/2500000000 : ℝ)|^4335 ≤ (5551207114171/12500000000000 : ℝ)^3311
        have hw : |(1344897533/2500000000 : ℝ)|=(1344897533/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2627256581/5000000000 : ℝ)|^4335 ≤ (21531335918637/50000000000000 : ℝ)^3311
        have hw : |(2627256581/5000000000 : ℝ)|=(2627256581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-511574127/2500000000 : ℝ)|^4335 ≤ (6263835618239/50000000000000 : ℝ)^3311
        have hw : |(-511574127/2500000000 : ℝ)|=(511574127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_box_15 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1035627001/2500000000 : ℝ)*x 0 + (4409370343/10000000000 : ℝ)*x 1 + (881874191/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1035627001/2500000000 : ℝ)^4335 ≤ (31542316250623/100000000000000 : ℝ)^3311 := by
    have hnat : (1035627001 : ℕ)^4335*100000000000000^3311 ≤ 31542316250623^3311*2500000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035627001 2500000000 31542316250623 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4409370343/10000000000 : ℝ)^4335 ≤ (2139302422321/6250000000000 : ℝ)^3311 := by
    have hnat : (4409370343 : ℕ)^4335*6250000000000^3311 ≤ 2139302422321^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4409370343 10000000000 2139302422321 6250000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (881874191/2000000000 : ℝ)^4335 ≤ (3422884497723/10000000000000 : ℝ)^3311 := by
    have hnat : (881874191 : ℕ)^4335*10000000000000^3311 ≤ 3422884497723^3311*2000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      881874191 2000000000 3422884497723 10000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1035627001/2500000000 : ℝ), (4409370343/10000000000 : ℝ), (881874191/2000000000 : ℝ)] ![(31542316250623/100000000000000 : ℝ), (2139302422321/6250000000000 : ℝ), (3422884497723/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1035627001/2500000000 : ℝ)|^4335 ≤ (31542316250623/100000000000000 : ℝ)^3311
        have hw : |(1035627001/2500000000 : ℝ)|=(1035627001/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4409370343/10000000000 : ℝ)|^4335 ≤ (2139302422321/6250000000000 : ℝ)^3311
        have hw : |(4409370343/10000000000 : ℝ)|=(4409370343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(881874191/2000000000 : ℝ)|^4335 ≤ (3422884497723/10000000000000 : ℝ)^3311
        have hw : |(881874191/2000000000 : ℝ)|=(881874191/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1375_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39007599/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14727/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (449/4000 : ℝ)*pair X i i ≤ pair X i h) :
    -(6287/10000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29503/50000 : ℝ) ∧ (16029/20000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (528/625 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14727/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (449/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14727/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (449/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14727/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (449/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14727/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (449/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14727/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (449/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14727/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (449/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (449/4000 : ℝ) ^ (2167/512 : ℝ) ≤ (9549660432674929/100000000000000000000 : ℝ) := by
    have hpowers : (449/4000 : ℝ)^2167 ≤ (9549660432674929/100000000000000000000 : ℝ)^512 := by
      have hnat : (449 : ℕ)^2167*100000000000000000000^512 ≤ 9549660432674929^512*4000^2167 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        449 4000 9549660432674929 100000000000000000000 2167 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (449/4000 : ℝ)) (X := (9549660432674929/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2167 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14727/100000 : ℝ) ^ (2167/512 : ℝ) ≤ (15068801582483639/50000000000000000000 : ℝ) := by
    have hpowers : (14727/100000 : ℝ)^2167 ≤ (15068801582483639/50000000000000000000 : ℝ)^512 := by
      have hnat : (14727 : ℕ)^2167*50000000000000000000^512 ≤ 15068801582483639^512*100000^2167 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14727 100000 15068801582483639 50000000000000000000 2167 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14727/100000 : ℝ)) (X := (15068801582483639/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2167 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009549660432674929/50000000000000000000 : ℝ) ≤ (5000225614655221/5000000000000000 : ℝ) ^ (2167/512 : ℝ) := by
    have hpowers : (50009549660432674929/50000000000000000000 : ℝ)^512 ≤ (5000225614655221/5000000000000000 : ℝ)^2167 := by
      have hnat : (50009549660432674929 : ℕ)^512*5000000000000000^2167 ≤ 5000225614655221^2167*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009549660432674929 50000000000000000000 5000225614655221 5000000000000000 512 2167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000225614655221/5000000000000000 : ℝ)) (X := (50009549660432674929/50000000000000000000 : ℝ)) (by norm_num) 2167 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100039687263597642207/100000000000000000000 : ℝ) ≤ (10000937554230371/10000000000000000 : ℝ) ^ (2167/512 : ℝ) := by
    have hpowers : (100039687263597642207/100000000000000000000 : ℝ)^512 ≤ (10000937554230371/10000000000000000 : ℝ)^2167 := by
      have hnat : (100039687263597642207 : ℕ)^512*10000000000000000^2167 ≤ 10000937554230371^2167*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100039687263597642207 100000000000000000000 10000937554230371 10000000000000000 512 2167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000937554230371/10000000000000000 : ℝ)) (X := (100039687263597642207/100000000000000000000 : ℝ)) (by norm_num) 2167 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015068801582483639/25000000000000000000 : ℝ) ≤ (100014238791503/100000000000000 : ℝ) ^ (2167/512 : ℝ) := by
    have hpowers : (25015068801582483639/25000000000000000000 : ℝ)^512 ≤ (100014238791503/100000000000000 : ℝ)^2167 := by
      have hnat : (25015068801582483639 : ℕ)^512*100000000000000^2167 ≤ 100014238791503^2167*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015068801582483639 25000000000000000000 100014238791503 100000000000000 512 2167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (100014238791503/100000000000000 : ℝ)) (X := (25015068801582483639/25000000000000000000 : ℝ)) (by norm_num) 2167 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9549660432674929/100000000000000000000 : ℝ) ≤ ((17505331105296380917/17510000000000000000 : ℝ)+2*(486324919929/350200000000000 : ℝ)*(449/4000 : ℝ))^(2167/512 : ℝ) := by
    rw [show (17505331105296380917/17510000000000000000 : ℝ)+2*(486324919929/350200000000000 : ℝ)*(449/4000 : ℝ)=(5000225614655221/5000000000000000 : ℝ) by norm_num, show 1+2*(9549660432674929/100000000000000000000 : ℝ)=(50009549660432674929/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15068801582483639/50000000000000000000 : ℝ)+(9549660432674929/100000000000000000000 : ℝ) ≤ ((17505331105296380917/17510000000000000000 : ℝ)+(486324919929/350200000000000 : ℝ)*((14727/100000 : ℝ)+(449/4000 : ℝ)))^(2167/512 : ℝ) := by
    rw [show (17505331105296380917/17510000000000000000 : ℝ)+(486324919929/350200000000000 : ℝ)*((14727/100000 : ℝ)+(449/4000 : ℝ))=(10000937554230371/10000000000000000 : ℝ) by norm_num, show 1+(15068801582483639/50000000000000000000 : ℝ)+(9549660432674929/100000000000000000000 : ℝ)=(100039687263597642207/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15068801582483639/50000000000000000000 : ℝ) ≤ ((17505331105296380917/17510000000000000000 : ℝ)+2*(486324919929/350200000000000 : ℝ)*(14727/100000 : ℝ))^(2167/512 : ℝ) := by
    rw [show (17505331105296380917/17510000000000000000 : ℝ)+2*(486324919929/350200000000000 : ℝ)*(14727/100000 : ℝ)=(100014238791503/100000000000000 : ℝ) by norm_num, show 1+2*(15068801582483639/50000000000000000000 : ℝ)=(25015068801582483639/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17505331105296380917/17510000000000000000 : ℝ)*(X 1 0+X 2 0)+(486324919929/350200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2167/512 : ℝ)) (lo := (449/4000 : ℝ)) (hi := (14727/100000 : ℝ)) (c := (17505331105296380917/17510000000000000000 : ℝ)) (alpha := (486324919929/350200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17505331105296380917/17510000000000000000 : ℝ)*(X 0 1+X 2 1)+(486324919929/350200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2167/512 : ℝ)) (lo := (449/4000 : ℝ)) (hi := (14727/100000 : ℝ)) (c := (17505331105296380917/17510000000000000000 : ℝ)) (alpha := (486324919929/350200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17505331105296380917/17510000000000000000 : ℝ)*(X 0 2+X 1 2)+(486324919929/350200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2167/512 : ℝ)) (lo := (449/4000 : ℝ)) (hi := (14727/100000 : ℝ)) (c := (17505331105296380917/17510000000000000000 : ℝ)) (alpha := (486324919929/350200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-115694993/625000000 : ℝ)*X 0 0+(1077711133/2000000000 : ℝ)*X 0 1+(42098091/78125000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1321393323/2500000000 : ℝ)*X 1 0+(-398473201/2000000000 : ℝ)*X 1 1+(67356949/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5285573027/10000000000 : ℝ)*X 2 0+(5388556139/10000000000 : ℝ)*X 2 1+(-996183033/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2232752661/5000000000 : ℝ)*X 0 0+(849632829/2000000000 : ℝ)*X 0 1+(1062041139/2500000000 : ℝ)*X 0 2+(2232752661/5000000000 : ℝ)*X 1 0+(849632829/2000000000 : ℝ)*X 1 1+(1062041139/2500000000 : ℝ)*X 1 2+(2232752661/5000000000 : ℝ)*X 2 0+(849632829/2000000000 : ℝ)*X 2 1+(1062041139/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-436646473/2000000000 : ℝ)*X 0 0+(1316402179/2500000000 : ℝ)*X 0 1+(2632804239/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1342952251/2500000000 : ℝ)*X 1 0+(-1020963449/5000000000 : ℝ)*X 1 1+(329100553/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2685904783/5000000000 : ℝ)*X 2 0+(2632804223/5000000000 : ℝ)*X 2 1+(-2041926679/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4169652623/10000000000 : ℝ)*X 0 0+(1099009527/2500000000 : ℝ)*X 0 1+(2198019119/5000000000 : ℝ)*X 0 2+(4169652623/10000000000 : ℝ)*X 1 0+(1099009527/2500000000 : ℝ)*X 1 1+(2198019119/5000000000 : ℝ)*X 1 2+(4169652623/10000000000 : ℝ)*X 2 0+(1099009527/2500000000 : ℝ)*X 2 1+(2198019119/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1056703053/5000000000 : ℝ)*X 0 0+(2590407413/5000000000 : ℝ)*X 0 1+(5402560429/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((131893643/250000000 : ℝ)*X 1 0+(-1986590383/10000000000 : ℝ)*X 1 1+(1080512099/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((329734103/625000000 : ℝ)*X 2 0+(337660001/625000000 : ℝ)*X 2 1+(-1986591133/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((281165471/625000000 : ℝ)*X 0 0+(846261061/2000000000 : ℝ)*X 0 1+(4231306517/10000000000 : ℝ)*X 0 2+(281165471/625000000 : ℝ)*X 1 0+(846261061/2000000000 : ℝ)*X 1 1+(4231306517/10000000000 : ℝ)*X 1 2+(281165471/625000000 : ℝ)*X 2 0+(846261061/2000000000 : ℝ)*X 2 1+(4231306517/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-960610379/5000000000 : ℝ)*X 0 0+(5471215997/10000000000 : ℝ)*X 0 1+(5254514529/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((672448603/1250000000 : ℝ)*X 1 0+(-2046296901/10000000000 : ℝ)*X 1 1+(2627257093/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1344897533/2500000000 : ℝ)*X 2 0+(2627256581/5000000000 : ℝ)*X 2 1+(-511574127/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1035627001/2500000000 : ℝ)*X 0 0+(4409370343/10000000000 : ℝ)*X 0 1+(881874191/2000000000 : ℝ)*X 0 2+(1035627001/2500000000 : ℝ)*X 1 0+(4409370343/10000000000 : ℝ)*X 1 1+(881874191/2000000000 : ℝ)*X 1 2+(1035627001/2500000000 : ℝ)*X 2 0+(4409370343/10000000000 : ℝ)*X 2 1+(881874191/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-6287/10000 : ℝ) ≤ (-550403148922850655489122919471453/875500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5752613/20000000000000 : ℝ)*(upper0) + (12751093/100000000000000 : ℝ)*(upper1) + (136602541/100000000000000 : ℝ)*(upper4) + (74550181/50000000000000 : ℝ)*(upper5) + (2957365136156797/100000000000000 : ℝ)*(major0) + (2957365136156797/100000000000000 : ℝ)*(major1) + (2957365136156797/100000000000000 : ℝ)*(major2) + (10490077157/100000000000000 : ℝ)*(sp2) + (3640726563/50000000000000 : ℝ)*(sp3) + (7891204325787/195312500000 : ℝ)*(sp4) + (161612338459061/4000000000000 : ℝ)*(sp5) + (505037246424921/12500000000000 : ℝ)*(sp6) + (473842573417017/25000000000000 : ℝ)*(sp7) + (11846673581/100000000000000 : ℝ)*(sp8) + (947688787560597/50000000000000 : ℝ)*(f.failure) + (161612338459061/4000000000000 : ℝ)*(f.sum) + (42866258174513/17510000000000000000000000000 : ℝ)*base65 + (40739260855297292849/1751000000000000000000000000000000 : ℝ)*base67 + (8369105311749707151/1751000000000000000000000000000000 : ℝ)*base70 + (2228240301314707151/1751000000000000000000000000000000 : ℝ)*base72 + (52543643405773/17510000000000000000000000000 : ℝ)*base73 + (10064437027718707151/1751000000000000000000000000000000 : ℝ)*base76 + (2171729534008292849/1751000000000000000000000000000000 : ℝ)*base77 + (77872966348593707151/1751000000000000000000000000000000 : ℝ)*base80 + (83437239572353/17510000000000000000000000000 : ℝ)*base81 + (6523397/1250000000000000000000 : ℝ)*base90 + (6523397/1250000000000000000000 : ℝ)*base92 + (6523397/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (29503/50000 : ℝ) ≤ (129154111120887183546166364026683/218875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9825003/25000000000000 : ℝ)*(lower1) + (48964221/100000000000000 : ℝ)*(upper2) + (1305439/4000000000000 : ℝ)*(lower4) + (756787190880311/25000000000000 : ℝ)*(major0) + (756787190880311/25000000000000 : ℝ)*(major1) + (756787190880311/25000000000000 : ℝ)*(major2) + (1023630581197463/25000000000000 : ℝ)*(sp0) + (2047258057251357/50000000000000 : ℝ)*(sp1) + (2047256497360621/50000000000000 : ℝ)*(sp2) + (485025286642591/25000000000000 : ℝ)*(sp3) + (10070520717/100000000000000 : ℝ)*(sp5) + (3297575547/25000000000000 : ℝ)*(sp6) + (50540111/6250000000000 : ℝ)*(sp7) + (1930116789/50000000000000 : ℝ)*(sp12) + (97005097760607/5000000000000 : ℝ)*(f.failure) + (409452618502343/10000000000000 : ℝ)*(f.sum) + (16114733481971/4377500000000000000000000000 : ℝ)*base66 + (1443696820226124813/437750000000000000000000000000000 : ℝ)*base68 + (3138284194850124813/437750000000000000000000000000000 : ℝ)*base70 + (3194936960245624813/437750000000000000000000000000000 : ℝ)*base72 + (2692984290039/4377500000000000000000000000 : ℝ)*base73 + (3331302194484624813/437750000000000000000000000000000 : ℝ)*base76 + (3413470334017124813/437750000000000000000000000000000 : ℝ)*base78 + (812735194136124813/437750000000000000000000000000000 : ℝ)*base80 + (8441577279299/4377500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (852593/125000000000000000000 : ℝ)*base89 + (852593/125000000000000000000 : ℝ)*base91 + (852593/125000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (16029/20000 : ℝ) ≤ (41276089949485720549318125664839/51500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (229267169/50000000000000 : ℝ)*(upper0) + (93388879/100000000000000 : ℝ)*(upper2) + (501688649/100000000000000 : ℝ)*(lower5) + (3337766960321513/100000000000000 : ℝ)*(major0) + (3337766960321513/100000000000000 : ℝ)*(major1) + (3337766960321513/100000000000000 : ℝ)*(major2) + (7748539829/12500000000000 : ℝ)*(sp1) + (20883120889/100000000000000 : ℝ)*(sp3) + (68487997/3125000000000 : ℝ)*(sp4) + (563704574039487/12500000000000 : ℝ)*(sp8) + (901915724330591/20000000000000 : ℝ)*(sp9) + (4509640609971587/100000000000000 : ℝ)*(sp10) + (1069578255862817/50000000000000 : ℝ)*(sp11) + (913019893/50000000000000 : ℝ)*(sp12) + (2139177394846523/100000000000000 : ℝ)*(f.failure) + (4509640609971587/100000000000000 : ℝ)*(f.sum) + (673213765059/1030000000000000000000000000 : ℝ)*base66 + (352629900955271613/103000000000000000000000000000000 : ℝ)*base67 + (208490210769728387/103000000000000000000000000000000 : ℝ)*base70 + (109145631208271613/103000000000000000000000000000000 : ℝ)*base71 + (25311174073181/1030000000000000000000000000 : ℝ)*base73 + (796058847894728387/103000000000000000000000000000000 : ℝ)*base76 + (52268164687728387/103000000000000000000000000000000 : ℝ)*base78 + (739346784214728387/103000000000000000000000000000000 : ℝ)*base80 + (45837852951/1030000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (10728277/2500000000000000000000 : ℝ)*base89 + (10728277/2500000000000000000000 : ℝ)*base91 + (10728277/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-528/625 : ℝ) ≤ (-369799700246131521434656246145757/437750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (37492239/100000000000000 : ℝ)*(lower1) + (135099069/50000000000000 : ℝ)*(lower2) + (37723193/20000000000000 : ℝ)*(lower3) + (274856309/100000000000000 : ℝ)*(upper5) + (1687320939542831/50000000000000 : ℝ)*(major0) + (1687320939542831/50000000000000 : ℝ)*(major1) + (1687320939542831/50000000000000 : ℝ)*(major2) + (211095179/2500000000000 : ℝ)*(sp4) + (7447580609/50000000000000 : ℝ)*(sp5) + (443391826423/100000000000000 : ℝ)*(sp6) + (4614623880238769/100000000000000 : ℝ)*(sp12) + (576827178610589/12500000000000 : ℝ)*(sp13) + (4614188932219507/100000000000000 : ℝ)*(sp14) + (67587829951689/3125000000000 : ℝ)*(sp15) + (67587829951689/3125000000000 : ℝ)*(f.failure) + (461463232404593/10000000000000 : ℝ)*(f.sum) + (52564557951/8755000000000000000000000000 : ℝ)*base66 + (11969752613970993973/875500000000000000000000000000000 : ℝ)*base68 + (10072684547672993973/875500000000000000000000000000000 : ℝ)*base70 + (2758418406113493973/875500000000000000000000000000000 : ℝ)*base72 + (25185361811941/8755000000000000000000000000 : ℝ)*base74 + (2418279112805493973/875500000000000000000000000000000 : ℝ)*base76 + (5957847166254493973/875500000000000000000000000000000 : ℝ)*base78 + (5550433873365493973/875500000000000000000000000000000 : ℝ)*base80 + (1132280316293/4377500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (447211/78125000000000000000 : ℝ)*base89 + (447211/78125000000000000000 : ℝ)*base91 + (447211/78125000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1375_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39007599/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14727/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (449/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6287/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(29503/50000 : ℝ) else (16029/20000 : ℝ) ≤ X j i ∧ X j i ≤ (528/625 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1375_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1375_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39007599/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14733/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11219/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6287/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(29503/50000 : ℝ) else (16029/20000 : ℝ) ≤ X j i ∧ X j i ≤ (528/625 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1375_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1375_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1375_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39007599/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14733/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11219/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6287/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(29503/50000 : ℝ) else (16029/20000 : ℝ) ≤ X j i ∧ X j i ≤ (528/625 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1375_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
