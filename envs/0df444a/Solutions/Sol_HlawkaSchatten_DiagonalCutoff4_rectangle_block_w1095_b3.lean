-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1095_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:58:46.534197+00:00
-- url     : https://prove2.me/submissions/fe46d541-71ad-4ec7-bd70-97113ef45e2c

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
theorem support_rectangle_w1095_s9_0 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-1094785057/5000000000 : ℝ)*x 0 + (5393822571/10000000000 : ℝ)*x 1 + (2632498509/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1094785057/5000000000 : ℝ)^259 ≤ (13300294293023/100000000000000 : ℝ)^195 := by
    have hnat : (1094785057 : ℕ)^259*100000000000000^195 ≤ 13300294293023^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094785057 5000000000 13300294293023 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393822571/10000000000 : ℝ)^259 ≤ (44045725108131/100000000000000 : ℝ)^195 := by
    have hnat : (5393822571 : ℕ)^259*100000000000000^195 ≤ 44045725108131^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393822571 10000000000 44045725108131 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632498509/5000000000 : ℝ)^259 ≤ (8530796117037/20000000000000 : ℝ)^195 := by
    have hnat : (2632498509 : ℕ)^259*20000000000000^195 ≤ 8530796117037^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632498509 5000000000 8530796117037 20000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1094785057/5000000000 : ℝ), (5393822571/10000000000 : ℝ), (2632498509/5000000000 : ℝ)] ![(13300294293023/100000000000000 : ℝ), (44045725108131/100000000000000 : ℝ), (8530796117037/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1094785057/5000000000 : ℝ)|^259 ≤ (13300294293023/100000000000000 : ℝ)^195
        have hw : |(-1094785057/5000000000 : ℝ)|=(1094785057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393822571/10000000000 : ℝ)|^259 ≤ (44045725108131/100000000000000 : ℝ)^195
        have hw : |(5393822571/10000000000 : ℝ)|=(5393822571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632498509/5000000000 : ℝ)|^259 ≤ (8530796117037/20000000000000 : ℝ)^195
        have hw : |(2632498509/5000000000 : ℝ)|=(2632498509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s9_1 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5344898469/10000000000 : ℝ)*x 0 + (-2254923589/10000000000 : ℝ)*x 1 + (1052999463/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344898469/10000000000 : ℝ)^259 ≤ (43515882493351/100000000000000 : ℝ)^195 := by
    have hnat : (5344898469 : ℕ)^259*100000000000000^195 ≤ 43515882493351^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344898469 10000000000 43515882493351 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2254923589/10000000000 : ℝ)^259 ≤ (13830133716853/100000000000000 : ℝ)^195 := by
    have hnat : (2254923589 : ℕ)^259*100000000000000^195 ≤ 13830133716853^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254923589 10000000000 13830133716853 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052999463/2000000000 : ℝ)^259 ≤ (4265398378101/10000000000000 : ℝ)^195 := by
    have hnat : (1052999463 : ℕ)^259*10000000000000^195 ≤ 4265398378101^195*2000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052999463 2000000000 4265398378101 10000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344898469/10000000000 : ℝ), (-2254923589/10000000000 : ℝ), (1052999463/2000000000 : ℝ)] ![(43515882493351/100000000000000 : ℝ), (13830133716853/100000000000000 : ℝ), (4265398378101/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344898469/10000000000 : ℝ)|^259 ≤ (43515882493351/100000000000000 : ℝ)^195
        have hw : |(5344898469/10000000000 : ℝ)|=(5344898469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2254923589/10000000000 : ℝ)|^259 ≤ (13830133716853/100000000000000 : ℝ)^195
        have hw : |(-2254923589/10000000000 : ℝ)|=(2254923589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052999463/2000000000 : ℝ)|^259 ≤ (4265398378101/10000000000000 : ℝ)^195
        have hw : |(1052999463/2000000000 : ℝ)|=(1052999463/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s9_2 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1068979731/2000000000 : ℝ)*x 0 + (1316249287/2500000000 : ℝ)*x 1 + (-1127461781/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068979731/2000000000 : ℝ)^259 ≤ (8703176900939/20000000000000 : ℝ)^195 := by
    have hnat : (1068979731 : ℕ)^259*20000000000000^195 ≤ 8703176900939^195*2000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068979731 2000000000 8703176900939 20000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316249287/2500000000 : ℝ)^259 ≤ (42653981984031/100000000000000 : ℝ)^195 := by
    have hnat : (1316249287 : ℕ)^259*100000000000000^195 ≤ 42653981984031^195*2500000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316249287 2500000000 42653981984031 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1127461781/5000000000 : ℝ)^259 ≤ (13830133496903/100000000000000 : ℝ)^195 := by
    have hnat : (1127461781 : ℕ)^259*100000000000000^195 ≤ 13830133496903^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1127461781 5000000000 13830133496903 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068979731/2000000000 : ℝ), (1316249287/2500000000 : ℝ), (-1127461781/5000000000 : ℝ)] ![(8703176900939/20000000000000 : ℝ), (42653981984031/100000000000000 : ℝ), (13830133496903/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068979731/2000000000 : ℝ)|^259 ≤ (8703176900939/20000000000000 : ℝ)^195
        have hw : |(1068979731/2000000000 : ℝ)|=(1068979731/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316249287/2500000000 : ℝ)|^259 ≤ (42653981984031/100000000000000 : ℝ)^195
        have hw : |(1316249287/2500000000 : ℝ)|=(1316249287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1127461781/5000000000 : ℝ)|^259 ≤ (13830133496903/100000000000000 : ℝ)^195
        have hw : |(-1127461781/5000000000 : ℝ)|=(1127461781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s9_3 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (437133943/1000000000 : ℝ)*x 0 + (530778479/1250000000 : ℝ)*x 1 + (562520119/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (437133943/1000000000 : ℝ)^259 ≤ (6663346105247/20000000000000 : ℝ)^195 := by
    have hnat : (437133943 : ℕ)^259*20000000000000^195 ≤ 6663346105247^195*1000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437133943 1000000000 6663346105247 20000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (530778479/1250000000 : ℝ)^259 ≤ (1282248078329/4000000000000 : ℝ)^195 := by
    have hnat : (530778479 : ℕ)^259*4000000000000^195 ≤ 1282248078329^195*1250000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530778479 1250000000 1282248078329 4000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (562520119/1250000000 : ℝ)^259 ≤ (34627067508831/100000000000000 : ℝ)^195 := by
    have hnat : (562520119 : ℕ)^259*100000000000000^195 ≤ 34627067508831^195*1250000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562520119 1250000000 34627067508831 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(437133943/1000000000 : ℝ), (530778479/1250000000 : ℝ), (562520119/1250000000 : ℝ)] ![(6663346105247/20000000000000 : ℝ), (1282248078329/4000000000000 : ℝ), (34627067508831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(437133943/1000000000 : ℝ)|^259 ≤ (6663346105247/20000000000000 : ℝ)^195
        have hw : |(437133943/1000000000 : ℝ)|=(437133943/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(530778479/1250000000 : ℝ)|^259 ≤ (1282248078329/4000000000000 : ℝ)^195
        have hw : |(530778479/1250000000 : ℝ)|=(530778479/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(562520119/1250000000 : ℝ)|^259 ≤ (34627067508831/100000000000000 : ℝ)^195
        have hw : |(562520119/1250000000 : ℝ)|=(562520119/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s9_4 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-2189574753/10000000000 : ℝ)*x 0 + (5265320219/10000000000 : ℝ)*x 1 + (2696749233/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2189574753/10000000000 : ℝ)^259 ≤ (13300331720631/100000000000000 : ℝ)^195 := by
    have hnat : (2189574753 : ℕ)^259*100000000000000^195 ≤ 13300331720631^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2189574753 10000000000 13300331720631 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265320219/10000000000 : ℝ)^259 ≤ (42657458377639/100000000000000 : ℝ)^195 := by
    have hnat : (5265320219 : ℕ)^259*100000000000000^195 ≤ 42657458377639^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265320219 10000000000 42657458377639 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696749233/5000000000 : ℝ)^259 ≤ (44042209878431/100000000000000 : ℝ)^195 := by
    have hnat : (2696749233 : ℕ)^259*100000000000000^195 ≤ 44042209878431^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696749233 5000000000 44042209878431 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2189574753/10000000000 : ℝ), (5265320219/10000000000 : ℝ), (2696749233/5000000000 : ℝ)] ![(13300331720631/100000000000000 : ℝ), (42657458377639/100000000000000 : ℝ), (44042209878431/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2189574753/10000000000 : ℝ)|^259 ≤ (13300331720631/100000000000000 : ℝ)^195
        have hw : |(-2189574753/10000000000 : ℝ)|=(2189574753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265320219/10000000000 : ℝ)|^259 ≤ (42657458377639/100000000000000 : ℝ)^195
        have hw : |(5265320219/10000000000 : ℝ)|=(5265320219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696749233/5000000000 : ℝ)|^259 ≤ (44042209878431/100000000000000 : ℝ)^195
        have hw : |(2696749233/5000000000 : ℝ)|=(2696749233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s9_5 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (166011749/312500000 : ℝ)*x 0 + (-26580281/125000000 : ℝ)*x 1 + (5393498431/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (166011749/312500000 : ℝ)^259 ≤ (5395568280621/12500000000000 : ℝ)^195 := by
    have hnat : (166011749 : ℕ)^259*12500000000000^195 ≤ 5395568280621^195*312500000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166011749 312500000 5395568280621 12500000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (26580281/125000000 : ℝ)^259 ≤ (799577764281/6250000000000 : ℝ)^195 := by
    have hnat : (26580281 : ℕ)^259*6250000000000^195 ≤ 799577764281^195*125000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26580281 125000000 799577764281 6250000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393498431/10000000000 : ℝ)^259 ≤ (22021104749413/50000000000000 : ℝ)^195 := by
    have hnat : (5393498431 : ℕ)^259*50000000000000^195 ≤ 22021104749413^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393498431 10000000000 22021104749413 50000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(166011749/312500000 : ℝ), (-26580281/125000000 : ℝ), (5393498431/10000000000 : ℝ)] ![(5395568280621/12500000000000 : ℝ), (799577764281/6250000000000 : ℝ), (22021104749413/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(166011749/312500000 : ℝ)|^259 ≤ (5395568280621/12500000000000 : ℝ)^195
        have hw : |(166011749/312500000 : ℝ)|=(166011749/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-26580281/125000000 : ℝ)|^259 ≤ (799577764281/6250000000000 : ℝ)^195
        have hw : |(-26580281/125000000 : ℝ)|=(26580281/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393498431/10000000000 : ℝ)|^259 ≤ (22021104749413/50000000000000 : ℝ)^195
        have hw : |(5393498431/10000000000 : ℝ)|=(5393498431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s9_6 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5312375999/10000000000 : ℝ)*x 0 + (337093651/625000000 : ℝ)*x 1 + (-106321123/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312375999/10000000000 : ℝ)^259 ≤ (43164546579521/100000000000000 : ℝ)^195 := by
    have hnat : (5312375999 : ℕ)^259*100000000000000^195 ≤ 43164546579521^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312375999 10000000000 43164546579521 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337093651/625000000 : ℝ)^259 ≤ (22021104668069/50000000000000 : ℝ)^195 := by
    have hnat : (337093651 : ℕ)^259*50000000000000^195 ≤ 22021104668069^195*625000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337093651 625000000 22021104668069 50000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (106321123/500000000 : ℝ)^259 ≤ (6396622034339/50000000000000 : ℝ)^195 := by
    have hnat : (106321123 : ℕ)^259*50000000000000^195 ≤ 6396622034339^195*500000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106321123 500000000 6396622034339 50000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312375999/10000000000 : ℝ), (337093651/625000000 : ℝ), (-106321123/500000000 : ℝ)] ![(43164546579521/100000000000000 : ℝ), (22021104668069/50000000000000 : ℝ), (6396622034339/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312375999/10000000000 : ℝ)|^259 ≤ (43164546579521/100000000000000 : ℝ)^195
        have hw : |(5312375999/10000000000 : ℝ)|=(5312375999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337093651/625000000 : ℝ)|^259 ≤ (22021104668069/50000000000000 : ℝ)^195
        have hw : |(337093651/625000000 : ℝ)|=(337093651/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-106321123/500000000 : ℝ)|^259 ≤ (6396622034339/50000000000000 : ℝ)^195
        have hw : |(-106321123/500000000 : ℝ)|=(106321123/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s9_7 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (874269823/2000000000 : ℝ)*x 0 + (1124881213/2500000000 : ℝ)*x 1 + (849373273/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (874269823/2000000000 : ℝ)^259 ≤ (266534628547/800000000000 : ℝ)^195 := by
    have hnat : (874269823 : ℕ)^259*800000000000^195 ≤ 266534628547^195*2000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      874269823 2000000000 266534628547 800000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1124881213/2500000000 : ℝ)^259 ≤ (17310283344419/50000000000000 : ℝ)^195 := by
    have hnat : (1124881213 : ℕ)^259*50000000000000^195 ≤ 17310283344419^195*2500000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124881213 2500000000 17310283344419 50000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (849373273/2000000000 : ℝ)^259 ≤ (400782559119/1250000000000 : ℝ)^195 := by
    have hnat : (849373273 : ℕ)^259*1250000000000^195 ≤ 400782559119^195*2000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849373273 2000000000 400782559119 1250000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(874269823/2000000000 : ℝ), (1124881213/2500000000 : ℝ), (849373273/2000000000 : ℝ)] ![(266534628547/800000000000 : ℝ), (17310283344419/50000000000000 : ℝ), (400782559119/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(874269823/2000000000 : ℝ)|^259 ≤ (266534628547/800000000000 : ℝ)^195
        have hw : |(874269823/2000000000 : ℝ)|=(874269823/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1124881213/2500000000 : ℝ)|^259 ≤ (17310283344419/50000000000000 : ℝ)^195
        have hw : |(1124881213/2500000000 : ℝ)|=(1124881213/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(849373273/2000000000 : ℝ)|^259 ≤ (400782559119/1250000000000 : ℝ)^195
        have hw : |(849373273/2000000000 : ℝ)|=(849373273/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1095_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18569689/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14021/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11291/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2823/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (701/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14021/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11291/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14021/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11291/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14021/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11291/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14021/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11291/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14021/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11291/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14021/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11291/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11291/100000 : ℝ) ^ (8287/2048 : ℝ) ≤ (14688890529404723/100000000000000000000 : ℝ) := by
    have hpowers : (11291/100000 : ℝ)^8287 ≤ (14688890529404723/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11291 : ℕ)^8287*100000000000000000000^2048 ≤ 14688890529404723^2048*100000^8287 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11291 100000 14688890529404723 100000000000000000000 8287 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11291/100000 : ℝ)) (X := (14688890529404723/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8287 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14021/100000 : ℝ) ^ (8287/2048 : ℝ) ≤ (7056150412105103/20000000000000000000 : ℝ) := by
    have hpowers : (14021/100000 : ℝ)^8287 ≤ (7056150412105103/20000000000000000000 : ℝ)^2048 := by
      have hnat : (14021 : ℕ)^8287*20000000000000000000^2048 ≤ 7056150412105103^2048*100000^8287 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14021 100000 7056150412105103 20000000000000000000 8287 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14021/100000 : ℝ)) (X := (7056150412105103/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8287 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014688890529404723/50000000000000000000 : ℝ) ≤ (5000362972385467/5000000000000000 : ℝ) ^ (8287/2048 : ℝ) := by
    have hpowers : (50014688890529404723/50000000000000000000 : ℝ)^2048 ≤ (5000362972385467/5000000000000000 : ℝ)^8287 := by
      have hnat : (50014688890529404723 : ℕ)^2048*5000000000000000^8287 ≤ 5000362972385467^8287*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014688890529404723 50000000000000000000 5000362972385467 5000000000000000 2048 8287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000362972385467/5000000000000000 : ℝ)) (X := (50014688890529404723/50000000000000000000 : ℝ)) (by norm_num) 8287 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024984821294965119/50000000000000000000 : ℝ) ≤ (2500308671967151/2500000000000000 : ℝ) ^ (8287/2048 : ℝ) := by
    have hpowers : (50024984821294965119/50000000000000000000 : ℝ)^2048 ≤ (2500308671967151/2500000000000000 : ℝ)^8287 := by
      have hnat : (50024984821294965119 : ℕ)^2048*2500000000000000^8287 ≤ 2500308671967151^8287*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024984821294965119 50000000000000000000 2500308671967151 2500000000000000 2048 8287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500308671967151/2500000000000000 : ℝ)) (X := (50024984821294965119/50000000000000000000 : ℝ)) (by norm_num) 8287 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10007056150412105103/10000000000000000000 : ℝ) ≤ (5000871715483137/5000000000000000 : ℝ) ^ (8287/2048 : ℝ) := by
    have hpowers : (10007056150412105103/10000000000000000000 : ℝ)^2048 ≤ (5000871715483137/5000000000000000 : ℝ)^8287 := by
      have hnat : (10007056150412105103 : ℕ)^2048*5000000000000000^8287 ≤ 5000871715483137^8287*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10007056150412105103 10000000000000000000 5000871715483137 5000000000000000 2048 8287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000871715483137/5000000000000000 : ℝ)) (X := (10007056150412105103/10000000000000000000 : ℝ)) (by norm_num) 8287 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14688890529404723/100000000000000000000 : ℝ) ≤ ((97466047830689521/97500000000000000 : ℝ)+2*(50874309767/27300000000000 : ℝ)*(11291/100000 : ℝ))^(8287/2048 : ℝ) := by
    rw [show (97466047830689521/97500000000000000 : ℝ)+2*(50874309767/27300000000000 : ℝ)*(11291/100000 : ℝ)=(5000362972385467/5000000000000000 : ℝ) by norm_num, show 1+2*(14688890529404723/100000000000000000000 : ℝ)=(50014688890529404723/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7056150412105103/20000000000000000000 : ℝ)+(14688890529404723/100000000000000000000 : ℝ) ≤ ((97466047830689521/97500000000000000 : ℝ)+(50874309767/27300000000000 : ℝ)*((14021/100000 : ℝ)+(11291/100000 : ℝ)))^(8287/2048 : ℝ) := by
    rw [show (97466047830689521/97500000000000000 : ℝ)+(50874309767/27300000000000 : ℝ)*((14021/100000 : ℝ)+(11291/100000 : ℝ))=(2500308671967151/2500000000000000 : ℝ) by norm_num, show 1+(7056150412105103/20000000000000000000 : ℝ)+(14688890529404723/100000000000000000000 : ℝ)=(50024984821294965119/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7056150412105103/20000000000000000000 : ℝ) ≤ ((97466047830689521/97500000000000000 : ℝ)+2*(50874309767/27300000000000 : ℝ)*(14021/100000 : ℝ))^(8287/2048 : ℝ) := by
    rw [show (97466047830689521/97500000000000000 : ℝ)+2*(50874309767/27300000000000 : ℝ)*(14021/100000 : ℝ)=(5000871715483137/5000000000000000 : ℝ) by norm_num, show 1+2*(7056150412105103/20000000000000000000 : ℝ)=(10007056150412105103/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (97466047830689521/97500000000000000 : ℝ)*(X 1 0+X 2 0)+(50874309767/27300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8287/2048 : ℝ)) (lo := (11291/100000 : ℝ)) (hi := (14021/100000 : ℝ)) (c := (97466047830689521/97500000000000000 : ℝ)) (alpha := (50874309767/27300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (97466047830689521/97500000000000000 : ℝ)*(X 0 1+X 2 1)+(50874309767/27300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8287/2048 : ℝ)) (lo := (11291/100000 : ℝ)) (hi := (14021/100000 : ℝ)) (c := (97466047830689521/97500000000000000 : ℝ)) (alpha := (50874309767/27300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (97466047830689521/97500000000000000 : ℝ)*(X 0 2+X 1 2)+(50874309767/27300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8287/2048 : ℝ)) (lo := (11291/100000 : ℝ)) (hi := (14021/100000 : ℝ)) (c := (97466047830689521/97500000000000000 : ℝ)) (alpha := (50874309767/27300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1094785057/5000000000 : ℝ)*X 0 0+(5393822571/10000000000 : ℝ)*X 0 1+(2632498509/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344898469/10000000000 : ℝ)*X 1 0+(-2254923589/10000000000 : ℝ)*X 1 1+(1052999463/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s9_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068979731/2000000000 : ℝ)*X 2 0+(1316249287/2500000000 : ℝ)*X 2 1+(-1127461781/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s9_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((437133943/1000000000 : ℝ)*X 0 0+(530778479/1250000000 : ℝ)*X 0 1+(562520119/1250000000 : ℝ)*X 0 2+(437133943/1000000000 : ℝ)*X 1 0+(530778479/1250000000 : ℝ)*X 1 1+(562520119/1250000000 : ℝ)*X 1 2+(437133943/1000000000 : ℝ)*X 2 0+(530778479/1250000000 : ℝ)*X 2 1+(562520119/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s9_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2189574753/10000000000 : ℝ)*X 0 0+(5265320219/10000000000 : ℝ)*X 0 1+(2696749233/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s9_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((166011749/312500000 : ℝ)*X 1 0+(-26580281/125000000 : ℝ)*X 1 1+(5393498431/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s9_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312375999/10000000000 : ℝ)*X 2 0+(337093651/625000000 : ℝ)*X 2 1+(-106321123/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s9_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((874269823/2000000000 : ℝ)*X 0 0+(1124881213/2500000000 : ℝ)*X 0 1+(849373273/2000000000 : ℝ)*X 0 2+(874269823/2000000000 : ℝ)*X 1 0+(1124881213/2500000000 : ℝ)*X 1 1+(849373273/2000000000 : ℝ)*X 1 2+(874269823/2000000000 : ℝ)*X 2 0+(1124881213/2500000000 : ℝ)*X 2 1+(849373273/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s9_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2282308501964402428854369/11375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1225922017/100000000000000 : ℝ)*(base19) + (1176575637/100000000000000 : ℝ)*(base23) + (121344657/50000000000000 : ℝ)*(upper3) + (170758031/100000000000000 : ℝ)*(upper4) + (104020489/100000000000000 : ℝ)*(upper5) + (5850294777231727/100000000000000 : ℝ)*(major0) + (5850294777231727/100000000000000 : ℝ)*(major1) + (5850294777231727/100000000000000 : ℝ)*(major2) + (1552495607323437/20000000000000 : ℝ)*(sp0) + (388126051918403/5000000000000 : ℝ)*(sp1) + (194063027192861/2500000000000 : ℝ)*(sp2) + (7876106153277/200000000000 : ℝ)*(sp3) + (44227672891/100000000000000 : ℝ)*(sp4) + (2841369357/20000000000000 : ℝ)*(sp7) + (1969033641742643/50000000000000 : ℝ)*(f.failure) + (7762522264290077/100000000000000 : ℝ)*(f.sum) + (2005071469979/1365000000000000000000000000 : ℝ)*base65 + (114382286954781877/22750000000000000000000000000000 : ℝ)*base68 + (92722804943468123/22750000000000000000000000000000 : ℝ)*base69 + (18436721389968123/22750000000000000000000000000000 : ℝ)*base71 + (5604719497409/1365000000000000000000000000 : ℝ)*base73 + (173245610587531877/22750000000000000000000000000000 : ℝ)*base76 + (54990679475031877/22750000000000000000000000000000 : ℝ)*base78 + (460147055303781877/22750000000000000000000000000000 : ℝ)*base80 + (230904056023/170625000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (4798027/625000000000000000000 : ℝ)*base89 + (4798027/625000000000000000000 : ℝ)*base91 + (4798027/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16221783831261565973011489/5687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (529045641/100000000000000 : ℝ)*(base19) + (711623879/100000000000000 : ℝ)*(base23) + (174386507/100000000000000 : ℝ)*(lower1) + (42012767/100000000000000 : ℝ)*(upper3) + (61790647/100000000000000 : ℝ)*(lower4) + (80156227/100000000000000 : ℝ)*(upper5) + (5879763400203187/100000000000000 : ℝ)*(major0) + (5879763400203187/100000000000000 : ℝ)*(major1) + (5879763400203187/100000000000000 : ℝ)*(major2) + (3387408783/100000000000000 : ℝ)*(sp2) + (1560324582740189/20000000000000 : ℝ)*(sp4) + (7801622384655303/100000000000000 : ℝ)*(sp5) + (3900809407334141/50000000000000 : ℝ)*(sp6) + (3957903791632689/100000000000000 : ℝ)*(sp7) + (3957903791632689/100000000000000 : ℝ)*(f.failure) + (1560324582740189/20000000000000 : ℝ)*(f.sum) + (1387657229821/1365000000000000000000000000 : ℝ)*base66 + (67875752890700337/22750000000000000000000000000000 : ℝ)*base68 + (413938785478700337/22750000000000000000000000000000 : ℝ)*base70 + (907835698460299663/22750000000000000000000000000000 : ℝ)*base71 + (1397356449809/1365000000000000000000000000 : ℝ)*base73 + (1050167087801950337/22750000000000000000000000000000 : ℝ)*base76 + (116239450886950337/22750000000000000000000000000000 : ℝ)*base78 + (74921092123450337/22750000000000000000000000000000 : ℝ)*base80 + (1813652822003/682500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (536279/1250000000000000000000 : ℝ)*base90 + (536279/1250000000000000000000 : ℝ)*base92 + (536279/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1095_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18569689/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14021/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11291/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2823/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (701/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1095_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1095_box_0 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-412222023/2000000000 : ℝ)*x 0 + (215078687/400000000 : ℝ)*x 1 + (5376967523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (412222023/2000000000 : ℝ)^259 ≤ (12273987856407/100000000000000 : ℝ)^195 := by
    have hnat : (412222023 : ℕ)^259*100000000000000^195 ≤ 12273987856407^195*2000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412222023 2000000000 12273987856407 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215078687/400000000 : ℝ)^259 ≤ (43863004178437/100000000000000 : ℝ)^195 := by
    have hnat : (215078687 : ℕ)^259*100000000000000^195 ≤ 43863004178437^195*400000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215078687 400000000 43863004178437 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5376967523/10000000000 : ℝ)^259 ≤ (43863007948993/100000000000000 : ℝ)^195 := by
    have hnat : (5376967523 : ℕ)^259*100000000000000^195 ≤ 43863007948993^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376967523 10000000000 43863007948993 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-412222023/2000000000 : ℝ), (215078687/400000000 : ℝ), (5376967523/10000000000 : ℝ)] ![(12273987856407/100000000000000 : ℝ), (43863004178437/100000000000000 : ℝ), (43863007948993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-412222023/2000000000 : ℝ)|^259 ≤ (12273987856407/100000000000000 : ℝ)^195
        have hw : |(-412222023/2000000000 : ℝ)|=(412222023/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(215078687/400000000 : ℝ)|^259 ≤ (43863004178437/100000000000000 : ℝ)^195
        have hw : |(215078687/400000000 : ℝ)|=(215078687/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5376967523/10000000000 : ℝ)|^259 ≤ (43863007948993/100000000000000 : ℝ)^195
        have hw : |(5376967523/10000000000 : ℝ)|=(5376967523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_box_1 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5295521009/10000000000 : ℝ)*x 0 + (-1085721959/5000000000 : ℝ)*x 1 + (2688483751/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295521009/10000000000 : ℝ)^259 ≤ (21491370817771/50000000000000 : ℝ)^195 := by
    have hnat : (5295521009 : ℕ)^259*50000000000000^195 ≤ 21491370817771^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295521009 10000000000 21491370817771 50000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1085721959/5000000000 : ℝ)^259 ≤ (3288562656897/25000000000000 : ℝ)^195 := by
    have hnat : (1085721959 : ℕ)^259*25000000000000^195 ≤ 3288562656897^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085721959 5000000000 3288562656897 25000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2688483751/5000000000 : ℝ)^259 ≤ (43863007721459/100000000000000 : ℝ)^195 := by
    have hnat : (2688483751 : ℕ)^259*100000000000000^195 ≤ 43863007721459^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688483751 5000000000 43863007721459 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295521009/10000000000 : ℝ), (-1085721959/5000000000 : ℝ), (2688483751/5000000000 : ℝ)] ![(21491370817771/50000000000000 : ℝ), (3288562656897/25000000000000 : ℝ), (43863007721459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295521009/10000000000 : ℝ)|^259 ≤ (21491370817771/50000000000000 : ℝ)^195
        have hw : |(5295521009/10000000000 : ℝ)|=(5295521009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1085721959/5000000000 : ℝ)|^259 ≤ (3288562656897/25000000000000 : ℝ)^195
        have hw : |(-1085721959/5000000000 : ℝ)|=(1085721959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2688483751/5000000000 : ℝ)|^259 ≤ (43863007721459/100000000000000 : ℝ)^195
        have hw : |(2688483751/5000000000 : ℝ)|=(2688483751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_box_2 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1323880407/2500000000 : ℝ)*x 0 + (336060451/625000000 : ℝ)*x 1 + (-1085721737/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323880407/2500000000 : ℝ)^259 ≤ (42982748308851/100000000000000 : ℝ)^195 := by
    have hnat : (1323880407 : ℕ)^259*100000000000000^195 ≤ 42982748308851^195*2500000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323880407 2500000000 42982748308851 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (336060451/625000000 : ℝ)^259 ≤ (43863004622669/100000000000000 : ℝ)^195 := by
    have hnat : (336060451 : ℕ)^259*100000000000000^195 ≤ 43863004622669^195*625000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336060451 625000000 43863004622669 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1085721737/5000000000 : ℝ)^259 ≤ (13154247055143/100000000000000 : ℝ)^195 := by
    have hnat : (1085721737 : ℕ)^259*100000000000000^195 ≤ 13154247055143^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085721737 5000000000 13154247055143 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323880407/2500000000 : ℝ), (336060451/625000000 : ℝ), (-1085721737/5000000000 : ℝ)] ![(42982748308851/100000000000000 : ℝ), (43863004622669/100000000000000 : ℝ), (13154247055143/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323880407/2500000000 : ℝ)|^259 ≤ (42982748308851/100000000000000 : ℝ)^195
        have hw : |(1323880407/2500000000 : ℝ)|=(1323880407/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(336060451/625000000 : ℝ)|^259 ≤ (43863004622669/100000000000000 : ℝ)^195
        have hw : |(336060451/625000000 : ℝ)|=(336060451/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1085721737/5000000000 : ℝ)|^259 ≤ (13154247055143/100000000000000 : ℝ)^195
        have hw : |(-1085721737/5000000000 : ℝ)|=(1085721737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_box_3 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4479391019/10000000000 : ℝ)*x 0 + (107986359/250000000 : ℝ)*x 1 + (4319454637/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4479391019/10000000000 : ℝ)^259 ≤ (2150934924489/6250000000000 : ℝ)^195 := by
    have hnat : (4479391019 : ℕ)^259*6250000000000^195 ≤ 2150934924489^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4479391019 10000000000 2150934924489 6250000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (107986359/250000000 : ℝ)^259 ≤ (32792519200207/100000000000000 : ℝ)^195 := by
    have hnat : (107986359 : ℕ)^259*100000000000000^195 ≤ 32792519200207^195*250000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107986359 250000000 32792519200207 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4319454637/10000000000 : ℝ)^259 ≤ (6558504398667/20000000000000 : ℝ)^195 := by
    have hnat : (4319454637 : ℕ)^259*20000000000000^195 ≤ 6558504398667^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4319454637 10000000000 6558504398667 20000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4479391019/10000000000 : ℝ), (107986359/250000000 : ℝ), (4319454637/10000000000 : ℝ)] ![(2150934924489/6250000000000 : ℝ), (32792519200207/100000000000000 : ℝ), (6558504398667/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4479391019/10000000000 : ℝ)|^259 ≤ (2150934924489/6250000000000 : ℝ)^195
        have hw : |(4479391019/10000000000 : ℝ)|=(4479391019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(107986359/250000000 : ℝ)|^259 ≤ (32792519200207/100000000000000 : ℝ)^195
        have hw : |(107986359/250000000 : ℝ)|=(107986359/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4319454637/10000000000 : ℝ)|^259 ≤ (6558504398667/20000000000000 : ℝ)^195
        have hw : |(4319454637/10000000000 : ℝ)|=(4319454637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_box_4 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-463883091/2000000000 : ℝ)*x 0 + (2640256603/5000000000 : ℝ)*x 1 + (41254013/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (463883091/2000000000 : ℝ)^259 ≤ (14357953127901/100000000000000 : ℝ)^195 := by
    have hnat : (463883091 : ℕ)^259*100000000000000^195 ≤ 14357953127901^195*2000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      463883091 2000000000 14357953127901 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2640256603/5000000000 : ℝ)^259 ≤ (10705255241031/25000000000000 : ℝ)^195 := by
    have hnat : (2640256603 : ℕ)^259*25000000000000^195 ≤ 10705255241031^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640256603 5000000000 10705255241031 25000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41254013/78125000 : ℝ)^259 ≤ (5352628237141/12500000000000 : ℝ)^195 := by
    have hnat : (41254013 : ℕ)^259*12500000000000^195 ≤ 5352628237141^195*78125000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41254013 78125000 5352628237141 12500000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-463883091/2000000000 : ℝ), (2640256603/5000000000 : ℝ), (41254013/78125000 : ℝ)] ![(14357953127901/100000000000000 : ℝ), (10705255241031/25000000000000 : ℝ), (5352628237141/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-463883091/2000000000 : ℝ)|^259 ≤ (14357953127901/100000000000000 : ℝ)^195
        have hw : |(-463883091/2000000000 : ℝ)|=(463883091/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2640256603/5000000000 : ℝ)|^259 ≤ (10705255241031/25000000000000 : ℝ)^195
        have hw : |(2640256603/5000000000 : ℝ)|=(2640256603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(41254013/78125000 : ℝ)|^259 ≤ (5352628237141/12500000000000 : ℝ)^195
        have hw : |(41254013/78125000 : ℝ)|=(41254013/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_box_5 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5363738397/10000000000 : ℝ)*x 0 + (-552310671/2500000000 : ℝ)*x 1 + (2640256747/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363738397/10000000000 : ℝ)^259 ≤ (43719729185243/100000000000000 : ℝ)^195 := by
    have hnat : (5363738397 : ℕ)^259*100000000000000^195 ≤ 43719729185243^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363738397 10000000000 43719729185243 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (552310671/2500000000 : ℝ)^259 ≤ (13459246740721/100000000000000 : ℝ)^195 := by
    have hnat : (552310671 : ℕ)^259*100000000000000^195 ≤ 13459246740721^195*2500000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      552310671 2500000000 13459246740721 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2640256747/5000000000 : ℝ)^259 ≤ (42821024066101/100000000000000 : ℝ)^195 := by
    have hnat : (2640256747 : ℕ)^259*100000000000000^195 ≤ 42821024066101^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640256747 5000000000 42821024066101 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363738397/10000000000 : ℝ), (-552310671/2500000000 : ℝ), (2640256747/5000000000 : ℝ)] ![(43719729185243/100000000000000 : ℝ), (13459246740721/100000000000000 : ℝ), (42821024066101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363738397/10000000000 : ℝ)|^259 ≤ (43719729185243/100000000000000 : ℝ)^195
        have hw : |(5363738397/10000000000 : ℝ)|=(5363738397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-552310671/2500000000 : ℝ)|^259 ≤ (13459246740721/100000000000000 : ℝ)^195
        have hw : |(-552310671/2500000000 : ℝ)|=(552310671/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2640256747/5000000000 : ℝ)|^259 ≤ (42821024066101/100000000000000 : ℝ)^195
        have hw : |(2640256747/5000000000 : ℝ)|=(2640256747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_box_6 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1340934579/2500000000 : ℝ)*x 0 + (2640256573/5000000000 : ℝ)*x 1 + (-441848651/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1340934579/2500000000 : ℝ)^259 ≤ (43719728308323/100000000000000 : ℝ)^195 := by
    have hnat : (1340934579 : ℕ)^259*100000000000000^195 ≤ 43719728308323^195*2500000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1340934579 2500000000 43719728308323 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2640256573/5000000000 : ℝ)^259 ≤ (42821020317879/100000000000000 : ℝ)^195 := by
    have hnat : (2640256573 : ℕ)^259*100000000000000^195 ≤ 42821020317879^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640256573 5000000000 42821020317879 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (441848651/2000000000 : ℝ)^259 ≤ (13459251361111/100000000000000 : ℝ)^195 := by
    have hnat : (441848651 : ℕ)^259*100000000000000^195 ≤ 13459251361111^195*2000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441848651 2000000000 13459251361111 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1340934579/2500000000 : ℝ), (2640256573/5000000000 : ℝ), (-441848651/2000000000 : ℝ)] ![(43719728308323/100000000000000 : ℝ), (42821020317879/100000000000000 : ℝ), (13459251361111/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1340934579/2500000000 : ℝ)|^259 ≤ (43719728308323/100000000000000 : ℝ)^195
        have hw : |(1340934579/2500000000 : ℝ)|=(1340934579/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2640256573/5000000000 : ℝ)|^259 ≤ (42821020317879/100000000000000 : ℝ)^195
        have hw : |(2640256573/5000000000 : ℝ)|=(2640256573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-441848651/2000000000 : ℝ)|^259 ≤ (13459251361111/100000000000000 : ℝ)^195
        have hw : |(-441848651/2000000000 : ℝ)|=(441848651/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_box_7 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1065736601/2500000000 : ℝ)*x 0 + (4427655473/10000000000 : ℝ)*x 1 + (4427655713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1065736601/2500000000 : ℝ)^259 ≤ (32223948421811/100000000000000 : ℝ)^195 := by
    have hnat : (1065736601 : ℕ)^259*100000000000000^195 ≤ 32223948421811^195*2500000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065736601 2500000000 32223948421811 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4427655473/10000000000 : ℝ)^259 ≤ (1694401228083/5000000000000 : ℝ)^195 := by
    have hnat : (4427655473 : ℕ)^259*5000000000000^195 ≤ 1694401228083^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4427655473 10000000000 1694401228083 5000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4427655713/10000000000 : ℝ)^259 ≤ (3388802700143/10000000000000 : ℝ)^195 := by
    have hnat : (4427655713 : ℕ)^259*10000000000000^195 ≤ 3388802700143^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4427655713 10000000000 3388802700143 10000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1065736601/2500000000 : ℝ), (4427655473/10000000000 : ℝ), (4427655713/10000000000 : ℝ)] ![(32223948421811/100000000000000 : ℝ), (1694401228083/5000000000000 : ℝ), (3388802700143/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1065736601/2500000000 : ℝ)|^259 ≤ (32223948421811/100000000000000 : ℝ)^195
        have hw : |(1065736601/2500000000 : ℝ)|=(1065736601/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4427655473/10000000000 : ℝ)|^259 ≤ (1694401228083/5000000000000 : ℝ)^195
        have hw : |(4427655473/10000000000 : ℝ)|=(4427655473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4427655713/10000000000 : ℝ)|^259 ≤ (3388802700143/10000000000000 : ℝ)^195
        have hw : |(4427655713/10000000000 : ℝ)|=(4427655713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_box_8 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-566363927/2500000000 : ℝ)*x 0 + (651875871/1250000000 : ℝ)*x 1 + (107731423/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (566363927/2500000000 : ℝ)^259 ≤ (6957998536679/50000000000000 : ℝ)^195 := by
    have hnat : (566363927 : ℕ)^259*50000000000000^195 ≤ 6957998536679^195*2500000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      566363927 2500000000 6957998536679 50000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (651875871/1250000000 : ℝ)^259 ≤ (21058454915387/50000000000000 : ℝ)^195 := by
    have hnat : (651875871 : ℕ)^259*50000000000000^195 ≤ 21058454915387^195*1250000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      651875871 1250000000 21058454915387 50000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (107731423/200000000 : ℝ)^259 ≤ (43967093070923/100000000000000 : ℝ)^195 := by
    have hnat : (107731423 : ℕ)^259*100000000000000^195 ≤ 43967093070923^195*200000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107731423 200000000 43967093070923 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-566363927/2500000000 : ℝ), (651875871/1250000000 : ℝ), (107731423/200000000 : ℝ)] ![(6957998536679/50000000000000 : ℝ), (21058454915387/50000000000000 : ℝ), (43967093070923/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-566363927/2500000000 : ℝ)|^259 ≤ (6957998536679/50000000000000 : ℝ)^195
        have hw : |(-566363927/2500000000 : ℝ)|=(566363927/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(651875871/1250000000 : ℝ)|^259 ≤ (21058454915387/50000000000000 : ℝ)^195
        have hw : |(651875871/1250000000 : ℝ)|=(651875871/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(107731423/200000000 : ℝ)|^259 ≤ (43967093070923/100000000000000 : ℝ)^195
        have hw : |(107731423/200000000 : ℝ)|=(107731423/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_box_9 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1322181443/2500000000 : ℝ)*x 0 + (-2167609329/10000000000 : ℝ)*x 1 + (168330353/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322181443/2500000000 : ℝ)^259 ≤ (5363687380751/12500000000000 : ℝ)^195 := by
    have hnat : (1322181443 : ℕ)^259*12500000000000^195 ≤ 5363687380751^195*2500000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322181443 2500000000 5363687380751 12500000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2167609329/10000000000 : ℝ)^259 ≤ (2624681256593/20000000000000 : ℝ)^195 := by
    have hnat : (2167609329 : ℕ)^259*20000000000000^195 ≤ 2624681256593^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2167609329 10000000000 2624681256593 20000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (168330353/312500000 : ℝ)^259 ≤ (35173675723/80000000000 : ℝ)^195 := by
    have hnat : (168330353 : ℕ)^259*80000000000^195 ≤ 35173675723^195*312500000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168330353 312500000 35173675723 80000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322181443/2500000000 : ℝ), (-2167609329/10000000000 : ℝ), (168330353/312500000 : ℝ)] ![(5363687380751/12500000000000 : ℝ), (2624681256593/20000000000000 : ℝ), (35173675723/80000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322181443/2500000000 : ℝ)|^259 ≤ (5363687380751/12500000000000 : ℝ)^195
        have hw : |(1322181443/2500000000 : ℝ)|=(1322181443/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2167609329/10000000000 : ℝ)|^259 ≤ (2624681256593/20000000000000 : ℝ)^195
        have hw : |(-2167609329/10000000000 : ℝ)|=(2167609329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(168330353/312500000 : ℝ)|^259 ≤ (35173675723/80000000000 : ℝ)^195
        have hw : |(168330353/312500000 : ℝ)|=(168330353/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_box_10 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2644362779/5000000000 : ℝ)*x 0 + (5386570473/10000000000 : ℝ)*x 1 + (-541902681/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644362779/5000000000 : ℝ)^259 ≤ (42909496739891/100000000000000 : ℝ)^195 := by
    have hnat : (2644362779 : ℕ)^259*100000000000000^195 ≤ 42909496739891^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644362779 5000000000 42909496739891 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5386570473/10000000000 : ℝ)^259 ≤ (21983542865689/50000000000000 : ℝ)^195 := by
    have hnat : (5386570473 : ℕ)^259*50000000000000^195 ≤ 21983542865689^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386570473 10000000000 21983542865689 50000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (541902681/2500000000 : ℝ)^259 ≤ (2624683500139/20000000000000 : ℝ)^195 := by
    have hnat : (541902681 : ℕ)^259*20000000000000^195 ≤ 2624683500139^195*2500000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541902681 2500000000 2624683500139 20000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644362779/5000000000 : ℝ), (5386570473/10000000000 : ℝ), (-541902681/2500000000 : ℝ)] ![(42909496739891/100000000000000 : ℝ), (21983542865689/50000000000000 : ℝ), (2624683500139/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644362779/5000000000 : ℝ)|^259 ≤ (42909496739891/100000000000000 : ℝ)^195
        have hw : |(2644362779/5000000000 : ℝ)|=(2644362779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5386570473/10000000000 : ℝ)|^259 ≤ (21983542865689/50000000000000 : ℝ)^195
        have hw : |(5386570473/10000000000 : ℝ)|=(5386570473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-541902681/2500000000 : ℝ)|^259 ≤ (2624683500139/20000000000000 : ℝ)^195
        have hw : |(-541902681/2500000000 : ℝ)|=(541902681/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_box_11 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (140645911/312500000 : ℝ)*x 0 + (861734899/2000000000 : ℝ)*x 1 + (538584417/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (140645911/312500000 : ℝ)^259 ≤ (17316130716043/50000000000000 : ℝ)^195 := by
    have hnat : (140645911 : ℕ)^259*50000000000000^195 ≤ 17316130716043^195*312500000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140645911 312500000 17316130716043 50000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (861734899/2000000000 : ℝ)^259 ≤ (8170966259443/25000000000000 : ℝ)^195 := by
    have hnat : (861734899 : ℕ)^259*25000000000000^195 ≤ 8170966259443^195*2000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      861734899 2000000000 8170966259443 25000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (538584417/1250000000 : ℝ)^259 ≤ (16341936755519/50000000000000 : ℝ)^195 := by
    have hnat : (538584417 : ℕ)^259*50000000000000^195 ≤ 16341936755519^195*1250000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538584417 1250000000 16341936755519 50000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(140645911/312500000 : ℝ), (861734899/2000000000 : ℝ), (538584417/1250000000 : ℝ)] ![(17316130716043/50000000000000 : ℝ), (8170966259443/25000000000000 : ℝ), (16341936755519/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(140645911/312500000 : ℝ)|^259 ≤ (17316130716043/50000000000000 : ℝ)^195
        have hw : |(140645911/312500000 : ℝ)|=(140645911/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(861734899/2000000000 : ℝ)|^259 ≤ (8170966259443/25000000000000 : ℝ)^195
        have hw : |(861734899/2000000000 : ℝ)|=(861734899/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(538584417/1250000000 : ℝ)|^259 ≤ (16341936755519/50000000000000 : ℝ)^195
        have hw : |(538584417/1250000000 : ℝ)|=(538584417/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_box_12 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-105770943/500000000 : ℝ)*x 0 + (544116103/1000000000 : ℝ)*x 1 + (5272497821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105770943/500000000 : ℝ)^259 ≤ (6352695017953/50000000000000 : ℝ)^195 := by
    have hnat : (105770943 : ℕ)^259*50000000000000^195 ≤ 6352695017953^195*500000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105770943 500000000 6352695017953 50000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (544116103/1000000000 : ℝ)^259 ≤ (44559899199263/100000000000000 : ℝ)^195 := by
    have hnat : (544116103 : ℕ)^259*100000000000000^195 ≤ 44559899199263^195*1000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544116103 1000000000 44559899199263 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5272497821/10000000000 : ℝ)^259 ≤ (42734710749927/100000000000000 : ℝ)^195 := by
    have hnat : (5272497821 : ℕ)^259*100000000000000^195 ≤ 42734710749927^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272497821 10000000000 42734710749927 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-105770943/500000000 : ℝ), (544116103/1000000000 : ℝ), (5272497821/10000000000 : ℝ)] ![(6352695017953/50000000000000 : ℝ), (44559899199263/100000000000000 : ℝ), (42734710749927/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-105770943/500000000 : ℝ)|^259 ≤ (6352695017953/50000000000000 : ℝ)^195
        have hw : |(-105770943/500000000 : ℝ)|=(105770943/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(544116103/1000000000 : ℝ)|^259 ≤ (44559899199263/100000000000000 : ℝ)^195
        have hw : |(544116103/1000000000 : ℝ)|=(544116103/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5272497821/10000000000 : ℝ)|^259 ≤ (42734710749927/100000000000000 : ℝ)^195
        have hw : |(5272497821/10000000000 : ℝ)|=(5272497821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_box_13 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2684702501/5000000000 : ℝ)*x 0 + (-1106162999/5000000000 : ℝ)*x 1 + (5272497811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684702501/5000000000 : ℝ)^259 ≤ (43781087473731/100000000000000 : ℝ)^195 := by
    have hnat : (2684702501 : ℕ)^259*100000000000000^195 ≤ 43781087473731^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684702501 5000000000 43781087473731 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1106162999/5000000000 : ℝ)^259 ≤ (2696840372119/20000000000000 : ℝ)^195 := by
    have hnat : (1106162999 : ℕ)^259*20000000000000^195 ≤ 2696840372119^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1106162999 5000000000 2696840372119 20000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5272497811/10000000000 : ℝ)^259 ≤ (21367355321137/50000000000000 : ℝ)^195 := by
    have hnat : (5272497811 : ℕ)^259*50000000000000^195 ≤ 21367355321137^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272497811 10000000000 21367355321137 50000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684702501/5000000000 : ℝ), (-1106162999/5000000000 : ℝ), (5272497811/10000000000 : ℝ)] ![(43781087473731/100000000000000 : ℝ), (2696840372119/20000000000000 : ℝ), (21367355321137/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684702501/5000000000 : ℝ)|^259 ≤ (43781087473731/100000000000000 : ℝ)^195
        have hw : |(2684702501/5000000000 : ℝ)|=(2684702501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1106162999/5000000000 : ℝ)|^259 ≤ (2696840372119/20000000000000 : ℝ)^195
        have hw : |(-1106162999/5000000000 : ℝ)|=(1106162999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5272497811/10000000000 : ℝ)|^259 ≤ (21367355321137/50000000000000 : ℝ)^195
        have hw : |(5272497811/10000000000 : ℝ)|=(5272497811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_box_14 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1342351251/2500000000 : ℝ)*x 0 + (2636248899/5000000000 : ℝ)*x 1 + (-1106163007/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1342351251/2500000000 : ℝ)^259 ≤ (43781087495391/100000000000000 : ℝ)^195 := by
    have hnat : (1342351251 : ℕ)^259*100000000000000^195 ≤ 43781087495391^195*2500000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342351251 2500000000 43781087495391 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2636248899/5000000000 : ℝ)^259 ≤ (10683677625581/25000000000000 : ℝ)^195 := by
    have hnat : (2636248899 : ℕ)^259*25000000000000^195 ≤ 10683677625581^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636248899 5000000000 10683677625581 25000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1106163007/5000000000 : ℝ)^259 ≤ (6742100995061/50000000000000 : ℝ)^195 := by
    have hnat : (1106163007 : ℕ)^259*50000000000000^195 ≤ 6742100995061^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1106163007 5000000000 6742100995061 50000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1342351251/2500000000 : ℝ), (2636248899/5000000000 : ℝ), (-1106163007/5000000000 : ℝ)] ![(43781087495391/100000000000000 : ℝ), (10683677625581/25000000000000 : ℝ), (6742100995061/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1342351251/2500000000 : ℝ)|^259 ≤ (43781087495391/100000000000000 : ℝ)^195
        have hw : |(1342351251/2500000000 : ℝ)|=(1342351251/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2636248899/5000000000 : ℝ)|^259 ≤ (10683677625581/25000000000000 : ℝ)^195
        have hw : |(2636248899/5000000000 : ℝ)|=(2636248899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1106163007/5000000000 : ℝ)|^259 ≤ (6742100995061/50000000000000 : ℝ)^195
        have hw : |(-1106163007/5000000000 : ℝ)|=(1106163007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_box_15 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (530591049/1250000000 : ℝ)*x 0 + (887328521/2000000000 : ℝ)*x 1 + (554580339/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530591049/1250000000 : ℝ)^259 ≤ (32041167843899/100000000000000 : ℝ)^195 := by
    have hnat : (530591049 : ℕ)^259*100000000000000^195 ≤ 32041167843899^195*1250000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530591049 1250000000 32041167843899 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (887328521/2000000000 : ℝ)^259 ≤ (33979415529421/100000000000000 : ℝ)^195 := by
    have hnat : (887328521 : ℕ)^259*100000000000000^195 ≤ 33979415529421^195*2000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      887328521 2000000000 33979415529421 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (554580339/1250000000 : ℝ)^259 ≤ (271835332943/800000000000 : ℝ)^195 := by
    have hnat : (554580339 : ℕ)^259*800000000000^195 ≤ 271835332943^195*1250000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      554580339 1250000000 271835332943 800000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530591049/1250000000 : ℝ), (887328521/2000000000 : ℝ), (554580339/1250000000 : ℝ)] ![(32041167843899/100000000000000 : ℝ), (33979415529421/100000000000000 : ℝ), (271835332943/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530591049/1250000000 : ℝ)|^259 ≤ (32041167843899/100000000000000 : ℝ)^195
        have hw : |(530591049/1250000000 : ℝ)|=(530591049/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(887328521/2000000000 : ℝ)|^259 ≤ (33979415529421/100000000000000 : ℝ)^195
        have hw : |(887328521/2000000000 : ℝ)|=(887328521/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(554580339/1250000000 : ℝ)|^259 ≤ (271835332943/800000000000 : ℝ)^195
        have hw : |(554580339/1250000000 : ℝ)|=(554580339/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1095_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18569689/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (701/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2823/25000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31113/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59263/100000 : ℝ) ∧ (79663/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (41509/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (701/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2823/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (701/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2823/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (701/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2823/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (701/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2823/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (701/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2823/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (701/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2823/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2823/25000 : ℝ) ^ (8287/2048 : ℝ) ≤ (14694155337683443/100000000000000000000 : ℝ) := by
    have hpowers : (2823/25000 : ℝ)^8287 ≤ (14694155337683443/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2823 : ℕ)^8287*100000000000000000000^2048 ≤ 14694155337683443^2048*25000^8287 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2823 25000 14694155337683443 100000000000000000000 8287 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2823/25000 : ℝ)) (X := (14694155337683443/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8287 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (701/5000 : ℝ) ^ (8287/2048 : ℝ) ≤ (4408821415931623/12500000000000000000 : ℝ) := by
    have hpowers : (701/5000 : ℝ)^8287 ≤ (4408821415931623/12500000000000000000 : ℝ)^2048 := by
      have hnat : (701 : ℕ)^8287*12500000000000000000^2048 ≤ 4408821415931623^2048*5000^8287 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        701 5000 4408821415931623 12500000000000000000 8287 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (701/5000 : ℝ)) (X := (4408821415931623/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8287 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014694155337683443/50000000000000000000 : ℝ) ≤ (5000363102468039/5000000000000000 : ℝ) ^ (8287/2048 : ℝ) := by
    have hpowers : (50014694155337683443/50000000000000000000 : ℝ)^2048 ≤ (5000363102468039/5000000000000000 : ℝ)^8287 := by
      have hnat : (50014694155337683443 : ℕ)^2048*5000000000000000^8287 ≤ 5000363102468039^8287*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014694155337683443 50000000000000000000 5000363102468039 5000000000000000 2048 8287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000363102468039/5000000000000000 : ℝ)) (X := (50014694155337683443/50000000000000000000 : ℝ)) (by norm_num) 8287 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100049964726665136427/100000000000000000000 : ℝ) ≤ (5000617283212519/5000000000000000 : ℝ) ^ (8287/2048 : ℝ) := by
    have hpowers : (100049964726665136427/100000000000000000000 : ℝ)^2048 ≤ (5000617283212519/5000000000000000 : ℝ)^8287 := by
      have hnat : (100049964726665136427 : ℕ)^2048*5000000000000000^8287 ≤ 5000617283212519^8287*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100049964726665136427 100000000000000000000 5000617283212519 5000000000000000 2048 8287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000617283212519/5000000000000000 : ℝ)) (X := (100049964726665136427/100000000000000000000 : ℝ)) (by norm_num) 8287 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254408821415931623/6250000000000000000 : ℝ) ≤ (5000871463956999/5000000000000000 : ℝ) ^ (8287/2048 : ℝ) := by
    have hpowers : (6254408821415931623/6250000000000000000 : ℝ)^2048 ≤ (5000871463956999/5000000000000000 : ℝ)^8287 := by
      have hnat : (6254408821415931623 : ℕ)^2048*5000000000000000^8287 ≤ 5000871463956999^8287*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254408821415931623 6250000000000000000 5000871463956999 5000000000000000 2048 8287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000871463956999/5000000000000000 : ℝ)) (X := (6254408821415931623/6250000000000000000 : ℝ)) (by norm_num) 8287 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14694155337683443/100000000000000000000 : ℝ) ≤ ((1704406265699934259/1705000000000000000 : ℝ)+2*(1588629653/852500000000 : ℝ)*(2823/25000 : ℝ))^(8287/2048 : ℝ) := by
    rw [show (1704406265699934259/1705000000000000000 : ℝ)+2*(1588629653/852500000000 : ℝ)*(2823/25000 : ℝ)=(5000363102468039/5000000000000000 : ℝ) by norm_num, show 1+2*(14694155337683443/100000000000000000000 : ℝ)=(50014694155337683443/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4408821415931623/12500000000000000000 : ℝ)+(14694155337683443/100000000000000000000 : ℝ) ≤ ((1704406265699934259/1705000000000000000 : ℝ)+(1588629653/852500000000 : ℝ)*((701/5000 : ℝ)+(2823/25000 : ℝ)))^(8287/2048 : ℝ) := by
    rw [show (1704406265699934259/1705000000000000000 : ℝ)+(1588629653/852500000000 : ℝ)*((701/5000 : ℝ)+(2823/25000 : ℝ))=(5000617283212519/5000000000000000 : ℝ) by norm_num, show 1+(4408821415931623/12500000000000000000 : ℝ)+(14694155337683443/100000000000000000000 : ℝ)=(100049964726665136427/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4408821415931623/12500000000000000000 : ℝ) ≤ ((1704406265699934259/1705000000000000000 : ℝ)+2*(1588629653/852500000000 : ℝ)*(701/5000 : ℝ))^(8287/2048 : ℝ) := by
    rw [show (1704406265699934259/1705000000000000000 : ℝ)+2*(1588629653/852500000000 : ℝ)*(701/5000 : ℝ)=(5000871463956999/5000000000000000 : ℝ) by norm_num, show 1+2*(4408821415931623/12500000000000000000 : ℝ)=(6254408821415931623/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1704406265699934259/1705000000000000000 : ℝ)*(X 1 0+X 2 0)+(1588629653/852500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8287/2048 : ℝ)) (lo := (2823/25000 : ℝ)) (hi := (701/5000 : ℝ)) (c := (1704406265699934259/1705000000000000000 : ℝ)) (alpha := (1588629653/852500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1704406265699934259/1705000000000000000 : ℝ)*(X 0 1+X 2 1)+(1588629653/852500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8287/2048 : ℝ)) (lo := (2823/25000 : ℝ)) (hi := (701/5000 : ℝ)) (c := (1704406265699934259/1705000000000000000 : ℝ)) (alpha := (1588629653/852500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1704406265699934259/1705000000000000000 : ℝ)*(X 0 2+X 1 2)+(1588629653/852500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8287/2048 : ℝ)) (lo := (2823/25000 : ℝ)) (hi := (701/5000 : ℝ)) (c := (1704406265699934259/1705000000000000000 : ℝ)) (alpha := (1588629653/852500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-412222023/2000000000 : ℝ)*X 0 0+(215078687/400000000 : ℝ)*X 0 1+(5376967523/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5295521009/10000000000 : ℝ)*X 1 0+(-1085721959/5000000000 : ℝ)*X 1 1+(2688483751/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1323880407/2500000000 : ℝ)*X 2 0+(336060451/625000000 : ℝ)*X 2 1+(-1085721737/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4479391019/10000000000 : ℝ)*X 0 0+(107986359/250000000 : ℝ)*X 0 1+(4319454637/10000000000 : ℝ)*X 0 2+(4479391019/10000000000 : ℝ)*X 1 0+(107986359/250000000 : ℝ)*X 1 1+(4319454637/10000000000 : ℝ)*X 1 2+(4479391019/10000000000 : ℝ)*X 2 0+(107986359/250000000 : ℝ)*X 2 1+(4319454637/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-463883091/2000000000 : ℝ)*X 0 0+(2640256603/5000000000 : ℝ)*X 0 1+(41254013/78125000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5363738397/10000000000 : ℝ)*X 1 0+(-552310671/2500000000 : ℝ)*X 1 1+(2640256747/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1340934579/2500000000 : ℝ)*X 2 0+(2640256573/5000000000 : ℝ)*X 2 1+(-441848651/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1065736601/2500000000 : ℝ)*X 0 0+(4427655473/10000000000 : ℝ)*X 0 1+(4427655713/10000000000 : ℝ)*X 0 2+(1065736601/2500000000 : ℝ)*X 1 0+(4427655473/10000000000 : ℝ)*X 1 1+(4427655713/10000000000 : ℝ)*X 1 2+(1065736601/2500000000 : ℝ)*X 2 0+(4427655473/10000000000 : ℝ)*X 2 1+(4427655713/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-566363927/2500000000 : ℝ)*X 0 0+(651875871/1250000000 : ℝ)*X 0 1+(107731423/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1322181443/2500000000 : ℝ)*X 1 0+(-2167609329/10000000000 : ℝ)*X 1 1+(168330353/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2644362779/5000000000 : ℝ)*X 2 0+(5386570473/10000000000 : ℝ)*X 2 1+(-541902681/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((140645911/312500000 : ℝ)*X 0 0+(861734899/2000000000 : ℝ)*X 0 1+(538584417/1250000000 : ℝ)*X 0 2+(140645911/312500000 : ℝ)*X 1 0+(861734899/2000000000 : ℝ)*X 1 1+(538584417/1250000000 : ℝ)*X 1 2+(140645911/312500000 : ℝ)*X 2 0+(861734899/2000000000 : ℝ)*X 2 1+(538584417/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-105770943/500000000 : ℝ)*X 0 0+(544116103/1000000000 : ℝ)*X 0 1+(5272497821/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2684702501/5000000000 : ℝ)*X 1 0+(-1106162999/5000000000 : ℝ)*X 1 1+(5272497811/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1342351251/2500000000 : ℝ)*X 2 0+(2636248899/5000000000 : ℝ)*X 2 1+(-1106163007/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((530591049/1250000000 : ℝ)*X 0 0+(887328521/2000000000 : ℝ)*X 0 1+(554580339/1250000000 : ℝ)*X 0 2+(530591049/1250000000 : ℝ)*X 1 0+(887328521/2000000000 : ℝ)*X 1 1+(554580339/1250000000 : ℝ)*X 1 2+(530591049/1250000000 : ℝ)*X 2 0+(887328521/2000000000 : ℝ)*X 2 1+(554580339/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31113/50000 : ℝ) ≤ (-212183481425181984848370333/341000000000000000000000000 : ℝ) := by norm_num
    linear_combination (102198261/100000000000000 : ℝ)*(upper1) + (19293847/6250000000000 : ℝ)*(lower4) + (540487/3125000000000 : ℝ)*(upper5) + (3881328354273053/100000000000000 : ℝ)*(major0) + (3881328354273053/100000000000000 : ℝ)*(major1) + (3881328354273053/100000000000000 : ℝ)*(major2) + (18041068193/50000000000000 : ℝ)*(sp2) + (5566445183/50000000000000 : ℝ)*(sp3) + (5170702077062843/100000000000000 : ℝ)*(sp4) + (517068424164383/10000000000000 : ℝ)*(sp5) + (1034136930215191/20000000000000 : ℝ)*(sp6) + (1306333070362713/50000000000000 : ℝ)*(sp7) + (9328074749/50000000000000 : ℝ)*(sp12) + (36491568511/100000000000000 : ℝ)*(sp13) + (163292329600987/6250000000000 : ℝ)*(f.failure) + (5170720733212341/100000000000000 : ℝ)*(f.sum) + (1599056667761/341000000000000000000000000 : ℝ)*base66 + (536951289605222727/170500000000000000000000000000000 : ℝ)*base67 + (1289699886491777273/170500000000000000000000000000000 : ℝ)*base70 + (373031952958222727/170500000000000000000000000000000 : ℝ)*base71 + (1617400767/5328125000000000000000000 : ℝ)*base74 + (2203143548177277273/170500000000000000000000000000000 : ℝ)*base76 + (1087373133610222727/170500000000000000000000000000000 : ℝ)*base77 + (87020434858777273/170500000000000000000000000000000 : ℝ)*base80 + (2284325895459/341000000000000000000000000 : ℝ)*base82 + (26793/78125000000000000000 : ℝ)*base89 + (26793/78125000000000000000 : ℝ)*base91 + (26793/78125000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (59263/100000 : ℝ) ≤ (202094019507421787791187067/341000000000000000000000000 : ℝ) := by norm_num
    linear_combination (24912993/20000000000000 : ℝ)*(lower1) + (30860751/20000000000000 : ℝ)*(lower2) + (24464739/12500000000000 : ℝ)*(lower3) + (28200749/20000000000000 : ℝ)*(upper4) + (394470520805083/10000000000000 : ℝ)*(major0) + (394470520805083/10000000000000 : ℝ)*(major1) + (394470520805083/10000000000000 : ℝ)*(major2) + (1042863322512303/20000000000000 : ℝ)*(sp0) + (1042862074189209/20000000000000 : ℝ)*(sp1) + (1303578599024359/25000000000000 : ℝ)*(sp2) + (265533415990653/10000000000000 : ℝ)*(sp3) + (624161547/10000000000000 : ℝ)*(sp5) + (2216464079/100000000000000 : ℝ)*(sp6) + (4607513611/100000000000000 : ℝ)*(sp7) + (1327669383710071/50000000000000 : ℝ)*(f.failure) + (1042863322512303/20000000000000 : ℝ)*(f.sum) + (2494055566971/341000000000000000000000000 : ℝ)*base65 + (47157231278638497/17050000000000000000000000000000 : ℝ)*base67 + (164303393244861503/17050000000000000000000000000000 : ℝ)*base70 + (926641652802588497/17050000000000000000000000000000 : ℝ)*base71 + (1478471183487/341000000000000000000000000 : ℝ)*base73 + (39154763691111503/17050000000000000000000000000000 : ℝ)*base76 + (1075917262195261503/17050000000000000000000000000000 : ℝ)*base78 + (52499497804388497/17050000000000000000000000000000 : ℝ)*base79 + (2082577466379/85250000000000000000000000 : ℝ)*base81 + (2862081/625000000000000000000 : ℝ)*base90 + (2862081/625000000000000000000 : ℝ)*base92 + (2862081/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (79663/100000 : ℝ) ≤ (33957477279878449521613135356639/42625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (27793983/10000000000000 : ℝ)*(upper0) + (8541531/1562500000000 : ℝ)*(upper2) + (191062267/100000000000000 : ℝ)*(lower3) + (794211413/100000000000000 : ℝ)*(lower5) + (2206430818582869/50000000000000 : ℝ)*(major0) + (2206430818582869/50000000000000 : ℝ)*(major1) + (2206430818582869/50000000000000 : ℝ)*(major2) + (310455634221/50000000000000 : ℝ)*(sp1) + (30527688217/10000000000000 : ℝ)*(sp3) + (7546595643/25000000000000 : ℝ)*(sp4) + (5828664301317347/100000000000000 : ℝ)*(sp8) + (5828073576431477/100000000000000 : ℝ)*(sp9) + (5828694487699919/100000000000000 : ℝ)*(sp10) + (2970168297800299/100000000000000 : ℝ)*(sp11) + (297047357468247/10000000000000 : ℝ)*(f.failure) + (5828694487699919/100000000000000 : ℝ)*(f.sum) + (3197168829/34100000000000000000000000 : ℝ)*base65 + (12854980280640929/85250000000000000000000000000000 : ℝ)*base68 + (601190436915390929/85250000000000000000000000000000 : ℝ)*base70 + (961872981467390929/85250000000000000000000000000000 : ℝ)*base72 + (2304998123661/85250000000000000000000000 : ℝ)*base74 + (416117223749890929/85250000000000000000000000000000 : ℝ)*base76 + (501370092412390929/85250000000000000000000000000000 : ℝ)*base78 + (3966014439785390929/85250000000000000000000000000000 : ℝ)*base80 + (547839169797/170500000000000000000000000 : ℝ)*base81 + (1665183/125000000000000000000 : ℝ)*base89 + (1665183/125000000000000000000 : ℝ)*base91 + (1665183/125000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-41509/50000 : ℝ) ≤ (-3538552861247349245947179358773/4262500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (147377/781250000000 : ℝ)*(lower1) + (644103/20000000000000 : ℝ)*(lower3) + (13559653/100000000000000 : ℝ)*(lower4) + (8483169/100000000000000 : ℝ)*(upper5) + (444757127864851/10000000000000 : ℝ)*(major0) + (444757127864851/10000000000000 : ℝ)*(major1) + (444757127864851/10000000000000 : ℝ)*(major2) + (26913132379/100000000000000 : ℝ)*(sp5) + (52934019391/100000000000000 : ℝ)*(sp6) + (4173016033/50000000000000 : ℝ)*(sp7) + (1482244125757199/25000000000000 : ℝ)*(sp12) + (5928949589896417/100000000000000 : ℝ)*(sp13) + (1185784713801881/20000000000000 : ℝ)*(sp14) + (2993829675870529/100000000000000 : ℝ)*(sp15) + (598767604380519/20000000000000 : ℝ)*(f.failure) + (1482244125757199/25000000000000 : ℝ)*(f.sum) + (107153103857/21312500000000000000000000 : ℝ)*base66 + (24149398454680409/17050000000000000000000000000000 : ℝ)*base67 + (915385328692269591/17050000000000000000000000000000 : ℝ)*base70 + (254859856666619591/17050000000000000000000000000000 : ℝ)*base72 + (1030408227361/341000000000000000000000000 : ℝ)*base74 + (278683971536119591/17050000000000000000000000000000 : ℝ)*base76 + (272520483303569591/17050000000000000000000000000000 : ℝ)*base78 + (8845495497119591/17050000000000000000000000000000 : ℝ)*base80 + (19036371895369/341000000000000000000000000 : ℝ)*base81 + (488591/250000000000000000000 : ℝ)*base89 + (488591/250000000000000000000 : ℝ)*base91 + (488591/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1095_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18569689/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (701/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2823/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31113/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(59263/100000 : ℝ) else (79663/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41509/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1095_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1095_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18569689/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14021/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11291/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31113/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(59263/100000 : ℝ) else (79663/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41509/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1095_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1095_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18569689/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14021/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11291/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31113/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(59263/100000 : ℝ) else (79663/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41509/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1095_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
