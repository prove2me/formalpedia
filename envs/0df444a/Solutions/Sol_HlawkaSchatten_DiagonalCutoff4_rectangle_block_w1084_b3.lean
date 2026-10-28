-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1084_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:54:19.6538+00:00
-- url     : https://prove2.me/submissions/9d25d679-2c50-4019-808b-20f8b876d1f5

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
theorem support_rectangle_w1084_s9_0 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2194938569/10000000000 : ℝ)*x 0 + (5394015267/10000000000 : ℝ)*x 1 + (5264803263/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2194938569/10000000000 : ℝ)^8277 ≤ (13331901932599/100000000000000 : ℝ)^6229 := by
    have hnat : (2194938569 : ℕ)^8277*100000000000000^6229 ≤ 13331901932599^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2194938569 10000000000 13331901932599 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394015267/10000000000 : ℝ)^8277 ≤ (22016029317301/50000000000000 : ℝ)^6229 := by
    have hnat : (5394015267 : ℕ)^8277*50000000000000^6229 ≤ 22016029317301^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394015267 10000000000 22016029317301 50000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264803263/10000000000 : ℝ)^8277 ≤ (42636039421867/100000000000000 : ℝ)^6229 := by
    have hnat : (5264803263 : ℕ)^8277*100000000000000^6229 ≤ 42636039421867^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264803263 10000000000 42636039421867 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2194938569/10000000000 : ℝ), (5394015267/10000000000 : ℝ), (5264803263/10000000000 : ℝ)] ![(13331901932599/100000000000000 : ℝ), (22016029317301/50000000000000 : ℝ), (42636039421867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2194938569/10000000000 : ℝ)|^8277 ≤ (13331901932599/100000000000000 : ℝ)^6229
        have hw : |(-2194938569/10000000000 : ℝ)|=(2194938569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394015267/10000000000 : ℝ)|^8277 ≤ (22016029317301/50000000000000 : ℝ)^6229
        have hw : |(5394015267/10000000000 : ℝ)|=(5394015267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264803263/10000000000 : ℝ)|^8277 ≤ (42636039421867/100000000000000 : ℝ)^6229
        have hw : |(5264803263/10000000000 : ℝ)|=(5264803263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s9_1 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672463971/5000000000 : ℝ)*x 0 + (-70640357/312500000 : ℝ)*x 1 + (1052960659/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672463971/5000000000 : ℝ)^8277 ≤ (43500404399511/100000000000000 : ℝ)^6229 := by
    have hnat : (2672463971 : ℕ)^8277*100000000000000^6229 ≤ 43500404399511^6229*5000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672463971 5000000000 43500404399511 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (70640357/312500000 : ℝ)^8277 ≤ (1732944476941/12500000000000 : ℝ)^6229 := by
    have hnat : (70640357 : ℕ)^8277*12500000000000^6229 ≤ 1732944476941^6229*312500000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70640357 312500000 1732944476941 12500000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052960659/2000000000 : ℝ)^8277 ≤ (5329504970777/12500000000000 : ℝ)^6229 := by
    have hnat : (1052960659 : ℕ)^8277*12500000000000^6229 ≤ 5329504970777^6229*2000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052960659 2000000000 5329504970777 12500000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672463971/5000000000 : ℝ), (-70640357/312500000 : ℝ), (1052960659/2000000000 : ℝ)] ![(43500404399511/100000000000000 : ℝ), (1732944476941/12500000000000 : ℝ), (5329504970777/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672463971/5000000000 : ℝ)|^8277 ≤ (43500404399511/100000000000000 : ℝ)^6229
        have hw : |(2672463971/5000000000 : ℝ)|=(2672463971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-70640357/312500000 : ℝ)|^8277 ≤ (1732944476941/12500000000000 : ℝ)^6229
        have hw : |(-70640357/312500000 : ℝ)|=(70640357/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052960659/2000000000 : ℝ)|^8277 ≤ (5329504970777/12500000000000 : ℝ)^6229
        have hw : |(1052960659/2000000000 : ℝ)|=(1052960659/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s9_2 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344927859/10000000000 : ℝ)*x 0 + (10282819/19531250 : ℝ)*x 1 + (-565122873/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344927859/10000000000 : ℝ)^8277 ≤ (10875100875477/25000000000000 : ℝ)^6229 := by
    have hnat : (5344927859 : ℕ)^8277*25000000000000^6229 ≤ 10875100875477^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344927859 10000000000 10875100875477 25000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (10282819/19531250 : ℝ)^8277 ≤ (21318020060663/50000000000000 : ℝ)^6229 := by
    have hnat : (10282819 : ℕ)^8277*50000000000000^6229 ≤ 21318020060663^6229*19531250^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10282819 19531250 21318020060663 50000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (565122873/2500000000 : ℝ)^8277 ≤ (1732944546211/12500000000000 : ℝ)^6229 := by
    have hnat : (565122873 : ℕ)^8277*12500000000000^6229 ≤ 1732944546211^6229*2500000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565122873 2500000000 1732944546211 12500000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344927859/10000000000 : ℝ), (10282819/19531250 : ℝ), (-565122873/2500000000 : ℝ)] ![(10875100875477/25000000000000 : ℝ), (21318020060663/50000000000000 : ℝ), (1732944546211/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344927859/10000000000 : ℝ)|^8277 ≤ (10875100875477/25000000000000 : ℝ)^6229
        have hw : |(5344927859/10000000000 : ℝ)|=(5344927859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(10282819/19531250 : ℝ)|^8277 ≤ (21318020060663/50000000000000 : ℝ)^6229
        have hw : |(10282819/19531250 : ℝ)|=(10282819/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-565122873/2500000000 : ℝ)|^8277 ≤ (1732944546211/12500000000000 : ℝ)^6229
        have hw : |(-565122873/2500000000 : ℝ)|=(565122873/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s9_3 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4372911159/10000000000 : ℝ)*x 0 + (4247702241/10000000000 : ℝ)*x 1 + (1125461259/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4372911159/10000000000 : ℝ)^8277 ≤ (8329166509683/25000000000000 : ℝ)^6229 := by
    have hnat : (4372911159 : ℕ)^8277*25000000000000^6229 ≤ 8329166509683^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4372911159 10000000000 8329166509683 25000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4247702241/10000000000 : ℝ)^8277 ≤ (32055075595873/100000000000000 : ℝ)^6229 := by
    have hnat : (4247702241 : ℕ)^8277*100000000000000^6229 ≤ 32055075595873^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4247702241 10000000000 32055075595873 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1125461259/2500000000 : ℝ)^8277 ≤ (8657064585621/25000000000000 : ℝ)^6229 := by
    have hnat : (1125461259 : ℕ)^8277*25000000000000^6229 ≤ 8657064585621^6229*2500000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125461259 2500000000 8657064585621 25000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4372911159/10000000000 : ℝ), (4247702241/10000000000 : ℝ), (1125461259/2500000000 : ℝ)] ![(8329166509683/25000000000000 : ℝ), (32055075595873/100000000000000 : ℝ), (8657064585621/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4372911159/10000000000 : ℝ)|^8277 ≤ (8329166509683/25000000000000 : ℝ)^6229
        have hw : |(4372911159/10000000000 : ℝ)|=(4372911159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4247702241/10000000000 : ℝ)|^8277 ≤ (32055075595873/100000000000000 : ℝ)^6229
        have hw : |(4247702241/10000000000 : ℝ)|=(4247702241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1125461259/2500000000 : ℝ)|^8277 ≤ (8657064585621/25000000000000 : ℝ)^6229
        have hw : |(1125461259/2500000000 : ℝ)|=(1125461259/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s9_4 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2194943103/10000000000 : ℝ)*x 0 + (526512663/1000000000 : ℝ)*x 1 + (5393691087/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2194943103/10000000000 : ℝ)^8277 ≤ (6665969263137/50000000000000 : ℝ)^6229 := by
    have hnat : (2194943103 : ℕ)^8277*50000000000000^6229 ≤ 6665969263137^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2194943103 10000000000 6665969263137 50000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526512663/1000000000 : ℝ)^8277 ≤ (5329939897857/12500000000000 : ℝ)^6229 := by
    have hnat : (526512663 : ℕ)^8277*12500000000000^6229 ≤ 5329939897857^6229*1000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526512663 1000000000 5329939897857 12500000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393691087/10000000000 : ℝ)^8277 ≤ (44028542274283/100000000000000 : ℝ)^6229 := by
    have hnat : (5393691087 : ℕ)^8277*100000000000000^6229 ≤ 44028542274283^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393691087 10000000000 44028542274283 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2194943103/10000000000 : ℝ), (526512663/1000000000 : ℝ), (5393691087/10000000000 : ℝ)] ![(6665969263137/50000000000000 : ℝ), (5329939897857/12500000000000 : ℝ), (44028542274283/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2194943103/10000000000 : ℝ)|^8277 ≤ (6665969263137/50000000000000 : ℝ)^6229
        have hw : |(-2194943103/10000000000 : ℝ)|=(2194943103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526512663/1000000000 : ℝ)|^8277 ≤ (5329939897857/12500000000000 : ℝ)^6229
        have hw : |(526512663/1000000000 : ℝ)|=(526512663/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393691087/10000000000 : ℝ)|^8277 ≤ (44028542274283/100000000000000 : ℝ)^6229
        have hw : |(5393691087/10000000000 : ℝ)|=(5393691087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s9_5 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (874584231/2000000000 : ℝ)*x 0 + (4501208319/10000000000 : ℝ)*x 1 + (2124170559/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (874584231/2000000000 : ℝ)^8277 ≤ (4164595904591/12500000000000 : ℝ)^6229 := by
    have hnat : (874584231 : ℕ)^8277*12500000000000^6229 ≤ 4164595904591^6229*2000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      874584231 2000000000 4164595904591 12500000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4501208319/10000000000 : ℝ)^8277 ≤ (6924350117843/20000000000000 : ℝ)^6229 := by
    have hnat : (4501208319 : ℕ)^8277*20000000000000^6229 ≤ 6924350117843^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4501208319 10000000000 6924350117843 20000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2124170559/5000000000 : ℝ)^8277 ≤ (16030741081311/50000000000000 : ℝ)^6229 := by
    have hnat : (2124170559 : ℕ)^8277*50000000000000^6229 ≤ 16030741081311^6229*5000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124170559 5000000000 16030741081311 50000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(874584231/2000000000 : ℝ), (4501208319/10000000000 : ℝ), (2124170559/5000000000 : ℝ)] ![(4164595904591/12500000000000 : ℝ), (6924350117843/20000000000000 : ℝ), (16030741081311/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(874584231/2000000000 : ℝ)|^8277 ≤ (4164595904591/12500000000000 : ℝ)^6229
        have hw : |(874584231/2000000000 : ℝ)|=(874584231/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4501208319/10000000000 : ℝ)|^8277 ≤ (6924350117843/20000000000000 : ℝ)^6229
        have hw : |(4501208319/10000000000 : ℝ)|=(4501208319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2124170559/5000000000 : ℝ)|^8277 ≤ (16030741081311/50000000000000 : ℝ)^6229
        have hw : |(2124170559/5000000000 : ℝ)|=(2124170559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1084_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5933733/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7007/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2819/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11277/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7007/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7007/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2819/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7007/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2819/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7007/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2819/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7007/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2819/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7007/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2819/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7007/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2819/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2819/25000 : ℝ) ^ (2069/512 : ℝ) ≤ (923897589091731/6250000000000000000 : ℝ) := by
    have hpowers : (2819/25000 : ℝ)^2069 ≤ (923897589091731/6250000000000000000 : ℝ)^512 := by
      have hnat : (2819 : ℕ)^2069*6250000000000000000^512 ≤ 923897589091731^512*25000^2069 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2819 25000 923897589091731 6250000000000000000 2069 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2819/25000 : ℝ)) (X := (923897589091731/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 2069 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7007/50000 : ℝ) ^ (2069/512 : ℝ) ≤ (35583131394105441/100000000000000000000 : ℝ) := by
    have hpowers : (7007/50000 : ℝ)^2069 ≤ (35583131394105441/100000000000000000000 : ℝ)^512 := by
      have hnat : (7007 : ℕ)^2069*100000000000000000000^512 ≤ 35583131394105441^512*50000^2069 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7007 50000 35583131394105441 100000000000000000000 2069 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7007/50000 : ℝ)) (X := (35583131394105441/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2069 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125923897589091731/3125000000000000000 : ℝ) ≤ (5000365767387451/5000000000000000 : ℝ) ^ (2069/512 : ℝ) := by
    have hpowers : (3125923897589091731/3125000000000000000 : ℝ)^512 ≤ (5000365767387451/5000000000000000 : ℝ)^2069 := by
      have hnat : (3125923897589091731 : ℕ)^512*5000000000000000^2069 ≤ 5000365767387451^2069*3125000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125923897589091731 3125000000000000000 5000365767387451 5000000000000000 512 2069 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000365767387451/5000000000000000 : ℝ)) (X := (3125923897589091731/3125000000000000000 : ℝ)) (by norm_num) 2069 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100050365492819573137/100000000000000000000 : ℝ) ≤ (10001246121162487/10000000000000000 : ℝ) ^ (2069/512 : ℝ) := by
    have hpowers : (100050365492819573137/100000000000000000000 : ℝ)^512 ≤ (10001246121162487/10000000000000000 : ℝ)^2069 := by
      have hnat : (100050365492819573137 : ℕ)^512*10000000000000000^2069 ≤ 10001246121162487^2069*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100050365492819573137 100000000000000000000 10001246121162487 10000000000000000 512 2069 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001246121162487/10000000000000000 : ℝ)) (X := (100050365492819573137/100000000000000000000 : ℝ)) (by norm_num) 2069 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035583131394105441/50000000000000000000 : ℝ) ≤ (1250220088443759/1250000000000000 : ℝ) ^ (2069/512 : ℝ) := by
    have hpowers : (50035583131394105441/50000000000000000000 : ℝ)^512 ≤ (1250220088443759/1250000000000000 : ℝ)^2069 := by
      have hnat : (50035583131394105441 : ℕ)^512*1250000000000000^2069 ≤ 1250220088443759^2069*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035583131394105441 50000000000000000000 1250220088443759 1250000000000000 512 2069 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250220088443759/1250000000000000 : ℝ)) (X := (50035583131394105441/50000000000000000000 : ℝ)) (by norm_num) 2069 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(923897589091731/6250000000000000000 : ℝ) ≤ ((184935121554059897/185000000000000000 : ℝ)+2*(2781548041/1480000000000 : ℝ)*(2819/25000 : ℝ))^(2069/512 : ℝ) := by
    rw [show (184935121554059897/185000000000000000 : ℝ)+2*(2781548041/1480000000000 : ℝ)*(2819/25000 : ℝ)=(5000365767387451/5000000000000000 : ℝ) by norm_num, show 1+2*(923897589091731/6250000000000000000 : ℝ)=(3125923897589091731/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35583131394105441/100000000000000000000 : ℝ)+(923897589091731/6250000000000000000 : ℝ) ≤ ((184935121554059897/185000000000000000 : ℝ)+(2781548041/1480000000000 : ℝ)*((7007/50000 : ℝ)+(2819/25000 : ℝ)))^(2069/512 : ℝ) := by
    rw [show (184935121554059897/185000000000000000 : ℝ)+(2781548041/1480000000000 : ℝ)*((7007/50000 : ℝ)+(2819/25000 : ℝ))=(10001246121162487/10000000000000000 : ℝ) by norm_num, show 1+(35583131394105441/100000000000000000000 : ℝ)+(923897589091731/6250000000000000000 : ℝ)=(100050365492819573137/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35583131394105441/100000000000000000000 : ℝ) ≤ ((184935121554059897/185000000000000000 : ℝ)+2*(2781548041/1480000000000 : ℝ)*(7007/50000 : ℝ))^(2069/512 : ℝ) := by
    rw [show (184935121554059897/185000000000000000 : ℝ)+2*(2781548041/1480000000000 : ℝ)*(7007/50000 : ℝ)=(1250220088443759/1250000000000000 : ℝ) by norm_num, show 1+2*(35583131394105441/100000000000000000000 : ℝ)=(50035583131394105441/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (184935121554059897/185000000000000000 : ℝ)*(X 1 0+X 2 0)+(2781548041/1480000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2069/512 : ℝ)) (lo := (2819/25000 : ℝ)) (hi := (7007/50000 : ℝ)) (c := (184935121554059897/185000000000000000 : ℝ)) (alpha := (2781548041/1480000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (184935121554059897/185000000000000000 : ℝ)*(X 0 1+X 2 1)+(2781548041/1480000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2069/512 : ℝ)) (lo := (2819/25000 : ℝ)) (hi := (7007/50000 : ℝ)) (c := (184935121554059897/185000000000000000 : ℝ)) (alpha := (2781548041/1480000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (184935121554059897/185000000000000000 : ℝ)*(X 0 2+X 1 2)+(2781548041/1480000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2069/512 : ℝ)) (lo := (2819/25000 : ℝ)) (hi := (7007/50000 : ℝ)) (c := (184935121554059897/185000000000000000 : ℝ)) (alpha := (2781548041/1480000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2194938569/10000000000 : ℝ)*X 0 0+(5394015267/10000000000 : ℝ)*X 0 1+(5264803263/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672463971/5000000000 : ℝ)*X 1 0+(-70640357/312500000 : ℝ)*X 1 1+(1052960659/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s9_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344927859/10000000000 : ℝ)*X 2 0+(10282819/19531250 : ℝ)*X 2 1+(-565122873/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s9_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4372911159/10000000000 : ℝ)*X 0 0+(4247702241/10000000000 : ℝ)*X 0 1+(1125461259/2500000000 : ℝ)*X 0 2+(4372911159/10000000000 : ℝ)*X 1 0+(4247702241/10000000000 : ℝ)*X 1 1+(1125461259/2500000000 : ℝ)*X 1 2+(4372911159/10000000000 : ℝ)*X 2 0+(4247702241/10000000000 : ℝ)*X 2 1+(1125461259/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s9_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2194943103/10000000000 : ℝ)*X 0 0+(526512663/1000000000 : ℝ)*X 0 1+(5393691087/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s9_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((874584231/2000000000 : ℝ)*X 0 0+(4501208319/10000000000 : ℝ)*X 0 1+(2124170559/5000000000 : ℝ)*X 0 2+(874584231/2000000000 : ℝ)*X 1 0+(4501208319/10000000000 : ℝ)*X 1 1+(2124170559/5000000000 : ℝ)*X 1 2+(874584231/2000000000 : ℝ)*X 2 0+(4501208319/10000000000 : ℝ)*X 2 1+(2124170559/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s9_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (31731325468549102817792289/9250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (144851879/20000000000000 : ℝ)*(base19) + (588209551/100000000000000 : ℝ)*(base23) + (565233/3125000000000 : ℝ)*(lower2) + (35269473/25000000000000 : ℝ)*(upper3) + (9605661/100000000000000 : ℝ)*(lower4) + (5837040173606221/100000000000000 : ℝ)*(major0) + (5837040173606221/100000000000000 : ℝ)*(major1) + (5837040173606221/100000000000000 : ℝ)*(major2) + (967405554144381/12500000000000 : ℝ)*(sp0) + (7739261293087141/100000000000000 : ℝ)*(sp1) + (1547852285827397/20000000000000 : ℝ)*(sp2) + (1967402918454901/50000000000000 : ℝ)*(sp3) + (8586031/48828125000 : ℝ)*(sp4) + (495144359/4000000000000 : ℝ)*(sp5) + (1967409107759389/50000000000000 : ℝ)*(f.failure) + (967407752168317/12500000000000 : ℝ)*(f.sum) + (302029476103/74000000000000000000000000 : ℝ)*base65 + (15760531107055763/18500000000000000000000000000000 : ℝ)*base68 + (59863890271444237/18500000000000000000000000000000 : ℝ)*base69 + (100140287294055763/18500000000000000000000000000000 : ℝ)*base72 + (168114824359/74000000000000000000000000 : ℝ)*base73 + (288584190743944237/18500000000000000000000000000000 : ℝ)*base75 + (564343243785444237/18500000000000000000000000000000 : ℝ)*base77 + (272513076648944237/18500000000000000000000000000000 : ℝ)*base79 + (178323189287/74000000000000000000000000 : ℝ)*base82 + (569137/200000000000000000000 : ℝ)*base89 + (569137/200000000000000000000 : ℝ)*base91 + (569137/200000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1084_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5933733/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7007/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2819/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11277/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7007/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1084_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1084_box_0 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-20660909/100000000 : ℝ)*x 0 + (2688561619/5000000000 : ℝ)*x 1 + (537712333/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20660909/100000000 : ℝ)^8277 ≤ (3075537532037/25000000000000 : ℝ)^6229 := by
    have hnat : (20660909 : ℕ)^8277*25000000000000^6229 ≤ 3075537532037^6229*100000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20660909 100000000 3075537532037 25000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2688561619/5000000000 : ℝ)^8277 ≤ (43848924430223/100000000000000 : ℝ)^6229 := by
    have hnat : (2688561619 : ℕ)^8277*100000000000000^6229 ≤ 43848924430223^6229*5000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688561619 5000000000 43848924430223 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (537712333/1000000000 : ℝ)^8277 ≤ (43848925427123/100000000000000 : ℝ)^6229 := by
    have hnat : (537712333 : ℕ)^8277*100000000000000^6229 ≤ 43848925427123^6229*1000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537712333 1000000000 43848925427123 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-20660909/100000000 : ℝ), (2688561619/5000000000 : ℝ), (537712333/1000000000 : ℝ)] ![(3075537532037/25000000000000 : ℝ), (43848924430223/100000000000000 : ℝ), (43848925427123/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-20660909/100000000 : ℝ)|^8277 ≤ (3075537532037/25000000000000 : ℝ)^6229
        have hw : |(-20660909/100000000 : ℝ)|=(20660909/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2688561619/5000000000 : ℝ)|^8277 ≤ (43848924430223/100000000000000 : ℝ)^6229
        have hw : |(2688561619/5000000000 : ℝ)|=(2688561619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(537712333/1000000000 : ℝ)|^8277 ≤ (43848925427123/100000000000000 : ℝ)^6229
        have hw : |(537712333/1000000000 : ℝ)|=(537712333/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_box_1 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1059080483/2000000000 : ℝ)*x 0 + (-217676769/1000000000 : ℝ)*x 1 + (672140419/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059080483/2000000000 : ℝ)^8277 ≤ (42965628593643/100000000000000 : ℝ)^6229 := by
    have hnat : (1059080483 : ℕ)^8277*100000000000000^6229 ≤ 42965628593643^6229*2000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059080483 2000000000 42965628593643 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (217676769/1000000000 : ℝ)^8277 ≤ (6592722867401/50000000000000 : ℝ)^6229 := by
    have hnat : (217676769 : ℕ)^8277*50000000000000^6229 ≤ 6592722867401^6229*1000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217676769 1000000000 6592722867401 50000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (672140419/1250000000 : ℝ)^8277 ≤ (5481115708189/12500000000000 : ℝ)^6229 := by
    have hnat : (672140419 : ℕ)^8277*12500000000000^6229 ≤ 5481115708189^6229*1250000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672140419 1250000000 5481115708189 12500000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1059080483/2000000000 : ℝ), (-217676769/1000000000 : ℝ), (672140419/1250000000 : ℝ)] ![(42965628593643/100000000000000 : ℝ), (6592722867401/50000000000000 : ℝ), (5481115708189/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1059080483/2000000000 : ℝ)|^8277 ≤ (42965628593643/100000000000000 : ℝ)^6229
        have hw : |(1059080483/2000000000 : ℝ)|=(1059080483/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-217676769/1000000000 : ℝ)|^8277 ≤ (6592722867401/50000000000000 : ℝ)^6229
        have hw : |(-217676769/1000000000 : ℝ)|=(217676769/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(672140419/1250000000 : ℝ)|^8277 ≤ (5481115708189/12500000000000 : ℝ)^6229
        have hw : |(672140419/1250000000 : ℝ)|=(672140419/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_box_2 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (211816103/400000000 : ℝ)*x 0 + (5377123229/10000000000 : ℝ)*x 1 + (-54419191/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211816103/400000000 : ℝ)^8277 ≤ (21482815159337/50000000000000 : ℝ)^6229 := by
    have hnat : (211816103 : ℕ)^8277*50000000000000^6229 ≤ 21482815159337^6229*400000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211816103 400000000 21482815159337 50000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5377123229/10000000000 : ℝ)^8277 ≤ (43848924332701/100000000000000 : ℝ)^6229 := by
    have hnat : (5377123229 : ℕ)^8277*100000000000000^6229 ≤ 43848924332701^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377123229 10000000000 43848924332701 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (54419191/250000000 : ℝ)^8277 ≤ (3296361333089/25000000000000 : ℝ)^6229 := by
    have hnat : (54419191 : ℕ)^8277*25000000000000^6229 ≤ 3296361333089^6229*250000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54419191 250000000 3296361333089 25000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(211816103/400000000 : ℝ), (5377123229/10000000000 : ℝ), (-54419191/250000000 : ℝ)] ![(21482815159337/50000000000000 : ℝ), (43848924332701/100000000000000 : ℝ), (3296361333089/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(211816103/400000000 : ℝ)|^8277 ≤ (21482815159337/50000000000000 : ℝ)^6229
        have hw : |(211816103/400000000 : ℝ)|=(211816103/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5377123229/10000000000 : ℝ)|^8277 ≤ (43848924332701/100000000000000 : ℝ)^6229
        have hw : |(5377123229/10000000000 : ℝ)|=(5377123229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-54419191/250000000 : ℝ)|^8277 ≤ (3296361333089/25000000000000 : ℝ)^6229
        have hw : |(-54419191/250000000 : ℝ)|=(54419191/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_box_3 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2240547051/5000000000 : ℝ)*x 0 + (2160484293/5000000000 : ℝ)*x 1 + (4320968847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2240547051/5000000000 : ℝ)^8277 ≤ (8604080818197/25000000000000 : ℝ)^6229 := by
    have hnat : (2240547051 : ℕ)^8277*25000000000000^6229 ≤ 8604080818197^6229*5000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2240547051 5000000000 8604080818197 25000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2160484293/5000000000 : ℝ)^8277 ≤ (16395918521309/50000000000000 : ℝ)^6229 := by
    have hnat : (2160484293 : ℕ)^8277*50000000000000^6229 ≤ 16395918521309^6229*5000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2160484293 5000000000 16395918521309 50000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4320968847/10000000000 : ℝ)^8277 ≤ (32791839674581/100000000000000 : ℝ)^6229 := by
    have hnat : (4320968847 : ℕ)^8277*100000000000000^6229 ≤ 32791839674581^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4320968847 10000000000 32791839674581 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2240547051/5000000000 : ℝ), (2160484293/5000000000 : ℝ), (4320968847/10000000000 : ℝ)] ![(8604080818197/25000000000000 : ℝ), (16395918521309/50000000000000 : ℝ), (32791839674581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2240547051/5000000000 : ℝ)|^8277 ≤ (8604080818197/25000000000000 : ℝ)^6229
        have hw : |(2240547051/5000000000 : ℝ)|=(2240547051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2160484293/5000000000 : ℝ)|^8277 ≤ (16395918521309/50000000000000 : ℝ)^6229
        have hw : |(2160484293/5000000000 : ℝ)|=(2160484293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4320968847/10000000000 : ℝ)|^8277 ≤ (32791839674581/100000000000000 : ℝ)^6229
        have hw : |(4320968847/10000000000 : ℝ)|=(4320968847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_box_4 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-290645673/1250000000 : ℝ)*x 0 + (1320088599/2500000000 : ℝ)*x 1 + (5280354009/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (290645673/1250000000 : ℝ)^8277 ≤ (14393073955941/100000000000000 : ℝ)^6229 := by
    have hnat : (290645673 : ℕ)^8277*100000000000000^6229 ≤ 14393073955941^6229*1250000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      290645673 1250000000 14393073955941 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1320088599/2500000000 : ℝ)^8277 ≤ (2140173254927/5000000000000 : ℝ)^6229 := by
    have hnat : (1320088599 : ℕ)^8277*5000000000000^6229 ≤ 2140173254927^6229*2500000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320088599 2500000000 2140173254927 5000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5280354009/10000000000 : ℝ)^8277 ≤ (5350432616253/12500000000000 : ℝ)^6229 := by
    have hnat : (5280354009 : ℕ)^8277*12500000000000^6229 ≤ 5350432616253^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280354009 10000000000 5350432616253 12500000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-290645673/1250000000 : ℝ), (1320088599/2500000000 : ℝ), (5280354009/10000000000 : ℝ)] ![(14393073955941/100000000000000 : ℝ), (2140173254927/5000000000000 : ℝ), (5350432616253/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-290645673/1250000000 : ℝ)|^8277 ≤ (14393073955941/100000000000000 : ℝ)^6229
        have hw : |(-290645673/1250000000 : ℝ)|=(290645673/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1320088599/2500000000 : ℝ)|^8277 ≤ (2140173254927/5000000000000 : ℝ)^6229
        have hw : |(1320088599/2500000000 : ℝ)|=(1320088599/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5280354009/10000000000 : ℝ)|^8277 ≤ (5350432616253/12500000000000 : ℝ)^6229
        have hw : |(5280354009/10000000000 : ℝ)|=(5280354009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_box_5 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1340964819/2500000000 : ℝ)*x 0 + (-1107328321/5000000000 : ℝ)*x 1 + (5280354273/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1340964819/2500000000 : ℝ)^8277 ≤ (8741051249191/20000000000000 : ℝ)^6229 := by
    have hnat : (1340964819 : ℕ)^8277*20000000000000^6229 ≤ 8741051249191^6229*2500000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1340964819 2500000000 8741051249191 20000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1107328321/5000000000 : ℝ)^8277 ≤ (337281999011/2500000000000 : ℝ)^6229 := by
    have hnat : (1107328321 : ℕ)^8277*2500000000000^6229 ≤ 337281999011^6229*5000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1107328321 5000000000 337281999011 2500000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5280354273/10000000000 : ℝ)^8277 ≤ (42803463773663/100000000000000 : ℝ)^6229 := by
    have hnat : (5280354273 : ℕ)^8277*100000000000000^6229 ≤ 42803463773663^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280354273 10000000000 42803463773663 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1340964819/2500000000 : ℝ), (-1107328321/5000000000 : ℝ), (5280354273/10000000000 : ℝ)] ![(8741051249191/20000000000000 : ℝ), (337281999011/2500000000000 : ℝ), (42803463773663/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1340964819/2500000000 : ℝ)|^8277 ≤ (8741051249191/20000000000000 : ℝ)^6229
        have hw : |(1340964819/2500000000 : ℝ)|=(1340964819/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1107328321/5000000000 : ℝ)|^8277 ≤ (337281999011/2500000000000 : ℝ)^6229
        have hw : |(-1107328321/5000000000 : ℝ)|=(1107328321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5280354273/10000000000 : ℝ)|^8277 ≤ (42803463773663/100000000000000 : ℝ)^6229
        have hw : |(5280354273/10000000000 : ℝ)|=(5280354273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_box_6 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1072771861/2000000000 : ℝ)*x 0 + (660044329/1250000000 : ℝ)*x 1 + (-2214656127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072771861/2000000000 : ℝ)^8277 ≤ (2185262827997/5000000000000 : ℝ)^6229 := by
    have hnat : (1072771861 : ℕ)^8277*5000000000000^6229 ≤ 2185262827997^6229*2000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072771861 2000000000 2185262827997 5000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (660044329/1250000000 : ℝ)^8277 ≤ (42803467640581/100000000000000 : ℝ)^6229 := by
    have hnat : (660044329 : ℕ)^8277*100000000000000^6229 ≤ 42803467640581^6229*1250000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660044329 1250000000 42803467640581 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2214656127/10000000000 : ℝ)^8277 ≤ (13491275791663/100000000000000 : ℝ)^6229 := by
    have hnat : (2214656127 : ℕ)^8277*100000000000000^6229 ≤ 13491275791663^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2214656127 10000000000 13491275791663 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072771861/2000000000 : ℝ), (660044329/1250000000 : ℝ), (-2214656127/10000000000 : ℝ)] ![(2185262827997/5000000000000 : ℝ), (42803467640581/100000000000000 : ℝ), (13491275791663/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072771861/2000000000 : ℝ)|^8277 ≤ (2185262827997/5000000000000 : ℝ)^6229
        have hw : |(1072771861/2000000000 : ℝ)|=(1072771861/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(660044329/1250000000 : ℝ)|^8277 ≤ (42803467640581/100000000000000 : ℝ)^6229
        have hw : |(660044329/1250000000 : ℝ)|=(660044329/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2214656127/10000000000 : ℝ)|^8277 ≤ (13491275791663/100000000000000 : ℝ)^6229
        have hw : |(-2214656127/10000000000 : ℝ)|=(2214656127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_box_7 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2132195639/5000000000 : ℝ)*x 0 + (4429298757/10000000000 : ℝ)*x 1 + (2214649441/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2132195639/5000000000 : ℝ)^8277 ≤ (32222534718599/100000000000000 : ℝ)^6229 := by
    have hnat : (2132195639 : ℕ)^8277*100000000000000^6229 ≤ 32222534718599^6229*5000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2132195639 5000000000 32222534718599 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4429298757/10000000000 : ℝ)^8277 ≤ (33888731999077/100000000000000 : ℝ)^6229 := by
    have hnat : (4429298757 : ℕ)^8277*100000000000000^6229 ≤ 33888731999077^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4429298757 10000000000 33888731999077 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2214649441/5000000000 : ℝ)^8277 ≤ (33888733269899/100000000000000 : ℝ)^6229 := by
    have hnat : (2214649441 : ℕ)^8277*100000000000000^6229 ≤ 33888733269899^6229*5000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2214649441 5000000000 33888733269899 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2132195639/5000000000 : ℝ), (4429298757/10000000000 : ℝ), (2214649441/5000000000 : ℝ)] ![(32222534718599/100000000000000 : ℝ), (33888731999077/100000000000000 : ℝ), (33888733269899/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2132195639/5000000000 : ℝ)|^8277 ≤ (32222534718599/100000000000000 : ℝ)^6229
        have hw : |(2132195639/5000000000 : ℝ)|=(2132195639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4429298757/10000000000 : ℝ)|^8277 ≤ (33888731999077/100000000000000 : ℝ)^6229
        have hw : |(4429298757/10000000000 : ℝ)|=(4429298757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2214649441/5000000000 : ℝ)|^8277 ≤ (33888733269899/100000000000000 : ℝ)^6229
        have hw : |(2214649441/5000000000 : ℝ)|=(2214649441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_box_8 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2271058749/10000000000 : ℝ)*x 0 + (651831937/1250000000 : ℝ)*x 1 + (5386726107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2271058749/10000000000 : ℝ)^8277 ≤ (871858714811/6250000000000 : ℝ)^6229 := by
    have hnat : (2271058749 : ℕ)^8277*6250000000000^6229 ≤ 871858714811^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2271058749 10000000000 871858714811 6250000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (651831937/1250000000 : ℝ)^8277 ≤ (42097250199161/100000000000000 : ℝ)^6229 := by
    have hnat : (651831937 : ℕ)^8277*100000000000000^6229 ≤ 42097250199161^6229*1250000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      651831937 1250000000 42097250199161 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5386726107/10000000000 : ℝ)^8277 ≤ (43953010357583/100000000000000 : ℝ)^6229 := by
    have hnat : (5386726107 : ℕ)^8277*100000000000000^6229 ≤ 43953010357583^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386726107 10000000000 43953010357583 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2271058749/10000000000 : ℝ), (651831937/1250000000 : ℝ), (5386726107/10000000000 : ℝ)] ![(871858714811/6250000000000 : ℝ), (42097250199161/100000000000000 : ℝ), (43953010357583/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2271058749/10000000000 : ℝ)|^8277 ≤ (871858714811/6250000000000 : ℝ)^6229
        have hw : |(-2271058749/10000000000 : ℝ)|=(2271058749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(651831937/1250000000 : ℝ)|^8277 ≤ (42097250199161/100000000000000 : ℝ)^6229
        have hw : |(651831937/1250000000 : ℝ)|=(651831937/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5386726107/10000000000 : ℝ)|^8277 ≤ (43953010357583/100000000000000 : ℝ)^6229
        have hw : |(5386726107/10000000000 : ℝ)|=(5386726107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_box_9 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5288605513/10000000000 : ℝ)*x 0 + (-2172936707/10000000000 : ℝ)*x 1 + (5386726713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288605513/10000000000 : ℝ)^8277 ≤ (8578472732061/20000000000000 : ℝ)^6229 := by
    have hnat : (5288605513 : ℕ)^8277*20000000000000^6229 ≤ 8578472732061^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288605513 10000000000 8578472732061 20000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2172936707/10000000000 : ℝ)^8277 ≤ (13154619401901/100000000000000 : ℝ)^6229 := by
    have hnat : (2172936707 : ℕ)^8277*100000000000000^6229 ≤ 13154619401901^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2172936707 10000000000 13154619401901 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5386726713/10000000000 : ℝ)^8277 ≤ (43953016927971/100000000000000 : ℝ)^6229 := by
    have hnat : (5386726713 : ℕ)^8277*100000000000000^6229 ≤ 43953016927971^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386726713 10000000000 43953016927971 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288605513/10000000000 : ℝ), (-2172936707/10000000000 : ℝ), (5386726713/10000000000 : ℝ)] ![(8578472732061/20000000000000 : ℝ), (13154619401901/100000000000000 : ℝ), (43953016927971/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288605513/10000000000 : ℝ)|^8277 ≤ (8578472732061/20000000000000 : ℝ)^6229
        have hw : |(5288605513/10000000000 : ℝ)|=(5288605513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2172936707/10000000000 : ℝ)|^8277 ≤ (13154619401901/100000000000000 : ℝ)^6229
        have hw : |(-2172936707/10000000000 : ℝ)|=(2172936707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5386726713/10000000000 : ℝ)|^8277 ≤ (43953016927971/100000000000000 : ℝ)^6229
        have hw : |(5386726713/10000000000 : ℝ)|=(5386726713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_box_10 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5288605403/10000000000 : ℝ)*x 0 + (5386726043/10000000000 : ℝ)*x 1 + (-2172937757/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288605403/10000000000 : ℝ)^8277 ≤ (42892362474847/100000000000000 : ℝ)^6229 := by
    have hnat : (5288605403 : ℕ)^8277*100000000000000^6229 ≤ 42892362474847^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288605403 10000000000 42892362474847 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5386726043/10000000000 : ℝ)^8277 ≤ (43953009663681/100000000000000 : ℝ)^6229 := by
    have hnat : (5386726043 : ℕ)^8277*100000000000000^6229 ≤ 43953009663681^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386726043 10000000000 43953009663681 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2172937757/10000000000 : ℝ)^8277 ≤ (13154627848369/100000000000000 : ℝ)^6229 := by
    have hnat : (2172937757 : ℕ)^8277*100000000000000^6229 ≤ 13154627848369^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2172937757 10000000000 13154627848369 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288605403/10000000000 : ℝ), (5386726043/10000000000 : ℝ), (-2172937757/10000000000 : ℝ)] ![(42892362474847/100000000000000 : ℝ), (43953009663681/100000000000000 : ℝ), (13154627848369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288605403/10000000000 : ℝ)|^8277 ≤ (42892362474847/100000000000000 : ℝ)^6229
        have hw : |(5288605403/10000000000 : ℝ)|=(5288605403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5386726043/10000000000 : ℝ)|^8277 ≤ (43953009663681/100000000000000 : ℝ)^6229
        have hw : |(5386726043/10000000000 : ℝ)|=(5386726043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2172937757/10000000000 : ℝ)|^8277 ≤ (13154627848369/100000000000000 : ℝ)^6229
        have hw : |(-2172937757/10000000000 : ℝ)|=(2172937757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_box_11 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2251163171/5000000000 : ℝ)*x 0 + (4310211977/10000000000 : ℝ)*x 1 + (862042429/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2251163171/5000000000 : ℝ)^8277 ≤ (34633177872789/100000000000000 : ℝ)^6229 := by
    have hnat : (2251163171 : ℕ)^8277*100000000000000^6229 ≤ 34633177872789^6229*5000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251163171 5000000000 34633177872789 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4310211977/10000000000 : ℝ)^8277 ≤ (408542627599/1250000000000 : ℝ)^6229 := by
    have hnat : (4310211977 : ℕ)^8277*1250000000000^6229 ≤ 408542627599^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4310211977 10000000000 408542627599 1250000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (862042429/2000000000 : ℝ)^8277 ≤ (32683411900669/100000000000000 : ℝ)^6229 := by
    have hnat : (862042429 : ℕ)^8277*100000000000000^6229 ≤ 32683411900669^6229*2000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      862042429 2000000000 32683411900669 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2251163171/5000000000 : ℝ), (4310211977/10000000000 : ℝ), (862042429/2000000000 : ℝ)] ![(34633177872789/100000000000000 : ℝ), (408542627599/1250000000000 : ℝ), (32683411900669/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2251163171/5000000000 : ℝ)|^8277 ≤ (34633177872789/100000000000000 : ℝ)^6229
        have hw : |(2251163171/5000000000 : ℝ)|=(2251163171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4310211977/10000000000 : ℝ)|^8277 ≤ (408542627599/1250000000000 : ℝ)^6229
        have hw : |(4310211977/10000000000 : ℝ)|=(4310211977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(862042429/2000000000 : ℝ)|^8277 ≤ (32683411900669/100000000000000 : ℝ)^6229
        have hw : |(862042429/2000000000 : ℝ)|=(862042429/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_box_12 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2120554103/10000000000 : ℝ)*x 0 + (2720750481/5000000000 : ℝ)*x 1 + (659042939/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2120554103/10000000000 : ℝ)^8277 ≤ (636745969319/5000000000000 : ℝ)^6229 := by
    have hnat : (2120554103 : ℕ)^8277*5000000000000^6229 ≤ 636745969319^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2120554103 10000000000 636745969319 5000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2720750481/5000000000 : ℝ)^8277 ≤ (44547882073593/100000000000000 : ℝ)^6229 := by
    have hnat : (2720750481 : ℕ)^8277*100000000000000^6229 ≤ 44547882073593^6229*5000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2720750481 5000000000 44547882073593 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (659042939/1250000000 : ℝ)^8277 ≤ (10679299630677/25000000000000 : ℝ)^6229 := by
    have hnat : (659042939 : ℕ)^8277*25000000000000^6229 ≤ 10679299630677^6229*1250000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659042939 1250000000 10679299630677 25000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2120554103/10000000000 : ℝ), (2720750481/5000000000 : ℝ), (659042939/1250000000 : ℝ)] ![(636745969319/5000000000000 : ℝ), (44547882073593/100000000000000 : ℝ), (10679299630677/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2120554103/10000000000 : ℝ)|^8277 ≤ (636745969319/5000000000000 : ℝ)^6229
        have hw : |(-2120554103/10000000000 : ℝ)|=(2120554103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2720750481/5000000000 : ℝ)|^8277 ≤ (44547882073593/100000000000000 : ℝ)^6229
        have hw : |(2720750481/5000000000 : ℝ)|=(2720750481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(659042939/1250000000 : ℝ)|^8277 ≤ (10679299630677/25000000000000 : ℝ)^6229
        have hw : |(659042939/1250000000 : ℝ)|=(659042939/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_box_13 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5369524407/10000000000 : ℝ)*x 0 + (-2217734327/10000000000 : ℝ)*x 1 + (1318085859/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369524407/10000000000 : ℝ)^8277 ≤ (43766603659479/100000000000000 : ℝ)^6229 := by
    have hnat : (5369524407 : ℕ)^8277*100000000000000^6229 ≤ 43766603659479^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369524407 10000000000 43766603659479 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2217734327/10000000000 : ℝ)^8277 ≤ (13516198622353/100000000000000 : ℝ)^6229 := by
    have hnat : (2217734327 : ℕ)^8277*100000000000000^6229 ≤ 13516198622353^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2217734327 10000000000 13516198622353 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1318085859/2500000000 : ℝ)^8277 ≤ (42717197704493/100000000000000 : ℝ)^6229 := by
    have hnat : (1318085859 : ℕ)^8277*100000000000000^6229 ≤ 42717197704493^6229*2500000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318085859 2500000000 42717197704493 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369524407/10000000000 : ℝ), (-2217734327/10000000000 : ℝ), (1318085859/2500000000 : ℝ)] ![(43766603659479/100000000000000 : ℝ), (13516198622353/100000000000000 : ℝ), (42717197704493/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369524407/10000000000 : ℝ)|^8277 ≤ (43766603659479/100000000000000 : ℝ)^6229
        have hw : |(5369524407/10000000000 : ℝ)|=(5369524407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2217734327/10000000000 : ℝ)|^8277 ≤ (13516198622353/100000000000000 : ℝ)^6229
        have hw : |(-2217734327/10000000000 : ℝ)|=(2217734327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1318085859/2500000000 : ℝ)|^8277 ≤ (42717197704493/100000000000000 : ℝ)^6229
        have hw : |(1318085859/2500000000 : ℝ)|=(1318085859/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_box_14 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (268476227/500000000 : ℝ)*x 0 + (1054468681/2000000000 : ℝ)*x 1 + (-221773419/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268476227/500000000 : ℝ)^8277 ≤ (43766605099979/100000000000000 : ℝ)^6229 := by
    have hnat : (268476227 : ℕ)^8277*100000000000000^6229 ≤ 43766605099979^6229*500000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268476227 500000000 43766605099979 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1054468681/2000000000 : ℝ)^8277 ≤ (10679299342687/25000000000000 : ℝ)^6229 := by
    have hnat : (1054468681 : ℕ)^8277*25000000000000^6229 ≤ 10679299342687^6229*2000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054468681 2000000000 10679299342687 25000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (221773419/1000000000 : ℝ)^8277 ≤ (13516197512871/100000000000000 : ℝ)^6229 := by
    have hnat : (221773419 : ℕ)^8277*100000000000000^6229 ≤ 13516197512871^6229*1000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221773419 1000000000 13516197512871 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268476227/500000000 : ℝ), (1054468681/2000000000 : ℝ), (-221773419/1000000000 : ℝ)] ![(43766605099979/100000000000000 : ℝ), (10679299342687/25000000000000 : ℝ), (13516197512871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268476227/500000000 : ℝ)|^8277 ≤ (43766605099979/100000000000000 : ℝ)^6229
        have hw : |(268476227/500000000 : ℝ)|=(268476227/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1054468681/2000000000 : ℝ)|^8277 ≤ (10679299342687/25000000000000 : ℝ)^6229
        have hw : |(1054468681/2000000000 : ℝ)|=(1054468681/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-221773419/1000000000 : ℝ)|^8277 ≤ (13516197512871/100000000000000 : ℝ)^6229
        have hw : |(-221773419/1000000000 : ℝ)|=(221773419/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_box_15 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2123111229/5000000000 : ℝ)*x 0 + (4438261191/10000000000 : ℝ)*x 1 + (887652297/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2123111229/5000000000 : ℝ)^8277 ≤ (4005029720169/12500000000000 : ℝ)^6229 := by
    have hnat : (2123111229 : ℕ)^8277*12500000000000^6229 ≤ 4005029720169^6229*5000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123111229 5000000000 4005029720169 12500000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4438261191/10000000000 : ℝ)^8277 ≤ (33979879614949/100000000000000 : ℝ)^6229 := by
    have hnat : (4438261191 : ℕ)^8277*100000000000000^6229 ≤ 33979879614949^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4438261191 10000000000 33979879614949 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (887652297/2000000000 : ℝ)^8277 ≤ (4247485325739/12500000000000 : ℝ)^6229 := by
    have hnat : (887652297 : ℕ)^8277*12500000000000^6229 ≤ 4247485325739^6229*2000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      887652297 2000000000 4247485325739 12500000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2123111229/5000000000 : ℝ), (4438261191/10000000000 : ℝ), (887652297/2000000000 : ℝ)] ![(4005029720169/12500000000000 : ℝ), (33979879614949/100000000000000 : ℝ), (4247485325739/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2123111229/5000000000 : ℝ)|^8277 ≤ (4005029720169/12500000000000 : ℝ)^6229
        have hw : |(2123111229/5000000000 : ℝ)|=(2123111229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4438261191/10000000000 : ℝ)|^8277 ≤ (33979879614949/100000000000000 : ℝ)^6229
        have hw : |(4438261191/10000000000 : ℝ)|=(4438261191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(887652297/2000000000 : ℝ)|^8277 ≤ (4247485325739/12500000000000 : ℝ)^6229
        have hw : |(887652297/2000000000 : ℝ)|=(887652297/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1084_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5933733/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7007/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11277/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31113/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29627/50000 : ℝ) ∧ (79629/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (41497/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7007/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11277/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7007/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11277/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7007/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11277/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7007/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11277/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7007/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11277/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7007/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11277/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11277/100000 : ℝ) ^ (2069/512 : ℝ) ≤ (2957531948254679/20000000000000000000 : ℝ) := by
    have hpowers : (11277/100000 : ℝ)^2069 ≤ (2957531948254679/20000000000000000000 : ℝ)^512 := by
      have hnat : (11277 : ℕ)^2069*20000000000000000000^512 ≤ 2957531948254679^512*100000^2069 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11277 100000 2957531948254679 20000000000000000000 2069 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11277/100000 : ℝ)) (X := (2957531948254679/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2069 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7007/50000 : ℝ) ^ (2069/512 : ℝ) ≤ (35583131394105441/100000000000000000000 : ℝ) := by
    have hpowers : (7007/50000 : ℝ)^2069 ≤ (35583131394105441/100000000000000000000 : ℝ)^512 := by
      have hnat : (7007 : ℕ)^2069*100000000000000000000^512 ≤ 35583131394105441^512*50000^2069 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7007 50000 35583131394105441 100000000000000000000 2069 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7007/50000 : ℝ)) (X := (35583131394105441/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2069 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002957531948254679/10000000000000000000 : ℝ) ≤ (2000146359388701/2000000000000000 : ℝ) ^ (2069/512 : ℝ) := by
    have hpowers : (10002957531948254679/10000000000000000000 : ℝ)^512 ≤ (2000146359388701/2000000000000000 : ℝ)^2069 := by
      have hnat : (10002957531948254679 : ℕ)^512*2000000000000000^2069 ≤ 2000146359388701^2069*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002957531948254679 10000000000000000000 2000146359388701 2000000000000000 512 2069 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000146359388701/2000000000000000 : ℝ)) (X := (10002957531948254679/10000000000000000000 : ℝ)) (by norm_num) 2069 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (25012592697783844709/25000000000000000000 : ℝ) ≤ (5000623126113141/5000000000000000 : ℝ) ^ (2069/512 : ℝ) := by
    have hpowers : (25012592697783844709/25000000000000000000 : ℝ)^512 ≤ (5000623126113141/5000000000000000 : ℝ)^2069 := by
      have hnat : (25012592697783844709 : ℕ)^512*5000000000000000^2069 ≤ 5000623126113141^2069*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012592697783844709 25000000000000000000 5000623126113141 5000000000000000 512 2069 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000623126113141/5000000000000000 : ℝ)) (X := (25012592697783844709/25000000000000000000 : ℝ)) (by norm_num) 2069 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035583131394105441/50000000000000000000 : ℝ) ≤ (10001760707509059/10000000000000000 : ℝ) ^ (2069/512 : ℝ) := by
    have hpowers : (50035583131394105441/50000000000000000000 : ℝ)^512 ≤ (10001760707509059/10000000000000000 : ℝ)^2069 := by
      have hnat : (50035583131394105441 : ℕ)^512*10000000000000000^2069 ≤ 10001760707509059^2069*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035583131394105441 50000000000000000000 10001760707509059 10000000000000000 512 2069 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001760707509059/10000000000000000 : ℝ)) (X := (50035583131394105441/50000000000000000000 : ℝ)) (by norm_num) 2069 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2957531948254679/20000000000000000000 : ℝ) ≤ ((3908628557683802961/3910000000000000000 : ℝ)+2*(514455282777/273700000000000 : ℝ)*(11277/100000 : ℝ))^(2069/512 : ℝ) := by
    rw [show (3908628557683802961/3910000000000000000 : ℝ)+2*(514455282777/273700000000000 : ℝ)*(11277/100000 : ℝ)=(2000146359388701/2000000000000000 : ℝ) by norm_num, show 1+2*(2957531948254679/20000000000000000000 : ℝ)=(10002957531948254679/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35583131394105441/100000000000000000000 : ℝ)+(2957531948254679/20000000000000000000 : ℝ) ≤ ((3908628557683802961/3910000000000000000 : ℝ)+(514455282777/273700000000000 : ℝ)*((7007/50000 : ℝ)+(11277/100000 : ℝ)))^(2069/512 : ℝ) := by
    rw [show (3908628557683802961/3910000000000000000 : ℝ)+(514455282777/273700000000000 : ℝ)*((7007/50000 : ℝ)+(11277/100000 : ℝ))=(5000623126113141/5000000000000000 : ℝ) by norm_num, show 1+(35583131394105441/100000000000000000000 : ℝ)+(2957531948254679/20000000000000000000 : ℝ)=(25012592697783844709/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35583131394105441/100000000000000000000 : ℝ) ≤ ((3908628557683802961/3910000000000000000 : ℝ)+2*(514455282777/273700000000000 : ℝ)*(7007/50000 : ℝ))^(2069/512 : ℝ) := by
    rw [show (3908628557683802961/3910000000000000000 : ℝ)+2*(514455282777/273700000000000 : ℝ)*(7007/50000 : ℝ)=(10001760707509059/10000000000000000 : ℝ) by norm_num, show 1+2*(35583131394105441/100000000000000000000 : ℝ)=(50035583131394105441/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3908628557683802961/3910000000000000000 : ℝ)*(X 1 0+X 2 0)+(514455282777/273700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2069/512 : ℝ)) (lo := (11277/100000 : ℝ)) (hi := (7007/50000 : ℝ)) (c := (3908628557683802961/3910000000000000000 : ℝ)) (alpha := (514455282777/273700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3908628557683802961/3910000000000000000 : ℝ)*(X 0 1+X 2 1)+(514455282777/273700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2069/512 : ℝ)) (lo := (11277/100000 : ℝ)) (hi := (7007/50000 : ℝ)) (c := (3908628557683802961/3910000000000000000 : ℝ)) (alpha := (514455282777/273700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3908628557683802961/3910000000000000000 : ℝ)*(X 0 2+X 1 2)+(514455282777/273700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2069/512 : ℝ)) (lo := (11277/100000 : ℝ)) (hi := (7007/50000 : ℝ)) (c := (3908628557683802961/3910000000000000000 : ℝ)) (alpha := (514455282777/273700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-20660909/100000000 : ℝ)*X 0 0+(2688561619/5000000000 : ℝ)*X 0 1+(537712333/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1059080483/2000000000 : ℝ)*X 1 0+(-217676769/1000000000 : ℝ)*X 1 1+(672140419/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((211816103/400000000 : ℝ)*X 2 0+(5377123229/10000000000 : ℝ)*X 2 1+(-54419191/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2240547051/5000000000 : ℝ)*X 0 0+(2160484293/5000000000 : ℝ)*X 0 1+(4320968847/10000000000 : ℝ)*X 0 2+(2240547051/5000000000 : ℝ)*X 1 0+(2160484293/5000000000 : ℝ)*X 1 1+(4320968847/10000000000 : ℝ)*X 1 2+(2240547051/5000000000 : ℝ)*X 2 0+(2160484293/5000000000 : ℝ)*X 2 1+(4320968847/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-290645673/1250000000 : ℝ)*X 0 0+(1320088599/2500000000 : ℝ)*X 0 1+(5280354009/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1340964819/2500000000 : ℝ)*X 1 0+(-1107328321/5000000000 : ℝ)*X 1 1+(5280354273/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1072771861/2000000000 : ℝ)*X 2 0+(660044329/1250000000 : ℝ)*X 2 1+(-2214656127/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2132195639/5000000000 : ℝ)*X 0 0+(4429298757/10000000000 : ℝ)*X 0 1+(2214649441/5000000000 : ℝ)*X 0 2+(2132195639/5000000000 : ℝ)*X 1 0+(4429298757/10000000000 : ℝ)*X 1 1+(2214649441/5000000000 : ℝ)*X 1 2+(2132195639/5000000000 : ℝ)*X 2 0+(4429298757/10000000000 : ℝ)*X 2 1+(2214649441/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2271058749/10000000000 : ℝ)*X 0 0+(651831937/1250000000 : ℝ)*X 0 1+(5386726107/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5288605513/10000000000 : ℝ)*X 1 0+(-2172936707/10000000000 : ℝ)*X 1 1+(5386726713/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5288605403/10000000000 : ℝ)*X 2 0+(5386726043/10000000000 : ℝ)*X 2 1+(-2172937757/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2251163171/5000000000 : ℝ)*X 0 0+(4310211977/10000000000 : ℝ)*X 0 1+(862042429/2000000000 : ℝ)*X 0 2+(2251163171/5000000000 : ℝ)*X 1 0+(4310211977/10000000000 : ℝ)*X 1 1+(862042429/2000000000 : ℝ)*X 1 2+(2251163171/5000000000 : ℝ)*X 2 0+(4310211977/10000000000 : ℝ)*X 2 1+(862042429/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2120554103/10000000000 : ℝ)*X 0 0+(2720750481/5000000000 : ℝ)*X 0 1+(659042939/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5369524407/10000000000 : ℝ)*X 1 0+(-2217734327/10000000000 : ℝ)*X 1 1+(1318085859/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((268476227/500000000 : ℝ)*X 2 0+(1054468681/2000000000 : ℝ)*X 2 1+(-221773419/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2123111229/5000000000 : ℝ)*X 0 0+(4438261191/10000000000 : ℝ)*X 0 1+(887652297/2000000000 : ℝ)*X 0 2+(2123111229/5000000000 : ℝ)*X 1 0+(4438261191/10000000000 : ℝ)*X 1 1+(887652297/2000000000 : ℝ)*X 1 2+(2123111229/5000000000 : ℝ)*X 2 0+(4438261191/10000000000 : ℝ)*X 2 1+(887652297/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31113/50000 : ℝ) ≤ (-18511390578075600623787536621193/29750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1085633/2500000000000 : ℝ)*(lower2) + (7247483/6250000000000 : ℝ)*(upper4) + (43726051/20000000000000 : ℝ)*(upper5) + (1935885415241327/50000000000000 : ℝ)*(major0) + (1935885415241327/50000000000000 : ℝ)*(major1) + (1935885415241327/50000000000000 : ℝ)*(major2) + (3467970877/25000000000000 : ℝ)*(sp1) + (8611413179/100000000000000 : ℝ)*(sp3) + (5154250529647131/100000000000000 : ℝ)*(sp4) + (644282758685769/12500000000000 : ℝ)*(sp5) + (5154188610329109/100000000000000 : ℝ)*(sp6) + (1304999081025727/50000000000000 : ℝ)*(sp7) + (25411722529/100000000000000 : ℝ)*(sp8) + (87331040551/100000000000000 : ℝ)*(sp14) + (2610006773464633/100000000000000 : ℝ)*(f.failure) + (257713797068483/5000000000000 : ℝ)*(f.sum) + (3728690600529/595000000000000000000000000 : ℝ)*base66 + (423325148676474577/59500000000000000000000000000000 : ℝ)*base68 + (390548204640974577/59500000000000000000000000000000 : ℝ)*base70 + (1214928702571474577/59500000000000000000000000000000 : ℝ)*base72 + (1217534394143/297500000000000000000000000 : ℝ)*base73 + (413303594675974577/59500000000000000000000000000000 : ℝ)*base76 + (675323976844974577/59500000000000000000000000000000 : ℝ)*base78 + (389022909764974577/59500000000000000000000000000000 : ℝ)*base80 + (146476342757/297500000000000000000000000 : ℝ)*base82 + (1164989/400000000000000000000 : ℝ)*base89 + (1164989/400000000000000000000 : ℝ)*base91 + (1164989/400000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (29627/50000 : ℝ) ≤ (57923419849282435807629181165239/97750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7103263/25000000000000 : ℝ)*(lower1) + (40341837/50000000000000 : ℝ)*(lower3) + (1955581/10000000000000 : ℝ)*(upper4) + (2151291/10000000000000 : ℝ)*(upper5) + (1967482261338733/50000000000000 : ℝ)*(major0) + (1967482261338733/50000000000000 : ℝ)*(major1) + (1967482261338733/50000000000000 : ℝ)*(major2) + (129939260510719/2500000000000 : ℝ)*(sp0) + (519756383720207/10000000000000 : ℝ)*(sp1) + (5197543146419783/100000000000000 : ℝ)*(sp2) + (2652604524878373/100000000000000 : ℝ)*(sp3) + (658322669/10000000000000 : ℝ)*(sp5) + (934107563/50000000000000 : ℝ)*(sp7) + (27274008977/100000000000000 : ℝ)*(sp10) + (2652606393093499/100000000000000 : ℝ)*(f.failure) + (129939260510719/2500000000000 : ℝ)*(f.sum) + (533484145769/427656250000000000000000000 : ℝ)*base66 + (12545347122740181109/1368500000000000000000000000000000 : ℝ)*base68 + (28753530493784318891/1368500000000000000000000000000000 : ℝ)*base69 + (8980252341534181109/1368500000000000000000000000000000 : ℝ)*base72 + (14034564211141/6842500000000000000000000000 : ℝ)*base73 + (48446362897399318891/1368500000000000000000000000000000 : ℝ)*base75 + (12639030787255181109/1368500000000000000000000000000000 : ℝ)*base78 + (14538707559143181109/1368500000000000000000000000000000 : ℝ)*base80 + (1336047105581/427656250000000000000000000 : ℝ)*base81 + (3101767/400000000000000000000 : ℝ)*base89 + (3101767/400000000000000000000 : ℝ)*base91 + (3101767/400000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (79629/100000 : ℝ) ≤ (38919747173594269372280773937091/48875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (99813167/50000000000000 : ℝ)*(upper0) + (9587107/50000000000000 : ℝ)*(lower1) + (301340561/100000000000000 : ℝ)*(upper2) + (645327729/100000000000000 : ℝ)*(lower5) + (1100784228565259/25000000000000 : ℝ)*(major0) + (1100784228565259/25000000000000 : ℝ)*(major1) + (1100784228565259/25000000000000 : ℝ)*(major2) + (2539383539/100000000000000 : ℝ)*(sp0) + (349297085149/100000000000000 : ℝ)*(sp1) + (18789060303/10000000000000 : ℝ)*(sp3) + (5811520585647799/100000000000000 : ℝ)*(sp8) + (5811173827946189/100000000000000 : ℝ)*(sp9) + (2905761562515669/50000000000000 : ℝ)*(sp10) + (742004770199997/25000000000000 : ℝ)*(sp11) + (1484103485701509/50000000000000 : ℝ)*(f.failure) + (2905761562515669/50000000000000 : ℝ)*(f.sum) + (226649250779/1955000000000000000000000000 : ℝ)*base66 + (680102103544668101/97750000000000000000000000000000 : ℝ)*base68 + (1210738916064918101/97750000000000000000000000000000 : ℝ)*base70 + (1806463946706168101/97750000000000000000000000000000 : ℝ)*base72 + (47443422195969/1955000000000000000000000000 : ℝ)*base74 + (1472502941370418101/97750000000000000000000000000000 : ℝ)*base76 + (2745171313956668101/97750000000000000000000000000000 : ℝ)*base78 + (1859798266711668101/97750000000000000000000000000000 : ℝ)*base80 + (417759641693/61093750000000000000000000 : ℝ)*base81 + (103097/200000000000000000000 : ℝ)*base89 + (103097/200000000000000000000 : ℝ)*base91 + (103097/200000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-41497/50000 : ℝ) ≤ (-668077993415885239525894677/805000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5015361/5000000000000 : ℝ)*(lower0) + (124094617/50000000000000 : ℝ)*(lower1) + (129002319/100000000000000 : ℝ)*(lower2) + (11583097/100000000000000 : ℝ)*(lower4) + (277361612537209/6250000000000 : ℝ)*(major0) + (277361612537209/6250000000000 : ℝ)*(major1) + (277361612537209/6250000000000 : ℝ)*(major2) + (14539354353/100000000000000 : ℝ)*(sp0) + (278036504749/50000000000000 : ℝ)*(sp5) + (243792750819/50000000000000 : ℝ)*(sp6) + (2955828274508603/50000000000000 : ℝ)*(sp12) + (5911115015362061/100000000000000 : ℝ)*(sp13) + (5911183502869921/100000000000000 : ℝ)*(sp14) + (74789104946167/2500000000000 : ℝ)*(sp15) + (74789104946167/2500000000000 : ℝ)*(f.failure) + (5911671088371559/100000000000000 : ℝ)*(f.sum) + (32257739596227/402500000000000000000000000 : ℝ)*base65 + (19137400051776121/10062500000000000000000000000000 : ℝ)*base68 + (65073111992776121/10062500000000000000000000000000 : ℝ)*base70 + (582474694542661379/10062500000000000000000000000000 : ℝ)*base71 + (1341424402979/805000000000000000000000000 : ℝ)*base73 + (63024402973879/10062500000000000000000000000000 : ℝ)*base75 + (283098448201723879/10062500000000000000000000000000 : ℝ)*base77 + (151739022966463621/10062500000000000000000000000000 : ℝ)*base80 + (41494943179/12578125000000000000000000 : ℝ)*base82 + (48589/10000000000000000000 : ℝ)*base90 + (48589/10000000000000000000 : ℝ)*base92 + (48589/10000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1084_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5933733/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7007/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11277/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31113/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(29627/50000 : ℝ) else (79629/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41497/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1084_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1084_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5933733/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7007/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2819/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31113/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(29627/50000 : ℝ) else (79629/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41497/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1084_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1084_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5933733/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7007/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2819/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31113/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(29627/50000 : ℝ) else (79629/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41497/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1084_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
