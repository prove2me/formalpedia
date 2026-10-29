-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1319_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:42:57.482802+00:00
-- url     : https://prove2.me/submissions/a4a2153b-370a-48e4-aafd-2ad1d97ca1d7

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
theorem support_rectangle_w1319_s6_0 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-206400347/1000000000 : ℝ)*x 0 + (676739359/1250000000 : ℝ)*x 1 + (1048771141/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (206400347/1000000000 : ℝ)^4279 ≤ (6281931100891/50000000000000 : ℝ)^3255 := by
    have hnat : (206400347 : ℕ)^4279*50000000000000^3255 ≤ 6281931100891^3255*1000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206400347 1000000000 6281931100891 50000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676739359/1250000000 : ℝ)^4279 ≤ (22317523646641/50000000000000 : ℝ)^3255 := by
    have hnat : (676739359 : ℕ)^4279*50000000000000^3255 ≤ 22317523646641^3255*1250000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676739359 1250000000 22317523646641 50000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048771141/2000000000 : ℝ)^4279 ≤ (2140054524713/5000000000000 : ℝ)^3255 := by
    have hnat : (1048771141 : ℕ)^4279*5000000000000^3255 ≤ 2140054524713^3255*2000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048771141 2000000000 2140054524713 5000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-206400347/1000000000 : ℝ), (676739359/1250000000 : ℝ), (1048771141/2000000000 : ℝ)] ![(6281931100891/50000000000000 : ℝ), (22317523646641/50000000000000 : ℝ), (2140054524713/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-206400347/1000000000 : ℝ)|^4279 ≤ (6281931100891/50000000000000 : ℝ)^3255
        have hw : |(-206400347/1000000000 : ℝ)|=(206400347/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676739359/1250000000 : ℝ)|^4279 ≤ (22317523646641/50000000000000 : ℝ)^3255
        have hw : |(676739359/1250000000 : ℝ)|=(676739359/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048771141/2000000000 : ℝ)|^4279 ≤ (2140054524713/5000000000000 : ℝ)^3255
        have hw : |(1048771141/2000000000 : ℝ)|=(1048771141/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_s6_1 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349388883/10000000000 : ℝ)*x 0 + (-67208421/312500000 : ℝ)*x 1 + (5243853973/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349388883/10000000000 : ℝ)^4279 ≤ (43937018476671/100000000000000 : ℝ)^3255 := by
    have hnat : (5349388883 : ℕ)^4279*100000000000000^3255 ≤ 43937018476671^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349388883 10000000000 43937018476671 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (67208421/312500000 : ℝ)^4279 ≤ (6630954801311/50000000000000 : ℝ)^3255 := by
    have hnat : (67208421 : ℕ)^4279*50000000000000^3255 ≤ 6630954801311^3255*312500000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67208421 312500000 6630954801311 50000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243853973/10000000000 : ℝ)^4279 ≤ (21400535955043/50000000000000 : ℝ)^3255 := by
    have hnat : (5243853973 : ℕ)^4279*50000000000000^3255 ≤ 21400535955043^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243853973 10000000000 21400535955043 50000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349388883/10000000000 : ℝ), (-67208421/312500000 : ℝ), (5243853973/10000000000 : ℝ)] ![(43937018476671/100000000000000 : ℝ), (6630954801311/50000000000000 : ℝ), (21400535955043/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349388883/10000000000 : ℝ)|^4279 ≤ (43937018476671/100000000000000 : ℝ)^3255
        have hw : |(5349388883/10000000000 : ℝ)|=(5349388883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-67208421/312500000 : ℝ)|^4279 ≤ (6630954801311/50000000000000 : ℝ)^3255
        have hw : |(-67208421/312500000 : ℝ)|=(67208421/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243853973/10000000000 : ℝ)|^4279 ≤ (21400535955043/50000000000000 : ℝ)^3255
        have hw : |(5243853973/10000000000 : ℝ)|=(5243853973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_s6_2 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534938663/1000000000 : ℝ)*x 0 + (1310963979/2500000000 : ℝ)*x 1 + (-2150669901/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534938663/1000000000 : ℝ)^4279 ≤ (21968497075107/50000000000000 : ℝ)^3255 := by
    have hnat : (534938663 : ℕ)^4279*50000000000000^3255 ≤ 21968497075107^3255*1000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534938663 1000000000 21968497075107 50000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310963979/2500000000 : ℝ)^4279 ≤ (42801092758267/100000000000000 : ℝ)^3255 := by
    have hnat : (1310963979 : ℕ)^4279*100000000000000^3255 ≤ 42801092758267^3255*2500000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310963979 2500000000 42801092758267 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2150669901/10000000000 : ℝ)^4279 ≤ (13261913080233/100000000000000 : ℝ)^3255 := by
    have hnat : (2150669901 : ℕ)^4279*100000000000000^3255 ≤ 13261913080233^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2150669901 10000000000 13261913080233 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534938663/1000000000 : ℝ), (1310963979/2500000000 : ℝ), (-2150669901/10000000000 : ℝ)] ![(21968497075107/50000000000000 : ℝ), (42801092758267/100000000000000 : ℝ), (13261913080233/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534938663/1000000000 : ℝ)|^4279 ≤ (21968497075107/50000000000000 : ℝ)^3255
        have hw : |(534938663/1000000000 : ℝ)|=(534938663/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310963979/2500000000 : ℝ)|^4279 ≤ (42801092758267/100000000000000 : ℝ)^3255
        have hw : |(1310963979/2500000000 : ℝ)|=(1310963979/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2150669901/10000000000 : ℝ)|^4279 ≤ (13261913080233/100000000000000 : ℝ)^3255
        have hw : |(-2150669901/10000000000 : ℝ)|=(2150669901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_s6_3 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1083166661/2500000000 : ℝ)*x 0 + (259968841/625000000 : ℝ)*x 1 + (4512626619/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1083166661/2500000000 : ℝ)^4279 ≤ (33302823222301/100000000000000 : ℝ)^3255 := by
    have hnat : (1083166661 : ℕ)^4279*100000000000000^3255 ≤ 33302823222301^3255*2500000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083166661 2500000000 33302823222301 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (259968841/625000000 : ℝ)^4279 ≤ (7891042239449/25000000000000 : ℝ)^3255 := by
    have hnat : (259968841 : ℕ)^4279*25000000000000^3255 ≤ 7891042239449^3255*625000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259968841 625000000 7891042239449 25000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4512626619/10000000000 : ℝ)^4279 ≤ (35133007807921/100000000000000 : ℝ)^3255 := by
    have hnat : (4512626619 : ℕ)^4279*100000000000000^3255 ≤ 35133007807921^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4512626619 10000000000 35133007807921 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1083166661/2500000000 : ℝ), (259968841/625000000 : ℝ), (4512626619/10000000000 : ℝ)] ![(33302823222301/100000000000000 : ℝ), (7891042239449/25000000000000 : ℝ), (35133007807921/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1083166661/2500000000 : ℝ)|^4279 ≤ (33302823222301/100000000000000 : ℝ)^3255
        have hw : |(1083166661/2500000000 : ℝ)|=(1083166661/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(259968841/625000000 : ℝ)|^4279 ≤ (7891042239449/25000000000000 : ℝ)^3255
        have hw : |(259968841/625000000 : ℝ)|=(259968841/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4512626619/10000000000 : ℝ)|^4279 ≤ (35133007807921/100000000000000 : ℝ)^3255
        have hw : |(4512626619/10000000000 : ℝ)|=(4512626619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_s6_4 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1032008303/5000000000 : ℝ)*x 0 + (5244462861/10000000000 : ℝ)*x 1 + (5413304061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1032008303/5000000000 : ℝ)^4279 ≤ (785247957343/6250000000000 : ℝ)^3255 := by
    have hnat : (1032008303 : ℕ)^4279*6250000000000^3255 ≤ 785247957343^3255*5000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1032008303 5000000000 785247957343 6250000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244462861/10000000000 : ℝ)^4279 ≤ (42807605331879/100000000000000 : ℝ)^3255 := by
    have hnat : (5244462861 : ℕ)^4279*100000000000000^3255 ≤ 42807605331879^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244462861 10000000000 42807605331879 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413304061/10000000000 : ℝ)^4279 ≤ (44628427338663/100000000000000 : ℝ)^3255 := by
    have hnat : (5413304061 : ℕ)^4279*100000000000000^3255 ≤ 44628427338663^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413304061 10000000000 44628427338663 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1032008303/5000000000 : ℝ), (5244462861/10000000000 : ℝ), (5413304061/10000000000 : ℝ)] ![(785247957343/6250000000000 : ℝ), (42807605331879/100000000000000 : ℝ), (44628427338663/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1032008303/5000000000 : ℝ)|^4279 ≤ (785247957343/6250000000000 : ℝ)^3255
        have hw : |(-1032008303/5000000000 : ℝ)|=(1032008303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244462861/10000000000 : ℝ)|^4279 ≤ (42807605331879/100000000000000 : ℝ)^3255
        have hw : |(5244462861/10000000000 : ℝ)|=(5244462861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413304061/10000000000 : ℝ)|^4279 ≤ (44628427338663/100000000000000 : ℝ)^3255
        have hw : |(5413304061/10000000000 : ℝ)|=(5413304061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_s6_5 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305702387/10000000000 : ℝ)*x 0 + (-396244233/2000000000 : ℝ)*x 1 + (338331493/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305702387/10000000000 : ℝ)^4279 ≤ (10866481647091/25000000000000 : ℝ)^3255 := by
    have hnat : (5305702387 : ℕ)^4279*25000000000000^3255 ≤ 10866481647091^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305702387 10000000000 10866481647091 25000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (396244233/2000000000 : ℝ)^4279 ≤ (11905647929529/100000000000000 : ℝ)^3255 := by
    have hnat : (396244233 : ℕ)^4279*100000000000000^3255 ≤ 11905647929529^3255*2000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      396244233 2000000000 11905647929529 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338331493/625000000 : ℝ)^4279 ≤ (22314212731863/50000000000000 : ℝ)^3255 := by
    have hnat : (338331493 : ℕ)^4279*50000000000000^3255 ≤ 22314212731863^3255*625000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338331493 625000000 22314212731863 50000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305702387/10000000000 : ℝ), (-396244233/2000000000 : ℝ), (338331493/625000000 : ℝ)] ![(10866481647091/25000000000000 : ℝ), (11905647929529/100000000000000 : ℝ), (22314212731863/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305702387/10000000000 : ℝ)|^4279 ≤ (10866481647091/25000000000000 : ℝ)^3255
        have hw : |(5305702387/10000000000 : ℝ)|=(5305702387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-396244233/2000000000 : ℝ)|^4279 ≤ (11905647929529/100000000000000 : ℝ)^3255
        have hw : |(-396244233/2000000000 : ℝ)|=(396244233/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(338331493/625000000 : ℝ)|^4279 ≤ (22314212731863/50000000000000 : ℝ)^3255
        have hw : |(338331493/625000000 : ℝ)|=(338331493/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_s6_6 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (82901593/156250000 : ℝ)*x 0 + (2706652169/5000000000 : ℝ)*x 1 + (-1981221141/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (82901593/156250000 : ℝ)^4279 ≤ (10866480475903/25000000000000 : ℝ)^3255 := by
    have hnat : (82901593 : ℕ)^4279*25000000000000^3255 ≤ 10866480475903^3255*156250000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82901593 156250000 10866480475903 25000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2706652169/5000000000 : ℝ)^4279 ≤ (44628430340729/100000000000000 : ℝ)^3255 := by
    have hnat : (2706652169 : ℕ)^4279*100000000000000^3255 ≤ 44628430340729^3255*5000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706652169 5000000000 44628430340729 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1981221141/10000000000 : ℝ)^4279 ≤ (372051491873/3125000000000 : ℝ)^3255 := by
    have hnat : (1981221141 : ℕ)^4279*3125000000000^3255 ≤ 372051491873^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1981221141 10000000000 372051491873 3125000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(82901593/156250000 : ℝ), (2706652169/5000000000 : ℝ), (-1981221141/10000000000 : ℝ)] ![(10866480475903/25000000000000 : ℝ), (44628430340729/100000000000000 : ℝ), (372051491873/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(82901593/156250000 : ℝ)|^4279 ≤ (10866480475903/25000000000000 : ℝ)^3255
        have hw : |(82901593/156250000 : ℝ)|=(82901593/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2706652169/5000000000 : ℝ)|^4279 ≤ (44628430340729/100000000000000 : ℝ)^3255
        have hw : |(2706652169/5000000000 : ℝ)|=(2706652169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1981221141/10000000000 : ℝ)|^4279 ≤ (372051491873/3125000000000 : ℝ)^3255
        have hw : |(-1981221141/10000000000 : ℝ)|=(1981221141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_s6_7 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2166346183/5000000000 : ℝ)*x 0 + (2255681849/5000000000 : ℝ)*x 1 + (4160770997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2166346183/5000000000 : ℝ)^4279 ≤ (16651541565917/50000000000000 : ℝ)^3255 := by
    have hnat : (2166346183 : ℕ)^4279*50000000000000^3255 ≤ 16651541565917^3255*5000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2166346183 5000000000 16651541565917 50000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2255681849/5000000000 : ℝ)^4279 ≤ (1404803307867/4000000000000 : ℝ)^3255 := by
    have hnat : (2255681849 : ℕ)^4279*4000000000000^3255 ≤ 1404803307867^3255*5000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2255681849 5000000000 1404803307867 4000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4160770997/10000000000 : ℝ)^4279 ≤ (1578841707743/5000000000000 : ℝ)^3255 := by
    have hnat : (4160770997 : ℕ)^4279*5000000000000^3255 ≤ 1578841707743^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4160770997 10000000000 1578841707743 5000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2166346183/5000000000 : ℝ), (2255681849/5000000000 : ℝ), (4160770997/10000000000 : ℝ)] ![(16651541565917/50000000000000 : ℝ), (1404803307867/4000000000000 : ℝ), (1578841707743/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2166346183/5000000000 : ℝ)|^4279 ≤ (16651541565917/50000000000000 : ℝ)^3255
        have hw : |(2166346183/5000000000 : ℝ)|=(2166346183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2255681849/5000000000 : ℝ)|^4279 ≤ (1404803307867/4000000000000 : ℝ)^3255
        have hw : |(2255681849/5000000000 : ℝ)|=(2255681849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4160770997/10000000000 : ℝ)|^4279 ≤ (1578841707743/5000000000000 : ℝ)^3255
        have hw : |(4160770997/10000000000 : ℝ)|=(4160770997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1319_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153823057/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7351/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2771/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11093/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14693/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7351/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2771/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7351/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2771/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7351/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2771/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7351/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2771/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7351/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2771/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7351/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2771/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2771/25000 : ℝ) ^ (2139/512 : ℝ) ≤ (10209296126850067/100000000000000000000 : ℝ) := by
    have hpowers : (2771/25000 : ℝ)^2139 ≤ (10209296126850067/100000000000000000000 : ℝ)^512 := by
      have hnat : (2771 : ℕ)^2139*100000000000000000000^512 ≤ 10209296126850067^512*25000^2139 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2771 25000 10209296126850067 100000000000000000000 2139 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2771/25000 : ℝ)) (X := (10209296126850067/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2139 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7351/50000 : ℝ) ^ (2139/512 : ℝ) ≤ (16614598320443057/50000000000000000000 : ℝ) := by
    have hpowers : (7351/50000 : ℝ)^2139 ≤ (16614598320443057/50000000000000000000 : ℝ)^512 := by
      have hnat : (7351 : ℕ)^2139*50000000000000000000^512 ≤ 16614598320443057^512*50000^2139 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7351 50000 16614598320443057 50000000000000000000 2139 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7351/50000 : ℝ)) (X := (16614598320443057/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2139 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010209296126850067/50000000000000000000 : ℝ) ≤ (10000488710027823/10000000000000000 : ℝ) ^ (2139/512 : ℝ) := by
    have hpowers : (50010209296126850067/50000000000000000000 : ℝ)^512 ≤ (10000488710027823/10000000000000000 : ℝ)^2139 := by
      have hnat : (50010209296126850067 : ℕ)^512*10000000000000000^2139 ≤ 10000488710027823^2139*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010209296126850067 50000000000000000000 10000488710027823 10000000000000000 512 2139 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000488710027823/10000000000000000 : ℝ)) (X := (50010209296126850067/50000000000000000000 : ℝ)) (by norm_num) 2139 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100043438492767736181/100000000000000000000 : ℝ) ≤ (2000207918045857/2000000000000000 : ℝ) ^ (2139/512 : ℝ) := by
    have hpowers : (100043438492767736181/100000000000000000000 : ℝ)^512 ≤ (2000207918045857/2000000000000000 : ℝ)^2139 := by
      have hnat : (100043438492767736181 : ℕ)^512*2000000000000000^2139 ≤ 2000207918045857^2139*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100043438492767736181 100000000000000000000 2000207918045857 2000000000000000 512 2139 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000207918045857/2000000000000000 : ℝ)) (X := (100043438492767736181/100000000000000000000 : ℝ)) (by norm_num) 2139 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016614598320443057/25000000000000000000 : ℝ) ≤ (10001590470430747/10000000000000000 : ℝ) ^ (2139/512 : ℝ) := by
    have hpowers : (25016614598320443057/25000000000000000000 : ℝ)^512 ≤ (10001590470430747/10000000000000000 : ℝ)^2139 := by
      have hnat : (25016614598320443057 : ℕ)^512*10000000000000000^2139 ≤ 10001590470430747^2139*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016614598320443057 25000000000000000000 10001590470430747 10000000000000000 512 2139 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001590470430747/10000000000000000 : ℝ)) (X := (25016614598320443057/25000000000000000000 : ℝ)) (by norm_num) 2139 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10209296126850067/100000000000000000000 : ℝ) ≤ ((18084778120287326999/18090000000000000000 : ℝ)+2*(275440100731/180900000000000 : ℝ)*(2771/25000 : ℝ))^(2139/512 : ℝ) := by
    rw [show (18084778120287326999/18090000000000000000 : ℝ)+2*(275440100731/180900000000000 : ℝ)*(2771/25000 : ℝ)=(10000488710027823/10000000000000000 : ℝ) by norm_num, show 1+2*(10209296126850067/100000000000000000000 : ℝ)=(50010209296126850067/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16614598320443057/50000000000000000000 : ℝ)+(10209296126850067/100000000000000000000 : ℝ) ≤ ((18084778120287326999/18090000000000000000 : ℝ)+(275440100731/180900000000000 : ℝ)*((7351/50000 : ℝ)+(2771/25000 : ℝ)))^(2139/512 : ℝ) := by
    rw [show (18084778120287326999/18090000000000000000 : ℝ)+(275440100731/180900000000000 : ℝ)*((7351/50000 : ℝ)+(2771/25000 : ℝ))=(2000207918045857/2000000000000000 : ℝ) by norm_num, show 1+(16614598320443057/50000000000000000000 : ℝ)+(10209296126850067/100000000000000000000 : ℝ)=(100043438492767736181/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16614598320443057/50000000000000000000 : ℝ) ≤ ((18084778120287326999/18090000000000000000 : ℝ)+2*(275440100731/180900000000000 : ℝ)*(7351/50000 : ℝ))^(2139/512 : ℝ) := by
    rw [show (18084778120287326999/18090000000000000000 : ℝ)+2*(275440100731/180900000000000 : ℝ)*(7351/50000 : ℝ)=(10001590470430747/10000000000000000 : ℝ) by norm_num, show 1+2*(16614598320443057/50000000000000000000 : ℝ)=(25016614598320443057/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18084778120287326999/18090000000000000000 : ℝ)*(X 1 0+X 2 0)+(275440100731/180900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2139/512 : ℝ)) (lo := (2771/25000 : ℝ)) (hi := (7351/50000 : ℝ)) (c := (18084778120287326999/18090000000000000000 : ℝ)) (alpha := (275440100731/180900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18084778120287326999/18090000000000000000 : ℝ)*(X 0 1+X 2 1)+(275440100731/180900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2139/512 : ℝ)) (lo := (2771/25000 : ℝ)) (hi := (7351/50000 : ℝ)) (c := (18084778120287326999/18090000000000000000 : ℝ)) (alpha := (275440100731/180900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18084778120287326999/18090000000000000000 : ℝ)*(X 0 2+X 1 2)+(275440100731/180900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2139/512 : ℝ)) (lo := (2771/25000 : ℝ)) (hi := (7351/50000 : ℝ)) (c := (18084778120287326999/18090000000000000000 : ℝ)) (alpha := (275440100731/180900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-206400347/1000000000 : ℝ)*X 0 0+(676739359/1250000000 : ℝ)*X 0 1+(1048771141/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349388883/10000000000 : ℝ)*X 1 0+(-67208421/312500000 : ℝ)*X 1 1+(5243853973/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534938663/1000000000 : ℝ)*X 2 0+(1310963979/2500000000 : ℝ)*X 2 1+(-2150669901/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1083166661/2500000000 : ℝ)*X 0 0+(259968841/625000000 : ℝ)*X 0 1+(4512626619/10000000000 : ℝ)*X 0 2+(1083166661/2500000000 : ℝ)*X 1 0+(259968841/625000000 : ℝ)*X 1 1+(4512626619/10000000000 : ℝ)*X 1 2+(1083166661/2500000000 : ℝ)*X 2 0+(259968841/625000000 : ℝ)*X 2 1+(4512626619/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1032008303/5000000000 : ℝ)*X 0 0+(5244462861/10000000000 : ℝ)*X 0 1+(5413304061/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305702387/10000000000 : ℝ)*X 1 0+(-396244233/2000000000 : ℝ)*X 1 1+(338331493/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((82901593/156250000 : ℝ)*X 2 0+(2706652169/5000000000 : ℝ)*X 2 1+(-1981221141/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2166346183/5000000000 : ℝ)*X 0 0+(2255681849/5000000000 : ℝ)*X 0 1+(4160770997/10000000000 : ℝ)*X 0 2+(2166346183/5000000000 : ℝ)*X 1 0+(2255681849/5000000000 : ℝ)*X 1 1+(4160770997/10000000000 : ℝ)*X 1 2+(2166346183/5000000000 : ℝ)*X 2 0+(2255681849/5000000000 : ℝ)*X 2 1+(4160770997/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (17765517481967943499199177/2250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (650042273/25000000000000 : ℝ)*(base19) + (752545979/100000000000000 : ℝ)*(base23) + (189872881/50000000000000 : ℝ)*(lower4) + (103781207/100000000000000 : ℝ)*(lower5) + (4356139936962141/100000000000000 : ℝ)*(major0) + (4356139936962141/100000000000000 : ℝ)*(major1) + (2178069968481071/50000000000000 : ℝ)*(major2) + (1176070124101927/20000000000000 : ℝ)*(sp0) + (5880360897386823/100000000000000 : ℝ)*(sp1) + (2940176420483847/50000000000000 : ℝ)*(sp2) + (176993242012729/6250000000000 : ℝ)*(sp3) + (12877046279/100000000000000 : ℝ)*(sp4) + (9904042243/100000000000000 : ℝ)*(sp6) + (12120485921/50000000000000 : ℝ)*(sp7) + (566383222635101/20000000000000 : ℝ)*(f.failure) + (1176072699511183/20000000000000 : ℝ)*(f.sum) + (155025811734887/18090000000000000000000000000 : ℝ)*base66 + (1562220298420655141/1809000000000000000000000000000000 : ℝ)*base68 + (952359168044285929/904500000000000000000000000000000 : ℝ)*base69 + (11391544915342655141/1809000000000000000000000000000000 : ℝ)*base72 + (32611631844913/18090000000000000000000000000 : ℝ)*base73 + (683466243338214071/904500000000000000000000000000000 : ℝ)*base76 + (772280676208842783/67000000000000000000000000000000 : ℝ)*base78 + (2495964416806842783/67000000000000000000000000000000 : ℝ)*base80 + (283625133591/167500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base87 + (11323757/2000000000000000000000 : ℝ)*base89 + (11323757/2000000000000000000000 : ℝ)*base91 + (8676243/2000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (114283855262970870025345453/12562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1555223741/100000000000000 : ℝ)*(base19) + (1206024807/100000000000000 : ℝ)*(base23) + (53051517/100000000000000 : ℝ)*(upper2) + (22316389/10000000000000 : ℝ)*(upper3) + (98585839/100000000000000 : ℝ)*(upper5) + (1096878574345641/25000000000000 : ℝ)*(major0) + (1096878574345641/25000000000000 : ℝ)*(major1) + (1096878574345641/25000000000000 : ℝ)*(major2) + (11440164953/50000000000000 : ℝ)*(sp1) + (27302055417/100000000000000 : ℝ)*(sp2) + (5922715781974807/100000000000000 : ℝ)*(sp4) + (5922691346421161/100000000000000 : ℝ)*(sp5) + (5922687273894583/100000000000000 : ℝ)*(sp6) + (285231250954957/10000000000000 : ℝ)*(sp7) + (285231250954957/10000000000000 : ℝ)*(f.failure) + (5922715781974807/100000000000000 : ℝ)*(f.sum) + (10647808723121/1507500000000000000000000000 : ℝ)*base66 + (119156514811903283/16750000000000000000000000000000 : ℝ)*base68 + (12250641964403283/16750000000000000000000000000000 : ℝ)*base70 + (199291466798403283/16750000000000000000000000000000 : ℝ)*base72 + (2180167247483/3015000000000000000000000000 : ℝ)*base73 + (71257529887653283/16750000000000000000000000000000 : ℝ)*base76 + (208174903350153283/16750000000000000000000000000000 : ℝ)*base78 + (62501335604846717/16750000000000000000000000000000 : ℝ)*base79 + (778207417061/1507500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (15043549/1000000000000000000000 : ℝ)*base89 + (15043549/1000000000000000000000 : ℝ)*base91 + (15043549/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1319_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153823057/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7351/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2771/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11093/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14693/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1319_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1319_s7_0 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-51600289/250000000 : ℝ)*x 0 + (5413837951/10000000000 : ℝ)*x 1 + (655490921/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (51600289/250000000 : ℝ)^4279 ≤ (628196346941/5000000000000 : ℝ)^3255 := by
    have hnat : (51600289 : ℕ)^4279*5000000000000^3255 ≤ 628196346941^3255*250000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51600289 250000000 628196346941 5000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5413837951/10000000000 : ℝ)^4279 ≤ (1115855340311/2500000000000 : ℝ)^3255 := by
    have hnat : (5413837951 : ℕ)^4279*2500000000000^3255 ≤ 1115855340311^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413837951 10000000000 1115855340311 2500000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655490921/1250000000 : ℝ)^4279 ≤ (21400929716121/50000000000000 : ℝ)^3255 := by
    have hnat : (655490921 : ℕ)^4279*50000000000000^3255 ≤ 21400929716121^3255*1250000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655490921 1250000000 21400929716121 50000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-51600289/250000000 : ℝ), (5413837951/10000000000 : ℝ), (655490921/1250000000 : ℝ)] ![(628196346941/5000000000000 : ℝ), (1115855340311/2500000000000 : ℝ), (21400929716121/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-51600289/250000000 : ℝ)|^4279 ≤ (628196346941/5000000000000 : ℝ)^3255
        have hw : |(-51600289/250000000 : ℝ)|=(51600289/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5413837951/10000000000 : ℝ)|^4279 ≤ (1115855340311/2500000000000 : ℝ)^3255
        have hw : |(5413837951/10000000000 : ℝ)|=(5413837951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655490921/1250000000 : ℝ)|^4279 ≤ (21400929716121/50000000000000 : ℝ)^3255
        have hw : |(655490921/1250000000 : ℝ)|=(655490921/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_s7_1 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668671041/1250000000 : ℝ)*x 0 + (-1075300047/5000000000 : ℝ)*x 1 + (5243927071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668671041/1250000000 : ℝ)^4279 ≤ (2746049783563/6250000000000 : ℝ)^3255 := by
    have hnat : (668671041 : ℕ)^4279*6250000000000^3255 ≤ 2746049783563^3255*1250000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668671041 1250000000 2746049783563 6250000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1075300047/5000000000 : ℝ)^4279 ≤ (13261347205281/100000000000000 : ℝ)^3255 := by
    have hnat : (1075300047 : ℕ)^4279*100000000000000^3255 ≤ 13261347205281^3255*5000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075300047 5000000000 13261347205281 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243927071/10000000000 : ℝ)^4279 ≤ (856037124909/2000000000000 : ℝ)^3255 := by
    have hnat : (5243927071 : ℕ)^4279*2000000000000^3255 ≤ 856037124909^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243927071 10000000000 856037124909 2000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668671041/1250000000 : ℝ), (-1075300047/5000000000 : ℝ), (5243927071/10000000000 : ℝ)] ![(2746049783563/6250000000000 : ℝ), (13261347205281/100000000000000 : ℝ), (856037124909/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668671041/1250000000 : ℝ)|^4279 ≤ (2746049783563/6250000000000 : ℝ)^3255
        have hw : |(668671041/1250000000 : ℝ)|=(668671041/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1075300047/5000000000 : ℝ)|^4279 ≤ (13261347205281/100000000000000 : ℝ)^3255
        have hw : |(-1075300047/5000000000 : ℝ)|=(1075300047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243927071/10000000000 : ℝ)|^4279 ≤ (856037124909/2000000000000 : ℝ)^3255
        have hw : |(5243927071/10000000000 : ℝ)|=(5243927071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_s7_2 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (213974729/400000000 : ℝ)*x 0 + (1310981781/2500000000 : ℝ)*x 1 + (-2150600161/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213974729/400000000 : ℝ)^4279 ≤ (549209942811/1250000000000 : ℝ)^3255 := by
    have hnat : (213974729 : ℕ)^4279*1250000000000^3255 ≤ 549209942811^3255*400000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213974729 400000000 549209942811 1250000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310981781/2500000000 : ℝ)^4279 ≤ (42801856814137/100000000000000 : ℝ)^3255 := by
    have hnat : (1310981781 : ℕ)^4279*100000000000000^3255 ≤ 42801856814137^3255*2500000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310981781 2500000000 42801856814137 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2150600161/10000000000 : ℝ)^4279 ≤ (13261347748399/100000000000000 : ℝ)^3255 := by
    have hnat : (2150600161 : ℕ)^4279*100000000000000^3255 ≤ 13261347748399^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2150600161 10000000000 13261347748399 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213974729/400000000 : ℝ), (1310981781/2500000000 : ℝ), (-2150600161/10000000000 : ℝ)] ![(549209942811/1250000000000 : ℝ), (42801856814137/100000000000000 : ℝ), (13261347748399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213974729/400000000 : ℝ)|^4279 ≤ (549209942811/1250000000000 : ℝ)^3255
        have hw : |(213974729/400000000 : ℝ)|=(213974729/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310981781/2500000000 : ℝ)|^4279 ≤ (42801856814137/100000000000000 : ℝ)^3255
        have hw : |(1310981781/2500000000 : ℝ)|=(1310981781/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2150600161/10000000000 : ℝ)|^4279 ≤ (13261347748399/100000000000000 : ℝ)^3255
        have hw : |(-2150600161/10000000000 : ℝ)|=(2150600161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_s7_3 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (433267189/1000000000 : ℝ)*x 0 + (4159656867/10000000000 : ℝ)*x 1 + (4512469959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (433267189/1000000000 : ℝ)^4279 ≤ (33302876230791/100000000000000 : ℝ)^3255 := by
    have hnat : (433267189 : ℕ)^4279*100000000000000^3255 ≤ 33302876230791^3255*1000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433267189 1000000000 33302876230791 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4159656867/10000000000 : ℝ)^4279 ≤ (15782859651981/50000000000000 : ℝ)^3255 := by
    have hnat : (4159656867 : ℕ)^4279*50000000000000^3255 ≤ 15782859651981^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4159656867 10000000000 15782859651981 50000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4512469959/10000000000 : ℝ)^4279 ≤ (35131404440793/100000000000000 : ℝ)^3255 := by
    have hnat : (4512469959 : ℕ)^4279*100000000000000^3255 ≤ 35131404440793^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4512469959 10000000000 35131404440793 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(433267189/1000000000 : ℝ), (4159656867/10000000000 : ℝ), (4512469959/10000000000 : ℝ)] ![(33302876230791/100000000000000 : ℝ), (15782859651981/50000000000000 : ℝ), (35131404440793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(433267189/1000000000 : ℝ)|^4279 ≤ (33302876230791/100000000000000 : ℝ)^3255
        have hw : |(433267189/1000000000 : ℝ)|=(433267189/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4159656867/10000000000 : ℝ)|^4279 ≤ (15782859651981/50000000000000 : ℝ)^3255
        have hw : |(4159656867/10000000000 : ℝ)|=(4159656867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4512469959/10000000000 : ℝ)|^4279 ≤ (35131404440793/100000000000000 : ℝ)^3255
        have hw : |(4512469959/10000000000 : ℝ)|=(4512469959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_s7_4 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2064024083/10000000000 : ℝ)*x 0 + (5244534031/10000000000 : ℝ)*x 1 + (216529123/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2064024083/10000000000 : ℝ)^4279 ≤ (12564027149351/100000000000000 : ℝ)^3255 := by
    have hnat : (2064024083 : ℕ)^4279*100000000000000^3255 ≤ 12564027149351^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064024083 10000000000 12564027149351 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244534031/10000000000 : ℝ)^4279 ≤ (8561673801563/20000000000000 : ℝ)^3255 := by
    have hnat : (5244534031 : ℕ)^4279*20000000000000^3255 ≤ 8561673801563^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244534031 10000000000 8561673801563 20000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216529123/400000000 : ℝ)^4279 ≤ (8925520764139/20000000000000 : ℝ)^3255 := by
    have hnat : (216529123 : ℕ)^4279*20000000000000^3255 ≤ 8925520764139^3255*400000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216529123 400000000 8925520764139 20000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2064024083/10000000000 : ℝ), (5244534031/10000000000 : ℝ), (216529123/400000000 : ℝ)] ![(12564027149351/100000000000000 : ℝ), (8561673801563/20000000000000 : ℝ), (8925520764139/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2064024083/10000000000 : ℝ)|^4279 ≤ (12564027149351/100000000000000 : ℝ)^3255
        have hw : |(-2064024083/10000000000 : ℝ)|=(2064024083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244534031/10000000000 : ℝ)|^4279 ≤ (8561673801563/20000000000000 : ℝ)^3255
        have hw : |(5244534031/10000000000 : ℝ)|=(5244534031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216529123/400000000 : ℝ)|^4279 ≤ (8925520764139/20000000000000 : ℝ)^3255
        have hw : |(216529123/400000000 : ℝ)|=(216529123/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_s7_5 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305721327/10000000000 : ℝ)*x 0 + (-495324839/2500000000 : ℝ)*x 1 + (5413228073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305721327/10000000000 : ℝ)^4279 ≤ (43466130563659/100000000000000 : ℝ)^3255 := by
    have hnat : (5305721327 : ℕ)^4279*100000000000000^3255 ≤ 43466130563659^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305721327 10000000000 43466130563659 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (495324839/2500000000 : ℝ)^4279 ≤ (11906265619903/100000000000000 : ℝ)^3255 := by
    have hnat : (495324839 : ℕ)^4279*100000000000000^3255 ≤ 11906265619903^3255*2500000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      495324839 2500000000 11906265619903 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413228073/10000000000 : ℝ)^4279 ≤ (2231380189951/5000000000000 : ℝ)^3255 := by
    have hnat : (5413228073 : ℕ)^4279*5000000000000^3255 ≤ 2231380189951^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413228073 10000000000 2231380189951 5000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305721327/10000000000 : ℝ), (-495324839/2500000000 : ℝ), (5413228073/10000000000 : ℝ)] ![(43466130563659/100000000000000 : ℝ), (11906265619903/100000000000000 : ℝ), (2231380189951/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305721327/10000000000 : ℝ)|^4279 ≤ (43466130563659/100000000000000 : ℝ)^3255
        have hw : |(5305721327/10000000000 : ℝ)|=(5305721327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-495324839/2500000000 : ℝ)|^4279 ≤ (11906265619903/100000000000000 : ℝ)^3255
        have hw : |(-495324839/2500000000 : ℝ)|=(495324839/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413228073/10000000000 : ℝ)|^4279 ≤ (2231380189951/5000000000000 : ℝ)^3255
        have hw : |(5413228073/10000000000 : ℝ)|=(5413228073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_s7_6 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652860673/5000000000 : ℝ)*x 0 + (1353307013/2500000000 : ℝ)*x 1 + (-1981299359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652860673/5000000000 : ℝ)^4279 ≤ (1086653269207/2500000000000 : ℝ)^3255 := by
    have hnat : (2652860673 : ℕ)^4279*2500000000000^3255 ≤ 1086653269207^3255*5000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652860673 5000000000 1086653269207 2500000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353307013/2500000000 : ℝ)^4279 ≤ (44627603571427/100000000000000 : ℝ)^3255 := by
    have hnat : (1353307013 : ℕ)^4279*100000000000000^3255 ≤ 44627603571427^3255*2500000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353307013 2500000000 44627603571427 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1981299359/10000000000 : ℝ)^4279 ≤ (11906265643603/100000000000000 : ℝ)^3255 := by
    have hnat : (1981299359 : ℕ)^4279*100000000000000^3255 ≤ 11906265643603^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1981299359 10000000000 11906265643603 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652860673/5000000000 : ℝ), (1353307013/2500000000 : ℝ), (-1981299359/10000000000 : ℝ)] ![(1086653269207/2500000000000 : ℝ), (44627603571427/100000000000000 : ℝ), (11906265643603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652860673/5000000000 : ℝ)|^4279 ≤ (1086653269207/2500000000000 : ℝ)^3255
        have hw : |(2652860673/5000000000 : ℝ)|=(2652860673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353307013/2500000000 : ℝ)|^4279 ≤ (44627603571427/100000000000000 : ℝ)^3255
        have hw : |(1353307013/2500000000 : ℝ)|=(1353307013/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1981299359/10000000000 : ℝ)|^4279 ≤ (11906265643603/100000000000000 : ℝ)^3255
        have hw : |(-1981299359/10000000000 : ℝ)|=(1981299359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_s7_7 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1083174473/2500000000 : ℝ)*x 0 + (4511209817/10000000000 : ℝ)*x 1 + (2080461623/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1083174473/2500000000 : ℝ)^4279 ≤ (6660627793941/20000000000000 : ℝ)^3255 := by
    have hnat : (1083174473 : ℕ)^4279*20000000000000^3255 ≤ 6660627793941^3255*2500000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083174473 2500000000 6660627793941 20000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4511209817/10000000000 : ℝ)^4279 ≤ (7023701582057/20000000000000 : ℝ)^3255 := by
    have hnat : (4511209817 : ℕ)^4279*20000000000000^3255 ≤ 7023701582057^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4511209817 10000000000 7023701582057 20000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2080461623/5000000000 : ℝ)^4279 ≤ (15789176551619/50000000000000 : ℝ)^3255 := by
    have hnat : (2080461623 : ℕ)^4279*50000000000000^3255 ≤ 15789176551619^3255*5000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080461623 5000000000 15789176551619 50000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1083174473/2500000000 : ℝ), (4511209817/10000000000 : ℝ), (2080461623/5000000000 : ℝ)] ![(6660627793941/20000000000000 : ℝ), (7023701582057/20000000000000 : ℝ), (15789176551619/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1083174473/2500000000 : ℝ)|^4279 ≤ (6660627793941/20000000000000 : ℝ)^3255
        have hw : |(1083174473/2500000000 : ℝ)|=(1083174473/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4511209817/10000000000 : ℝ)|^4279 ≤ (7023701582057/20000000000000 : ℝ)^3255
        have hw : |(4511209817/10000000000 : ℝ)|=(4511209817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2080461623/5000000000 : ℝ)|^4279 ≤ (15789176551619/50000000000000 : ℝ)^3255
        have hw : |(2080461623/5000000000 : ℝ)|=(2080461623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1319_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153823057/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14693/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11093/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2219/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14691/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14693/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11093/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14693/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11093/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14693/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11093/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14693/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11093/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14693/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11093/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14693/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11093/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11093/100000 : ℝ) ^ (2139/512 : ℝ) ≤ (5121986617869567/50000000000000000000 : ℝ) := by
    have hpowers : (11093/100000 : ℝ)^2139 ≤ (5121986617869567/50000000000000000000 : ℝ)^512 := by
      have hnat : (11093 : ℕ)^2139*50000000000000000000^512 ≤ 5121986617869567^512*100000^2139 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11093 100000 5121986617869567 50000000000000000000 2139 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11093/100000 : ℝ)) (X := (5121986617869567/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2139 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14693/100000 : ℝ) ^ (2139/512 : ℝ) ≤ (4143037162344521/12500000000000000000 : ℝ) := by
    have hpowers : (14693/100000 : ℝ)^2139 ≤ (4143037162344521/12500000000000000000 : ℝ)^512 := by
      have hnat : (14693 : ℕ)^2139*12500000000000000000^512 ≤ 4143037162344521^512*100000^2139 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14693 100000 4143037162344521 12500000000000000000 2139 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14693/100000 : ℝ)) (X := (4143037162344521/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2139 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005121986617869567/25000000000000000000 : ℝ) ≤ (10000490369861209/10000000000000000 : ℝ) ^ (2139/512 : ℝ) := by
    have hpowers : (25005121986617869567/25000000000000000000 : ℝ)^512 ≤ (10000490369861209/10000000000000000 : ℝ)^2139 := by
      have hnat : (25005121986617869567 : ℕ)^512*10000000000000000^2139 ≤ 10000490369861209^2139*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005121986617869567 25000000000000000000 10000490369861209 10000000000000000 512 2139 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000490369861209/10000000000000000 : ℝ)) (X := (25005121986617869567/25000000000000000000 : ℝ)) (by norm_num) 2139 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50021694135267247651/50000000000000000000 : ℝ) ≤ (1000103838848569/1000000000000000 : ℝ) ^ (2139/512 : ℝ) := by
    have hpowers : (50021694135267247651/50000000000000000000 : ℝ)^512 ≤ (1000103838848569/1000000000000000 : ℝ)^2139 := by
      have hnat : (50021694135267247651 : ℕ)^512*1000000000000000^2139 ≤ 1000103838848569^2139*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021694135267247651 50000000000000000000 1000103838848569 1000000000000000 512 2139 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000103838848569/1000000000000000 : ℝ)) (X := (50021694135267247651/50000000000000000000 : ℝ)) (by norm_num) 2139 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254143037162344521/6250000000000000000 : ℝ) ≤ (10001586407110171/10000000000000000 : ℝ) ^ (2139/512 : ℝ) := by
    have hpowers : (6254143037162344521/6250000000000000000 : ℝ)^512 ≤ (10001586407110171/10000000000000000 : ℝ)^2139 := by
      have hnat : (6254143037162344521 : ℕ)^512*10000000000000000^2139 ≤ 10001586407110171^2139*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254143037162344521 6250000000000000000 10001586407110171 10000000000000000 512 2139 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001586407110171/10000000000000000 : ℝ)) (X := (6254143037162344521/6250000000000000000 : ℝ)) (by norm_num) 2139 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5121986617869567/50000000000000000000 : ℝ) ≤ ((5998267831716269489/6000000000000000000 : ℝ)+2*(182672874827/120000000000000 : ℝ)*(11093/100000 : ℝ))^(2139/512 : ℝ) := by
    rw [show (5998267831716269489/6000000000000000000 : ℝ)+2*(182672874827/120000000000000 : ℝ)*(11093/100000 : ℝ)=(10000490369861209/10000000000000000 : ℝ) by norm_num, show 1+2*(5121986617869567/50000000000000000000 : ℝ)=(25005121986617869567/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4143037162344521/12500000000000000000 : ℝ)+(5121986617869567/50000000000000000000 : ℝ) ≤ ((5998267831716269489/6000000000000000000 : ℝ)+(182672874827/120000000000000 : ℝ)*((14693/100000 : ℝ)+(11093/100000 : ℝ)))^(2139/512 : ℝ) := by
    rw [show (5998267831716269489/6000000000000000000 : ℝ)+(182672874827/120000000000000 : ℝ)*((14693/100000 : ℝ)+(11093/100000 : ℝ))=(1000103838848569/1000000000000000 : ℝ) by norm_num, show 1+(4143037162344521/12500000000000000000 : ℝ)+(5121986617869567/50000000000000000000 : ℝ)=(50021694135267247651/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4143037162344521/12500000000000000000 : ℝ) ≤ ((5998267831716269489/6000000000000000000 : ℝ)+2*(182672874827/120000000000000 : ℝ)*(14693/100000 : ℝ))^(2139/512 : ℝ) := by
    rw [show (5998267831716269489/6000000000000000000 : ℝ)+2*(182672874827/120000000000000 : ℝ)*(14693/100000 : ℝ)=(10001586407110171/10000000000000000 : ℝ) by norm_num, show 1+2*(4143037162344521/12500000000000000000 : ℝ)=(6254143037162344521/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5998267831716269489/6000000000000000000 : ℝ)*(X 1 0+X 2 0)+(182672874827/120000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2139/512 : ℝ)) (lo := (11093/100000 : ℝ)) (hi := (14693/100000 : ℝ)) (c := (5998267831716269489/6000000000000000000 : ℝ)) (alpha := (182672874827/120000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5998267831716269489/6000000000000000000 : ℝ)*(X 0 1+X 2 1)+(182672874827/120000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2139/512 : ℝ)) (lo := (11093/100000 : ℝ)) (hi := (14693/100000 : ℝ)) (c := (5998267831716269489/6000000000000000000 : ℝ)) (alpha := (182672874827/120000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5998267831716269489/6000000000000000000 : ℝ)*(X 0 2+X 1 2)+(182672874827/120000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2139/512 : ℝ)) (lo := (11093/100000 : ℝ)) (hi := (14693/100000 : ℝ)) (c := (5998267831716269489/6000000000000000000 : ℝ)) (alpha := (182672874827/120000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-51600289/250000000 : ℝ)*X 0 0+(5413837951/10000000000 : ℝ)*X 0 1+(655490921/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668671041/1250000000 : ℝ)*X 1 0+(-1075300047/5000000000 : ℝ)*X 1 1+(5243927071/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((213974729/400000000 : ℝ)*X 2 0+(1310981781/2500000000 : ℝ)*X 2 1+(-2150600161/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((433267189/1000000000 : ℝ)*X 0 0+(4159656867/10000000000 : ℝ)*X 0 1+(4512469959/10000000000 : ℝ)*X 0 2+(433267189/1000000000 : ℝ)*X 1 0+(4159656867/10000000000 : ℝ)*X 1 1+(4512469959/10000000000 : ℝ)*X 1 2+(433267189/1000000000 : ℝ)*X 2 0+(4159656867/10000000000 : ℝ)*X 2 1+(4512469959/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2064024083/10000000000 : ℝ)*X 0 0+(5244534031/10000000000 : ℝ)*X 0 1+(216529123/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305721327/10000000000 : ℝ)*X 1 0+(-495324839/2500000000 : ℝ)*X 1 1+(5413228073/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652860673/5000000000 : ℝ)*X 2 0+(1353307013/2500000000 : ℝ)*X 2 1+(-1981299359/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1083174473/2500000000 : ℝ)*X 0 0+(4511209817/10000000000 : ℝ)*X 0 1+(2080461623/5000000000 : ℝ)*X 0 2+(1083174473/2500000000 : ℝ)*X 1 0+(4511209817/10000000000 : ℝ)*X 1 1+(2080461623/5000000000 : ℝ)*X 1 2+(1083174473/2500000000 : ℝ)*X 2 0+(4511209817/10000000000 : ℝ)*X 2 1+(2080461623/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (186045986205683770551781029/50000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (22845769/2500000000000 : ℝ)*(base19) + (794228797/100000000000000 : ℝ)*(base23) + (6672457/20000000000000 : ℝ)*(upper3) + (4750407/100000000000000 : ℝ)*(lower4) + (2179964144840139/50000000000000 : ℝ)*(major0) + (2179964144840139/50000000000000 : ℝ)*(major1) + (2179964144840139/50000000000000 : ℝ)*(major2) + (1471366041684127/25000000000000 : ℝ)*(sp0) + (5885476629318057/100000000000000 : ℝ)*(sp1) + (5885474890942793/100000000000000 : ℝ)*(sp2) + (566874080104819/20000000000000 : ℝ)*(sp3) + (13376412309/100000000000000 : ℝ)*(sp4) + (464494307/25000000000000 : ℝ)*(sp6) + (4255828491/50000000000000 : ℝ)*(sp7) + (2834378912181077/100000000000000 : ℝ)*(f.failure) + (5885477543148817/100000000000000 : ℝ)*(f.sum) + (843177273349/1000000000000000000000000000 : ℝ)*base66 + (680374495865289657/100000000000000000000000000000000 : ℝ)*base67 + (100875850865289657/100000000000000000000000000000000 : ℝ)*base69 + (445238011465289657/100000000000000000000000000000000 : ℝ)*base71 + (1490781207349/1000000000000000000000000000 : ℝ)*base74 + (303766358065289657/100000000000000000000000000000000 : ℝ)*base75 + (1134178250234710343/100000000000000000000000000000000 : ℝ)*base78 + (186266954234710343/100000000000000000000000000000000 : ℝ)*base80 + (4285244941651/1000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (1692389/10000000000000000000000 : ℝ)*base89 + (1692389/10000000000000000000000 : ℝ)*base91 + (1692389/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11395125309776632970512879/2500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (865082827/100000000000000 : ℝ)*(base19) + (226259737/25000000000000 : ℝ)*(base23) + (73964363/25000000000000 : ℝ)*(lower1) + (24937681/25000000000000 : ℝ)*(upper3) + (9919733/100000000000000 : ℝ)*(lower4) + (112393227/100000000000000 : ℝ)*(upper5) + (109783392036511/2500000000000 : ℝ)*(major0) + (109783392036511/2500000000000 : ℝ)*(major1) + (109783392036511/2500000000000 : ℝ)*(major2) + (3876091/100000000000000 : ℝ)*(sp2) + (296393721441153/5000000000000 : ℝ)*(sp4) + (5927873563740233/100000000000000 : ℝ)*(sp5) + (5927873519908021/100000000000000 : ℝ)*(sp6) + (1427398391081397/50000000000000 : ℝ)*(sp7) + (1427398391081397/50000000000000 : ℝ)*(f.failure) + (296393721441153/5000000000000 : ℝ)*(f.sum) + (205685368397/150000000000000000000000000 : ℝ)*base65 + (1042868821054293/5000000000000000000000000000000 : ℝ)*base67 + (65141207508945707/5000000000000000000000000000000 : ℝ)*base70 + (266417989416054293/5000000000000000000000000000000 : ℝ)*base71 + (186097003903/150000000000000000000000000 : ℝ)*base74 + (647919965053945707/5000000000000000000000000000000 : ℝ)*base76 + (48046388333945707/5000000000000000000000000000000 : ℝ)*base78 + (14054343758945707/5000000000000000000000000000000 : ℝ)*base80 + (462883211503/150000000000000000000000000 : ℝ)*base82 + (22370629/5000000000000000000000 : ℝ)*base89 + (22370629/5000000000000000000000 : ℝ)*base91 + (22370629/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1319_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153823057/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14693/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11093/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2219/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14691/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1319_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1319_box_0 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-473726363/2500000000 : ℝ)*x 0 + (5390897643/10000000000 : ℝ)*x 1 + (2695448911/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (473726363/2500000000 : ℝ)^4279 ≤ (11228498665151/100000000000000 : ℝ)^3255 := by
    have hnat : (473726363 : ℕ)^4279*100000000000000^3255 ≤ 11228498665151^3255*2500000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      473726363 2500000000 11228498665151 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390897643/10000000000 : ℝ)^4279 ≤ (4438574969389/10000000000000 : ℝ)^3255 := by
    have hnat : (5390897643 : ℕ)^4279*10000000000000^3255 ≤ 4438574969389^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390897643 10000000000 4438574969389 10000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695448911/5000000000 : ℝ)^4279 ≤ (44385751631323/100000000000000 : ℝ)^3255 := by
    have hnat : (2695448911 : ℕ)^4279*100000000000000^3255 ≤ 44385751631323^3255*5000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695448911 5000000000 44385751631323 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-473726363/2500000000 : ℝ), (5390897643/10000000000 : ℝ), (2695448911/5000000000 : ℝ)] ![(11228498665151/100000000000000 : ℝ), (4438574969389/10000000000000 : ℝ), (44385751631323/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-473726363/2500000000 : ℝ)|^4279 ≤ (11228498665151/100000000000000 : ℝ)^3255
        have hw : |(-473726363/2500000000 : ℝ)|=(473726363/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390897643/10000000000 : ℝ)|^4279 ≤ (4438574969389/10000000000000 : ℝ)^3255
        have hw : |(5390897643/10000000000 : ℝ)|=(5390897643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695448911/5000000000 : ℝ)|^4279 ≤ (44385751631323/100000000000000 : ℝ)^3255
        have hw : |(2695448911/5000000000 : ℝ)|=(2695448911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_box_1 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5284826323/10000000000 : ℝ)*x 0 + (-1020054843/5000000000 : ℝ)*x 1 + (5390897581/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5284826323/10000000000 : ℝ)^4279 ≤ (43241240151537/100000000000000 : ℝ)^3255 := by
    have hnat : (5284826323 : ℕ)^4279*100000000000000^3255 ≤ 43241240151537^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5284826323 10000000000 43241240151537 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1020054843/5000000000 : ℝ)^4279 ≤ (6186505407181/50000000000000 : ℝ)^3255 := by
    have hnat : (1020054843 : ℕ)^4279*50000000000000^3255 ≤ 6186505407181^3255*5000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1020054843 5000000000 6186505407181 50000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390897581/10000000000 : ℝ)^4279 ≤ (44385749022823/100000000000000 : ℝ)^3255 := by
    have hnat : (5390897581 : ℕ)^4279*100000000000000^3255 ≤ 44385749022823^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390897581 10000000000 44385749022823 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5284826323/10000000000 : ℝ), (-1020054843/5000000000 : ℝ), (5390897581/10000000000 : ℝ)] ![(43241240151537/100000000000000 : ℝ), (6186505407181/50000000000000 : ℝ), (44385749022823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5284826323/10000000000 : ℝ)|^4279 ≤ (43241240151537/100000000000000 : ℝ)^3255
        have hw : |(5284826323/10000000000 : ℝ)|=(5284826323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1020054843/5000000000 : ℝ)|^4279 ≤ (6186505407181/50000000000000 : ℝ)^3255
        have hw : |(-1020054843/5000000000 : ℝ)|=(1020054843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390897581/10000000000 : ℝ)|^4279 ≤ (44385749022823/100000000000000 : ℝ)^3255
        have hw : |(5390897581/10000000000 : ℝ)|=(5390897581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_box_2 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (660603263/1250000000 : ℝ)*x 0 + (1078179547/2000000000 : ℝ)*x 1 + (-2040109773/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (660603263/1250000000 : ℝ)^4279 ≤ (4324123779593/10000000000000 : ℝ)^3255 := by
    have hnat : (660603263 : ℕ)^4279*10000000000000^3255 ≤ 4324123779593^3255*1250000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660603263 1250000000 4324123779593 10000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078179547/2000000000 : ℝ)^4279 ≤ (8877150137933/20000000000000 : ℝ)^3255 := by
    have hnat : (1078179547 : ℕ)^4279*20000000000000^3255 ≤ 8877150137933^3255*2000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078179547 2000000000 8877150137933 20000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2040109773/10000000000 : ℝ)^4279 ≤ (12373011507999/100000000000000 : ℝ)^3255 := by
    have hnat : (2040109773 : ℕ)^4279*100000000000000^3255 ≤ 12373011507999^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2040109773 10000000000 12373011507999 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(660603263/1250000000 : ℝ), (1078179547/2000000000 : ℝ), (-2040109773/10000000000 : ℝ)] ![(4324123779593/10000000000000 : ℝ), (8877150137933/20000000000000 : ℝ), (12373011507999/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(660603263/1250000000 : ℝ)|^4279 ≤ (4324123779593/10000000000000 : ℝ)^3255
        have hw : |(660603263/1250000000 : ℝ)|=(660603263/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078179547/2000000000 : ℝ)|^4279 ≤ (8877150137933/20000000000000 : ℝ)^3255
        have hw : |(1078179547/2000000000 : ℝ)|=(1078179547/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2040109773/10000000000 : ℝ)|^4279 ≤ (12373011507999/100000000000000 : ℝ)^3255
        have hw : |(-2040109773/10000000000 : ℝ)|=(2040109773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_box_3 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (70022109/156250000 : ℝ)*x 0 + (4262242311/10000000000 : ℝ)*x 1 + (106556061/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (70022109/156250000 : ℝ)^4279 ≤ (34813912541927/100000000000000 : ℝ)^3255 := by
    have hnat : (70022109 : ℕ)^4279*100000000000000^3255 ≤ 34813912541927^3255*156250000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70022109 156250000 34813912541927 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4262242311/10000000000 : ℝ)^4279 ≤ (32593043071323/100000000000000 : ℝ)^3255 := by
    have hnat : (4262242311 : ℕ)^4279*100000000000000^3255 ≤ 32593043071323^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4262242311 10000000000 32593043071323 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (106556061/250000000 : ℝ)^4279 ≤ (32593044368107/100000000000000 : ℝ)^3255 := by
    have hnat : (106556061 : ℕ)^4279*100000000000000^3255 ≤ 32593044368107^3255*250000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106556061 250000000 32593044368107 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(70022109/156250000 : ℝ), (4262242311/10000000000 : ℝ), (106556061/250000000 : ℝ)] ![(34813912541927/100000000000000 : ℝ), (32593043071323/100000000000000 : ℝ), (32593044368107/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(70022109/156250000 : ℝ)|^4279 ≤ (34813912541927/100000000000000 : ℝ)^3255
        have hw : |(70022109/156250000 : ℝ)|=(70022109/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4262242311/10000000000 : ℝ)|^4279 ≤ (32593043071323/100000000000000 : ℝ)^3255
        have hw : |(4262242311/10000000000 : ℝ)|=(4262242311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(106556061/250000000 : ℝ)|^4279 ≤ (32593044368107/100000000000000 : ℝ)^3255
        have hw : |(106556061/250000000 : ℝ)|=(106556061/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_box_4 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2235874207/10000000000 : ℝ)*x 0 + (1052878083/2000000000 : ℝ)*x 1 + (5264390883/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2235874207/10000000000 : ℝ)^4279 ≤ (348921806897/2500000000000 : ℝ)^3255 := by
    have hnat : (2235874207 : ℕ)^4279*2500000000000^3255 ≤ 348921806897^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2235874207 10000000000 348921806897 2500000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052878083/2000000000 : ℝ)^4279 ≤ (21510780667573/50000000000000 : ℝ)^3255 := by
    have hnat : (1052878083 : ℕ)^4279*50000000000000^3255 ≤ 21510780667573^3255*2000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052878083 2000000000 21510780667573 50000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264390883/10000000000 : ℝ)^4279 ≤ (21510783181457/50000000000000 : ℝ)^3255 := by
    have hnat : (5264390883 : ℕ)^4279*50000000000000^3255 ≤ 21510783181457^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264390883 10000000000 21510783181457 50000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2235874207/10000000000 : ℝ), (1052878083/2000000000 : ℝ), (5264390883/10000000000 : ℝ)] ![(348921806897/2500000000000 : ℝ), (21510780667573/50000000000000 : ℝ), (21510783181457/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2235874207/10000000000 : ℝ)|^4279 ≤ (348921806897/2500000000000 : ℝ)^3255
        have hw : |(-2235874207/10000000000 : ℝ)|=(2235874207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1052878083/2000000000 : ℝ)|^4279 ≤ (21510780667573/50000000000000 : ℝ)^3255
        have hw : |(1052878083/2000000000 : ℝ)|=(1052878083/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264390883/10000000000 : ℝ)|^4279 ≤ (21510783181457/50000000000000 : ℝ)^3255
        have hw : |(5264390883/10000000000 : ℝ)|=(5264390883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_box_5 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2686884543/5000000000 : ℝ)*x 0 + (-209070777/1000000000 : ℝ)*x 1 + (2632195367/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2686884543/5000000000 : ℝ)^4279 ≤ (22100224449811/50000000000000 : ℝ)^3255 := by
    have hnat : (2686884543 : ℕ)^4279*50000000000000^3255 ≤ 22100224449811^3255*5000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2686884543 5000000000 22100224449811 50000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209070777/1000000000 : ℝ)^4279 ≤ (1597248289707/12500000000000 : ℝ)^3255 := by
    have hnat : (209070777 : ℕ)^4279*12500000000000^3255 ≤ 1597248289707^3255*1000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209070777 1000000000 1597248289707 12500000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632195367/5000000000 : ℝ)^4279 ≤ (43021564762193/100000000000000 : ℝ)^3255 := by
    have hnat : (2632195367 : ℕ)^4279*100000000000000^3255 ≤ 43021564762193^3255*5000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632195367 5000000000 43021564762193 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2686884543/5000000000 : ℝ), (-209070777/1000000000 : ℝ), (2632195367/5000000000 : ℝ)] ![(22100224449811/50000000000000 : ℝ), (1597248289707/12500000000000 : ℝ), (43021564762193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2686884543/5000000000 : ℝ)|^4279 ≤ (22100224449811/50000000000000 : ℝ)^3255
        have hw : |(2686884543/5000000000 : ℝ)|=(2686884543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-209070777/1000000000 : ℝ)|^4279 ≤ (1597248289707/12500000000000 : ℝ)^3255
        have hw : |(-209070777/1000000000 : ℝ)|=(209070777/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632195367/5000000000 : ℝ)|^4279 ≤ (43021564762193/100000000000000 : ℝ)^3255
        have hw : |(2632195367/5000000000 : ℝ)|=(2632195367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_box_6 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1343442297/2500000000 : ℝ)*x 0 + (5264390623/10000000000 : ℝ)*x 1 + (-1045353891/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1343442297/2500000000 : ℝ)^4279 ≤ (4420045000253/10000000000000 : ℝ)^3255 := by
    have hnat : (1343442297 : ℕ)^4279*10000000000000^3255 ≤ 4420045000253^3255*2500000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343442297 2500000000 4420045000253 10000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264390623/10000000000 : ℝ)^4279 ≤ (4302156356971/10000000000000 : ℝ)^3255 := by
    have hnat : (5264390623 : ℕ)^4279*10000000000000^3255 ≤ 4302156356971^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264390623 10000000000 4302156356971 10000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1045353891/5000000000 : ℝ)^4279 ≤ (12777986414071/100000000000000 : ℝ)^3255 := by
    have hnat : (1045353891 : ℕ)^4279*100000000000000^3255 ≤ 12777986414071^3255*5000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045353891 5000000000 12777986414071 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1343442297/2500000000 : ℝ), (5264390623/10000000000 : ℝ), (-1045353891/5000000000 : ℝ)] ![(4420045000253/10000000000000 : ℝ), (4302156356971/10000000000000 : ℝ), (12777986414071/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1343442297/2500000000 : ℝ)|^4279 ≤ (4420045000253/10000000000000 : ℝ)^3255
        have hw : |(1343442297/2500000000 : ℝ)|=(1343442297/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264390623/10000000000 : ℝ)|^4279 ≤ (4302156356971/10000000000000 : ℝ)^3255
        have hw : |(5264390623/10000000000 : ℝ)|=(5264390623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1045353891/5000000000 : ℝ)|^4279 ≤ (12777986414071/100000000000000 : ℝ)^3255
        have hw : |(-1045353891/5000000000 : ℝ)|=(1045353891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_box_7 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4183038407/10000000000 : ℝ)*x 0 + (2205688183/5000000000 : ℝ)*x 1 + (551422023/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4183038407/10000000000 : ℝ)^4279 ≤ (3974896971917/12500000000000 : ℝ)^3255 := by
    have hnat : (4183038407 : ℕ)^4279*12500000000000^3255 ≤ 3974896971917^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4183038407 10000000000 3974896971917 12500000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2205688183/5000000000 : ℝ)^4279 ≤ (17050206514171/50000000000000 : ℝ)^3255 := by
    have hnat : (2205688183 : ℕ)^4279*50000000000000^3255 ≤ 17050206514171^3255*5000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2205688183 5000000000 17050206514171 50000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (551422023/1250000000 : ℝ)^4279 ≤ (8525102794717/25000000000000 : ℝ)^3255 := by
    have hnat : (551422023 : ℕ)^4279*25000000000000^3255 ≤ 8525102794717^3255*1250000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551422023 1250000000 8525102794717 25000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4183038407/10000000000 : ℝ), (2205688183/5000000000 : ℝ), (551422023/1250000000 : ℝ)] ![(3974896971917/12500000000000 : ℝ), (17050206514171/50000000000000 : ℝ), (8525102794717/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4183038407/10000000000 : ℝ)|^4279 ≤ (3974896971917/12500000000000 : ℝ)^3255
        have hw : |(4183038407/10000000000 : ℝ)|=(4183038407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2205688183/5000000000 : ℝ)|^4279 ≤ (17050206514171/50000000000000 : ℝ)^3255
        have hw : |(2205688183/5000000000 : ℝ)|=(2205688183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(551422023/1250000000 : ℝ)|^4279 ≤ (8525102794717/25000000000000 : ℝ)^3255
        have hw : |(551422023/1250000000 : ℝ)|=(551422023/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_box_8 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-135270871/625000000 : ℝ)*x 0 + (5177409461/10000000000 : ℝ)*x 1 + (5404926639/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (135270871/625000000 : ℝ)^4279 ≤ (13372788647229/100000000000000 : ℝ)^3255 := by
    have hnat : (135270871 : ℕ)^4279*100000000000000^3255 ≤ 13372788647229^3255*625000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135270871 625000000 13372788647229 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5177409461/10000000000 : ℝ)^4279 ≤ (10522388642393/25000000000000 : ℝ)^3255 := by
    have hnat : (5177409461 : ℕ)^4279*25000000000000^3255 ≤ 10522388642393^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177409461 10000000000 10522388642393 25000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5404926639/10000000000 : ℝ)^4279 ≤ (44537656765261/100000000000000 : ℝ)^3255 := by
    have hnat : (5404926639 : ℕ)^4279*100000000000000^3255 ≤ 44537656765261^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404926639 10000000000 44537656765261 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-135270871/625000000 : ℝ), (5177409461/10000000000 : ℝ), (5404926639/10000000000 : ℝ)] ![(13372788647229/100000000000000 : ℝ), (10522388642393/25000000000000 : ℝ), (44537656765261/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-135270871/625000000 : ℝ)|^4279 ≤ (13372788647229/100000000000000 : ℝ)^3255
        have hw : |(-135270871/625000000 : ℝ)|=(135270871/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5177409461/10000000000 : ℝ)|^4279 ≤ (10522388642393/25000000000000 : ℝ)^3255
        have hw : |(5177409461/10000000000 : ℝ)|=(5177409461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5404926639/10000000000 : ℝ)|^4279 ≤ (44537656765261/100000000000000 : ℝ)^3255
        have hw : |(5404926639/10000000000 : ℝ)|=(5404926639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_box_9 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5274957161/10000000000 : ℝ)*x 0 + (-101718227/500000000 : ℝ)*x 1 + (5404926689/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5274957161/10000000000 : ℝ)^4279 ≤ (43135116704407/100000000000000 : ℝ)^3255 := by
    have hnat : (5274957161 : ℕ)^4279*100000000000000^3255 ≤ 43135116704407^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274957161 10000000000 43135116704407 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (101718227/500000000 : ℝ)^4279 ≤ (6163612987461/50000000000000 : ℝ)^3255 := by
    have hnat : (101718227 : ℕ)^4279*50000000000000^3255 ≤ 6163612987461^3255*500000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      101718227 500000000 6163612987461 50000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5404926689/10000000000 : ℝ)^4279 ≤ (44537657306887/100000000000000 : ℝ)^3255 := by
    have hnat : (5404926689 : ℕ)^4279*100000000000000^3255 ≤ 44537657306887^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404926689 10000000000 44537657306887 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5274957161/10000000000 : ℝ), (-101718227/500000000 : ℝ), (5404926689/10000000000 : ℝ)] ![(43135116704407/100000000000000 : ℝ), (6163612987461/50000000000000 : ℝ), (44537657306887/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5274957161/10000000000 : ℝ)|^4279 ≤ (43135116704407/100000000000000 : ℝ)^3255
        have hw : |(5274957161/10000000000 : ℝ)|=(5274957161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-101718227/500000000 : ℝ)|^4279 ≤ (6163612987461/50000000000000 : ℝ)^3255
        have hw : |(-101718227/500000000 : ℝ)|=(101718227/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5404926689/10000000000 : ℝ)|^4279 ≤ (44537657306887/100000000000000 : ℝ)^3255
        have hw : |(5404926689/10000000000 : ℝ)|=(5404926689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_box_10 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5274957251/10000000000 : ℝ)*x 0 + (5404926627/10000000000 : ℝ)*x 1 + (-2034364503/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5274957251/10000000000 : ℝ)^4279 ≤ (5391889708987/12500000000000 : ℝ)^3255 := by
    have hnat : (5274957251 : ℕ)^4279*12500000000000^3255 ≤ 5391889708987^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274957251 10000000000 5391889708987 12500000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5404926627/10000000000 : ℝ)^4279 ≤ (44537656635271/100000000000000 : ℝ)^3255 := by
    have hnat : (5404926627 : ℕ)^4279*100000000000000^3255 ≤ 44537656635271^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404926627 10000000000 44537656635271 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2034364503/10000000000 : ℝ)^4279 ≤ (12327225680189/100000000000000 : ℝ)^3255 := by
    have hnat : (2034364503 : ℕ)^4279*100000000000000^3255 ≤ 12327225680189^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2034364503 10000000000 12327225680189 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5274957251/10000000000 : ℝ), (5404926627/10000000000 : ℝ), (-2034364503/10000000000 : ℝ)] ![(5391889708987/12500000000000 : ℝ), (44537656635271/100000000000000 : ℝ), (12327225680189/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5274957251/10000000000 : ℝ)|^4279 ≤ (5391889708987/12500000000000 : ℝ)^3255
        have hw : |(5274957251/10000000000 : ℝ)|=(5274957251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5404926627/10000000000 : ℝ)|^4279 ≤ (44537656635271/100000000000000 : ℝ)^3255
        have hw : |(5404926627/10000000000 : ℝ)|=(5404926627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2034364503/10000000000 : ℝ)|^4279 ≤ (12327225680189/100000000000000 : ℝ)^3255
        have hw : |(-2034364503/10000000000 : ℝ)|=(2034364503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_box_11 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (451394321/1000000000 : ℝ)*x 0 + (4245690733/10000000000 : ℝ)*x 1 + (849138137/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (451394321/1000000000 : ℝ)^4279 ≤ (7029296681117/20000000000000 : ℝ)^3255 := by
    have hnat : (451394321 : ℕ)^4279*20000000000000^3255 ≤ 7029296681117^3255*1000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451394321 1000000000 7029296681117 20000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4245690733/10000000000 : ℝ)^4279 ≤ (16213379265121/50000000000000 : ℝ)^3255 := by
    have hnat : (4245690733 : ℕ)^4279*50000000000000^3255 ≤ 16213379265121^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4245690733 10000000000 16213379265121 50000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (849138137/2000000000 : ℝ)^4279 ≤ (32426758048307/100000000000000 : ℝ)^3255 := by
    have hnat : (849138137 : ℕ)^4279*100000000000000^3255 ≤ 32426758048307^3255*2000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849138137 2000000000 32426758048307 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(451394321/1000000000 : ℝ), (4245690733/10000000000 : ℝ), (849138137/2000000000 : ℝ)] ![(7029296681117/20000000000000 : ℝ), (16213379265121/50000000000000 : ℝ), (32426758048307/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(451394321/1000000000 : ℝ)|^4279 ≤ (7029296681117/20000000000000 : ℝ)^3255
        have hw : |(451394321/1000000000 : ℝ)|=(451394321/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4245690733/10000000000 : ℝ)|^4279 ≤ (16213379265121/50000000000000 : ℝ)^3255
        have hw : |(4245690733/10000000000 : ℝ)|=(4245690733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(849138137/2000000000 : ℝ)|^4279 ≤ (32426758048307/100000000000000 : ℝ)^3255
        have hw : |(849138137/2000000000 : ℝ)|=(849138137/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_box_12 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1966828791/10000000000 : ℝ)*x 0 + (68445263/125000000 : ℝ)*x 1 + (5253340713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1966828791/10000000000 : ℝ)^4279 ≤ (589604121141/5000000000000 : ℝ)^3255 := by
    have hnat : (1966828791 : ℕ)^4279*5000000000000^3255 ≤ 589604121141^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1966828791 10000000000 589604121141 5000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (68445263/125000000 : ℝ)^4279 ≤ (5663128124023/12500000000000 : ℝ)^3255 := by
    have hnat : (68445263 : ℕ)^4279*12500000000000^3255 ≤ 5663128124023^3255*125000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68445263 125000000 5663128124023 12500000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5253340713/10000000000 : ℝ)^4279 ≤ (8580578512039/20000000000000 : ℝ)^3255 := by
    have hnat : (5253340713 : ℕ)^4279*20000000000000^3255 ≤ 8580578512039^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253340713 10000000000 8580578512039 20000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1966828791/10000000000 : ℝ), (68445263/125000000 : ℝ), (5253340713/10000000000 : ℝ)] ![(589604121141/5000000000000 : ℝ), (5663128124023/12500000000000 : ℝ), (8580578512039/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1966828791/10000000000 : ℝ)|^4279 ≤ (589604121141/5000000000000 : ℝ)^3255
        have hw : |(-1966828791/10000000000 : ℝ)|=(1966828791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(68445263/125000000 : ℝ)|^4279 ≤ (5663128124023/12500000000000 : ℝ)^3255
        have hw : |(68445263/125000000 : ℝ)|=(68445263/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5253340713/10000000000 : ℝ)|^4279 ≤ (8580578512039/20000000000000 : ℝ)^3255
        have hw : |(5253340713/10000000000 : ℝ)|=(5253340713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_box_13 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1345383703/2500000000 : ℝ)*x 0 + (-1047511333/5000000000 : ℝ)*x 1 + (1313335279/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1345383703/2500000000 : ℝ)^4279 ≤ (442844373779/1000000000000 : ℝ)^3255 := by
    have hnat : (1345383703 : ℕ)^4279*1000000000000^3255 ≤ 442844373779^3255*2500000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1345383703 2500000000 442844373779 1000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1047511333/5000000000 : ℝ)^4279 ≤ (800791607527/6250000000000 : ℝ)^3255 := by
    have hnat : (1047511333 : ℕ)^4279*6250000000000^3255 ≤ 800791607527^3255*5000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047511333 5000000000 800791607527 6250000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1313335279/2500000000 : ℝ)^4279 ≤ (42902896886801/100000000000000 : ℝ)^3255 := by
    have hnat : (1313335279 : ℕ)^4279*100000000000000^3255 ≤ 42902896886801^3255*2500000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313335279 2500000000 42902896886801 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1345383703/2500000000 : ℝ), (-1047511333/5000000000 : ℝ), (1313335279/2500000000 : ℝ)] ![(442844373779/1000000000000 : ℝ), (800791607527/6250000000000 : ℝ), (42902896886801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1345383703/2500000000 : ℝ)|^4279 ≤ (442844373779/1000000000000 : ℝ)^3255
        have hw : |(1345383703/2500000000 : ℝ)|=(1345383703/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1047511333/5000000000 : ℝ)|^4279 ≤ (800791607527/6250000000000 : ℝ)^3255
        have hw : |(-1047511333/5000000000 : ℝ)|=(1047511333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1313335279/2500000000 : ℝ)|^4279 ≤ (42902896886801/100000000000000 : ℝ)^3255
        have hw : |(1313335279/2500000000 : ℝ)|=(1313335279/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_box_14 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2690767527/5000000000 : ℝ)*x 0 + (5253341373/10000000000 : ℝ)*x 1 + (-2095021997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2690767527/5000000000 : ℝ)^4279 ≤ (44284439995791/100000000000000 : ℝ)^3255 := by
    have hnat : (2690767527 : ℕ)^4279*100000000000000^3255 ≤ 44284439995791^3255*5000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2690767527 5000000000 44284439995791 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5253341373/10000000000 : ℝ)^4279 ≤ (83794725871/195312500000 : ℝ)^3255 := by
    have hnat : (5253341373 : ℕ)^4279*195312500000^3255 ≤ 83794725871^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253341373 10000000000 83794725871 195312500000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2095021997/10000000000 : ℝ)^4279 ≤ (6406330170923/50000000000000 : ℝ)^3255 := by
    have hnat : (2095021997 : ℕ)^4279*50000000000000^3255 ≤ 6406330170923^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2095021997 10000000000 6406330170923 50000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2690767527/5000000000 : ℝ), (5253341373/10000000000 : ℝ), (-2095021997/10000000000 : ℝ)] ![(44284439995791/100000000000000 : ℝ), (83794725871/195312500000 : ℝ), (6406330170923/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2690767527/5000000000 : ℝ)|^4279 ≤ (44284439995791/100000000000000 : ℝ)^3255
        have hw : |(2690767527/5000000000 : ℝ)|=(2690767527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5253341373/10000000000 : ℝ)|^4279 ≤ (83794725871/195312500000 : ℝ)^3255
        have hw : |(5253341373/10000000000 : ℝ)|=(5253341373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2095021997/10000000000 : ℝ)|^4279 ≤ (6406330170923/50000000000000 : ℝ)^3255
        have hw : |(-2095021997/10000000000 : ℝ)|=(2095021997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_box_15 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (166261229/400000000 : ℝ)*x 0 + (138262227/312500000 : ℝ)*x 1 + (276524459/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (166261229/400000000 : ℝ)^4279 ≤ (15767268549331/50000000000000 : ℝ)^3255 := by
    have hnat : (166261229 : ℕ)^4279*50000000000000^3255 ≤ 15767268549331^3255*400000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166261229 400000000 15767268549331 50000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (138262227/312500000 : ℝ)^4279 ≤ (34232731035451/100000000000000 : ℝ)^3255 := by
    have hnat : (138262227 : ℕ)^4279*100000000000000^3255 ≤ 34232731035451^3255*312500000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138262227 312500000 34232731035451 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (276524459/625000000 : ℝ)^4279 ≤ (855818296229/2500000000000 : ℝ)^3255 := by
    have hnat : (276524459 : ℕ)^4279*2500000000000^3255 ≤ 855818296229^3255*625000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276524459 625000000 855818296229 2500000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(166261229/400000000 : ℝ), (138262227/312500000 : ℝ), (276524459/625000000 : ℝ)] ![(15767268549331/50000000000000 : ℝ), (34232731035451/100000000000000 : ℝ), (855818296229/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(166261229/400000000 : ℝ)|^4279 ≤ (15767268549331/50000000000000 : ℝ)^3255
        have hw : |(166261229/400000000 : ℝ)|=(166261229/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(138262227/312500000 : ℝ)|^4279 ≤ (34232731035451/100000000000000 : ℝ)^3255
        have hw : |(138262227/312500000 : ℝ)|=(138262227/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(276524459/625000000 : ℝ)|^4279 ≤ (855818296229/2500000000000 : ℝ)^3255
        have hw : |(276524459/625000000 : ℝ)|=(276524459/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1319_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153823057/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14691/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2219/20000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62847/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58897/100000 : ℝ) ∧ (79819/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (42131/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14691/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2219/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14691/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2219/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14691/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2219/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14691/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2219/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14691/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2219/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14691/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2219/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2219/20000 : ℝ) ^ (2139/512 : ℝ) ≤ (512584570561603/5000000000000000000 : ℝ) := by
    have hpowers : (2219/20000 : ℝ)^2139 ≤ (512584570561603/5000000000000000000 : ℝ)^512 := by
      have hnat : (2219 : ℕ)^2139*5000000000000000000^512 ≤ 512584570561603^512*20000^2139 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2219 20000 512584570561603 5000000000000000000 2139 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2219/20000 : ℝ)) (X := (512584570561603/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2139 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14691/100000 : ℝ) ^ (2139/512 : ℝ) ≤ (16562726603105527/50000000000000000000 : ℝ) := by
    have hpowers : (14691/100000 : ℝ)^2139 ≤ (16562726603105527/50000000000000000000 : ℝ)^512 := by
      have hnat : (14691 : ℕ)^2139*50000000000000000000^512 ≤ 16562726603105527^512*100000^2139 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14691 100000 16562726603105527 50000000000000000000 2139 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14691/100000 : ℝ)) (X := (16562726603105527/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2139 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500512584570561603/2500000000000000000 : ℝ) ≤ (500024536964729/500000000000000 : ℝ) ^ (2139/512 : ℝ) := by
    have hpowers : (2500512584570561603/2500000000000000000 : ℝ)^512 ≤ (500024536964729/500000000000000 : ℝ)^2139 := by
      have hnat : (2500512584570561603 : ℕ)^512*500000000000000^2139 ≤ 500024536964729^2139*2500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500512584570561603 2500000000000000000 500024536964729 500000000000000 512 2139 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500024536964729/500000000000000 : ℝ)) (X := (2500512584570561603/2500000000000000000 : ℝ)) (by norm_num) 2139 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50021688572308721557/50000000000000000000 : ℝ) ≤ (400041524890357/400000000000000 : ℝ) ^ (2139/512 : ℝ) := by
    have hpowers : (50021688572308721557/50000000000000000000 : ℝ)^512 ≤ (400041524890357/400000000000000 : ℝ)^2139 := by
      have hnat : (50021688572308721557 : ℕ)^512*400000000000000^2139 ≤ 400041524890357^2139*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021688572308721557 50000000000000000000 400041524890357 400000000000000 512 2139 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400041524890357/400000000000000 : ℝ)) (X := (50021688572308721557/50000000000000000000 : ℝ)) (by norm_num) 2139 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016562726603105527/25000000000000000000 : ℝ) ≤ (1000158550522327/1000000000000000 : ℝ) ^ (2139/512 : ℝ) := by
    have hpowers : (25016562726603105527/25000000000000000000 : ℝ)^512 ≤ (1000158550522327/1000000000000000 : ℝ)^2139 := by
      have hnat : (25016562726603105527 : ℕ)^512*1000000000000000^2139 ≤ 1000158550522327^2139*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016562726603105527 25000000000000000000 1000158550522327 1000000000000000 512 2139 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000158550522327/1000000000000000 : ℝ)) (X := (25016562726603105527/25000000000000000000 : ℝ)) (by norm_num) 2139 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(512584570561603/5000000000000000000 : ℝ) ≤ ((3594961827052449413/3596000000000000000 : ℝ)+2*(109476592869/71920000000000 : ℝ)*(2219/20000 : ℝ))^(2139/512 : ℝ) := by
    rw [show (3594961827052449413/3596000000000000000 : ℝ)+2*(109476592869/71920000000000 : ℝ)*(2219/20000 : ℝ)=(500024536964729/500000000000000 : ℝ) by norm_num, show 1+2*(512584570561603/5000000000000000000 : ℝ)=(2500512584570561603/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16562726603105527/50000000000000000000 : ℝ)+(512584570561603/5000000000000000000 : ℝ) ≤ ((3594961827052449413/3596000000000000000 : ℝ)+(109476592869/71920000000000 : ℝ)*((14691/100000 : ℝ)+(2219/20000 : ℝ)))^(2139/512 : ℝ) := by
    rw [show (3594961827052449413/3596000000000000000 : ℝ)+(109476592869/71920000000000 : ℝ)*((14691/100000 : ℝ)+(2219/20000 : ℝ))=(400041524890357/400000000000000 : ℝ) by norm_num, show 1+(16562726603105527/50000000000000000000 : ℝ)+(512584570561603/5000000000000000000 : ℝ)=(50021688572308721557/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16562726603105527/50000000000000000000 : ℝ) ≤ ((3594961827052449413/3596000000000000000 : ℝ)+2*(109476592869/71920000000000 : ℝ)*(14691/100000 : ℝ))^(2139/512 : ℝ) := by
    rw [show (3594961827052449413/3596000000000000000 : ℝ)+2*(109476592869/71920000000000 : ℝ)*(14691/100000 : ℝ)=(1000158550522327/1000000000000000 : ℝ) by norm_num, show 1+2*(16562726603105527/50000000000000000000 : ℝ)=(25016562726603105527/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3594961827052449413/3596000000000000000 : ℝ)*(X 1 0+X 2 0)+(109476592869/71920000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2139/512 : ℝ)) (lo := (2219/20000 : ℝ)) (hi := (14691/100000 : ℝ)) (c := (3594961827052449413/3596000000000000000 : ℝ)) (alpha := (109476592869/71920000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3594961827052449413/3596000000000000000 : ℝ)*(X 0 1+X 2 1)+(109476592869/71920000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2139/512 : ℝ)) (lo := (2219/20000 : ℝ)) (hi := (14691/100000 : ℝ)) (c := (3594961827052449413/3596000000000000000 : ℝ)) (alpha := (109476592869/71920000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3594961827052449413/3596000000000000000 : ℝ)*(X 0 2+X 1 2)+(109476592869/71920000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2139/512 : ℝ)) (lo := (2219/20000 : ℝ)) (hi := (14691/100000 : ℝ)) (c := (3594961827052449413/3596000000000000000 : ℝ)) (alpha := (109476592869/71920000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-473726363/2500000000 : ℝ)*X 0 0+(5390897643/10000000000 : ℝ)*X 0 1+(2695448911/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5284826323/10000000000 : ℝ)*X 1 0+(-1020054843/5000000000 : ℝ)*X 1 1+(5390897581/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((660603263/1250000000 : ℝ)*X 2 0+(1078179547/2000000000 : ℝ)*X 2 1+(-2040109773/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((70022109/156250000 : ℝ)*X 0 0+(4262242311/10000000000 : ℝ)*X 0 1+(106556061/250000000 : ℝ)*X 0 2+(70022109/156250000 : ℝ)*X 1 0+(4262242311/10000000000 : ℝ)*X 1 1+(106556061/250000000 : ℝ)*X 1 2+(70022109/156250000 : ℝ)*X 2 0+(4262242311/10000000000 : ℝ)*X 2 1+(106556061/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2235874207/10000000000 : ℝ)*X 0 0+(1052878083/2000000000 : ℝ)*X 0 1+(5264390883/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2686884543/5000000000 : ℝ)*X 1 0+(-209070777/1000000000 : ℝ)*X 1 1+(2632195367/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1343442297/2500000000 : ℝ)*X 2 0+(5264390623/10000000000 : ℝ)*X 2 1+(-1045353891/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4183038407/10000000000 : ℝ)*X 0 0+(2205688183/5000000000 : ℝ)*X 0 1+(551422023/1250000000 : ℝ)*X 0 2+(4183038407/10000000000 : ℝ)*X 1 0+(2205688183/5000000000 : ℝ)*X 1 1+(551422023/1250000000 : ℝ)*X 1 2+(4183038407/10000000000 : ℝ)*X 2 0+(2205688183/5000000000 : ℝ)*X 2 1+(551422023/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-135270871/625000000 : ℝ)*X 0 0+(5177409461/10000000000 : ℝ)*X 0 1+(5404926639/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5274957161/10000000000 : ℝ)*X 1 0+(-101718227/500000000 : ℝ)*X 1 1+(5404926689/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5274957251/10000000000 : ℝ)*X 2 0+(5404926627/10000000000 : ℝ)*X 2 1+(-2034364503/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((451394321/1000000000 : ℝ)*X 0 0+(4245690733/10000000000 : ℝ)*X 0 1+(849138137/2000000000 : ℝ)*X 0 2+(451394321/1000000000 : ℝ)*X 1 0+(4245690733/10000000000 : ℝ)*X 1 1+(849138137/2000000000 : ℝ)*X 1 2+(451394321/1000000000 : ℝ)*X 2 0+(4245690733/10000000000 : ℝ)*X 2 1+(849138137/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1966828791/10000000000 : ℝ)*X 0 0+(68445263/125000000 : ℝ)*X 0 1+(5253340713/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1345383703/2500000000 : ℝ)*X 1 0+(-1047511333/5000000000 : ℝ)*X 1 1+(1313335279/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2690767527/5000000000 : ℝ)*X 2 0+(5253341373/10000000000 : ℝ)*X 2 1+(-2095021997/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((166261229/400000000 : ℝ)*X 0 0+(138262227/312500000 : ℝ)*X 0 1+(276524459/625000000 : ℝ)*X 0 2+(166261229/400000000 : ℝ)*X 1 0+(138262227/312500000 : ℝ)*X 1 1+(276524459/625000000 : ℝ)*X 1 2+(166261229/400000000 : ℝ)*X 2 0+(138262227/312500000 : ℝ)*X 2 1+(276524459/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62847/100000 : ℝ) ≤ (-112994401166672859009882569418069/179800000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4053309/25000000000000 : ℝ)*(lower0) + (27644901/100000000000000 : ℝ)*(upper1) + (4985151/100000000000000 : ℝ)*(lower2) + (1242689/5000000000000 : ℝ)*(lower3) + (289475711534703/10000000000000 : ℝ)*(major0) + (289475711534703/10000000000000 : ℝ)*(major1) + (2894757115347031/100000000000000 : ℝ)*(major2) + (3944819863/100000000000000 : ℝ)*(sp2) + (513904893/25000000000000 : ℝ)*(sp3) + (1964291141073507/50000000000000 : ℝ)*(sp4) + (392858774566189/10000000000000 : ℝ)*(sp5) + (3928583800842027/100000000000000 : ℝ)*(sp6) + (940936297128123/50000000000000 : ℝ)*(sp7) + (5463514877/100000000000000 : ℝ)*(sp12) + (940937324937909/50000000000000 : ℝ)*(f.failure) + (392858774566189/10000000000000 : ℝ)*(f.sum) + (28046266440521/7192000000000000000000000000 : ℝ)*base65 + (394165558304105661/35960000000000000000000000000000 : ℝ)*base68 + (1916309396643542803/359600000000000000000000000000000 : ℝ)*base69 + (284085062195465661/35960000000000000000000000000000 : ℝ)*base72 + (5198385609567/7192000000000000000000000000 : ℝ)*base74 + (2340505568362342803/359600000000000000000000000000000 : ℝ)*base75 + (4098380713428731/1160000000000000000000000000000 : ℝ)*base78 + (3332198198548731/1160000000000000000000000000000 : ℝ)*base80 + (3131794539803/1798000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (2432187/5000000000000000000000 : ℝ)*base90 + (2432187/5000000000000000000000 : ℝ)*base92 + (52432187/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (58897/100000 : ℝ) ≤ (1654699522427335082733463485651/2809375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4609759/100000000000000 : ℝ)*(lower0) + (6443573/25000000000000 : ℝ)*(upper2) + (9271181/20000000000000 : ℝ)*(lower4) + (13914417/100000000000000 : ℝ)*(lower5) + (23145922429183/781250000000 : ℝ)*(major0) + (23145922429183/781250000000 : ℝ)*(major1) + (23145922429183/781250000000 : ℝ)*(major2) + (3979687754002803/100000000000000 : ℝ)*(sp0) + (397967794946293/10000000000000 : ℝ)*(sp1) + (497461646717209/12500000000000 : ℝ)*(sp2) + (481506968279267/25000000000000 : ℝ)*(sp3) + (31670263/1562500000000 : ℝ)*(sp7) + (15224274741/100000000000000 : ℝ)*(sp9) + (5419734869/100000000000000 : ℝ)*(sp12) + (19260299000139/1000000000000 : ℝ)*(f.failure) + (497461646717209/12500000000000 : ℝ)*(f.sum) + (5314547223221/899000000000000000000000000 : ℝ)*base65 + (402371139287/2832031250000000000000000000 : ℝ)*base67 + (11911717612033/45312500000000000000000000000 : ℝ)*base70 + (380912222469217/45312500000000000000000000000 : ℝ)*base71 + (904629975149/224750000000000000000000000 : ℝ)*base74 + (240586831975467/45312500000000000000000000000 : ℝ)*base75 + (400437936460309/90625000000000000000000000000 : ℝ)*base77 + (262881120727191/90625000000000000000000000000 : ℝ)*base80 + (165807509673/112375000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (404923/100000000000000000000 : ℝ)*base89 + (404923/100000000000000000000 : ℝ)*base91 + (404923/100000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (79819/100000 : ℝ) ≤ (143518518861591308003767756944543/179800000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (874891/100000000000000 : ℝ)*(lower2) + (11707899/100000000000000 : ℝ)*(lower3) + (15391371/50000000000000 : ℝ)*(upper4) + (53437/5000000000000 : ℝ)*(lower5) + (409463005768271/12500000000000 : ℝ)*(major0) + (409463005768271/12500000000000 : ℝ)*(major1) + (3275704046146169/100000000000000 : ℝ)*(major2) + (24010270979/100000000000000 : ℝ)*(sp1) + (4001554263/25000000000000 : ℝ)*(sp2) + (1850630099/25000000000000 : ℝ)*(sp3) + (2197636845261371/50000000000000 : ℝ)*(sp8) + (4395249680251763/100000000000000 : ℝ)*(sp9) + (439525768430569/10000000000000 : ℝ)*(sp10) + (1064759966174317/50000000000000 : ℝ)*(sp11) + (212952733486903/10000000000000 : ℝ)*(f.failure) + (2197636845261371/50000000000000 : ℝ)*(f.sum) + (3363322504591/1438400000000000000000000000 : ℝ)*base66 + (115575099894643827/44950000000000000000000000000000 : ℝ)*base68 + (5616650000336951203/359600000000000000000000000000000 : ℝ)*base70 + (327780920323156173/44950000000000000000000000000000 : ℝ)*base71 + (6674056884433/1438400000000000000000000000 : ℝ)*base73 + (1967601940669751203/359600000000000000000000000000000 : ℝ)*base76 + (63925827698883067/1450000000000000000000000000000 : ℝ)*base78 + (10952918965183067/1450000000000000000000000000000 : ℝ)*base80 + (54064943699/14500000000000000000000000 : ℝ)*base82 + (8922471/1000000000000000000000 : ℝ)*base89 + (8922471/1000000000000000000000 : ℝ)*base91 + (1077529/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-42131/50000 : ℝ) ≤ (-30299680758990321508667267678697/35960000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (16367669/100000000000000 : ℝ)*(lower0) + (61088259/100000000000000 : ℝ)*(lower1) + (249069503/100000000000000 : ℝ)*(lower2) + (97788613/50000000000000 : ℝ)*(upper5) + (1655953014192943/50000000000000 : ℝ)*(major0) + (1655953014192943/50000000000000 : ℝ)*(major1) + (3311906028385887/100000000000000 : ℝ)*(major2) + (1452568897/6250000000000 : ℝ)*(sp0) + (11283367371/6250000000000 : ℝ)*(sp5) + (6490542669/50000000000000 : ℝ)*(sp7) + (2249406563110647/50000000000000 : ℝ)*(sp12) + (449865583344571/10000000000000 : ℝ)*(sp13) + (2249418183661823/50000000000000 : ℝ)*(sp14) + (2153049175510527/100000000000000 : ℝ)*(sp15) + (430612431319173/20000000000000 : ℝ)*(f.failure) + (2249418183661823/50000000000000 : ℝ)*(f.sum) + (30136898169001/7192000000000000000000000000 : ℝ)*base65 + (1580010087249432541/179800000000000000000000000000000 : ℝ)*base68 + (2644298697275734331/359600000000000000000000000000000 : ℝ)*base69 + (1346579653404432541/179800000000000000000000000000000 : ℝ)*base72 + (49092770300317/1438400000000000000000000000 : ℝ)*base73 + (1289096681762934331/359600000000000000000000000000000 : ℝ)*base75 + (47358655344921211/5800000000000000000000000000000 : ℝ)*base78 + (60174093305121211/5800000000000000000000000000000 : ℝ)*base80 + (1191367025903/1798000000000000000000000000 : ℝ)*base81 + (13571861/2000000000000000000000 : ℝ)*base89 + (13571861/2000000000000000000000 : ℝ)*base91 + (6428139/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1319_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153823057/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14691/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2219/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62847/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58897/100000 : ℝ) else (79819/100000 : ℝ) ≤ X j i ∧ X j i ≤ (42131/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1319_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1319_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153823057/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7351/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2771/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62847/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58897/100000 : ℝ) else (79819/100000 : ℝ) ≤ X j i ∧ X j i ≤ (42131/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1319_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1319_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1319_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153823057/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7351/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2771/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62847/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58897/100000 : ℝ) else (79819/100000 : ℝ) ≤ X j i ∧ X j i ≤ (42131/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1319_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
