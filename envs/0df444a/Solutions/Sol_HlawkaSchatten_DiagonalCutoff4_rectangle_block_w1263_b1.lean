-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1263_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:55:36.548348+00:00
-- url     : https://prove2.me/submissions/7c6893f5-bafd-4b35-bfa4-ba234958682f

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
theorem support_rectangle_w1263_s3_0 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-263457027/1250000000 : ℝ)*x 0 + (5417853643/10000000000 : ℝ)*x 1 + (5242195403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (263457027/1250000000 : ℝ)^1057 ≤ (12814033164447/100000000000000 : ℝ)^801 := by
    have hnat : (263457027 : ℕ)^1057*100000000000000^801 ≤ 12814033164447^801*1250000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263457027 1250000000 12814033164447 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5417853643/10000000000 : ℝ)^1057 ≤ (4454083260947/10000000000000 : ℝ)^801 := by
    have hnat : (5417853643 : ℕ)^1057*10000000000000^801 ≤ 4454083260947^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417853643 10000000000 4454083260947 10000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242195403/10000000000 : ℝ)^1057 ≤ (21322567107539/50000000000000 : ℝ)^801 := by
    have hnat : (5242195403 : ℕ)^1057*50000000000000^801 ≤ 21322567107539^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242195403 10000000000 21322567107539 50000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-263457027/1250000000 : ℝ), (5417853643/10000000000 : ℝ), (5242195403/10000000000 : ℝ)] ![(12814033164447/100000000000000 : ℝ), (4454083260947/10000000000000 : ℝ), (21322567107539/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-263457027/1250000000 : ℝ)|^1057 ≤ (12814033164447/100000000000000 : ℝ)^801
        have hw : |(-263457027/1250000000 : ℝ)|=(263457027/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5417853643/10000000000 : ℝ)|^1057 ≤ (4454083260947/10000000000000 : ℝ)^801
        have hw : |(5417853643/10000000000 : ℝ)|=(5417853643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242195403/10000000000 : ℝ)|^1057 ≤ (21322567107539/50000000000000 : ℝ)^801
        have hw : |(5242195403/10000000000 : ℝ)|=(5242195403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s3_1 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (133775787/250000000 : ℝ)*x 0 + (-2197232649/10000000000 : ℝ)*x 1 + (655274439/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133775787/250000000 : ℝ)^1057 ≤ (43817338759857/100000000000000 : ℝ)^801 := by
    have hnat : (133775787 : ℕ)^1057*100000000000000^801 ≤ 43817338759857^801*250000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133775787 250000000 43817338759857 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2197232649/10000000000 : ℝ)^1057 ≤ (270750516761/2000000000000 : ℝ)^801 := by
    have hnat : (2197232649 : ℕ)^1057*2000000000000^801 ≤ 270750516761^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2197232649 10000000000 270750516761 2000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655274439/1250000000 : ℝ)^1057 ≤ (1332660480787/3125000000000 : ℝ)^801 := by
    have hnat : (655274439 : ℕ)^1057*3125000000000^801 ≤ 1332660480787^801*1250000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655274439 1250000000 1332660480787 3125000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133775787/250000000 : ℝ), (-2197232649/10000000000 : ℝ), (655274439/1250000000 : ℝ)] ![(43817338759857/100000000000000 : ℝ), (270750516761/2000000000000 : ℝ), (1332660480787/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133775787/250000000 : ℝ)|^1057 ≤ (43817338759857/100000000000000 : ℝ)^801
        have hw : |(133775787/250000000 : ℝ)|=(133775787/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2197232649/10000000000 : ℝ)|^1057 ≤ (270750516761/2000000000000 : ℝ)^801
        have hw : |(-2197232649/10000000000 : ℝ)|=(2197232649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655274439/1250000000 : ℝ)|^1057 ≤ (1332660480787/3125000000000 : ℝ)^801
        have hw : |(655274439/1250000000 : ℝ)|=(655274439/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s3_2 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (267551573/500000000 : ℝ)*x 0 + (1310548999/2500000000 : ℝ)*x 1 + (-2197232037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267551573/500000000 : ℝ)^1057 ≤ (342322957373/781250000000 : ℝ)^801 := by
    have hnat : (267551573 : ℕ)^1057*781250000000^801 ≤ 342322957373^801*500000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267551573 500000000 342322957373 781250000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310548999/2500000000 : ℝ)^1057 ≤ (8529028116177/20000000000000 : ℝ)^801 := by
    have hnat : (1310548999 : ℕ)^1057*20000000000000^801 ≤ 8529028116177^801*2500000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310548999 2500000000 8529028116177 20000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2197232037/10000000000 : ℝ)^1057 ≤ (3384380215579/25000000000000 : ℝ)^801 := by
    have hnat : (2197232037 : ℕ)^1057*25000000000000^801 ≤ 3384380215579^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2197232037 10000000000 3384380215579 25000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267551573/500000000 : ℝ), (1310548999/2500000000 : ℝ), (-2197232037/10000000000 : ℝ)] ![(342322957373/781250000000 : ℝ), (8529028116177/20000000000000 : ℝ), (3384380215579/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267551573/500000000 : ℝ)|^1057 ≤ (342322957373/781250000000 : ℝ)^801
        have hw : |(267551573/500000000 : ℝ)|=(267551573/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310548999/2500000000 : ℝ)|^1057 ≤ (8529028116177/20000000000000 : ℝ)^801
        have hw : |(1310548999/2500000000 : ℝ)|=(1310548999/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2197232037/10000000000 : ℝ)|^1057 ≤ (3384380215579/25000000000000 : ℝ)^801
        have hw : |(-2197232037/10000000000 : ℝ)|=(2197232037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s3_3 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4346300881/10000000000 : ℝ)*x 0 + (521371269/1250000000 : ℝ)*x 1 + (2264374449/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4346300881/10000000000 : ℝ)^1057 ≤ (33301415308183/100000000000000 : ℝ)^801 := by
    have hnat : (4346300881 : ℕ)^1057*100000000000000^801 ≤ 33301415308183^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4346300881 10000000000 33301415308183 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (521371269/1250000000 : ℝ)^1057 ≤ (31540216038053/100000000000000 : ℝ)^801 := by
    have hnat : (521371269 : ℕ)^1057*100000000000000^801 ≤ 31540216038053^801*1250000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521371269 1250000000 31540216038053 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2264374449/5000000000 : ℝ)^1057 ≤ (35158368643789/100000000000000 : ℝ)^801 := by
    have hnat : (2264374449 : ℕ)^1057*100000000000000^801 ≤ 35158368643789^801*5000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2264374449 5000000000 35158368643789 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4346300881/10000000000 : ℝ), (521371269/1250000000 : ℝ), (2264374449/5000000000 : ℝ)] ![(33301415308183/100000000000000 : ℝ), (31540216038053/100000000000000 : ℝ), (35158368643789/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4346300881/10000000000 : ℝ)|^1057 ≤ (33301415308183/100000000000000 : ℝ)^801
        have hw : |(4346300881/10000000000 : ℝ)|=(4346300881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(521371269/1250000000 : ℝ)|^1057 ≤ (31540216038053/100000000000000 : ℝ)^801
        have hw : |(521371269/1250000000 : ℝ)|=(521371269/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2264374449/5000000000 : ℝ)|^1057 ≤ (35158368643789/100000000000000 : ℝ)^801
        have hw : |(2264374449/5000000000 : ℝ)|=(2264374449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s3_4 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2107670181/10000000000 : ℝ)*x 0 + (2621412833/5000000000 : ℝ)*x 1 + (5417219633/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2107670181/10000000000 : ℝ)^1057 ≤ (12814145203633/100000000000000 : ℝ)^801 := by
    have hnat : (2107670181 : ℕ)^1057*100000000000000^801 ≤ 12814145203633^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107670181 10000000000 12814145203633 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621412833/5000000000 : ℝ)^1057 ≤ (21325950083501/50000000000000 : ℝ)^801 := by
    have hnat : (2621412833 : ℕ)^1057*50000000000000^801 ≤ 21325950083501^801*5000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621412833 5000000000 21325950083501 50000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5417219633/10000000000 : ℝ)^1057 ≤ (44533954619793/100000000000000 : ℝ)^801 := by
    have hnat : (5417219633 : ℕ)^1057*100000000000000^801 ≤ 44533954619793^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417219633 10000000000 44533954619793 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2107670181/10000000000 : ℝ), (2621412833/5000000000 : ℝ), (5417219633/10000000000 : ℝ)] ![(12814145203633/100000000000000 : ℝ), (21325950083501/50000000000000 : ℝ), (44533954619793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2107670181/10000000000 : ℝ)|^1057 ≤ (12814145203633/100000000000000 : ℝ)^801
        have hw : |(-2107670181/10000000000 : ℝ)|=(2107670181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621412833/5000000000 : ℝ)|^1057 ≤ (21325950083501/50000000000000 : ℝ)^801
        have hw : |(2621412833/5000000000 : ℝ)|=(2621412833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5417219633/10000000000 : ℝ)|^1057 ≤ (44533954619793/100000000000000 : ℝ)^801
        have hw : |(5417219633/10000000000 : ℝ)|=(5417219633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s3_5 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5306155007/10000000000 : ℝ)*x 0 + (-505551961/2500000000 : ℝ)*x 1 + (5417219471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5306155007/10000000000 : ℝ)^1057 ≤ (8666614067771/20000000000000 : ℝ)^801 := by
    have hnat : (5306155007 : ℕ)^1057*20000000000000^801 ≤ 8666614067771^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5306155007 10000000000 8666614067771 20000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (505551961/2500000000 : ℝ)^1057 ≤ (6066488393389/50000000000000 : ℝ)^801 := by
    have hnat : (505551961 : ℕ)^1057*50000000000000^801 ≤ 6066488393389^801*2500000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      505551961 2500000000 6066488393389 50000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5417219471/10000000000 : ℝ)^1057 ≤ (22266976431193/50000000000000 : ℝ)^801 := by
    have hnat : (5417219471 : ℕ)^1057*50000000000000^801 ≤ 22266976431193^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417219471 10000000000 22266976431193 50000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5306155007/10000000000 : ℝ), (-505551961/2500000000 : ℝ), (5417219471/10000000000 : ℝ)] ![(8666614067771/20000000000000 : ℝ), (6066488393389/50000000000000 : ℝ), (22266976431193/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5306155007/10000000000 : ℝ)|^1057 ≤ (8666614067771/20000000000000 : ℝ)^801
        have hw : |(5306155007/10000000000 : ℝ)|=(5306155007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-505551961/2500000000 : ℝ)|^1057 ≤ (6066488393389/50000000000000 : ℝ)^801
        have hw : |(-505551961/2500000000 : ℝ)|=(505551961/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5417219471/10000000000 : ℝ)|^1057 ≤ (22266976431193/50000000000000 : ℝ)^801
        have hw : |(5417219471/10000000000 : ℝ)|=(5417219471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s3_6 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5306154341/10000000000 : ℝ)*x 0 + (1083443983/2000000000 : ℝ)*x 1 + (-1011104071/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5306154341/10000000000 : ℝ)^1057 ≤ (10833265790409/25000000000000 : ℝ)^801 := by
    have hnat : (5306154341 : ℕ)^1057*25000000000000^801 ≤ 10833265790409^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5306154341 10000000000 10833265790409 25000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1083443983/2000000000 : ℝ)^1057 ≤ (44533957678983/100000000000000 : ℝ)^801 := by
    have hnat : (1083443983 : ℕ)^1057*100000000000000^801 ≤ 44533957678983^801*2000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083443983 2000000000 44533957678983 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1011104071/5000000000 : ℝ)^1057 ≤ (12132979146171/100000000000000 : ℝ)^801 := by
    have hnat : (1011104071 : ℕ)^1057*100000000000000^801 ≤ 12132979146171^801*5000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1011104071 5000000000 12132979146171 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5306154341/10000000000 : ℝ), (1083443983/2000000000 : ℝ), (-1011104071/5000000000 : ℝ)] ![(10833265790409/25000000000000 : ℝ), (44533957678983/100000000000000 : ℝ), (12132979146171/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5306154341/10000000000 : ℝ)|^1057 ≤ (10833265790409/25000000000000 : ℝ)^801
        have hw : |(5306154341/10000000000 : ℝ)|=(5306154341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1083443983/2000000000 : ℝ)|^1057 ≤ (44533957678983/100000000000000 : ℝ)^801
        have hw : |(1083443983/2000000000 : ℝ)|=(1083443983/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1011104071/5000000000 : ℝ)|^1057 ≤ (12132979146171/100000000000000 : ℝ)^801
        have hw : |(-1011104071/5000000000 : ℝ)|=(1011104071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s3_7 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4346328687/10000000000 : ℝ)*x 0 + (4527464413/10000000000 : ℝ)*x 1 + (1043065143/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4346328687/10000000000 : ℝ)^1057 ≤ (33301696449281/100000000000000 : ℝ)^801 := by
    have hnat : (4346328687 : ℕ)^1057*100000000000000^801 ≤ 33301696449281^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4346328687 10000000000 33301696449281 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4527464413/10000000000 : ℝ)^1057 ≤ (8786302566913/25000000000000 : ℝ)^801 := by
    have hnat : (4527464413 : ℕ)^1057*25000000000000^801 ≤ 8786302566913^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4527464413 10000000000 8786302566913 25000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043065143/2500000000 : ℝ)^1057 ≤ (31553093272647/100000000000000 : ℝ)^801 := by
    have hnat : (1043065143 : ℕ)^1057*100000000000000^801 ≤ 31553093272647^801*2500000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043065143 2500000000 31553093272647 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4346328687/10000000000 : ℝ), (4527464413/10000000000 : ℝ), (1043065143/2500000000 : ℝ)] ![(33301696449281/100000000000000 : ℝ), (8786302566913/25000000000000 : ℝ), (31553093272647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4346328687/10000000000 : ℝ)|^1057 ≤ (33301696449281/100000000000000 : ℝ)^801
        have hw : |(4346328687/10000000000 : ℝ)|=(4346328687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4527464413/10000000000 : ℝ)|^1057 ≤ (8786302566913/25000000000000 : ℝ)^801
        have hw : |(4527464413/10000000000 : ℝ)|=(4527464413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043065143/2500000000 : ℝ)|^1057 ≤ (31553093272647/100000000000000 : ℝ)^801
        have hw : |(1043065143/2500000000 : ℝ)|=(1043065143/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1263_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151839963/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16169/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9583/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2741/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7341/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16169/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9583/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16169/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9583/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16169/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9583/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16169/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9583/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16169/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9583/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16169/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9583/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9583/100000 : ℝ) ^ (8455/2048 : ℝ) ≤ (6240400206139111/100000000000000000000 : ℝ) := by
    have hpowers : (9583/100000 : ℝ)^8455 ≤ (6240400206139111/100000000000000000000 : ℝ)^2048 := by
      have hnat : (9583 : ℕ)^8455*100000000000000000000^2048 ≤ 6240400206139111^2048*100000^8455 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9583 100000 6240400206139111 100000000000000000000 8455 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9583/100000 : ℝ)) (X := (6240400206139111/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8455 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (16169/100000 : ℝ) ^ (8455/2048 : ℝ) ≤ (27044773426005147/50000000000000000000 : ℝ) := by
    have hpowers : (16169/100000 : ℝ)^8455 ≤ (27044773426005147/50000000000000000000 : ℝ)^2048 := by
      have hnat : (16169 : ℕ)^8455*50000000000000000000^2048 ≤ 27044773426005147^2048*100000^8455 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16169 100000 27044773426005147 50000000000000000000 8455 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16169/100000 : ℝ)) (X := (27044773426005147/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8455 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006240400206139111/50000000000000000000 : ℝ) ≤ (1250037787508297/1250000000000000 : ℝ) ^ (8455/2048 : ℝ) := by
    have hpowers : (50006240400206139111/50000000000000000000 : ℝ)^2048 ≤ (1250037787508297/1250000000000000 : ℝ)^8455 := by
      have hnat : (50006240400206139111 : ℕ)^2048*1250000000000000^8455 ≤ 1250037787508297^8455*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006240400206139111 50000000000000000000 1250037787508297 1250000000000000 2048 8455 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250037787508297/1250000000000000 : ℝ)) (X := (50006240400206139111/50000000000000000000 : ℝ)) (by norm_num) 8455 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20012065989411629881/20000000000000000000 : ℝ) ≤ (10001460999394513/10000000000000000 : ℝ) ^ (8455/2048 : ℝ) := by
    have hpowers : (20012065989411629881/20000000000000000000 : ℝ)^2048 ≤ (10001460999394513/10000000000000000 : ℝ)^8455 := by
      have hnat : (20012065989411629881 : ℕ)^2048*10000000000000000^8455 ≤ 10001460999394513^8455*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20012065989411629881 20000000000000000000 10001460999394513 10000000000000000 2048 8455 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001460999394513/10000000000000000 : ℝ)) (X := (20012065989411629881/20000000000000000000 : ℝ)) (by norm_num) 8455 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25027044773426005147/25000000000000000000 : ℝ) ≤ (200052393974453/200000000000000 : ℝ) ^ (8455/2048 : ℝ) := by
    have hpowers : (25027044773426005147/25000000000000000000 : ℝ)^2048 ≤ (200052393974453/200000000000000 : ℝ)^8455 := by
      have hnat : (25027044773426005147 : ℕ)^2048*200000000000000^8455 ≤ 200052393974453^8455*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25027044773426005147 25000000000000000000 200052393974453 200000000000000 2048 8455 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200052393974453/200000000000000 : ℝ)) (X := (25027044773426005147/25000000000000000000 : ℝ)) (by norm_num) 8455 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6240400206139111/100000000000000000000 : ℝ) ≤ ((889726801579919981/890000000000000000 : ℝ)+2*(1158699328137/658600000000000 : ℝ)*(9583/100000 : ℝ))^(8455/2048 : ℝ) := by
    rw [show (889726801579919981/890000000000000000 : ℝ)+2*(1158699328137/658600000000000 : ℝ)*(9583/100000 : ℝ)=(1250037787508297/1250000000000000 : ℝ) by norm_num, show 1+2*(6240400206139111/100000000000000000000 : ℝ)=(50006240400206139111/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27044773426005147/50000000000000000000 : ℝ)+(6240400206139111/100000000000000000000 : ℝ) ≤ ((889726801579919981/890000000000000000 : ℝ)+(1158699328137/658600000000000 : ℝ)*((16169/100000 : ℝ)+(9583/100000 : ℝ)))^(8455/2048 : ℝ) := by
    rw [show (889726801579919981/890000000000000000 : ℝ)+(1158699328137/658600000000000 : ℝ)*((16169/100000 : ℝ)+(9583/100000 : ℝ))=(10001460999394513/10000000000000000 : ℝ) by norm_num, show 1+(27044773426005147/50000000000000000000 : ℝ)+(6240400206139111/100000000000000000000 : ℝ)=(20012065989411629881/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27044773426005147/50000000000000000000 : ℝ) ≤ ((889726801579919981/890000000000000000 : ℝ)+2*(1158699328137/658600000000000 : ℝ)*(16169/100000 : ℝ))^(8455/2048 : ℝ) := by
    rw [show (889726801579919981/890000000000000000 : ℝ)+2*(1158699328137/658600000000000 : ℝ)*(16169/100000 : ℝ)=(200052393974453/200000000000000 : ℝ) by norm_num, show 1+2*(27044773426005147/50000000000000000000 : ℝ)=(25027044773426005147/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (889726801579919981/890000000000000000 : ℝ)*(X 1 0+X 2 0)+(1158699328137/658600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8455/2048 : ℝ)) (lo := (9583/100000 : ℝ)) (hi := (16169/100000 : ℝ)) (c := (889726801579919981/890000000000000000 : ℝ)) (alpha := (1158699328137/658600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (889726801579919981/890000000000000000 : ℝ)*(X 0 1+X 2 1)+(1158699328137/658600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8455/2048 : ℝ)) (lo := (9583/100000 : ℝ)) (hi := (16169/100000 : ℝ)) (c := (889726801579919981/890000000000000000 : ℝ)) (alpha := (1158699328137/658600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (889726801579919981/890000000000000000 : ℝ)*(X 0 2+X 1 2)+(1158699328137/658600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8455/2048 : ℝ)) (lo := (9583/100000 : ℝ)) (hi := (16169/100000 : ℝ)) (c := (889726801579919981/890000000000000000 : ℝ)) (alpha := (1158699328137/658600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-263457027/1250000000 : ℝ)*X 0 0+(5417853643/10000000000 : ℝ)*X 0 1+(5242195403/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((133775787/250000000 : ℝ)*X 1 0+(-2197232649/10000000000 : ℝ)*X 1 1+(655274439/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((267551573/500000000 : ℝ)*X 2 0+(1310548999/2500000000 : ℝ)*X 2 1+(-2197232037/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4346300881/10000000000 : ℝ)*X 0 0+(521371269/1250000000 : ℝ)*X 0 1+(2264374449/5000000000 : ℝ)*X 0 2+(4346300881/10000000000 : ℝ)*X 1 0+(521371269/1250000000 : ℝ)*X 1 1+(2264374449/5000000000 : ℝ)*X 1 2+(4346300881/10000000000 : ℝ)*X 2 0+(521371269/1250000000 : ℝ)*X 2 1+(2264374449/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2107670181/10000000000 : ℝ)*X 0 0+(2621412833/5000000000 : ℝ)*X 0 1+(5417219633/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5306155007/10000000000 : ℝ)*X 1 0+(-505551961/2500000000 : ℝ)*X 1 1+(5417219471/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5306154341/10000000000 : ℝ)*X 2 0+(1083443983/2000000000 : ℝ)*X 2 1+(-1011104071/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4346328687/10000000000 : ℝ)*X 0 0+(4527464413/10000000000 : ℝ)*X 0 1+(1043065143/2500000000 : ℝ)*X 0 2+(4346328687/10000000000 : ℝ)*X 1 0+(4527464413/10000000000 : ℝ)*X 1 1+(1043065143/2500000000 : ℝ)*X 1 2+(4346328687/10000000000 : ℝ)*X 2 0+(4527464413/10000000000 : ℝ)*X 2 1+(1043065143/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (729609666306364079775462729/102906250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (775673807/100000000000000 : ℝ)*(base19) + (368003467/100000000000000 : ℝ)*(base23) + (253224983/100000000000000 : ℝ)*(lower2) + (154499/6250000000000 : ℝ)*(lower3) + (265249311723319/6250000000000 : ℝ)*(major0) + (265249311723319/6250000000000 : ℝ)*(major1) + (265249311723319/6250000000000 : ℝ)*(major2) + (1423225441432637/25000000000000 : ℝ)*(sp0) + (5692925762349547/100000000000000 : ℝ)*(sp1) + (5692936524036243/100000000000000 : ℝ)*(sp2) + (87344721379753/3125000000000 : ℝ)*(sp3) + (17563154581/50000000000000 : ℝ)*(sp4) + (2588504089/25000000000000 : ℝ)*(sp5) + (38135233/390625000000 : ℝ)*(sp7) + (87345026461617/3125000000000 : ℝ)*(f.failure) + (569293689203971/10000000000000 : ℝ)*(f.sum) + (39302473841397/8232500000000000000000000000 : ℝ)*base65 + (796137165421583257/205812500000000000000000000000000 : ℝ)*base68 + (212883841929458257/205812500000000000000000000000000 : ℝ)*base70 + (737699151436166743/205812500000000000000000000000000 : ℝ)*base71 + (25170841361339/16465000000000000000000000000 : ℝ)*base73 + (574671828713833257/205812500000000000000000000000000 : ℝ)*base76 + (1198066575979666743/205812500000000000000000000000000 : ℝ)*base77 + (3346307323808833257/205812500000000000000000000000000 : ℝ)*base80 + (55696570624679/16465000000000000000000000000 : ℝ)*base81 + (3799829/312500000000000000000 : ℝ)*base90 + (3799829/312500000000000000000 : ℝ)*base92 + (3799829/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (416570709274871628179684289/411625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (425007087/20000000000000 : ℝ)*(base19) + (1284358817/100000000000000 : ℝ)*(base23) + (16217429/50000000000000 : ℝ)*(lower4) + (166404689/50000000000000 : ℝ)*(upper5) + (2137357408909979/50000000000000 : ℝ)*(major0) + (2137357408909979/50000000000000 : ℝ)*(major1) + (2137357408909979/50000000000000 : ℝ)*(major2) + (18697881/781250000000 : ℝ)*(sp0) + (10545446227/20000000000000 : ℝ)*(sp1) + (15598686689/50000000000000 : ℝ)*(sp2) + (1146830138834499/20000000000000 : ℝ)*(sp4) + (5734098235234693/100000000000000 : ℝ)*(sp5) + (1433530151442267/25000000000000 : ℝ)*(sp6) + (2815276514404813/100000000000000 : ℝ)*(sp7) + (2815276514404813/100000000000000 : ℝ)*(f.failure) + (5734153087501263/100000000000000 : ℝ)*(f.sum) + (35264486183803/16465000000000000000000000000 : ℝ)*base65 + (485145630734905237/1646500000000000000000000000000000 : ℝ)*base68 + (10008176631392905237/1646500000000000000000000000000000 : ℝ)*base70 + (6115813267368405237/1646500000000000000000000000000000 : ℝ)*base72 + (25532266399707/16465000000000000000000000000 : ℝ)*base74 + (8654960570098905237/1646500000000000000000000000000000 : ℝ)*base76 + (3074741625958905237/1646500000000000000000000000000000 : ℝ)*base78 + (1315425254414094763/1646500000000000000000000000000000 : ℝ)*base79 + (52240010741913/16465000000000000000000000000 : ℝ)*base81 + (27058081/10000000000000000000000 : ℝ)*base90 + (27058081/10000000000000000000000 : ℝ)*base92 + (27058081/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1263_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151839963/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16169/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9583/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2741/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7341/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1263_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1263_s4_0 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2109820803/10000000000 : ℝ)*x 0 + (5396660123/10000000000 : ℝ)*x 1 + (5261970051/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2109820803/10000000000 : ℝ)^1057 ≤ (801962635339/6250000000000 : ℝ)^801 := by
    have hnat : (2109820803 : ℕ)^1057*6250000000000^801 ≤ 801962635339^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109820803 10000000000 801962635339 6250000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5396660123/10000000000 : ℝ)^1057 ≤ (44311056526683/100000000000000 : ℝ)^801 := by
    have hnat : (5396660123 : ℕ)^1057*100000000000000^801 ≤ 44311056526683^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396660123 10000000000 44311056526683 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5261970051/10000000000 : ℝ)^1057 ≤ (10714385325563/25000000000000 : ℝ)^801 := by
    have hnat : (5261970051 : ℕ)^1057*25000000000000^801 ≤ 10714385325563^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261970051 10000000000 10714385325563 25000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2109820803/10000000000 : ℝ), (5396660123/10000000000 : ℝ), (5261970051/10000000000 : ℝ)] ![(801962635339/6250000000000 : ℝ), (44311056526683/100000000000000 : ℝ), (10714385325563/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2109820803/10000000000 : ℝ)|^1057 ≤ (801962635339/6250000000000 : ℝ)^801
        have hw : |(-2109820803/10000000000 : ℝ)|=(2109820803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5396660123/10000000000 : ℝ)|^1057 ≤ (44311056526683/100000000000000 : ℝ)^801
        have hw : |(5396660123/10000000000 : ℝ)|=(5396660123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5261970051/10000000000 : ℝ)|^1057 ≤ (10714385325563/25000000000000 : ℝ)^801
        have hw : |(5261970051/10000000000 : ℝ)|=(5261970051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s4_1 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2672839529/5000000000 : ℝ)*x 0 + (-2178193633/10000000000 : ℝ)*x 1 + (5261969967/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672839529/5000000000 : ℝ)^1057 ≤ (21879755799523/50000000000000 : ℝ)^801 := by
    have hnat : (2672839529 : ℕ)^1057*50000000000000^801 ≤ 21879755799523^801*5000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672839529 5000000000 21879755799523 50000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2178193633/10000000000 : ℝ)^1057 ≤ (1672868498329/12500000000000 : ℝ)^801 := by
    have hnat : (2178193633 : ℕ)^1057*12500000000000^801 ≤ 1672868498329^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178193633 10000000000 1672868498329 12500000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5261969967/10000000000 : ℝ)^1057 ≤ (42857540399433/100000000000000 : ℝ)^801 := by
    have hnat : (5261969967 : ℕ)^1057*100000000000000^801 ≤ 42857540399433^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261969967 10000000000 42857540399433 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672839529/5000000000 : ℝ), (-2178193633/10000000000 : ℝ), (5261969967/10000000000 : ℝ)] ![(21879755799523/50000000000000 : ℝ), (1672868498329/12500000000000 : ℝ), (42857540399433/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672839529/5000000000 : ℝ)|^1057 ≤ (21879755799523/50000000000000 : ℝ)^801
        have hw : |(2672839529/5000000000 : ℝ)|=(2672839529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2178193633/10000000000 : ℝ)|^1057 ≤ (1672868498329/12500000000000 : ℝ)^801
        have hw : |(-2178193633/10000000000 : ℝ)|=(2178193633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5261969967/10000000000 : ℝ)|^1057 ≤ (42857540399433/100000000000000 : ℝ)^801
        have hw : |(5261969967/10000000000 : ℝ)|=(5261969967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s4_2 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5345679101/10000000000 : ℝ)*x 0 + (2630984917/5000000000 : ℝ)*x 1 + (-272274219/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345679101/10000000000 : ℝ)^1057 ≤ (2187975603177/5000000000000 : ℝ)^801 := by
    have hnat : (5345679101 : ℕ)^1057*5000000000000^801 ≤ 2187975603177^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345679101 10000000000 2187975603177 5000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2630984917/5000000000 : ℝ)^1057 ≤ (4285753896997/10000000000000 : ℝ)^801 := by
    have hnat : (2630984917 : ℕ)^1057*10000000000000^801 ≤ 4285753896997^801*5000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630984917 5000000000 4285753896997 10000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (272274219/1250000000 : ℝ)^1057 ≤ (13382948951449/100000000000000 : ℝ)^801 := by
    have hnat : (272274219 : ℕ)^1057*100000000000000^801 ≤ 13382948951449^801*1250000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272274219 1250000000 13382948951449 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345679101/10000000000 : ℝ), (2630984917/5000000000 : ℝ), (-272274219/1250000000 : ℝ)] ![(2187975603177/5000000000000 : ℝ), (4285753896997/10000000000000 : ℝ), (13382948951449/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345679101/10000000000 : ℝ)|^1057 ≤ (2187975603177/5000000000000 : ℝ)^801
        have hw : |(5345679101/10000000000 : ℝ)|=(5345679101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2630984917/5000000000 : ℝ)|^1057 ≤ (4285753896997/10000000000000 : ℝ)^801
        have hw : |(2630984917/5000000000 : ℝ)|=(2630984917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-272274219/1250000000 : ℝ)|^1057 ≤ (13382948951449/100000000000000 : ℝ)^801
        have hw : |(-272274219/1250000000 : ℝ)|=(272274219/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s4_3 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (543450077/1250000000 : ℝ)*x 0 + (4212525817/10000000000 : ℝ)*x 1 + (2243431413/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (543450077/1250000000 : ℝ)^1057 ≤ (33314557292379/100000000000000 : ℝ)^801 := by
    have hnat : (543450077 : ℕ)^1057*100000000000000^801 ≤ 33314557292379^801*1250000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543450077 1250000000 33314557292379 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4212525817/10000000000 : ℝ)^1057 ≤ (1597777126171/5000000000000 : ℝ)^801 := by
    have hnat : (4212525817 : ℕ)^1057*5000000000000^801 ≤ 1597777126171^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4212525817 10000000000 1597777126171 5000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2243431413/5000000000 : ℝ)^1057 ≤ (34729900169767/100000000000000 : ℝ)^801 := by
    have hnat : (2243431413 : ℕ)^1057*100000000000000^801 ≤ 34729900169767^801*5000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2243431413 5000000000 34729900169767 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(543450077/1250000000 : ℝ), (4212525817/10000000000 : ℝ), (2243431413/5000000000 : ℝ)] ![(33314557292379/100000000000000 : ℝ), (1597777126171/5000000000000 : ℝ), (34729900169767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(543450077/1250000000 : ℝ)|^1057 ≤ (33314557292379/100000000000000 : ℝ)^801
        have hw : |(543450077/1250000000 : ℝ)|=(543450077/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4212525817/10000000000 : ℝ)|^1057 ≤ (1597777126171/5000000000000 : ℝ)^801
        have hw : |(4212525817/10000000000 : ℝ)|=(4212525817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2243431413/5000000000 : ℝ)|^1057 ≤ (34729900169767/100000000000000 : ℝ)^801
        have hw : |(2243431413/5000000000 : ℝ)|=(2243431413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s4_4 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2109826741/10000000000 : ℝ)*x 0 + (1315585249/2500000000 : ℝ)*x 1 + (1079257551/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2109826741/10000000000 : ℝ)^1057 ≤ (6415724910373/50000000000000 : ℝ)^801 := by
    have hnat : (2109826741 : ℕ)^1057*50000000000000^801 ≤ 6415724910373^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109826741 10000000000 6415724910373 50000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1315585249/2500000000 : ℝ)^1057 ≤ (42861528206133/100000000000000 : ℝ)^801 := by
    have hnat : (1315585249 : ℕ)^1057*100000000000000^801 ≤ 42861528206133^801*2500000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315585249 2500000000 42861528206133 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1079257551/2000000000 : ℝ)^1057 ≤ (22153510979189/50000000000000 : ℝ)^801 := by
    have hnat : (1079257551 : ℕ)^1057*50000000000000^801 ≤ 22153510979189^801*2000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079257551 2000000000 22153510979189 50000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2109826741/10000000000 : ℝ), (1315585249/2500000000 : ℝ), (1079257551/2000000000 : ℝ)] ![(6415724910373/50000000000000 : ℝ), (42861528206133/100000000000000 : ℝ), (22153510979189/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2109826741/10000000000 : ℝ)|^1057 ≤ (6415724910373/50000000000000 : ℝ)^801
        have hw : |(-2109826741/10000000000 : ℝ)|=(2109826741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1315585249/2500000000 : ℝ)|^1057 ≤ (42861528206133/100000000000000 : ℝ)^801
        have hw : |(1315585249/2500000000 : ℝ)|=(1315585249/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1079257551/2000000000 : ℝ)|^1057 ≤ (22153510979189/50000000000000 : ℝ)^801
        have hw : |(1079257551/2000000000 : ℝ)|=(1079257551/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s4_5 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5311265851/10000000000 : ℝ)*x 0 + (-408775133/2000000000 : ℝ)*x 1 + (5396287613/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311265851/10000000000 : ℝ)^1057 ≤ (43388156365957/100000000000000 : ℝ)^801 := by
    have hnat : (5311265851 : ℕ)^1057*100000000000000^801 ≤ 43388156365957^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311265851 10000000000 43388156365957 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (408775133/2000000000 : ℝ)^1057 ≤ (6152411600569/50000000000000 : ℝ)^801 := by
    have hnat : (408775133 : ℕ)^1057*50000000000000^801 ≤ 6152411600569^801*2000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      408775133 2000000000 6152411600569 50000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5396287613/10000000000 : ℝ)^1057 ≤ (34614859703/78125000000 : ℝ)^801 := by
    have hnat : (5396287613 : ℕ)^1057*78125000000^801 ≤ 34614859703^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396287613 10000000000 34614859703 78125000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311265851/10000000000 : ℝ), (-408775133/2000000000 : ℝ), (5396287613/10000000000 : ℝ)] ![(43388156365957/100000000000000 : ℝ), (6152411600569/50000000000000 : ℝ), (34614859703/78125000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311265851/10000000000 : ℝ)|^1057 ≤ (43388156365957/100000000000000 : ℝ)^801
        have hw : |(5311265851/10000000000 : ℝ)|=(5311265851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-408775133/2000000000 : ℝ)|^1057 ≤ (6152411600569/50000000000000 : ℝ)^801
        have hw : |(-408775133/2000000000 : ℝ)|=(408775133/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5396287613/10000000000 : ℝ)|^1057 ≤ (34614859703/78125000000 : ℝ)^801
        have hw : |(5396287613/10000000000 : ℝ)|=(5396287613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s4_6 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5311265767/10000000000 : ℝ)*x 0 + (5396287467/10000000000 : ℝ)*x 1 + (-1021937989/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311265767/10000000000 : ℝ)^1057 ≤ (43388155460443/100000000000000 : ℝ)^801 := by
    have hnat : (5311265767 : ℕ)^1057*100000000000000^801 ≤ 43388155460443^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311265767 10000000000 43388155460443 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5396287467/10000000000 : ℝ)^1057 ≤ (44307018837963/100000000000000 : ℝ)^801 := by
    have hnat : (5396287467 : ℕ)^1057*100000000000000^801 ≤ 44307018837963^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396287467 10000000000 44307018837963 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1021937989/5000000000 : ℝ)^1057 ≤ (3076206421937/25000000000000 : ℝ)^801 := by
    have hnat : (1021937989 : ℕ)^1057*25000000000000^801 ≤ 3076206421937^801*5000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1021937989 5000000000 3076206421937 25000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311265767/10000000000 : ℝ), (5396287467/10000000000 : ℝ), (-1021937989/5000000000 : ℝ)] ![(43388155460443/100000000000000 : ℝ), (44307018837963/100000000000000 : ℝ), (3076206421937/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311265767/10000000000 : ℝ)|^1057 ≤ (43388155460443/100000000000000 : ℝ)^801
        have hw : |(5311265767/10000000000 : ℝ)|=(5311265767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5396287467/10000000000 : ℝ)|^1057 ≤ (44307018837963/100000000000000 : ℝ)^801
        have hw : |(5396287467/10000000000 : ℝ)|=(5396287467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1021937989/5000000000 : ℝ)|^1057 ≤ (3076206421937/25000000000000 : ℝ)^801
        have hw : |(-1021937989/5000000000 : ℝ)|=(1021937989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s4_7 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (217380659/500000000 : ℝ)*x 0 + (4486106671/10000000000 : ℝ)*x 1 + (26333029/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (217380659/500000000 : ℝ)^1057 ≤ (16657342168313/50000000000000 : ℝ)^801 := by
    have hnat : (217380659 : ℕ)^1057*50000000000000^801 ≤ 16657342168313^801*500000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217380659 500000000 16657342168313 50000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4486106671/10000000000 : ℝ)^1057 ≤ (34722176879709/100000000000000 : ℝ)^801 := by
    have hnat : (4486106671 : ℕ)^1057*100000000000000^801 ≤ 34722176879709^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4486106671 10000000000 34722176879709 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (26333029/62500000 : ℝ)^1057 ≤ (6392627754083/20000000000000 : ℝ)^801 := by
    have hnat : (26333029 : ℕ)^1057*20000000000000^801 ≤ 6392627754083^801*62500000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26333029 62500000 6392627754083 20000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(217380659/500000000 : ℝ), (4486106671/10000000000 : ℝ), (26333029/62500000 : ℝ)] ![(16657342168313/50000000000000 : ℝ), (34722176879709/100000000000000 : ℝ), (6392627754083/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(217380659/500000000 : ℝ)|^1057 ≤ (16657342168313/50000000000000 : ℝ)^801
        have hw : |(217380659/500000000 : ℝ)|=(217380659/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4486106671/10000000000 : ℝ)|^1057 ≤ (34722176879709/100000000000000 : ℝ)^801
        have hw : |(4486106671/10000000000 : ℝ)|=(4486106671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(26333029/62500000 : ℝ)|^1057 ≤ (6392627754083/20000000000000 : ℝ)^801
        have hw : |(26333029/62500000 : ℝ)|=(26333029/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1263_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151839963/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7341/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2741/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5693/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14239/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7341/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2741/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7341/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2741/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7341/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2741/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7341/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2741/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7341/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2741/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7341/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2741/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2741/25000 : ℝ) ^ (8455/2048 : ℝ) ≤ (5439523837560107/50000000000000000000 : ℝ) := by
    have hpowers : (2741/25000 : ℝ)^8455 ≤ (5439523837560107/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2741 : ℕ)^8455*50000000000000000000^2048 ≤ 5439523837560107^2048*25000^8455 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2741 25000 5439523837560107 50000000000000000000 8455 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2741/25000 : ℝ)) (X := (5439523837560107/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8455 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7341/50000 : ℝ) ^ (8455/2048 : ℝ) ≤ (3631960606174971/10000000000000000000 : ℝ) := by
    have hpowers : (7341/50000 : ℝ)^8455 ≤ (3631960606174971/10000000000000000000 : ℝ)^2048 := by
      have hnat : (7341 : ℕ)^8455*10000000000000000000^2048 ≤ 3631960606174971^2048*50000^8455 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7341 50000 3631960606174971 10000000000000000000 8455 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7341/50000 : ℝ)) (X := (3631960606174971/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8455 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005439523837560107/25000000000000000000 : ℝ) ≤ (2500131747209409/2500000000000000 : ℝ) ^ (8455/2048 : ℝ) := by
    have hpowers : (25005439523837560107/25000000000000000000 : ℝ)^2048 ≤ (2500131747209409/2500000000000000 : ℝ)^8455 := by
      have hnat : (25005439523837560107 : ℕ)^2048*2500000000000000^8455 ≤ 2500131747209409^8455*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005439523837560107 25000000000000000000 2500131747209409 2500000000000000 2048 8455 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500131747209409/2500000000000000 : ℝ)) (X := (25005439523837560107/25000000000000000000 : ℝ)) (by norm_num) 8455 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011799663434217481/25000000000000000000 : ℝ) ≤ (1250142882261091/1250000000000000 : ℝ) ^ (8455/2048 : ℝ) := by
    have hpowers : (25011799663434217481/25000000000000000000 : ℝ)^2048 ≤ (1250142882261091/1250000000000000 : ℝ)^8455 := by
      have hnat : (25011799663434217481 : ℕ)^2048*1250000000000000^8455 ≤ 1250142882261091^8455*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011799663434217481 25000000000000000000 1250142882261091 1250000000000000 2048 8455 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250142882261091/1250000000000000 : ℝ)) (X := (25011799663434217481/25000000000000000000 : ℝ)) (by norm_num) 8455 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003631960606174971/5000000000000000000 : ℝ) ≤ (500087956366991/500000000000000 : ℝ) ^ (8455/2048 : ℝ) := by
    have hpowers : (5003631960606174971/5000000000000000000 : ℝ)^2048 ≤ (500087956366991/500000000000000 : ℝ)^8455 := by
      have hnat : (5003631960606174971 : ℕ)^2048*500000000000000^8455 ≤ 500087956366991^8455*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003631960606174971 5000000000000000000 500087956366991 500000000000000 2048 8455 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500087956366991/500000000000000 : ℝ)) (X := (5003631960606174971/5000000000000000000 : ℝ)) (by norm_num) 8455 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5439523837560107/50000000000000000000 : ℝ) ≤ ((4646056272245048159/4647500000000000000 : ℝ)+2*(154017312773/92950000000000 : ℝ)*(2741/25000 : ℝ))^(8455/2048 : ℝ) := by
    rw [show (4646056272245048159/4647500000000000000 : ℝ)+2*(154017312773/92950000000000 : ℝ)*(2741/25000 : ℝ)=(2500131747209409/2500000000000000 : ℝ) by norm_num, show 1+2*(5439523837560107/50000000000000000000 : ℝ)=(25005439523837560107/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3631960606174971/10000000000000000000 : ℝ)+(5439523837560107/50000000000000000000 : ℝ) ≤ ((4646056272245048159/4647500000000000000 : ℝ)+(154017312773/92950000000000 : ℝ)*((7341/50000 : ℝ)+(2741/25000 : ℝ)))^(8455/2048 : ℝ) := by
    rw [show (4646056272245048159/4647500000000000000 : ℝ)+(154017312773/92950000000000 : ℝ)*((7341/50000 : ℝ)+(2741/25000 : ℝ))=(1250142882261091/1250000000000000 : ℝ) by norm_num, show 1+(3631960606174971/10000000000000000000 : ℝ)+(5439523837560107/50000000000000000000 : ℝ)=(25011799663434217481/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3631960606174971/10000000000000000000 : ℝ) ≤ ((4646056272245048159/4647500000000000000 : ℝ)+2*(154017312773/92950000000000 : ℝ)*(7341/50000 : ℝ))^(8455/2048 : ℝ) := by
    rw [show (4646056272245048159/4647500000000000000 : ℝ)+2*(154017312773/92950000000000 : ℝ)*(7341/50000 : ℝ)=(500087956366991/500000000000000 : ℝ) by norm_num, show 1+2*(3631960606174971/10000000000000000000 : ℝ)=(5003631960606174971/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4646056272245048159/4647500000000000000 : ℝ)*(X 1 0+X 2 0)+(154017312773/92950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8455/2048 : ℝ)) (lo := (2741/25000 : ℝ)) (hi := (7341/50000 : ℝ)) (c := (4646056272245048159/4647500000000000000 : ℝ)) (alpha := (154017312773/92950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4646056272245048159/4647500000000000000 : ℝ)*(X 0 1+X 2 1)+(154017312773/92950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8455/2048 : ℝ)) (lo := (2741/25000 : ℝ)) (hi := (7341/50000 : ℝ)) (c := (4646056272245048159/4647500000000000000 : ℝ)) (alpha := (154017312773/92950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4646056272245048159/4647500000000000000 : ℝ)*(X 0 2+X 1 2)+(154017312773/92950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8455/2048 : ℝ)) (lo := (2741/25000 : ℝ)) (hi := (7341/50000 : ℝ)) (c := (4646056272245048159/4647500000000000000 : ℝ)) (alpha := (154017312773/92950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2109820803/10000000000 : ℝ)*X 0 0+(5396660123/10000000000 : ℝ)*X 0 1+(5261970051/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672839529/5000000000 : ℝ)*X 1 0+(-2178193633/10000000000 : ℝ)*X 1 1+(5261969967/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345679101/10000000000 : ℝ)*X 2 0+(2630984917/5000000000 : ℝ)*X 2 1+(-272274219/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((543450077/1250000000 : ℝ)*X 0 0+(4212525817/10000000000 : ℝ)*X 0 1+(2243431413/5000000000 : ℝ)*X 0 2+(543450077/1250000000 : ℝ)*X 1 0+(4212525817/10000000000 : ℝ)*X 1 1+(2243431413/5000000000 : ℝ)*X 1 2+(543450077/1250000000 : ℝ)*X 2 0+(4212525817/10000000000 : ℝ)*X 2 1+(2243431413/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2109826741/10000000000 : ℝ)*X 0 0+(1315585249/2500000000 : ℝ)*X 0 1+(1079257551/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5311265851/10000000000 : ℝ)*X 1 0+(-408775133/2000000000 : ℝ)*X 1 1+(5396287613/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5311265767/10000000000 : ℝ)*X 2 0+(5396287467/10000000000 : ℝ)*X 2 1+(-1021937989/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((217380659/500000000 : ℝ)*X 0 0+(4486106671/10000000000 : ℝ)*X 0 1+(26333029/62500000 : ℝ)*X 0 2+(217380659/500000000 : ℝ)*X 1 0+(4486106671/10000000000 : ℝ)*X 1 1+(26333029/62500000 : ℝ)*X 1 2+(217380659/500000000 : ℝ)*X 2 0+(4486106671/10000000000 : ℝ)*X 2 1+(26333029/62500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (73841788557058111413818649/21125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (164862133/50000000000000 : ℝ)*(base19) + (561677497/100000000000000 : ℝ)*(base23) + (93694069/100000000000000 : ℝ)*(upper2) + (16261191/50000000000000 : ℝ)*(upper3) + (5534814021285593/100000000000000 : ℝ)*(major0) + (5534814021285593/100000000000000 : ℝ)*(major1) + (5534814021285593/100000000000000 : ℝ)*(major2) + (7424460444626941/100000000000000 : ℝ)*(sp0) + (3712232340711779/50000000000000 : ℝ)*(sp1) + (371223198870563/5000000000000 : ℝ)*(sp2) + (911289311519679/25000000000000 : ℝ)*(sp3) + (4566520883/100000000000000 : ℝ)*(sp4) + (236029533/50000000000000 : ℝ)*(sp6) + (2834414499/50000000000000 : ℝ)*(sp7) + (3645162914907713/100000000000000 : ℝ)*(f.failure) + (464029063196739/6250000000000 : ℝ)*(f.sum) + (377590070037/211250000000000000000000000 : ℝ)*base65 + (89048332477947883/42250000000000000000000000000000 : ℝ)*base68 + (179690804407697883/42250000000000000000000000000000 : ℝ)*base70 + (187001286019302117/42250000000000000000000000000000 : ℝ)*base71 + (1900550775361/422500000000000000000000000 : ℝ)*base74 + (86152493799802117/42250000000000000000000000000000 : ℝ)*base75 + (175026684633802117/42250000000000000000000000000000 : ℝ)*base77 + (533536536717302117/42250000000000000000000000000000 : ℝ)*base79 + (992508558331/422500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (9665381/10000000000000000000000 : ℝ)*base90 + (9665381/10000000000000000000000 : ℝ)*base92 + (9665381/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (41689559756515712727881967/4468750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (468309967/20000000000000 : ℝ)*(base19) + (231391929/10000000000000 : ℝ)*(base23) + (33421673/50000000000000 : ℝ)*(upper3) + (118756853/100000000000000 : ℝ)*(lower4) + (275476999/100000000000000 : ℝ)*(upper5) + (2782761007149927/50000000000000 : ℝ)*(major0) + (2782761007149927/50000000000000 : ℝ)*(major1) + (2782761007149927/50000000000000 : ℝ)*(major2) + (13477403027/20000000000000 : ℝ)*(sp1) + (46836397303/100000000000000 : ℝ)*(sp2) + (7465656882477819/100000000000000 : ℝ)*(sp4) + (149311743078257/2000000000000 : ℝ)*(sp5) + (3732803866080613/50000000000000 : ℝ)*(sp6) + (1832693417575403/50000000000000 : ℝ)*(sp7) + (1832693417575403/50000000000000 : ℝ)*(f.failure) + (7465656882477819/100000000000000 : ℝ)*(f.sum) + (18541904426989/9295000000000000000000000000 : ℝ)*base65 + (1686153991770634393/232375000000000000000000000000000 : ℝ)*base67 + (2393774990587509393/232375000000000000000000000000000 : ℝ)*base69 + (1221335186215615607/232375000000000000000000000000000 : ℝ)*base72 + (56441979525589/9295000000000000000000000000 : ℝ)*base73 + (1382439196368759393/232375000000000000000000000000000 : ℝ)*base75 + (213629989267509393/232375000000000000000000000000000 : ℝ)*base77 + (4630869358935634393/232375000000000000000000000000000 : ℝ)*base79 + (436828821551/145234375000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (41230089/5000000000000000000000 : ℝ)*base89 + (41230089/5000000000000000000000 : ℝ)*base91 + (41230089/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1263_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151839963/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7341/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2741/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5693/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14239/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1263_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1263_s5_0 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-263779389/1250000000 : ℝ)*x 0 + (5391910153/10000000000 : ℝ)*x 1 + (2633223943/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (263779389/1250000000 : ℝ)^1057 ≤ (6417363649181/50000000000000 : ℝ)^801 := by
    have hnat : (263779389 : ℕ)^1057*50000000000000^801 ≤ 6417363649181^801*1250000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263779389 1250000000 6417363649181 50000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391910153/10000000000 : ℝ)^1057 ≤ (8851919554323/20000000000000 : ℝ)^801 := by
    have hnat : (5391910153 : ℕ)^1057*20000000000000^801 ≤ 8851919554323^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391910153 10000000000 8851919554323 20000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633223943/5000000000 : ℝ)^1057 ≤ (21452837458697/50000000000000 : ℝ)^801 := by
    have hnat : (2633223943 : ℕ)^1057*50000000000000^801 ≤ 21452837458697^801*5000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633223943 5000000000 21452837458697 50000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-263779389/1250000000 : ℝ), (5391910153/10000000000 : ℝ), (2633223943/5000000000 : ℝ)] ![(6417363649181/50000000000000 : ℝ), (8851919554323/20000000000000 : ℝ), (21452837458697/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-263779389/1250000000 : ℝ)|^1057 ≤ (6417363649181/50000000000000 : ℝ)^801
        have hw : |(-263779389/1250000000 : ℝ)|=(263779389/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391910153/10000000000 : ℝ)|^1057 ≤ (8851919554323/20000000000000 : ℝ)^801
        have hw : |(5391910153/10000000000 : ℝ)|=(5391910153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633223943/5000000000 : ℝ)|^1057 ≤ (21452837458697/50000000000000 : ℝ)^801
        have hw : |(2633223943/5000000000 : ℝ)|=(2633223943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s5_1 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5344476093/10000000000 : ℝ)*x 0 + (-2173858071/10000000000 : ℝ)*x 1 + (5266447881/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344476093/10000000000 : ℝ)^1057 ≤ (136707866883/312500000000 : ℝ)^801 := by
    have hnat : (5344476093 : ℕ)^1057*312500000000^801 ≤ 136707866883^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344476093 10000000000 136707866883 312500000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2173858071/10000000000 : ℝ)^1057 ≤ (3336951931939/25000000000000 : ℝ)^801 := by
    have hnat : (2173858071 : ℕ)^1057*25000000000000^801 ≤ 3336951931939^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173858071 10000000000 3336951931939 25000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266447881/10000000000 : ℝ)^1057 ≤ (1072641871591/2500000000000 : ℝ)^801 := by
    have hnat : (5266447881 : ℕ)^1057*2500000000000^801 ≤ 1072641871591^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266447881 10000000000 1072641871591 2500000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344476093/10000000000 : ℝ), (-2173858071/10000000000 : ℝ), (5266447881/10000000000 : ℝ)] ![(136707866883/312500000000 : ℝ), (3336951931939/25000000000000 : ℝ), (1072641871591/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344476093/10000000000 : ℝ)|^1057 ≤ (136707866883/312500000000 : ℝ)^801
        have hw : |(5344476093/10000000000 : ℝ)|=(5344476093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2173858071/10000000000 : ℝ)|^1057 ≤ (3336951931939/25000000000000 : ℝ)^801
        have hw : |(-2173858071/10000000000 : ℝ)|=(2173858071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266447881/10000000000 : ℝ)|^1057 ≤ (1072641871591/2500000000000 : ℝ)^801
        have hw : |(5266447881/10000000000 : ℝ)|=(5266447881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s5_2 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2672238041/5000000000 : ℝ)*x 0 + (5266447879/10000000000 : ℝ)*x 1 + (-2173858087/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672238041/5000000000 : ℝ)^1057 ≤ (8749303456749/20000000000000 : ℝ)^801 := by
    have hnat : (2672238041 : ℕ)^1057*20000000000000^801 ≤ 8749303456749^801*5000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672238041 5000000000 8749303456749 20000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266447879/10000000000 : ℝ)^1057 ≤ (42905674842139/100000000000000 : ℝ)^801 := by
    have hnat : (5266447879 : ℕ)^1057*100000000000000^801 ≤ 42905674842139^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266447879 10000000000 42905674842139 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2173858087/10000000000 : ℝ)^1057 ≤ (3336951964349/25000000000000 : ℝ)^801 := by
    have hnat : (2173858087 : ℕ)^1057*25000000000000^801 ≤ 3336951964349^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173858087 10000000000 3336951964349 25000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672238041/5000000000 : ℝ), (5266447879/10000000000 : ℝ), (-2173858087/10000000000 : ℝ)] ![(8749303456749/20000000000000 : ℝ), (42905674842139/100000000000000 : ℝ), (3336951964349/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672238041/5000000000 : ℝ)|^1057 ≤ (8749303456749/20000000000000 : ℝ)^801
        have hw : |(2672238041/5000000000 : ℝ)|=(2672238041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266447879/10000000000 : ℝ)|^1057 ≤ (42905674842139/100000000000000 : ℝ)^801
        have hw : |(5266447879/10000000000 : ℝ)|=(5266447879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2173858087/10000000000 : ℝ)|^1057 ≤ (3336951964349/25000000000000 : ℝ)^801
        have hw : |(-2173858087/10000000000 : ℝ)|=(2173858087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s5_3 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4347846441/10000000000 : ℝ)*x 0 + (2110946081/5000000000 : ℝ)*x 1 + (4477433663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4347846441/10000000000 : ℝ)^1057 ≤ (1041157594967/3125000000000 : ℝ)^801 := by
    have hnat : (4347846441 : ℕ)^1057*3125000000000^801 ≤ 1041157594967^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4347846441 10000000000 1041157594967 3125000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2110946081/5000000000 : ℝ)^1057 ≤ (16024667763597/50000000000000 : ℝ)^801 := by
    have hnat : (2110946081 : ℕ)^1057*50000000000000^801 ≤ 16024667763597^801*5000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110946081 5000000000 16024667763597 50000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4477433663/10000000000 : ℝ)^1057 ≤ (17316810712679/50000000000000 : ℝ)^801 := by
    have hnat : (4477433663 : ℕ)^1057*50000000000000^801 ≤ 17316810712679^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4477433663 10000000000 17316810712679 50000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4347846441/10000000000 : ℝ), (2110946081/5000000000 : ℝ), (4477433663/10000000000 : ℝ)] ![(1041157594967/3125000000000 : ℝ), (16024667763597/50000000000000 : ℝ), (17316810712679/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4347846441/10000000000 : ℝ)|^1057 ≤ (1041157594967/3125000000000 : ℝ)^801
        have hw : |(4347846441/10000000000 : ℝ)|=(4347846441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2110946081/5000000000 : ℝ)|^1057 ≤ (16024667763597/50000000000000 : ℝ)^801
        have hw : |(2110946081/5000000000 : ℝ)|=(2110946081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4477433663/10000000000 : ℝ)|^1057 ≤ (17316810712679/50000000000000 : ℝ)^801
        have hw : |(4477433663/10000000000 : ℝ)|=(4477433663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s5_4 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-211023989/1000000000 : ℝ)*x 0 + (5266770171/10000000000 : ℝ)*x 1 + (2695793369/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211023989/1000000000 : ℝ)^1057 ≤ (6417382823263/50000000000000 : ℝ)^801 := by
    have hnat : (211023989 : ℕ)^1057*50000000000000^801 ≤ 6417382823263^801*1000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211023989 1000000000 6417382823263 50000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266770171/10000000000 : ℝ)^1057 ≤ (2681821235123/6250000000000 : ℝ)^801 := by
    have hnat : (5266770171 : ℕ)^1057*6250000000000^801 ≤ 2681821235123^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266770171 10000000000 2681821235123 6250000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695793369/5000000000 : ℝ)^1057 ≤ (22128047292459/50000000000000 : ℝ)^801 := by
    have hnat : (2695793369 : ℕ)^1057*50000000000000^801 ≤ 22128047292459^801*5000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695793369 5000000000 22128047292459 50000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-211023989/1000000000 : ℝ), (5266770171/10000000000 : ℝ), (2695793369/5000000000 : ℝ)] ![(6417382823263/50000000000000 : ℝ), (2681821235123/6250000000000 : ℝ), (22128047292459/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-211023989/1000000000 : ℝ)|^1057 ≤ (6417382823263/50000000000000 : ℝ)^801
        have hw : |(-211023989/1000000000 : ℝ)|=(211023989/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266770171/10000000000 : ℝ)|^1057 ≤ (2681821235123/6250000000000 : ℝ)^801
        have hw : |(5266770171/10000000000 : ℝ)|=(5266770171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695793369/5000000000 : ℝ)|^1057 ≤ (22128047292459/50000000000000 : ℝ)^801
        have hw : |(2695793369/5000000000 : ℝ)|=(2695793369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s5_5 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1328104763/2500000000 : ℝ)*x 0 + (-102435957/500000000 : ℝ)*x 1 + (1347896701/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328104763/2500000000 : ℝ)^1057 ≤ (21700294107177/50000000000000 : ℝ)^801 := by
    have hnat : (1328104763 : ℕ)^1057*50000000000000^801 ≤ 21700294107177^801*2500000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328104763 2500000000 21700294107177 50000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (102435957/500000000 : ℝ)^1057 ≤ (493732658757/4000000000000 : ℝ)^801 := by
    have hnat : (102435957 : ℕ)^1057*4000000000000^801 ≤ 493732658757^801*500000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      102435957 500000000 493732658757 4000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347896701/2500000000 : ℝ)^1057 ≤ (22128047649907/50000000000000 : ℝ)^801 := by
    have hnat : (1347896701 : ℕ)^1057*50000000000000^801 ≤ 22128047649907^801*2500000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347896701 2500000000 22128047649907 50000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328104763/2500000000 : ℝ), (-102435957/500000000 : ℝ), (1347896701/2500000000 : ℝ)] ![(21700294107177/50000000000000 : ℝ), (493732658757/4000000000000 : ℝ), (22128047649907/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328104763/2500000000 : ℝ)|^1057 ≤ (21700294107177/50000000000000 : ℝ)^801
        have hw : |(1328104763/2500000000 : ℝ)|=(1328104763/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-102435957/500000000 : ℝ)|^1057 ≤ (493732658757/4000000000000 : ℝ)^801
        have hw : |(-102435957/500000000 : ℝ)|=(102435957/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347896701/2500000000 : ℝ)|^1057 ≤ (22128047649907/50000000000000 : ℝ)^801
        have hw : |(1347896701/2500000000 : ℝ)|=(1347896701/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s5_6 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1328104721/2500000000 : ℝ)*x 0 + (5391587001/10000000000 : ℝ)*x 1 + (-20487191/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328104721/2500000000 : ℝ)^1057 ≤ (21700293201601/50000000000000 : ℝ)^801 := by
    have hnat : (1328104721 : ℕ)^1057*50000000000000^801 ≤ 21700293201601^801*2500000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328104721 2500000000 21700293201601 50000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391587001/10000000000 : ℝ)^1057 ≤ (4425609743367/10000000000000 : ℝ)^801 := by
    have hnat : (5391587001 : ℕ)^1057*10000000000000^801 ≤ 4425609743367^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391587001 10000000000 4425609743367 10000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (20487191/100000000 : ℝ)^1057 ≤ (12343316150907/100000000000000 : ℝ)^801 := by
    have hnat : (20487191 : ℕ)^1057*100000000000000^801 ≤ 12343316150907^801*100000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20487191 100000000 12343316150907 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328104721/2500000000 : ℝ), (5391587001/10000000000 : ℝ), (-20487191/100000000 : ℝ)] ![(21700293201601/50000000000000 : ℝ), (4425609743367/10000000000000 : ℝ), (12343316150907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328104721/2500000000 : ℝ)|^1057 ≤ (21700293201601/50000000000000 : ℝ)^801
        have hw : |(1328104721/2500000000 : ℝ)|=(1328104721/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391587001/10000000000 : ℝ)|^1057 ≤ (4425609743367/10000000000000 : ℝ)^801
        have hw : |(5391587001/10000000000 : ℝ)|=(5391587001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-20487191/100000000 : ℝ)|^1057 ≤ (12343316150907/100000000000000 : ℝ)^801
        have hw : |(-20487191/100000000 : ℝ)|=(20487191/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s5_7 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4347856077/10000000000 : ℝ)*x 0 + (559597209/1250000000 : ℝ)*x 1 + (4222550831/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4347856077/10000000000 : ℝ)^1057 ≤ (16658570238843/50000000000000 : ℝ)^801 := by
    have hnat : (4347856077 : ℕ)^1057*50000000000000^801 ≤ 16658570238843^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4347856077 10000000000 16658570238843 50000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (559597209/1250000000 : ℝ)^1057 ≤ (6925385135999/20000000000000 : ℝ)^801 := by
    have hnat : (559597209 : ℕ)^1057*20000000000000^801 ≤ 6925385135999^801*1250000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      559597209 1250000000 6925385135999 20000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4222550831/10000000000 : ℝ)^1057 ≤ (32055933832639/100000000000000 : ℝ)^801 := by
    have hnat : (4222550831 : ℕ)^1057*100000000000000^801 ≤ 32055933832639^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4222550831 10000000000 32055933832639 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4347856077/10000000000 : ℝ), (559597209/1250000000 : ℝ), (4222550831/10000000000 : ℝ)] ![(16658570238843/50000000000000 : ℝ), (6925385135999/20000000000000 : ℝ), (32055933832639/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4347856077/10000000000 : ℝ)|^1057 ≤ (16658570238843/50000000000000 : ℝ)^801
        have hw : |(4347856077/10000000000 : ℝ)|=(4347856077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(559597209/1250000000 : ℝ)|^1057 ≤ (6925385135999/20000000000000 : ℝ)^801
        have hw : |(559597209/1250000000 : ℝ)|=(559597209/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4222550831/10000000000 : ℝ)|^1057 ≤ (32055933832639/100000000000000 : ℝ)^801
        have hw : |(4222550831/10000000000 : ℝ)|=(4222550831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1263_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151839963/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14239/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5693/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11481/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14139/100000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (5693/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14239/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5693/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14239/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5693/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14239/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5693/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14239/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5693/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14239/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5693/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5693/50000 : ℝ) ^ (8455/2048 : ℝ) ≤ (12714691332577369/100000000000000000000 : ℝ) := by
    have hpowers : (5693/50000 : ℝ)^8455 ≤ (12714691332577369/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5693 : ℕ)^8455*100000000000000000000^2048 ≤ 12714691332577369^2048*50000^8455 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5693 50000 12714691332577369 100000000000000000000 8455 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5693/50000 : ℝ)) (X := (12714691332577369/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8455 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14239/100000 : ℝ) ^ (8455/2048 : ℝ) ≤ (16002193588170103/50000000000000000000 : ℝ) := by
    have hpowers : (14239/100000 : ℝ)^8455 ≤ (16002193588170103/50000000000000000000 : ℝ)^2048 := by
      have hnat : (14239 : ℕ)^8455*50000000000000000000^2048 ≤ 16002193588170103^2048*100000^8455 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14239 100000 16002193588170103 50000000000000000000 8455 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14239/100000 : ℝ)) (X := (16002193588170103/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8455 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50012714691332577369/50000000000000000000 : ℝ) ≤ (10000615900161481/10000000000000000 : ℝ) ^ (8455/2048 : ℝ) := by
    have hpowers : (50012714691332577369/50000000000000000000 : ℝ)^2048 ≤ (10000615900161481/10000000000000000 : ℝ)^8455 := by
      have hnat : (50012714691332577369 : ℕ)^2048*10000000000000000^8455 ≤ 10000615900161481^8455*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50012714691332577369 50000000000000000000 10000615900161481 10000000000000000 2048 8455 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000615900161481/10000000000000000 : ℝ)) (X := (50012714691332577369/50000000000000000000 : ℝ)) (by norm_num) 8455 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (4001788763140356703/4000000000000000000 : ℝ) ≤ (10001083017849463/10000000000000000 : ℝ) ^ (8455/2048 : ℝ) := by
    have hpowers : (4001788763140356703/4000000000000000000 : ℝ)^2048 ≤ (10001083017849463/10000000000000000 : ℝ)^8455 := by
      have hnat : (4001788763140356703 : ℕ)^2048*10000000000000000^8455 ≤ 10001083017849463^8455*4000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4001788763140356703 4000000000000000000 10001083017849463 10000000000000000 2048 8455 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001083017849463/10000000000000000 : ℝ)) (X := (4001788763140356703/4000000000000000000 : ℝ)) (by norm_num) 8455 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016002193588170103/25000000000000000000 : ℝ) ≤ (2000310027107489/2000000000000000 : ℝ) ^ (8455/2048 : ℝ) := by
    have hpowers : (25016002193588170103/25000000000000000000 : ℝ)^2048 ≤ (2000310027107489/2000000000000000 : ℝ)^8455 := by
      have hnat : (25016002193588170103 : ℕ)^2048*2000000000000000^8455 ≤ 2000310027107489^8455*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016002193588170103 25000000000000000000 2000310027107489 2000000000000000 2048 8455 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000310027107489/2000000000000000 : ℝ)) (X := (25016002193588170103/25000000000000000000 : ℝ)) (by norm_num) 8455 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(12714691332577369/100000000000000000000 : ℝ) ≤ ((9507039986389993063/9510000000000000000 : ℝ)+2*(77852947997/47550000000000 : ℝ)*(5693/50000 : ℝ))^(8455/2048 : ℝ) := by
    rw [show (9507039986389993063/9510000000000000000 : ℝ)+2*(77852947997/47550000000000 : ℝ)*(5693/50000 : ℝ)=(10000615900161481/10000000000000000 : ℝ) by norm_num, show 1+2*(12714691332577369/100000000000000000000 : ℝ)=(50012714691332577369/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16002193588170103/50000000000000000000 : ℝ)+(12714691332577369/100000000000000000000 : ℝ) ≤ ((9507039986389993063/9510000000000000000 : ℝ)+(77852947997/47550000000000 : ℝ)*((14239/100000 : ℝ)+(5693/50000 : ℝ)))^(8455/2048 : ℝ) := by
    rw [show (9507039986389993063/9510000000000000000 : ℝ)+(77852947997/47550000000000 : ℝ)*((14239/100000 : ℝ)+(5693/50000 : ℝ))=(10001083017849463/10000000000000000 : ℝ) by norm_num, show 1+(16002193588170103/50000000000000000000 : ℝ)+(12714691332577369/100000000000000000000 : ℝ)=(4001788763140356703/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16002193588170103/50000000000000000000 : ℝ) ≤ ((9507039986389993063/9510000000000000000 : ℝ)+2*(77852947997/47550000000000 : ℝ)*(14239/100000 : ℝ))^(8455/2048 : ℝ) := by
    rw [show (9507039986389993063/9510000000000000000 : ℝ)+2*(77852947997/47550000000000 : ℝ)*(14239/100000 : ℝ)=(2000310027107489/2000000000000000 : ℝ) by norm_num, show 1+2*(16002193588170103/50000000000000000000 : ℝ)=(25016002193588170103/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9507039986389993063/9510000000000000000 : ℝ)*(X 1 0+X 2 0)+(77852947997/47550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8455/2048 : ℝ)) (lo := (5693/50000 : ℝ)) (hi := (14239/100000 : ℝ)) (c := (9507039986389993063/9510000000000000000 : ℝ)) (alpha := (77852947997/47550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9507039986389993063/9510000000000000000 : ℝ)*(X 0 1+X 2 1)+(77852947997/47550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8455/2048 : ℝ)) (lo := (5693/50000 : ℝ)) (hi := (14239/100000 : ℝ)) (c := (9507039986389993063/9510000000000000000 : ℝ)) (alpha := (77852947997/47550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9507039986389993063/9510000000000000000 : ℝ)*(X 0 2+X 1 2)+(77852947997/47550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8455/2048 : ℝ)) (lo := (5693/50000 : ℝ)) (hi := (14239/100000 : ℝ)) (c := (9507039986389993063/9510000000000000000 : ℝ)) (alpha := (77852947997/47550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-263779389/1250000000 : ℝ)*X 0 0+(5391910153/10000000000 : ℝ)*X 0 1+(2633223943/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344476093/10000000000 : ℝ)*X 1 0+(-2173858071/10000000000 : ℝ)*X 1 1+(5266447881/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672238041/5000000000 : ℝ)*X 2 0+(5266447879/10000000000 : ℝ)*X 2 1+(-2173858087/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4347846441/10000000000 : ℝ)*X 0 0+(2110946081/5000000000 : ℝ)*X 0 1+(4477433663/10000000000 : ℝ)*X 0 2+(4347846441/10000000000 : ℝ)*X 1 0+(2110946081/5000000000 : ℝ)*X 1 1+(4477433663/10000000000 : ℝ)*X 1 2+(4347846441/10000000000 : ℝ)*X 2 0+(2110946081/5000000000 : ℝ)*X 2 1+(4477433663/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-211023989/1000000000 : ℝ)*X 0 0+(5266770171/10000000000 : ℝ)*X 0 1+(2695793369/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328104763/2500000000 : ℝ)*X 1 0+(-102435957/500000000 : ℝ)*X 1 1+(1347896701/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328104721/2500000000 : ℝ)*X 2 0+(5391587001/10000000000 : ℝ)*X 2 1+(-20487191/100000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4347856077/10000000000 : ℝ)*X 0 0+(559597209/1250000000 : ℝ)*X 0 1+(4222550831/10000000000 : ℝ)*X 0 2+(4347856077/10000000000 : ℝ)*X 1 0+(559597209/1250000000 : ℝ)*X 1 1+(4222550831/10000000000 : ℝ)*X 1 2+(4347856077/10000000000 : ℝ)*X 2 0+(559597209/1250000000 : ℝ)*X 2 1+(4222550831/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (109953605799662203593880877/15850000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1359792337/100000000000000 : ℝ)*(base19) + (612071817/50000000000000 : ℝ)*(base23) + (31864733/50000000000000 : ℝ)*(lower2) + (192648933/100000000000000 : ℝ)*(upper3) + (3756293/5000000000000 : ℝ)*(upper5) + (594194804593207/10000000000000 : ℝ)*(major0) + (594194804593207/10000000000000 : ℝ)*(major1) + (594194804593207/10000000000000 : ℝ)*(major2) + (7970563579741501/100000000000000 : ℝ)*(sp0) + (7970597942712351/100000000000000 : ℝ)*(sp1) + (3985299039180527/50000000000000 : ℝ)*(sp2) + (1956638049766613/50000000000000 : ℝ)*(sp3) + (35722763187/100000000000000 : ℝ)*(sp4) + (20458588347/100000000000000 : ℝ)*(sp7) + (1956648279060787/50000000000000 : ℝ)*(f.failure) + (498162456406543/6250000000000 : ℝ)*(f.sum) + (1927323553823/951000000000000000000000000 : ℝ)*base65 + (57202857330123041/95100000000000000000000000000000 : ℝ)*base67 + (1615210307869023041/95100000000000000000000000000000 : ℝ)*base69 + (1537501821079923041/95100000000000000000000000000000 : ℝ)*base71 + (4823118883609/951000000000000000000000000 : ℝ)*base74 + (1976138835930123041/95100000000000000000000000000000 : ℝ)*base75 + (456406372926423041/95100000000000000000000000000000 : ℝ)*base77 + (1456252257926523041/95100000000000000000000000000000 : ℝ)*base79 + (2686755393869/951000000000000000000000000 : ℝ)*base81 + (72830881/5000000000000000000000 : ℝ)*base89 + (72830881/5000000000000000000000 : ℝ)*base91 + (72830881/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (645992931087490901708697229/79250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1019965487/100000000000000 : ℝ)*(base19) + (44300783/5000000000000 : ℝ)*(base23) + (37308277/25000000000000 : ℝ)*(upper3) + (17325237/50000000000000 : ℝ)*(lower4) + (2986311240321083/50000000000000 : ℝ)*(major0) + (2986311240321083/50000000000000 : ℝ)*(major1) + (2986311240321083/50000000000000 : ℝ)*(major2) + (29861744667/100000000000000 : ℝ)*(sp1) + (38841512643/100000000000000 : ℝ)*(sp2) + (6925261/781250000000 : ℝ)*(sp3) + (8011746312310031/100000000000000 : ℝ)*(sp4) + (8011715430599877/100000000000000 : ℝ)*(sp5) + (8011706584781727/100000000000000 : ℝ)*(sp6) + (1966748745414937/50000000000000 : ℝ)*(sp7) + (3933498377263281/100000000000000 : ℝ)*(f.failure) + (8011746312310031/100000000000000 : ℝ)*(f.sum) + (1216743647647/594375000000000000000000000 : ℝ)*base66 + (529446667324652771/475500000000000000000000000000000 : ℝ)*base68 + (246521330474847229/475500000000000000000000000000000 : ℝ)*base69 + (1810897222507347229/475500000000000000000000000000000 : ℝ)*base71 + (17894526071681/4755000000000000000000000000 : ℝ)*base74 + (9186663954028652771/475500000000000000000000000000000 : ℝ)*base76 + (248795105397152771/475500000000000000000000000000000 : ℝ)*base78 + (9192904328061152771/475500000000000000000000000000000 : ℝ)*base80 + (30913434908531/4755000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (28298603/10000000000000000000000 : ℝ)*base89 + (28298603/10000000000000000000000 : ℝ)*base91 + (28298603/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1263_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151839963/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14239/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5693/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11481/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14139/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1263_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1263_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151839963/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16169/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9583/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11481/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14139/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1263_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1263_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1263_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151839963/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16169/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9583/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11481/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14139/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1263_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
