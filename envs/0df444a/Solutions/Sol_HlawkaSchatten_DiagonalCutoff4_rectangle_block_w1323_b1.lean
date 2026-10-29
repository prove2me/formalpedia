-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1323_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:44:14.763291+00:00
-- url     : https://prove2.me/submissions/69e98403-e63f-442a-9a9b-cbaad07e373d

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
theorem support_rectangle_w1323_s3_0 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-128658411/625000000 : ℝ)*x 0 + (5429666231/10000000000 : ℝ)*x 1 + (1307329121/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (128658411/625000000 : ℝ)^4283 ≤ (12527761181079/100000000000000 : ℝ)^3259 := by
    have hnat : (128658411 : ℕ)^4283*100000000000000^3259 ≤ 12527761181079^3259*625000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128658411 625000000 12527761181079 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5429666231/10000000000 : ℝ)^4283 ≤ (8963281608709/20000000000000 : ℝ)^3259 := by
    have hnat : (5429666231 : ℕ)^4283*20000000000000^3259 ≤ 8963281608709^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429666231 10000000000 8963281608709 20000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1307329121/2500000000 : ℝ)^4283 ≤ (10663957689403/25000000000000 : ℝ)^3259 := by
    have hnat : (1307329121 : ℕ)^4283*25000000000000^3259 ≤ 10663957689403^3259*2500000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307329121 2500000000 10663957689403 25000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-128658411/625000000 : ℝ), (5429666231/10000000000 : ℝ), (1307329121/2500000000 : ℝ)] ![(12527761181079/100000000000000 : ℝ), (8963281608709/20000000000000 : ℝ), (10663957689403/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-128658411/625000000 : ℝ)|^4283 ≤ (12527761181079/100000000000000 : ℝ)^3259
        have hw : |(-128658411/625000000 : ℝ)|=(128658411/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5429666231/10000000000 : ℝ)|^4283 ≤ (8963281608709/20000000000000 : ℝ)^3259
        have hw : |(5429666231/10000000000 : ℝ)|=(5429666231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1307329121/2500000000 : ℝ)|^4283 ≤ (10663957689403/25000000000000 : ℝ)^3259
        have hw : |(1307329121/2500000000 : ℝ)|=(1307329121/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_s3_1 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676689831/5000000000 : ℝ)*x 0 + (-1080489657/5000000000 : ℝ)*x 1 + (13073291/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676689831/5000000000 : ℝ)^4283 ≤ (21995362915627/50000000000000 : ℝ)^3259 := by
    have hnat : (2676689831 : ℕ)^4283*50000000000000^3259 ≤ 21995362915627^3259*5000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676689831 5000000000 21995362915627 50000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1080489657/5000000000 : ℝ)^4283 ≤ (13353444288699/100000000000000 : ℝ)^3259 := by
    have hnat : (1080489657 : ℕ)^4283*100000000000000^3259 ≤ 13353444288699^3259*5000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080489657 5000000000 13353444288699 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13073291/25000000 : ℝ)^4283 ≤ (42655829857127/100000000000000 : ℝ)^3259 := by
    have hnat : (13073291 : ℕ)^4283*100000000000000^3259 ≤ 42655829857127^3259*25000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13073291 25000000 42655829857127 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676689831/5000000000 : ℝ), (-1080489657/5000000000 : ℝ), (13073291/25000000 : ℝ)] ![(21995362915627/50000000000000 : ℝ), (13353444288699/100000000000000 : ℝ), (42655829857127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676689831/5000000000 : ℝ)|^4283 ≤ (21995362915627/50000000000000 : ℝ)^3259
        have hw : |(2676689831/5000000000 : ℝ)|=(2676689831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1080489657/5000000000 : ℝ)|^4283 ≤ (13353444288699/100000000000000 : ℝ)^3259
        have hw : |(-1080489657/5000000000 : ℝ)|=(1080489657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(13073291/25000000 : ℝ)|^4283 ≤ (42655829857127/100000000000000 : ℝ)^3259
        have hw : |(13073291/25000000 : ℝ)|=(13073291/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_s3_2 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676689913/5000000000 : ℝ)*x 0 + (1045863157/2000000000 : ℝ)*x 1 + (-540244977/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676689913/5000000000 : ℝ)^4283 ≤ (5498840950293/12500000000000 : ℝ)^3259 := by
    have hnat : (2676689913 : ℕ)^4283*12500000000000^3259 ≤ 5498840950293^3259*5000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676689913 5000000000 5498840950293 12500000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1045863157/2000000000 : ℝ)^4283 ≤ (42655823264291/100000000000000 : ℝ)^3259 := by
    have hnat : (1045863157 : ℕ)^4283*100000000000000^3259 ≤ 42655823264291^3259*2000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045863157 2000000000 42655823264291 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (540244977/2500000000 : ℝ)^4283 ≤ (13353449112539/100000000000000 : ℝ)^3259 := by
    have hnat : (540244977 : ℕ)^4283*100000000000000^3259 ≤ 13353449112539^3259*2500000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540244977 2500000000 13353449112539 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676689913/5000000000 : ℝ), (1045863157/2000000000 : ℝ), (-540244977/2500000000 : ℝ)] ![(5498840950293/12500000000000 : ℝ), (42655823264291/100000000000000 : ℝ), (13353449112539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676689913/5000000000 : ℝ)|^4283 ≤ (5498840950293/12500000000000 : ℝ)^3259
        have hw : |(2676689913/5000000000 : ℝ)|=(2676689913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1045863157/2000000000 : ℝ)|^4283 ≤ (42655823264291/100000000000000 : ℝ)^3259
        have hw : |(1045863157/2000000000 : ℝ)|=(1045863157/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-540244977/2500000000 : ℝ)|^4283 ≤ (13353449112539/100000000000000 : ℝ)^3259
        have hw : |(-540244977/2500000000 : ℝ)|=(540244977/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_s3_3 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2165212863/5000000000 : ℝ)*x 0 + (1031705191/2500000000 : ℝ)*x 1 + (35495863/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2165212863/5000000000 : ℝ)^4283 ≤ (6658187583821/20000000000000 : ℝ)^3259 := by
    have hnat : (2165212863 : ℕ)^4283*20000000000000^3259 ≤ 6658187583821^3259*5000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2165212863 5000000000 6658187583821 20000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1031705191/2500000000 : ℝ)^4283 ≤ (15624618303407/50000000000000 : ℝ)^3259 := by
    have hnat : (1031705191 : ℕ)^4283*50000000000000^3259 ≤ 15624618303407^3259*2500000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031705191 2500000000 15624618303407 50000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (35495863/78125000 : ℝ)^4283 ≤ (8864956363739/25000000000000 : ℝ)^3259 := by
    have hnat : (35495863 : ℕ)^4283*25000000000000^3259 ≤ 8864956363739^3259*78125000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35495863 78125000 8864956363739 25000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2165212863/5000000000 : ℝ), (1031705191/2500000000 : ℝ), (35495863/78125000 : ℝ)] ![(6658187583821/20000000000000 : ℝ), (15624618303407/50000000000000 : ℝ), (8864956363739/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2165212863/5000000000 : ℝ)|^4283 ≤ (6658187583821/20000000000000 : ℝ)^3259
        have hw : |(2165212863/5000000000 : ℝ)|=(2165212863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1031705191/2500000000 : ℝ)|^4283 ≤ (15624618303407/50000000000000 : ℝ)^3259
        have hw : |(1031705191/2500000000 : ℝ)|=(1031705191/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(35495863/78125000 : ℝ)|^4283 ≤ (8864956363739/25000000000000 : ℝ)^3259
        have hw : |(35495863/78125000 : ℝ)|=(35495863/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_s3_4 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-257319387/1250000000 : ℝ)*x 0 + (2615080463/5000000000 : ℝ)*x 1 + (2714408267/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (257319387/1250000000 : ℝ)^4283 ≤ (6263962649697/50000000000000 : ℝ)^3259 := by
    have hnat : (257319387 : ℕ)^4283*50000000000000^3259 ≤ 6263962649697^3259*1250000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257319387 1250000000 6263962649697 50000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2615080463/5000000000 : ℝ)^4283 ≤ (21332441727831/50000000000000 : ℝ)^3259 := by
    have hnat : (2615080463 : ℕ)^4283*50000000000000^3259 ≤ 21332441727831^3259*5000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615080463 5000000000 21332441727831 50000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2714408267/5000000000 : ℝ)^4283 ≤ (8961438245019/20000000000000 : ℝ)^3259 := by
    have hnat : (2714408267 : ℕ)^4283*20000000000000^3259 ≤ 8961438245019^3259*5000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714408267 5000000000 8961438245019 20000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-257319387/1250000000 : ℝ), (2615080463/5000000000 : ℝ), (2714408267/5000000000 : ℝ)] ![(6263962649697/50000000000000 : ℝ), (21332441727831/50000000000000 : ℝ), (8961438245019/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-257319387/1250000000 : ℝ)|^4283 ≤ (6263962649697/50000000000000 : ℝ)^3259
        have hw : |(-257319387/1250000000 : ℝ)|=(257319387/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2615080463/5000000000 : ℝ)|^4283 ≤ (21332441727831/50000000000000 : ℝ)^3259
        have hw : |(2615080463/5000000000 : ℝ)|=(2615080463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2714408267/5000000000 : ℝ)|^4283 ≤ (8961438245019/20000000000000 : ℝ)^3259
        have hw : |(2714408267/5000000000 : ℝ)|=(2714408267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_s3_5 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (132547159/250000000 : ℝ)*x 0 + (-980739737/5000000000 : ℝ)*x 1 + (5428816739/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132547159/250000000 : ℝ)^4283 ≤ (43435474886619/100000000000000 : ℝ)^3259 := by
    have hnat : (132547159 : ℕ)^4283*100000000000000^3259 ≤ 43435474886619^3259*250000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132547159 250000000 43435474886619 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (980739737/5000000000 : ℝ)^4283 ≤ (11757331646257/100000000000000 : ℝ)^3259 := by
    have hnat : (980739737 : ℕ)^4283*100000000000000^3259 ≤ 11757331646257^3259*5000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      980739737 5000000000 11757331646257 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5428816739/10000000000 : ℝ)^4283 ≤ (44807193448713/100000000000000 : ℝ)^3259 := by
    have hnat : (5428816739 : ℕ)^4283*100000000000000^3259 ≤ 44807193448713^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428816739 10000000000 44807193448713 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132547159/250000000 : ℝ), (-980739737/5000000000 : ℝ), (5428816739/10000000000 : ℝ)] ![(43435474886619/100000000000000 : ℝ), (11757331646257/100000000000000 : ℝ), (44807193448713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132547159/250000000 : ℝ)|^4283 ≤ (43435474886619/100000000000000 : ℝ)^3259
        have hw : |(132547159/250000000 : ℝ)|=(132547159/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-980739737/5000000000 : ℝ)|^4283 ≤ (11757331646257/100000000000000 : ℝ)^3259
        have hw : |(-980739737/5000000000 : ℝ)|=(980739737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5428816739/10000000000 : ℝ)|^4283 ≤ (44807193448713/100000000000000 : ℝ)^3259
        have hw : |(5428816739/10000000000 : ℝ)|=(5428816739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_s3_6 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5301888083/10000000000 : ℝ)*x 0 + (542881553/1000000000 : ℝ)*x 1 + (-1961478783/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5301888083/10000000000 : ℝ)^4283 ≤ (21717746718721/50000000000000 : ℝ)^3259 := by
    have hnat : (5301888083 : ℕ)^4283*50000000000000^3259 ≤ 21717746718721^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5301888083 10000000000 21717746718721 50000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (542881553/1000000000 : ℝ)^4283 ≤ (5600897541849/12500000000000 : ℝ)^3259 := by
    have hnat : (542881553 : ℕ)^4283*12500000000000^3259 ≤ 5600897541849^3259*1000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542881553 1000000000 5600897541849 12500000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1961478783/10000000000 : ℝ)^4283 ≤ (11757326202901/100000000000000 : ℝ)^3259 := by
    have hnat : (1961478783 : ℕ)^4283*100000000000000^3259 ≤ 11757326202901^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1961478783 10000000000 11757326202901 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5301888083/10000000000 : ℝ), (542881553/1000000000 : ℝ), (-1961478783/10000000000 : ℝ)] ![(21717746718721/50000000000000 : ℝ), (5600897541849/12500000000000 : ℝ), (11757326202901/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5301888083/10000000000 : ℝ)|^4283 ≤ (21717746718721/50000000000000 : ℝ)^3259
        have hw : |(5301888083/10000000000 : ℝ)|=(5301888083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(542881553/1000000000 : ℝ)|^4283 ≤ (5600897541849/12500000000000 : ℝ)^3259
        have hw : |(542881553/1000000000 : ℝ)|=(542881553/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1961478783/10000000000 : ℝ)|^4283 ≤ (11757326202901/100000000000000 : ℝ)^3259
        have hw : |(-1961478783/10000000000 : ℝ)|=(1961478783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_s3_7 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1082617093/2500000000 : ℝ)*x 0 + (181668567/400000000 : ℝ)*x 1 + (4128587417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1082617093/2500000000 : ℝ)^4283 ≤ (16645684390519/50000000000000 : ℝ)^3259 := by
    have hnat : (1082617093 : ℕ)^4283*50000000000000^3259 ≤ 16645684390519^3259*2500000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082617093 2500000000 16645684390519 50000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (181668567/400000000 : ℝ)^4283 ≤ (35441812614503/100000000000000 : ℝ)^3259 := by
    have hnat : (181668567 : ℕ)^4283*100000000000000^3259 ≤ 35441812614503^3259*400000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      181668567 400000000 35441812614503 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4128587417/10000000000 : ℝ)^4283 ≤ (15633409297399/50000000000000 : ℝ)^3259 := by
    have hnat : (4128587417 : ℕ)^4283*50000000000000^3259 ≤ 15633409297399^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4128587417 10000000000 15633409297399 50000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1082617093/2500000000 : ℝ), (181668567/400000000 : ℝ), (4128587417/10000000000 : ℝ)] ![(16645684390519/50000000000000 : ℝ), (35441812614503/100000000000000 : ℝ), (15633409297399/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1082617093/2500000000 : ℝ)|^4283 ≤ (16645684390519/50000000000000 : ℝ)^3259
        have hw : |(1082617093/2500000000 : ℝ)|=(1082617093/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(181668567/400000000 : ℝ)|^4283 ≤ (35441812614503/100000000000000 : ℝ)^3259
        have hw : |(181668567/400000000 : ℝ)|=(181668567/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4128587417/10000000000 : ℝ)|^4283 ≤ (15633409297399/50000000000000 : ℝ)^3259
        have hw : |(4128587417/10000000000 : ℝ)|=(4128587417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1323_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76990221/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16181/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (389/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (1079/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15029/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16181/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (389/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16181/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (389/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16181/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (389/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16181/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (389/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16181/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (389/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16181/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (389/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (389/4000 : ℝ) ^ (2141/512 : ℝ) ≤ (5857577942984289/100000000000000000000 : ℝ) := by
    have hpowers : (389/4000 : ℝ)^2141 ≤ (5857577942984289/100000000000000000000 : ℝ)^512 := by
      have hnat : (389 : ℕ)^2141*100000000000000000000^512 ≤ 5857577942984289^512*4000^2141 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        389 4000 5857577942984289 100000000000000000000 2141 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (389/4000 : ℝ)) (X := (5857577942984289/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2141 512 (by norm_num) hpowers
    exact h
  have hpowhi : (16181/100000 : ℝ) ^ (2141/512 : ℝ) ≤ (12310754735737223/25000000000000000000 : ℝ) := by
    have hpowers : (16181/100000 : ℝ)^2141 ≤ (12310754735737223/25000000000000000000 : ℝ)^512 := by
      have hnat : (16181 : ℕ)^2141*25000000000000000000^512 ≤ 12310754735737223^512*100000^2141 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16181 100000 12310754735737223 25000000000000000000 2141 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16181/100000 : ℝ)) (X := (12310754735737223/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2141 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005857577942984289/50000000000000000000 : ℝ) ≤ (200005602888843/200000000000000 : ℝ) ^ (2141/512 : ℝ) := by
    have hpowers : (50005857577942984289/50000000000000000000 : ℝ)^512 ≤ (200005602888843/200000000000000 : ℝ)^2141 := by
      have hnat : (50005857577942984289 : ℕ)^512*200000000000000^2141 ≤ 200005602888843^2141*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005857577942984289 50000000000000000000 200005602888843 200000000000000 512 2141 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200005602888843/200000000000000 : ℝ)) (X := (50005857577942984289/50000000000000000000 : ℝ)) (by norm_num) 2141 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100055100596885933181/100000000000000000000 : ℝ) ≤ (2000263480559073/2000000000000000 : ℝ) ^ (2141/512 : ℝ) := by
    have hpowers : (100055100596885933181/100000000000000000000 : ℝ)^512 ≤ (2000263480559073/2000000000000000 : ℝ)^2141 := by
      have hnat : (100055100596885933181 : ℕ)^512*2000000000000000^2141 ≤ 2000263480559073^2141*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100055100596885933181 100000000000000000000 2000263480559073 2000000000000000 512 2141 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000263480559073/2000000000000000 : ℝ)) (X := (100055100596885933181/100000000000000000000 : ℝ)) (by norm_num) 2141 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (12512310754735737223/12500000000000000000 : ℝ) ≤ (500117733057429/500000000000000 : ℝ) ^ (2141/512 : ℝ) := by
    have hpowers : (12512310754735737223/12500000000000000000 : ℝ)^512 ≤ (500117733057429/500000000000000 : ℝ)^2141 := by
      have hnat : (12512310754735737223 : ℕ)^512*500000000000000^2141 ≤ 500117733057429^2141*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12512310754735737223 12500000000000000000 500117733057429 500000000000000 512 2141 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500117733057429/500000000000000 : ℝ)) (X := (12512310754735737223/12500000000000000000 : ℝ)) (by norm_num) 2141 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5857577942984289/100000000000000000000 : ℝ) ≤ ((430277559583656591/430400000000000000 : ℝ)+2*(69150556881/43040000000000 : ℝ)*(389/4000 : ℝ))^(2141/512 : ℝ) := by
    rw [show (430277559583656591/430400000000000000 : ℝ)+2*(69150556881/43040000000000 : ℝ)*(389/4000 : ℝ)=(200005602888843/200000000000000 : ℝ) by norm_num, show 1+2*(5857577942984289/100000000000000000000 : ℝ)=(50005857577942984289/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(12310754735737223/25000000000000000000 : ℝ)+(5857577942984289/100000000000000000000 : ℝ) ≤ ((430277559583656591/430400000000000000 : ℝ)+(69150556881/43040000000000 : ℝ)*((16181/100000 : ℝ)+(389/4000 : ℝ)))^(2141/512 : ℝ) := by
    rw [show (430277559583656591/430400000000000000 : ℝ)+(69150556881/43040000000000 : ℝ)*((16181/100000 : ℝ)+(389/4000 : ℝ))=(2000263480559073/2000000000000000 : ℝ) by norm_num, show 1+(12310754735737223/25000000000000000000 : ℝ)+(5857577942984289/100000000000000000000 : ℝ)=(100055100596885933181/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(12310754735737223/25000000000000000000 : ℝ) ≤ ((430277559583656591/430400000000000000 : ℝ)+2*(69150556881/43040000000000 : ℝ)*(16181/100000 : ℝ))^(2141/512 : ℝ) := by
    rw [show (430277559583656591/430400000000000000 : ℝ)+2*(69150556881/43040000000000 : ℝ)*(16181/100000 : ℝ)=(500117733057429/500000000000000 : ℝ) by norm_num, show 1+2*(12310754735737223/25000000000000000000 : ℝ)=(12512310754735737223/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (430277559583656591/430400000000000000 : ℝ)*(X 1 0+X 2 0)+(69150556881/43040000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2141/512 : ℝ)) (lo := (389/4000 : ℝ)) (hi := (16181/100000 : ℝ)) (c := (430277559583656591/430400000000000000 : ℝ)) (alpha := (69150556881/43040000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (430277559583656591/430400000000000000 : ℝ)*(X 0 1+X 2 1)+(69150556881/43040000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2141/512 : ℝ)) (lo := (389/4000 : ℝ)) (hi := (16181/100000 : ℝ)) (c := (430277559583656591/430400000000000000 : ℝ)) (alpha := (69150556881/43040000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (430277559583656591/430400000000000000 : ℝ)*(X 0 2+X 1 2)+(69150556881/43040000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2141/512 : ℝ)) (lo := (389/4000 : ℝ)) (hi := (16181/100000 : ℝ)) (c := (430277559583656591/430400000000000000 : ℝ)) (alpha := (69150556881/43040000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-128658411/625000000 : ℝ)*X 0 0+(5429666231/10000000000 : ℝ)*X 0 1+(1307329121/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676689831/5000000000 : ℝ)*X 1 0+(-1080489657/5000000000 : ℝ)*X 1 1+(13073291/25000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676689913/5000000000 : ℝ)*X 2 0+(1045863157/2000000000 : ℝ)*X 2 1+(-540244977/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2165212863/5000000000 : ℝ)*X 0 0+(1031705191/2500000000 : ℝ)*X 0 1+(35495863/78125000 : ℝ)*X 0 2+(2165212863/5000000000 : ℝ)*X 1 0+(1031705191/2500000000 : ℝ)*X 1 1+(35495863/78125000 : ℝ)*X 1 2+(2165212863/5000000000 : ℝ)*X 2 0+(1031705191/2500000000 : ℝ)*X 2 1+(35495863/78125000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-257319387/1250000000 : ℝ)*X 0 0+(2615080463/5000000000 : ℝ)*X 0 1+(2714408267/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((132547159/250000000 : ℝ)*X 1 0+(-980739737/5000000000 : ℝ)*X 1 1+(5428816739/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5301888083/10000000000 : ℝ)*X 2 0+(542881553/1000000000 : ℝ)*X 2 1+(-1961478783/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1082617093/2500000000 : ℝ)*X 0 0+(181668567/400000000 : ℝ)*X 0 1+(4128587417/10000000000 : ℝ)*X 0 2+(1082617093/2500000000 : ℝ)*X 1 0+(181668567/400000000 : ℝ)*X 1 1+(4128587417/10000000000 : ℝ)*X 1 2+(1082617093/2500000000 : ℝ)*X 2 0+(181668567/400000000 : ℝ)*X 2 1+(4128587417/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (52537923640647220594957863/21520000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (643443591/100000000000000 : ℝ)*(base19) + (43470609/5000000000000 : ℝ)*(base23) + (40964421/20000000000000 : ℝ)*(upper3) + (37783613/50000000000000 : ℝ)*(lower4) + (3695696314428669/100000000000000 : ℝ)*(major0) + (3695696314428669/100000000000000 : ℝ)*(major1) + (3695696314428669/100000000000000 : ℝ)*(major2) + (2495640956902651/50000000000000 : ℝ)*(sp0) + (2495642144395551/50000000000000 : ℝ)*(sp1) + (1247819245775237/25000000000000 : ℝ)*(sp2) + (1200050733310129/50000000000000 : ℝ)*(sp3) + (3018429391/100000000000000 : ℝ)*(sp4) + (1415944313/20000000000000 : ℝ)*(sp6) + (1229724787/20000000000000 : ℝ)*(sp7) + (1200053807622097/50000000000000 : ℝ)*(f.failure) + (4991284932234693/100000000000000 : ℝ)*(f.sum) + (2755872139891/2152000000000000000000000000 : ℝ)*base66 + (169792518037497379/43040000000000000000000000000000 : ℝ)*base67 + (114762176425337379/43040000000000000000000000000000 : ℝ)*base69 + (253805444106982621/43040000000000000000000000000000 : ℝ)*base72 + (6358581543621/2152000000000000000000000000 : ℝ)*base73 + (615096846437817379/43040000000000000000000000000000 : ℝ)*base75 + (11185409820742621/43040000000000000000000000000000 : ℝ)*base78 + (768201921119417379/43040000000000000000000000000000 : ℝ)*base79 + (10420856596333/2152000000000000000000000000 : ℝ)*base81 + (7513437/2500000000000000000000 : ℝ)*base89 + (7513437/2500000000000000000000 : ℝ)*base91 + (7513437/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (60503396075792104170676017/10760000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1509746339/100000000000000 : ℝ)*(base19) + (3620782573/100000000000000 : ℝ)*(base23) + (16598307/5000000000000 : ℝ)*(upper3) + (91206267/100000000000000 : ℝ)*(lower4) + (42456641/25000000000000 : ℝ)*(upper5) + (1863603640713771/50000000000000 : ℝ)*(major0) + (1863603640713771/50000000000000 : ℝ)*(major1) + (1863603640713771/50000000000000 : ℝ)*(major2) + (11562896397/50000000000000 : ℝ)*(sp1) + (54337461161/100000000000000 : ℝ)*(sp2) + (1006768498866733/20000000000000 : ℝ)*(sp4) + (1258454464698633/25000000000000 : ℝ)*(sp5) + (1258446134022483/25000000000000 : ℝ)*(sp6) + (2420571881088341/100000000000000 : ℝ)*(sp7) + (2420571881088341/100000000000000 : ℝ)*(f.failure) + (1006768498866733/20000000000000 : ℝ)*(f.sum) + (480077351339/1076000000000000000000000000 : ℝ)*base65 + (174015275824324661/21520000000000000000000000000000 : ℝ)*base67 + (55017964424484661/21520000000000000000000000000000 : ℝ)*base69 + (24297604328875339/21520000000000000000000000000000 : ℝ)*base72 + (276902496253/215200000000000000000000000 : ℝ)*base74 + (1552048694724661/21520000000000000000000000000000 : ℝ)*base75 + (127119715416244661/21520000000000000000000000000000 : ℝ)*base77 + (111567962039275339/21520000000000000000000000000000 : ℝ)*base80 + (6449787927977/1076000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (5886639/5000000000000000000000 : ℝ)*base90 + (5886639/5000000000000000000000 : ℝ)*base92 + (5886639/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1323_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76990221/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16181/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (389/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1079/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15029/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1323_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1323_s4_0 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2060153849/10000000000 : ℝ)*x 0 + (5416615073/10000000000 : ℝ)*x 1 + (5241305181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2060153849/10000000000 : ℝ)^4283 ≤ (12540713655557/100000000000000 : ℝ)^3259 := by
    have hnat : (2060153849 : ℕ)^4283*100000000000000^3259 ≤ 12540713655557^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2060153849 10000000000 12540713655557 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5416615073/10000000000 : ℝ)^4283 ≤ (44674889760387/100000000000000 : ℝ)^3259 := by
    have hnat : (5416615073 : ℕ)^4283*100000000000000^3259 ≤ 44674889760387^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416615073 10000000000 44674889760387 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5241305181/10000000000 : ℝ)^4283 ≤ (42784396566819/100000000000000 : ℝ)^3259 := by
    have hnat : (5241305181 : ℕ)^4283*100000000000000^3259 ≤ 42784396566819^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241305181 10000000000 42784396566819 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2060153849/10000000000 : ℝ), (5416615073/10000000000 : ℝ), (5241305181/10000000000 : ℝ)] ![(12540713655557/100000000000000 : ℝ), (44674889760387/100000000000000 : ℝ), (42784396566819/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2060153849/10000000000 : ℝ)|^4283 ≤ (12540713655557/100000000000000 : ℝ)^3259
        have hw : |(-2060153849/10000000000 : ℝ)|=(2060153849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5416615073/10000000000 : ℝ)|^4283 ≤ (44674889760387/100000000000000 : ℝ)^3259
        have hw : |(5416615073/10000000000 : ℝ)|=(5416615073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5241305181/10000000000 : ℝ)|^4283 ≤ (42784396566819/100000000000000 : ℝ)^3259
        have hw : |(5241305181/10000000000 : ℝ)|=(5241305181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_s4_1 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (133751603/250000000 : ℝ)*x 0 + (-2149547137/10000000000 : ℝ)*x 1 + (5241305017/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133751603/250000000 : ℝ)^4283 ≤ (1373591365147/3125000000000 : ℝ)^3259 := by
    have hnat : (133751603 : ℕ)^4283*3125000000000^3259 ≤ 1373591365147^3259*250000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133751603 250000000 1373591365147 3125000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2149547137/10000000000 : ℝ)^4283 ≤ (6630340749159/50000000000000 : ℝ)^3259 := by
    have hnat : (2149547137 : ℕ)^4283*50000000000000^3259 ≤ 6630340749159^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149547137 10000000000 6630340749159 50000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5241305017/10000000000 : ℝ)^4283 ≤ (5348049350933/12500000000000 : ℝ)^3259 := by
    have hnat : (5241305017 : ℕ)^4283*12500000000000^3259 ≤ 5348049350933^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241305017 10000000000 5348049350933 12500000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133751603/250000000 : ℝ), (-2149547137/10000000000 : ℝ), (5241305017/10000000000 : ℝ)] ![(1373591365147/3125000000000 : ℝ), (6630340749159/50000000000000 : ℝ), (5348049350933/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133751603/250000000 : ℝ)|^4283 ≤ (1373591365147/3125000000000 : ℝ)^3259
        have hw : |(133751603/250000000 : ℝ)|=(133751603/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2149547137/10000000000 : ℝ)|^4283 ≤ (6630340749159/50000000000000 : ℝ)^3259
        have hw : |(-2149547137/10000000000 : ℝ)|=(2149547137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5241305017/10000000000 : ℝ)|^4283 ≤ (5348049350933/12500000000000 : ℝ)^3259
        have hw : |(5241305017/10000000000 : ℝ)|=(5241305017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_s4_2 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070012827/2000000000 : ℝ)*x 0 + (5241304747/10000000000 : ℝ)*x 1 + (-1074773737/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070012827/2000000000 : ℝ)^4283 ≤ (21977461923331/50000000000000 : ℝ)^3259 := by
    have hnat : (1070012827 : ℕ)^4283*50000000000000^3259 ≤ 21977461923331^3259*2000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070012827 2000000000 21977461923331 50000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5241304747/10000000000 : ℝ)^4283 ≤ (10696097977741/25000000000000 : ℝ)^3259 := by
    have hnat : (5241304747 : ℕ)^4283*25000000000000^3259 ≤ 10696097977741^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241304747 10000000000 10696097977741 25000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1074773737/5000000000 : ℝ)^4283 ≤ (6630342115259/50000000000000 : ℝ)^3259 := by
    have hnat : (1074773737 : ℕ)^4283*50000000000000^3259 ≤ 6630342115259^3259*5000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074773737 5000000000 6630342115259 50000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070012827/2000000000 : ℝ), (5241304747/10000000000 : ℝ), (-1074773737/5000000000 : ℝ)] ![(21977461923331/50000000000000 : ℝ), (10696097977741/25000000000000 : ℝ), (6630342115259/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070012827/2000000000 : ℝ)|^4283 ≤ (21977461923331/50000000000000 : ℝ)^3259
        have hw : |(1070012827/2000000000 : ℝ)|=(1070012827/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5241304747/10000000000 : ℝ)|^4283 ≤ (10696097977741/25000000000000 : ℝ)^3259
        have hw : |(5241304747/10000000000 : ℝ)|=(5241304747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1074773737/5000000000 : ℝ)|^4283 ≤ (6630342115259/50000000000000 : ℝ)^3259
        have hw : |(-1074773737/5000000000 : ℝ)|=(1074773737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_s4_3 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4331408053/10000000000 : ℝ)*x 0 + (4152734881/10000000000 : ℝ)*x 1 + (564663961/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4331408053/10000000000 : ℝ)^4283 ≤ (33300862923507/100000000000000 : ℝ)^3259 := by
    have hnat : (4331408053 : ℕ)^4283*100000000000000^3259 ≤ 33300862923507^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4331408053 10000000000 33300862923507 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4152734881/10000000000 : ℝ)^4283 ≤ (3938421796899/12500000000000 : ℝ)^3259 := by
    have hnat : (4152734881 : ℕ)^4283*12500000000000^3259 ≤ 3938421796899^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4152734881 10000000000 3938421796899 12500000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (564663961/1250000000 : ℝ)^4283 ≤ (35191762688471/100000000000000 : ℝ)^3259 := by
    have hnat : (564663961 : ℕ)^4283*100000000000000^3259 ≤ 35191762688471^3259*1250000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      564663961 1250000000 35191762688471 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4331408053/10000000000 : ℝ), (4152734881/10000000000 : ℝ), (564663961/1250000000 : ℝ)] ![(33300862923507/100000000000000 : ℝ), (3938421796899/12500000000000 : ℝ), (35191762688471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4331408053/10000000000 : ℝ)|^4283 ≤ (33300862923507/100000000000000 : ℝ)^3259
        have hw : |(4331408053/10000000000 : ℝ)|=(4331408053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4152734881/10000000000 : ℝ)|^4283 ≤ (3938421796899/12500000000000 : ℝ)^3259
        have hw : |(4152734881/10000000000 : ℝ)|=(4152734881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(564663961/1250000000 : ℝ)|^4283 ≤ (35191762688471/100000000000000 : ℝ)^3259
        have hw : |(564663961/1250000000 : ℝ)|=(564663961/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_s4_4 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-257520943/1250000000 : ℝ)*x 0 + (5241952349/10000000000 : ℝ)*x 1 + (5415964429/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (257520943/1250000000 : ℝ)^4283 ≤ (2508164642949/20000000000000 : ℝ)^3259 := by
    have hnat : (257520943 : ℕ)^4283*20000000000000^3259 ≤ 2508164642949^3259*1250000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257520943 1250000000 2508164642949 20000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5241952349/10000000000 : ℝ)^4283 ≤ (42791339374519/100000000000000 : ℝ)^3259 := by
    have hnat : (5241952349 : ℕ)^4283*100000000000000^3259 ≤ 42791339374519^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241952349 10000000000 42791339374519 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5415964429/10000000000 : ℝ)^4283 ≤ (44667837400561/100000000000000 : ℝ)^3259 := by
    have hnat : (5415964429 : ℕ)^4283*100000000000000^3259 ≤ 44667837400561^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415964429 10000000000 44667837400561 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-257520943/1250000000 : ℝ), (5241952349/10000000000 : ℝ), (5415964429/10000000000 : ℝ)] ![(2508164642949/20000000000000 : ℝ), (42791339374519/100000000000000 : ℝ), (44667837400561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-257520943/1250000000 : ℝ)|^4283 ≤ (2508164642949/20000000000000 : ℝ)^3259
        have hw : |(-257520943/1250000000 : ℝ)|=(257520943/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5241952349/10000000000 : ℝ)|^4283 ≤ (42791339374519/100000000000000 : ℝ)^3259
        have hw : |(5241952349/10000000000 : ℝ)|=(5241952349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5415964429/10000000000 : ℝ)|^4283 ≤ (44667837400561/100000000000000 : ℝ)^3259
        have hw : |(5415964429/10000000000 : ℝ)|=(5415964429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_s4_5 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652504221/5000000000 : ℝ)*x 0 + (-98744399/500000000 : ℝ)*x 1 + (676995553/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652504221/5000000000 : ℝ)^4283 ≤ (2716818259337/6250000000000 : ℝ)^3259 := by
    have hnat : (2652504221 : ℕ)^4283*6250000000000^3259 ≤ 2716818259337^3259*5000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652504221 5000000000 2716818259337 6250000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (98744399/500000000 : ℝ)^4283 ≤ (593153524267/5000000000000 : ℝ)^3259 := by
    have hnat : (98744399 : ℕ)^4283*5000000000000^3259 ≤ 593153524267^3259*500000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      98744399 500000000 593153524267 5000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676995553/1250000000 : ℝ)^4283 ≤ (44667837346367/100000000000000 : ℝ)^3259 := by
    have hnat : (676995553 : ℕ)^4283*100000000000000^3259 ≤ 44667837346367^3259*1250000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676995553 1250000000 44667837346367 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652504221/5000000000 : ℝ), (-98744399/500000000 : ℝ), (676995553/1250000000 : ℝ)] ![(2716818259337/6250000000000 : ℝ), (593153524267/5000000000000 : ℝ), (44667837346367/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652504221/5000000000 : ℝ)|^4283 ≤ (2716818259337/6250000000000 : ℝ)^3259
        have hw : |(2652504221/5000000000 : ℝ)|=(2652504221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-98744399/500000000 : ℝ)|^4283 ≤ (593153524267/5000000000000 : ℝ)^3259
        have hw : |(-98744399/500000000 : ℝ)|=(98744399/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(676995553/1250000000 : ℝ)|^4283 ≤ (44667837346367/100000000000000 : ℝ)^3259
        have hw : |(676995553/1250000000 : ℝ)|=(676995553/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_s4_6 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305008457/10000000000 : ℝ)*x 0 + (2707982203/5000000000 : ℝ)*x 1 + (-394977597/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305008457/10000000000 : ℝ)^4283 ≤ (1086727307773/2500000000000 : ℝ)^3259 := by
    have hnat : (5305008457 : ℕ)^4283*2500000000000^3259 ≤ 1086727307773^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305008457 10000000000 1086727307773 2500000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2707982203/5000000000 : ℝ)^4283 ≤ (11166959287817/25000000000000 : ℝ)^3259 := by
    have hnat : (2707982203 : ℕ)^4283*25000000000000^3259 ≤ 11166959287817^3259*5000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707982203 5000000000 11166959287817 25000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (394977597/2000000000 : ℝ)^4283 ≤ (2965767631203/25000000000000 : ℝ)^3259 := by
    have hnat : (394977597 : ℕ)^4283*25000000000000^3259 ≤ 2965767631203^3259*2000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      394977597 2000000000 2965767631203 25000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305008457/10000000000 : ℝ), (2707982203/5000000000 : ℝ), (-394977597/2000000000 : ℝ)] ![(1086727307773/2500000000000 : ℝ), (11166959287817/25000000000000 : ℝ), (2965767631203/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305008457/10000000000 : ℝ)|^4283 ≤ (1086727307773/2500000000000 : ℝ)^3259
        have hw : |(5305008457/10000000000 : ℝ)|=(5305008457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2707982203/5000000000 : ℝ)|^4283 ≤ (11166959287817/25000000000000 : ℝ)^3259
        have hw : |(2707982203/5000000000 : ℝ)|=(2707982203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-394977597/2000000000 : ℝ)|^4283 ≤ (2965767631203/25000000000000 : ℝ)^3259
        have hw : |(-394977597/2000000000 : ℝ)|=(394977597/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_s4_7 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4331436481/10000000000 : ℝ)*x 0 + (4515965361/10000000000 : ℝ)*x 1 + (4154088339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4331436481/10000000000 : ℝ)^4283 ≤ (1332046006327/4000000000000 : ℝ)^3259 := by
    have hnat : (4331436481 : ℕ)^4283*4000000000000^3259 ≤ 1332046006327^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4331436481 10000000000 1332046006327 4000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4515965361/10000000000 : ℝ)^4283 ≤ (35177979334933/100000000000000 : ℝ)^3259 := by
    have hnat : (4515965361 : ℕ)^4283*100000000000000^3259 ≤ 35177979334933^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4515965361 10000000000 35177979334933 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4154088339/10000000000 : ℝ)^4283 ≤ (7880217622313/25000000000000 : ℝ)^3259 := by
    have hnat : (4154088339 : ℕ)^4283*25000000000000^3259 ≤ 7880217622313^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4154088339 10000000000 7880217622313 25000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4331436481/10000000000 : ℝ), (4515965361/10000000000 : ℝ), (4154088339/10000000000 : ℝ)] ![(1332046006327/4000000000000 : ℝ), (35177979334933/100000000000000 : ℝ), (7880217622313/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4331436481/10000000000 : ℝ)|^4283 ≤ (1332046006327/4000000000000 : ℝ)^3259
        have hw : |(4331436481/10000000000 : ℝ)|=(4331436481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4515965361/10000000000 : ℝ)|^4283 ≤ (35177979334933/100000000000000 : ℝ)^3259
        have hw : |(4515965361/10000000000 : ℝ)|=(4515965361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4154088339/10000000000 : ℝ)|^4283 ≤ (7880217622313/25000000000000 : ℝ)^3259
        have hw : |(4154088339/10000000000 : ℝ)|=(4154088339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1323_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76990221/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15029/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1079/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (5523/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3689/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15029/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1079/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15029/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1079/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15029/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1079/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15029/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1079/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15029/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1079/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15029/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1079/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1079/10000 : ℝ) ^ (2141/512 : ℝ) ≤ (1130715127723909/12500000000000000000 : ℝ) := by
    have hpowers : (1079/10000 : ℝ)^2141 ≤ (1130715127723909/12500000000000000000 : ℝ)^512 := by
      have hnat : (1079 : ℕ)^2141*12500000000000000000^512 ≤ 1130715127723909^512*10000^2141 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1079 10000 1130715127723909 12500000000000000000 2141 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1079/10000 : ℝ)) (X := (1130715127723909/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2141 512 (by norm_num) hpowers
    exact h
  have hpowhi : (15029/100000 : ℝ) ^ (2141/512 : ℝ) ≤ (9039770661660119/25000000000000000000 : ℝ) := by
    have hpowers : (15029/100000 : ℝ)^2141 ≤ (9039770661660119/25000000000000000000 : ℝ)^512 := by
      have hnat : (15029 : ℕ)^2141*25000000000000000000^512 ≤ 9039770661660119^512*100000^2141 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15029 100000 9039770661660119 25000000000000000000 2141 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15029/100000 : ℝ)) (X := (9039770661660119/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2141 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251130715127723909/6250000000000000000 : ℝ) ≤ (5000216305018181/5000000000000000 : ℝ) ^ (2141/512 : ℝ) := by
    have hpowers : (6251130715127723909/6250000000000000000 : ℝ)^512 ≤ (5000216305018181/5000000000000000 : ℝ)^2141 := by
      have hnat : (6251130715127723909 : ℕ)^512*5000000000000000^2141 ≤ 5000216305018181^2141*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251130715127723909 6250000000000000000 5000216305018181 5000000000000000 512 2141 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000216305018181/5000000000000000 : ℝ)) (X := (6251130715127723909/6250000000000000000 : ℝ)) (by norm_num) 2141 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011301200917107937/25000000000000000000 : ℝ) ≤ (1250135105559637/1250000000000000 : ℝ) ^ (2141/512 : ℝ) := by
    have hpowers : (25011301200917107937/25000000000000000000 : ℝ)^512 ≤ (1250135105559637/1250000000000000 : ℝ)^2141 := by
      have hnat : (25011301200917107937 : ℕ)^512*1250000000000000^2141 ≤ 1250135105559637^2141*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011301200917107937 25000000000000000000 1250135105559637 1250000000000000 512 2141 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250135105559637/1250000000000000 : ℝ)) (X := (25011301200917107937/25000000000000000000 : ℝ)) (by norm_num) 2141 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (12509039770661660119/12500000000000000000 : ℝ) ≤ (1000172907891783/1000000000000000 : ℝ) ^ (2141/512 : ℝ) := by
    have hpowers : (12509039770661660119/12500000000000000000 : ℝ)^512 ≤ (1000172907891783/1000000000000000 : ℝ)^2141 := by
      have hnat : (12509039770661660119 : ℕ)^512*1000000000000000^2141 ≤ 1000172907891783^2141*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12509039770661660119 12500000000000000000 1000172907891783 1000000000000000 512 2141 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000172907891783/1000000000000000 : ℝ)) (X := (12509039770661660119/12500000000000000000 : ℝ)) (by norm_num) 2141 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1130715127723909/12500000000000000000 : ℝ) ≤ ((21188922467356549399/21195000000000000000 : ℝ)+2*(324117220367/211950000000000 : ℝ)*(1079/10000 : ℝ))^(2141/512 : ℝ) := by
    rw [show (21188922467356549399/21195000000000000000 : ℝ)+2*(324117220367/211950000000000 : ℝ)*(1079/10000 : ℝ)=(5000216305018181/5000000000000000 : ℝ) by norm_num, show 1+2*(1130715127723909/12500000000000000000 : ℝ)=(6251130715127723909/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9039770661660119/25000000000000000000 : ℝ)+(1130715127723909/12500000000000000000 : ℝ) ≤ ((21188922467356549399/21195000000000000000 : ℝ)+(324117220367/211950000000000 : ℝ)*((15029/100000 : ℝ)+(1079/10000 : ℝ)))^(2141/512 : ℝ) := by
    rw [show (21188922467356549399/21195000000000000000 : ℝ)+(324117220367/211950000000000 : ℝ)*((15029/100000 : ℝ)+(1079/10000 : ℝ))=(1250135105559637/1250000000000000 : ℝ) by norm_num, show 1+(9039770661660119/25000000000000000000 : ℝ)+(1130715127723909/12500000000000000000 : ℝ)=(25011301200917107937/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9039770661660119/25000000000000000000 : ℝ) ≤ ((21188922467356549399/21195000000000000000 : ℝ)+2*(324117220367/211950000000000 : ℝ)*(15029/100000 : ℝ))^(2141/512 : ℝ) := by
    rw [show (21188922467356549399/21195000000000000000 : ℝ)+2*(324117220367/211950000000000 : ℝ)*(15029/100000 : ℝ)=(1000172907891783/1000000000000000 : ℝ) by norm_num, show 1+2*(9039770661660119/25000000000000000000 : ℝ)=(12509039770661660119/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (21188922467356549399/21195000000000000000 : ℝ)*(X 1 0+X 2 0)+(324117220367/211950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2141/512 : ℝ)) (lo := (1079/10000 : ℝ)) (hi := (15029/100000 : ℝ)) (c := (21188922467356549399/21195000000000000000 : ℝ)) (alpha := (324117220367/211950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (21188922467356549399/21195000000000000000 : ℝ)*(X 0 1+X 2 1)+(324117220367/211950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2141/512 : ℝ)) (lo := (1079/10000 : ℝ)) (hi := (15029/100000 : ℝ)) (c := (21188922467356549399/21195000000000000000 : ℝ)) (alpha := (324117220367/211950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (21188922467356549399/21195000000000000000 : ℝ)*(X 0 2+X 1 2)+(324117220367/211950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2141/512 : ℝ)) (lo := (1079/10000 : ℝ)) (hi := (15029/100000 : ℝ)) (c := (21188922467356549399/21195000000000000000 : ℝ)) (alpha := (324117220367/211950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2060153849/10000000000 : ℝ)*X 0 0+(5416615073/10000000000 : ℝ)*X 0 1+(5241305181/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((133751603/250000000 : ℝ)*X 1 0+(-2149547137/10000000000 : ℝ)*X 1 1+(5241305017/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1070012827/2000000000 : ℝ)*X 2 0+(5241304747/10000000000 : ℝ)*X 2 1+(-1074773737/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4331408053/10000000000 : ℝ)*X 0 0+(4152734881/10000000000 : ℝ)*X 0 1+(564663961/1250000000 : ℝ)*X 0 2+(4331408053/10000000000 : ℝ)*X 1 0+(4152734881/10000000000 : ℝ)*X 1 1+(564663961/1250000000 : ℝ)*X 1 2+(4331408053/10000000000 : ℝ)*X 2 0+(4152734881/10000000000 : ℝ)*X 2 1+(564663961/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-257520943/1250000000 : ℝ)*X 0 0+(5241952349/10000000000 : ℝ)*X 0 1+(5415964429/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652504221/5000000000 : ℝ)*X 1 0+(-98744399/500000000 : ℝ)*X 1 1+(676995553/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305008457/10000000000 : ℝ)*X 2 0+(2707982203/5000000000 : ℝ)*X 2 1+(-394977597/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4331436481/10000000000 : ℝ)*X 0 0+(4515965361/10000000000 : ℝ)*X 0 1+(4154088339/10000000000 : ℝ)*X 0 2+(4331436481/10000000000 : ℝ)*X 1 0+(4515965361/10000000000 : ℝ)*X 1 1+(4154088339/10000000000 : ℝ)*X 1 2+(4331436481/10000000000 : ℝ)*X 2 0+(4515965361/10000000000 : ℝ)*X 2 1+(4154088339/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18965919159812365532371/7065000000000000000000000000 : ℝ) := by norm_num
    linear_combination (444426813/50000000000000 : ℝ)*(base19) + (17896217/2000000000000 : ℝ)*(base23) + (42202787/50000000000000 : ℝ)*(upper3) + (29925197/100000000000000 : ℝ)*(lower4) + (4223572214705021/100000000000000 : ℝ)*(major0) + (4223572214705021/100000000000000 : ℝ)*(major1) + (4223572214705021/100000000000000 : ℝ)*(major2) + (1426050649811219/25000000000000 : ℝ)*(sp0) + (5704215739055931/100000000000000 : ℝ)*(sp1) + (570420789959831/10000000000000 : ℝ)*(sp2) + (274291652092127/10000000000000 : ℝ)*(sp3) + (14028664681/100000000000000 : ℝ)*(sp4) + (1958375099/25000000000000 : ℝ)*(sp6) + (11191096221/100000000000000 : ℝ)*(sp7) + (685731928004373/25000000000000 : ℝ)*(f.failure) + (5704216627909557/100000000000000 : ℝ)*(f.sum) + (31060646120071/21195000000000000000000000000 : ℝ)*base66 + (1547947070018489207/706500000000000000000000000000000 : ℝ)*base68 + (800388197972489207/706500000000000000000000000000000 : ℝ)*base70 + (5050904185472010793/706500000000000000000000000000000 : ℝ)*base71 + (30711702010567/10597500000000000000000000000 : ℝ)*base73 + (844735995665489207/706500000000000000000000000000000 : ℝ)*base76 + (5888696540909010793/706500000000000000000000000000000 : ℝ)*base77 + (6182448244943010793/706500000000000000000000000000000 : ℝ)*base79 + (17345019329009/21195000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (3736433/1250000000000000000000 : ℝ)*base89 + (3736433/1250000000000000000000 : ℝ)*base91 + (3736433/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1588729168416745982378095319/353250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (80402713/10000000000000 : ℝ)*(base19) + (879158801/100000000000000 : ℝ)*(base23) + (1826047/2000000000000 : ℝ)*(upper3) + (28011671/100000000000000 : ℝ)*(lower4) + (100751183/100000000000000 : ℝ)*(upper5) + (4255048462797973/100000000000000 : ℝ)*(major0) + (4255048462797973/100000000000000 : ℝ)*(major1) + (4255048462797973/100000000000000 : ℝ)*(major2) + (7855093181/50000000000000 : ℝ)*(sp1) + (16426112579/100000000000000 : ℝ)*(sp2) + (1436681836356621/25000000000000 : ℝ)*(sp4) + (89792356737703/1562500000000 : ℝ)*(sp5) + (179584688754847/3125000000000 : ℝ)*(sp6) + (690842357563497/25000000000000 : ℝ)*(sp7) + (690842357563497/25000000000000 : ℝ)*(f.failure) + (1436681836356621/25000000000000 : ℝ)*(f.sum) + (3747632289221/10597500000000000000000000000 : ℝ)*base65 + (2865200098650889409/706500000000000000000000000000000 : ℝ)*base67 + (759714950454889409/706500000000000000000000000000000 : ℝ)*base69 + (5272368848988889409/706500000000000000000000000000000 : ℝ)*base71 + (6486182288131/2649375000000000000000000000 : ℝ)*base74 + (2585567320935889409/706500000000000000000000000000000 : ℝ)*base75 + (5850032364560389409/706500000000000000000000000000000 : ℝ)*base77 + (5096517980114389409/706500000000000000000000000000000 : ℝ)*base79 + (6391407854447/5298750000000000000000000000 : ℝ)*base82 + (6937163/1250000000000000000000 : ℝ)*base90 + (6937163/1250000000000000000000 : ℝ)*base92 + (6937163/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1323_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76990221/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15029/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1079/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5523/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3689/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1323_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1323_s5_0 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1030221603/5000000000 : ℝ)*x 0 + (1353535913/2500000000 : ℝ)*x 1 + (1310896541/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1030221603/5000000000 : ℝ)^4283 ≤ (3135757135761/25000000000000 : ℝ)^3259 := by
    have hnat : (1030221603 : ℕ)^4283*25000000000000^3259 ≤ 3135757135761^3259*5000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030221603 5000000000 3135757135761 25000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353535913/2500000000 : ℝ)^4283 ≤ (5581012916369/12500000000000 : ℝ)^3259 := by
    have hnat : (1353535913 : ℕ)^4283*12500000000000^3259 ≤ 5581012916369^3259*2500000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353535913 2500000000 5581012916369 12500000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310896541/2500000000 : ℝ)^4283 ≤ (5351108514157/12500000000000 : ℝ)^3259 := by
    have hnat : (1310896541 : ℕ)^4283*12500000000000^3259 ≤ 5351108514157^3259*2500000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310896541 2500000000 5351108514157 12500000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1030221603/5000000000 : ℝ), (1353535913/2500000000 : ℝ), (1310896541/2500000000 : ℝ)] ![(3135757135761/25000000000000 : ℝ), (5581012916369/12500000000000 : ℝ), (5351108514157/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1030221603/5000000000 : ℝ)|^4283 ≤ (3135757135761/25000000000000 : ℝ)^3259
        have hw : |(-1030221603/5000000000 : ℝ)|=(1030221603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353535913/2500000000 : ℝ)|^4283 ≤ (5581012916369/12500000000000 : ℝ)^3259
        have hw : |(1353535913/2500000000 : ℝ)|=(1353535913/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310896541/2500000000 : ℝ)|^4283 ≤ (5351108514157/12500000000000 : ℝ)^3259
        have hw : |(1310896541/2500000000 : ℝ)|=(1310896541/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_s5_1 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349433873/10000000000 : ℝ)*x 0 + (-53684187/250000000 : ℝ)*x 1 + (5243586169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349433873/10000000000 : ℝ)^4283 ≤ (21974059445163/50000000000000 : ℝ)^3259 := by
    have hnat : (5349433873 : ℕ)^4283*50000000000000^3259 ≤ 21974059445163^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349433873 10000000000 21974059445163 50000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (53684187/250000000 : ℝ)^4283 ≤ (13243012922883/100000000000000 : ℝ)^3259 := by
    have hnat : (53684187 : ℕ)^4283*100000000000000^3259 ≤ 13243012922883^3259*250000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53684187 250000000 13243012922883 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243586169/10000000000 : ℝ)^4283 ≤ (21404434083451/50000000000000 : ℝ)^3259 := by
    have hnat : (5243586169 : ℕ)^4283*50000000000000^3259 ≤ 21404434083451^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243586169 10000000000 21404434083451 50000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349433873/10000000000 : ℝ), (-53684187/250000000 : ℝ), (5243586169/10000000000 : ℝ)] ![(21974059445163/50000000000000 : ℝ), (13243012922883/100000000000000 : ℝ), (21404434083451/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349433873/10000000000 : ℝ)|^4283 ≤ (21974059445163/50000000000000 : ℝ)^3259
        have hw : |(5349433873/10000000000 : ℝ)|=(5349433873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-53684187/250000000 : ℝ)|^4283 ≤ (13243012922883/100000000000000 : ℝ)^3259
        have hw : |(-53684187/250000000 : ℝ)|=(53684187/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243586169/10000000000 : ℝ)|^4283 ≤ (21404434083451/50000000000000 : ℝ)^3259
        have hw : |(5243586169/10000000000 : ℝ)|=(5243586169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_s5_2 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349433907/10000000000 : ℝ)*x 0 + (1048717231/2000000000 : ℝ)*x 1 + (-1073683727/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349433907/10000000000 : ℝ)^4283 ≤ (21974059628709/50000000000000 : ℝ)^3259 := by
    have hnat : (5349433907 : ℕ)^4283*50000000000000^3259 ≤ 21974059628709^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349433907 10000000000 21974059628709 50000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048717231/2000000000 : ℝ)^4283 ≤ (42808868016693/100000000000000 : ℝ)^3259 := by
    have hnat : (1048717231 : ℕ)^4283*100000000000000^3259 ≤ 42808868016693^3259*2000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048717231 2000000000 42808868016693 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1073683727/5000000000 : ℝ)^4283 ≤ (13243012712157/100000000000000 : ℝ)^3259 := by
    have hnat : (1073683727 : ℕ)^4283*100000000000000^3259 ≤ 13243012712157^3259*5000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073683727 5000000000 13243012712157 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349433907/10000000000 : ℝ), (1048717231/2000000000 : ℝ), (-1073683727/5000000000 : ℝ)] ![(21974059628709/50000000000000 : ℝ), (42808868016693/100000000000000 : ℝ), (13243012712157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349433907/10000000000 : ℝ)|^4283 ≤ (21974059628709/50000000000000 : ℝ)^3259
        have hw : |(5349433907/10000000000 : ℝ)|=(5349433907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048717231/2000000000 : ℝ)|^4283 ≤ (42808868016693/100000000000000 : ℝ)^3259
        have hw : |(1048717231/2000000000 : ℝ)|=(1048717231/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1073683727/5000000000 : ℝ)|^4283 ≤ (13243012712157/100000000000000 : ℝ)^3259
        have hw : |(-1073683727/5000000000 : ℝ)|=(1073683727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_s5_3 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (216578993/500000000 : ℝ)*x 0 + (4157655407/10000000000 : ℝ)*x 1 + (902469651/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (216578993/500000000 : ℝ)^4283 ≤ (16651299429659/50000000000000 : ℝ)^3259 := by
    have hnat : (216578993 : ℕ)^4283*50000000000000^3259 ≤ 16651299429659^3259*500000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216578993 500000000 16651299429659 50000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4157655407/10000000000 : ℝ)^4283 ≤ (31556446410029/100000000000000 : ℝ)^3259 := by
    have hnat : (4157655407 : ℕ)^4283*100000000000000^3259 ≤ 31556446410029^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4157655407 10000000000 31556446410029 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (902469651/2000000000 : ℝ)^4283 ≤ (35140954717897/100000000000000 : ℝ)^3259 := by
    have hnat : (902469651 : ℕ)^4283*100000000000000^3259 ≤ 35140954717897^3259*2000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      902469651 2000000000 35140954717897 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(216578993/500000000 : ℝ), (4157655407/10000000000 : ℝ), (902469651/2000000000 : ℝ)] ![(16651299429659/50000000000000 : ℝ), (31556446410029/100000000000000 : ℝ), (35140954717897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(216578993/500000000 : ℝ)|^4283 ≤ (16651299429659/50000000000000 : ℝ)^3259
        have hw : |(216578993/500000000 : ℝ)|=(216578993/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4157655407/10000000000 : ℝ)|^4283 ≤ (31556446410029/100000000000000 : ℝ)^3259
        have hw : |(4157655407/10000000000 : ℝ)|=(4157655407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(902469651/2000000000 : ℝ)|^4283 ≤ (35140954717897/100000000000000 : ℝ)^3259
        have hw : |(902469651/2000000000 : ℝ)|=(902469651/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_s5_4 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2060455771/10000000000 : ℝ)*x 0 + (5244198999/10000000000 : ℝ)*x 1 + (5413527651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2060455771/10000000000 : ℝ)^4283 ≤ (501725162669/4000000000000 : ℝ)^3259 := by
    have hnat : (2060455771 : ℕ)^4283*4000000000000^3259 ≤ 501725162669^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2060455771 10000000000 501725162669 4000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244198999/10000000000 : ℝ)^4283 ≤ (42815443489141/100000000000000 : ℝ)^3259 := by
    have hnat : (5244198999 : ℕ)^4283*100000000000000^3259 ≤ 42815443489141^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244198999 10000000000 42815443489141 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413527651/10000000000 : ℝ)^4283 ≤ (44641427418879/100000000000000 : ℝ)^3259 := by
    have hnat : (5413527651 : ℕ)^4283*100000000000000^3259 ≤ 44641427418879^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413527651 10000000000 44641427418879 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2060455771/10000000000 : ℝ), (5244198999/10000000000 : ℝ), (5413527651/10000000000 : ℝ)] ![(501725162669/4000000000000 : ℝ), (42815443489141/100000000000000 : ℝ), (44641427418879/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2060455771/10000000000 : ℝ)|^4283 ≤ (501725162669/4000000000000 : ℝ)^3259
        have hw : |(-2060455771/10000000000 : ℝ)|=(2060455771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244198999/10000000000 : ℝ)|^4283 ≤ (42815443489141/100000000000000 : ℝ)^3259
        have hw : |(5244198999/10000000000 : ℝ)|=(5244198999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413527651/10000000000 : ℝ)|^4283 ≤ (44641427418879/100000000000000 : ℝ)^3259
        have hw : |(5413527651/10000000000 : ℝ)|=(5413527651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_s5_5 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305599969/10000000000 : ℝ)*x 0 + (-123589123/625000000 : ℝ)*x 1 + (5413527653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305599969/10000000000 : ℝ)^4283 ≤ (21737731081681/50000000000000 : ℝ)^3259 := by
    have hnat : (5305599969 : ℕ)^4283*50000000000000^3259 ≤ 21737731081681^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305599969 10000000000 21737731081681 50000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (123589123/625000000 : ℝ)^4283 ≤ (148538879829/1250000000000 : ℝ)^3259 := by
    have hnat : (123589123 : ℕ)^4283*1250000000000^3259 ≤ 148538879829^3259*625000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      123589123 625000000 148538879829 1250000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413527653/10000000000 : ℝ)^4283 ≤ (22320713720277/50000000000000 : ℝ)^3259 := by
    have hnat : (5413527653 : ℕ)^4283*50000000000000^3259 ≤ 22320713720277^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413527653 10000000000 22320713720277 50000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305599969/10000000000 : ℝ), (-123589123/625000000 : ℝ), (5413527653/10000000000 : ℝ)] ![(21737731081681/50000000000000 : ℝ), (148538879829/1250000000000 : ℝ), (22320713720277/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305599969/10000000000 : ℝ)|^4283 ≤ (21737731081681/50000000000000 : ℝ)^3259
        have hw : |(5305599969/10000000000 : ℝ)|=(5305599969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-123589123/625000000 : ℝ)|^4283 ≤ (148538879829/1250000000000 : ℝ)^3259
        have hw : |(-123589123/625000000 : ℝ)|=(123589123/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413527653/10000000000 : ℝ)|^4283 ≤ (22320713720277/50000000000000 : ℝ)^3259
        have hw : |(5413527653/10000000000 : ℝ)|=(5413527653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_s5_6 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (165799999/312500000 : ℝ)*x 0 + (2706763827/5000000000 : ℝ)*x 1 + (-123589123/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165799999/312500000 : ℝ)^4283 ≤ (43475462152593/100000000000000 : ℝ)^3259 := by
    have hnat : (165799999 : ℕ)^4283*100000000000000^3259 ≤ 43475462152593^3259*312500000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165799999 312500000 43475462152593 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2706763827/5000000000 : ℝ)^4283 ≤ (44641427451391/100000000000000 : ℝ)^3259 := by
    have hnat : (2706763827 : ℕ)^4283*100000000000000^3259 ≤ 44641427451391^3259*5000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706763827 5000000000 44641427451391 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (123589123/625000000 : ℝ)^4283 ≤ (148538879829/1250000000000 : ℝ)^3259 := by
    have hnat : (123589123 : ℕ)^4283*1250000000000^3259 ≤ 148538879829^3259*625000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      123589123 625000000 148538879829 1250000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165799999/312500000 : ℝ), (2706763827/5000000000 : ℝ), (-123589123/625000000 : ℝ)] ![(43475462152593/100000000000000 : ℝ), (44641427451391/100000000000000 : ℝ), (148538879829/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165799999/312500000 : ℝ)|^4283 ≤ (43475462152593/100000000000000 : ℝ)^3259
        have hw : |(165799999/312500000 : ℝ)|=(165799999/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2706763827/5000000000 : ℝ)|^4283 ≤ (44641427451391/100000000000000 : ℝ)^3259
        have hw : |(2706763827/5000000000 : ℝ)|=(2706763827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-123589123/625000000 : ℝ)|^4283 ≤ (148538879829/1250000000000 : ℝ)^3259
        have hw : |(-123589123/625000000 : ℝ)|=(123589123/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_s5_7 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2165802989/5000000000 : ℝ)*x 0 + (1127768457/2500000000 : ℝ)*x 1 + (259933529/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2165802989/5000000000 : ℝ)^4283 ≤ (33302862757163/100000000000000 : ℝ)^3259 := by
    have hnat : (2165802989 : ℕ)^4283*100000000000000^3259 ≤ 33302862757163^3259*5000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2165802989 5000000000 33302862757163 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1127768457/2500000000 : ℝ)^4283 ≤ (17563955966197/50000000000000 : ℝ)^3259 := by
    have hnat : (1127768457 : ℕ)^4283*50000000000000^3259 ≤ 17563955966197^3259*2500000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1127768457 2500000000 17563955966197 50000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (259933529/625000000 : ℝ)^4283 ≤ (15784612644961/50000000000000 : ℝ)^3259 := by
    have hnat : (259933529 : ℕ)^4283*50000000000000^3259 ≤ 15784612644961^3259*625000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259933529 625000000 15784612644961 50000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2165802989/5000000000 : ℝ), (1127768457/2500000000 : ℝ), (259933529/625000000 : ℝ)] ![(33302862757163/100000000000000 : ℝ), (17563955966197/50000000000000 : ℝ), (15784612644961/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2165802989/5000000000 : ℝ)|^4283 ≤ (33302862757163/100000000000000 : ℝ)^3259
        have hw : |(2165802989/5000000000 : ℝ)|=(2165802989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1127768457/2500000000 : ℝ)|^4283 ≤ (17563955966197/50000000000000 : ℝ)^3259
        have hw : |(1127768457/2500000000 : ℝ)|=(1127768457/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(259933529/625000000 : ℝ)|^4283 ≤ (15784612644961/50000000000000 : ℝ)^3259
        have hw : |(259933529/625000000 : ℝ)|=(259933529/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1323_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76990221/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3689/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5523/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5547/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2941/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3689/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5523/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3689/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5523/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3689/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5523/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3689/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5523/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3689/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5523/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3689/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5523/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5523/50000 : ℝ) ^ (2141/512 : ℝ) ≤ (9977628296179617/100000000000000000000 : ℝ) := by
    have hpowers : (5523/50000 : ℝ)^2141 ≤ (9977628296179617/100000000000000000000 : ℝ)^512 := by
      have hnat : (5523 : ℕ)^2141*100000000000000000000^512 ≤ 9977628296179617^512*50000^2141 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5523 50000 9977628296179617 100000000000000000000 2141 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5523/50000 : ℝ)) (X := (9977628296179617/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2141 512 (by norm_num) hpowers
    exact h
  have hpowhi : (3689/25000 : ℝ) ^ (2141/512 : ℝ) ≤ (33490800775811871/100000000000000000000 : ℝ) := by
    have hpowers : (3689/25000 : ℝ)^2141 ≤ (33490800775811871/100000000000000000000 : ℝ)^512 := by
      have hnat : (3689 : ℕ)^2141*100000000000000000000^512 ≤ 33490800775811871^512*25000^2141 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3689 25000 33490800775811871 100000000000000000000 2141 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3689/25000 : ℝ)) (X := (33490800775811871/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2141 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009977628296179617/50000000000000000000 : ℝ) ≤ (2500119293739237/2500000000000000 : ℝ) ^ (2141/512 : ℝ) := by
    have hpowers : (50009977628296179617/50000000000000000000 : ℝ)^512 ≤ (2500119293739237/2500000000000000 : ℝ)^2141 := by
      have hnat : (50009977628296179617 : ℕ)^512*2500000000000000^2141 ≤ 2500119293739237^2141*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009977628296179617 50000000000000000000 2500119293739237 2500000000000000 512 2141 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500119293739237/2500000000000000 : ℝ)) (X := (50009977628296179617/50000000000000000000 : ℝ)) (by norm_num) 2141 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (1563179194204249867/1562500000000000000 : ℝ) ≤ (10001039334714941/10000000000000000 : ℝ) ^ (2141/512 : ℝ) := by
    have hpowers : (1563179194204249867/1562500000000000000 : ℝ)^512 ≤ (10001039334714941/10000000000000000 : ℝ)^2141 := by
      have hnat : (1563179194204249867 : ℕ)^512*10000000000000000^2141 ≤ 10001039334714941^2141*1562500000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1563179194204249867 1562500000000000000 10001039334714941 10000000000000000 512 2141 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001039334714941/10000000000000000 : ℝ)) (X := (1563179194204249867/1562500000000000000 : ℝ)) (by norm_num) 2141 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033490800775811871/50000000000000000000 : ℝ) ≤ (5000800747236467/5000000000000000 : ℝ) ^ (2141/512 : ℝ) := by
    have hpowers : (50033490800775811871/50000000000000000000 : ℝ)^512 ≤ (5000800747236467/5000000000000000 : ℝ)^2141 := by
      have hnat : (50033490800775811871 : ℕ)^512*5000000000000000^2141 ≤ 5000800747236467^2141*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033490800775811871 50000000000000000000 5000800747236467 5000000000000000 512 2141 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000800747236467/5000000000000000 : ℝ)) (X := (50033490800775811871/50000000000000000000 : ℝ)) (by norm_num) 2141 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9977628296179617/100000000000000000000 : ℝ) ≤ ((1324619681632739133/1325000000000000000 : ℝ)+2*(562159757993/371000000000000 : ℝ)*(5523/50000 : ℝ))^(2141/512 : ℝ) := by
    rw [show (1324619681632739133/1325000000000000000 : ℝ)+2*(562159757993/371000000000000 : ℝ)*(5523/50000 : ℝ)=(2500119293739237/2500000000000000 : ℝ) by norm_num, show 1+2*(9977628296179617/100000000000000000000 : ℝ)=(50009977628296179617/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33490800775811871/100000000000000000000 : ℝ)+(9977628296179617/100000000000000000000 : ℝ) ≤ ((1324619681632739133/1325000000000000000 : ℝ)+(562159757993/371000000000000 : ℝ)*((3689/25000 : ℝ)+(5523/50000 : ℝ)))^(2141/512 : ℝ) := by
    rw [show (1324619681632739133/1325000000000000000 : ℝ)+(562159757993/371000000000000 : ℝ)*((3689/25000 : ℝ)+(5523/50000 : ℝ))=(10001039334714941/10000000000000000 : ℝ) by norm_num, show 1+(33490800775811871/100000000000000000000 : ℝ)+(9977628296179617/100000000000000000000 : ℝ)=(1563179194204249867/1562500000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33490800775811871/100000000000000000000 : ℝ) ≤ ((1324619681632739133/1325000000000000000 : ℝ)+2*(562159757993/371000000000000 : ℝ)*(3689/25000 : ℝ))^(2141/512 : ℝ) := by
    rw [show (1324619681632739133/1325000000000000000 : ℝ)+2*(562159757993/371000000000000 : ℝ)*(3689/25000 : ℝ)=(5000800747236467/5000000000000000 : ℝ) by norm_num, show 1+2*(33490800775811871/100000000000000000000 : ℝ)=(50033490800775811871/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1324619681632739133/1325000000000000000 : ℝ)*(X 1 0+X 2 0)+(562159757993/371000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2141/512 : ℝ)) (lo := (5523/50000 : ℝ)) (hi := (3689/25000 : ℝ)) (c := (1324619681632739133/1325000000000000000 : ℝ)) (alpha := (562159757993/371000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1324619681632739133/1325000000000000000 : ℝ)*(X 0 1+X 2 1)+(562159757993/371000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2141/512 : ℝ)) (lo := (5523/50000 : ℝ)) (hi := (3689/25000 : ℝ)) (c := (1324619681632739133/1325000000000000000 : ℝ)) (alpha := (562159757993/371000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1324619681632739133/1325000000000000000 : ℝ)*(X 0 2+X 1 2)+(562159757993/371000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2141/512 : ℝ)) (lo := (5523/50000 : ℝ)) (hi := (3689/25000 : ℝ)) (c := (1324619681632739133/1325000000000000000 : ℝ)) (alpha := (562159757993/371000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1030221603/5000000000 : ℝ)*X 0 0+(1353535913/2500000000 : ℝ)*X 0 1+(1310896541/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349433873/10000000000 : ℝ)*X 1 0+(-53684187/250000000 : ℝ)*X 1 1+(5243586169/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349433907/10000000000 : ℝ)*X 2 0+(1048717231/2000000000 : ℝ)*X 2 1+(-1073683727/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((216578993/500000000 : ℝ)*X 0 0+(4157655407/10000000000 : ℝ)*X 0 1+(902469651/2000000000 : ℝ)*X 0 2+(216578993/500000000 : ℝ)*X 1 0+(4157655407/10000000000 : ℝ)*X 1 1+(902469651/2000000000 : ℝ)*X 1 2+(216578993/500000000 : ℝ)*X 2 0+(4157655407/10000000000 : ℝ)*X 2 1+(902469651/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2060455771/10000000000 : ℝ)*X 0 0+(5244198999/10000000000 : ℝ)*X 0 1+(5413527651/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305599969/10000000000 : ℝ)*X 1 0+(-123589123/625000000 : ℝ)*X 1 1+(5413527653/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((165799999/312500000 : ℝ)*X 2 0+(2706763827/5000000000 : ℝ)*X 2 1+(-123589123/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2165802989/5000000000 : ℝ)*X 0 0+(1127768457/2500000000 : ℝ)*X 0 1+(259933529/625000000 : ℝ)*X 0 2+(2165802989/5000000000 : ℝ)*X 1 0+(1127768457/2500000000 : ℝ)*X 1 1+(259933529/625000000 : ℝ)*X 1 2+(2165802989/5000000000 : ℝ)*X 2 0+(1127768457/2500000000 : ℝ)*X 2 1+(259933529/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (295677076193594779616815413/28984375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1933791179/100000000000000 : ℝ)*(base19) + (1832248011/100000000000000 : ℝ)*(base23) + (14850947/20000000000000 : ℝ)*(lower2) + (24864167/10000000000000 : ℝ)*(upper3) + (184279183/100000000000000 : ℝ)*(upper5) + (271330770251983/6250000000000 : ℝ)*(major0) + (271330770251983/6250000000000 : ℝ)*(major1) + (271330770251983/6250000000000 : ℝ)*(major2) + (5863165591772443/100000000000000 : ℝ)*(sp0) + (5863203323459907/100000000000000 : ℝ)*(sp1) + (234528137000123/4000000000000 : ℝ)*(sp2) + (352419876655869/12500000000000 : ℝ)*(sp3) + (39665478643/100000000000000 : ℝ)*(sp4) + (20037523489/100000000000000 : ℝ)*(sp7) + (70484476269261/2500000000000 : ℝ)*(f.failure) + (2931602628625543/50000000000000 : ℝ)*(f.sum) + (87749823819573/9275000000000000000000000000 : ℝ)*base66 + (588664070073463577/57968750000000000000000000000000 : ℝ)*base68 + (146486117353463577/57968750000000000000000000000000 : ℝ)*base70 + (231828039129036423/57968750000000000000000000000000 : ℝ)*base71 + (16750778671737/2318750000000000000000000000 : ℝ)*base74 + (911064367993776077/57968750000000000000000000000000 : ℝ)*base76 + (1444688162963776077/57968750000000000000000000000000 : ℝ)*base78 + (283108842928463577/57968750000000000000000000000000 : ℝ)*base80 + (8707299965151/4637500000000000000000000000 : ℝ)*base81 + (103319/125000000000000000000 : ℝ)*base90 + (103319/125000000000000000000 : ℝ)*base92 + (103319/125000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (203927941719108333784521/18550000000000000000000000000 : ℝ) := by norm_num
    linear_combination (482345109/25000000000000 : ℝ)*(base19) + (26205379/1250000000000 : ℝ)*(base23) + (112291479/50000000000000 : ℝ)*(upper3) + (76235009/100000000000000 : ℝ)*(lower4) + (56477809/25000000000000 : ℝ)*(upper5) + (4372737148668501/100000000000000 : ℝ)*(major0) + (4372737148668501/100000000000000 : ℝ)*(major1) + (4372737148668501/100000000000000 : ℝ)*(major2) + (608208597/1562500000000 : ℝ)*(sp1) + (41887759713/100000000000000 : ℝ)*(sp2) + (369104598082259/6250000000000 : ℝ)*(sp4) + (5905632714585499/100000000000000 : ℝ)*(sp5) + (5905629585126111/100000000000000 : ℝ)*(sp6) + (1419900180786759/50000000000000 : ℝ)*(sp7) + (1419900180786759/50000000000000 : ℝ)*(f.failure) + (369104598082259/6250000000000 : ℝ)*(f.sum) + (14553054669493/18550000000000000000000000000 : ℝ)*base65 + (3602381704947627569/927500000000000000000000000000000 : ℝ)*base68 + (6016506230912372431/927500000000000000000000000000000 : ℝ)*base69 + (3949222235579872431/927500000000000000000000000000000 : ℝ)*base71 + (114766219665107/18550000000000000000000000000 : ℝ)*base74 + (7208641221899872431/927500000000000000000000000000000 : ℝ)*base75 + (116295956680127569/927500000000000000000000000000000 : ℝ)*base78 + (7822698932105127569/927500000000000000000000000000000 : ℝ)*base80 + (76044345381393/18550000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (4283739/2500000000000000000000 : ℝ)*base89 + (4283739/2500000000000000000000 : ℝ)*base91 + (4283739/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1323_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76990221/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3689/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5523/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5547/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2941/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1323_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1323_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76990221/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16181/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (389/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5547/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2941/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1323_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1323_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1323_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76990221/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16181/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (389/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5547/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2941/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1323_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
