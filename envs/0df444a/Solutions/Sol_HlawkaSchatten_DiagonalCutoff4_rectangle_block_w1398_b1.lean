-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1398_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:44:41.500001+00:00
-- url     : https://prove2.me/submissions/f3fe74e4-995e-4a7b-9b45-3b59f3ae8137

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
theorem support_rectangle_w1398_s3_0 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-498823653/2500000000 : ℝ)*x 0 + (1355134341/2500000000 : ℝ)*x 1 + (5236285729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (498823653/2500000000 : ℝ)^2179 ≤ (12162201329859/100000000000000 : ℝ)^1667 := by
    have hnat : (498823653 : ℕ)^2179*100000000000000^1667 ≤ 12162201329859^1667*2500000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      498823653 2500000000 12162201329859 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1355134341/2500000000 : ℝ)^2179 ≤ (28069618137/62500000000 : ℝ)^1667 := by
    have hnat : (1355134341 : ℕ)^2179*62500000000^1667 ≤ 28069618137^1667*2500000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355134341 2500000000 28069618137 62500000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5236285729/10000000000 : ℝ)^2179 ≤ (42926409626103/100000000000000 : ℝ)^1667 := by
    have hnat : (5236285729 : ℕ)^2179*100000000000000^1667 ≤ 42926409626103^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5236285729 10000000000 42926409626103 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-498823653/2500000000 : ℝ), (1355134341/2500000000 : ℝ), (5236285729/10000000000 : ℝ)] ![(12162201329859/100000000000000 : ℝ), (28069618137/62500000000 : ℝ), (42926409626103/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-498823653/2500000000 : ℝ)|^2179 ≤ (12162201329859/100000000000000 : ℝ)^1667
        have hw : |(-498823653/2500000000 : ℝ)|=(498823653/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1355134341/2500000000 : ℝ)|^2179 ≤ (28069618137/62500000000 : ℝ)^1667
        have hw : |(1355134341/2500000000 : ℝ)|=(1355134341/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5236285729/10000000000 : ℝ)|^2179 ≤ (42926409626103/100000000000000 : ℝ)^1667
        have hw : |(5236285729/10000000000 : ℝ)|=(5236285729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1398_s3_1 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5350717227/10000000000 : ℝ)*x 0 + (-2089339187/10000000000 : ℝ)*x 1 + (327267803/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350717227/10000000000 : ℝ)^2179 ≤ (44156724417699/100000000000000 : ℝ)^1667 := by
    have hnat : (5350717227 : ℕ)^2179*100000000000000^1667 ≤ 44156724417699^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350717227 10000000000 44156724417699 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2089339187/10000000000 : ℝ)^2179 ≤ (3229218844457/25000000000000 : ℝ)^1667 := by
    have hnat : (2089339187 : ℕ)^2179*25000000000000^1667 ≤ 3229218844457^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2089339187 10000000000 3229218844457 25000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (327267803/625000000 : ℝ)^2179 ≤ (42926400185521/100000000000000 : ℝ)^1667 := by
    have hnat : (327267803 : ℕ)^2179*100000000000000^1667 ≤ 42926400185521^1667*625000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327267803 625000000 42926400185521 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350717227/10000000000 : ℝ), (-2089339187/10000000000 : ℝ), (327267803/625000000 : ℝ)] ![(44156724417699/100000000000000 : ℝ), (3229218844457/25000000000000 : ℝ), (42926400185521/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350717227/10000000000 : ℝ)|^2179 ≤ (44156724417699/100000000000000 : ℝ)^1667
        have hw : |(5350717227/10000000000 : ℝ)|=(5350717227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2089339187/10000000000 : ℝ)|^2179 ≤ (3229218844457/25000000000000 : ℝ)^1667
        have hw : |(-2089339187/10000000000 : ℝ)|=(2089339187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(327267803/625000000 : ℝ)|^2179 ≤ (42926400185521/100000000000000 : ℝ)^1667
        have hw : |(327267803/625000000 : ℝ)|=(327267803/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1398_s3_2 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (214028647/400000000 : ℝ)*x 0 + (1047257147/2000000000 : ℝ)*x 1 + (-417867883/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214028647/400000000 : ℝ)^2179 ≤ (44156713069623/100000000000000 : ℝ)^1667 := by
    have hnat : (214028647 : ℕ)^2179*100000000000000^1667 ≤ 44156713069623^1667*400000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214028647 400000000 44156713069623 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1047257147/2000000000 : ℝ)^2179 ≤ (21463204845199/50000000000000 : ℝ)^1667 := by
    have hnat : (1047257147 : ℕ)^2179*50000000000000^1667 ≤ 21463204845199^1667*2000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047257147 2000000000 21463204845199 50000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (417867883/2000000000 : ℝ)^2179 ≤ (6458438610159/50000000000000 : ℝ)^1667 := by
    have hnat : (417867883 : ℕ)^2179*50000000000000^1667 ≤ 6458438610159^1667*2000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417867883 2000000000 6458438610159 50000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214028647/400000000 : ℝ), (1047257147/2000000000 : ℝ), (-417867883/2000000000 : ℝ)] ![(44156713069623/100000000000000 : ℝ), (21463204845199/50000000000000 : ℝ), (6458438610159/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214028647/400000000 : ℝ)|^2179 ≤ (44156713069623/100000000000000 : ℝ)^1667
        have hw : |(214028647/400000000 : ℝ)|=(214028647/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1047257147/2000000000 : ℝ)|^2179 ≤ (21463204845199/50000000000000 : ℝ)^1667
        have hw : |(1047257147/2000000000 : ℝ)|=(1047257147/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-417867883/2000000000 : ℝ)|^2179 ≤ (6458438610159/50000000000000 : ℝ)^1667
        have hw : |(-417867883/2000000000 : ℝ)|=(417867883/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1398_s3_3 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4311413509/10000000000 : ℝ)*x 0 + (4118481451/10000000000 : ℝ)*x 1 + (4512555627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4311413509/10000000000 : ℝ)^2179 ≤ (4162050072523/12500000000000 : ℝ)^1667 := by
    have hnat : (4311413509 : ℕ)^2179*12500000000000^1667 ≤ 4162050072523^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4311413509 10000000000 4162050072523 12500000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4118481451/10000000000 : ℝ)^2179 ≤ (15681154219861/50000000000000 : ℝ)^1667 := by
    have hnat : (4118481451 : ℕ)^2179*50000000000000^1667 ≤ 15681154219861^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4118481451 10000000000 15681154219861 50000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4512555627/10000000000 : ℝ)^2179 ≤ (17670645485149/50000000000000 : ℝ)^1667 := by
    have hnat : (4512555627 : ℕ)^2179*50000000000000^1667 ≤ 17670645485149^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4512555627 10000000000 17670645485149 50000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4311413509/10000000000 : ℝ), (4118481451/10000000000 : ℝ), (4512555627/10000000000 : ℝ)] ![(4162050072523/12500000000000 : ℝ), (15681154219861/50000000000000 : ℝ), (17670645485149/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4311413509/10000000000 : ℝ)|^2179 ≤ (4162050072523/12500000000000 : ℝ)^1667
        have hw : |(4311413509/10000000000 : ℝ)|=(4311413509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4118481451/10000000000 : ℝ)|^2179 ≤ (15681154219861/50000000000000 : ℝ)^1667
        have hw : |(4118481451/10000000000 : ℝ)|=(4118481451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4512555627/10000000000 : ℝ)|^2179 ≤ (17670645485149/50000000000000 : ℝ)^1667
        have hw : |(4512555627/10000000000 : ℝ)|=(4512555627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1398_s3_4 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-997655877/5000000000 : ℝ)*x 0 + (523703127/1000000000 : ℝ)*x 1 + (2709893529/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (997655877/5000000000 : ℝ)^2179 ≤ (12162337910407/100000000000000 : ℝ)^1667 := by
    have hnat : (997655877 : ℕ)^2179*100000000000000^1667 ≤ 12162337910407^1667*5000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      997655877 5000000000 12162337910407 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (523703127/1000000000 : ℝ)^2179 ≤ (42934398837017/100000000000000 : ℝ)^1667 := by
    have hnat : (523703127 : ℕ)^2179*100000000000000^1667 ≤ 42934398837017^1667*1000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523703127 1000000000 42934398837017 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2709893529/5000000000 : ℝ)^2179 ≤ (701613488141/1562500000000 : ℝ)^1667 := by
    have hnat : (2709893529 : ℕ)^2179*1562500000000^1667 ≤ 701613488141^1667*5000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709893529 5000000000 701613488141 1562500000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-997655877/5000000000 : ℝ), (523703127/1000000000 : ℝ), (2709893529/5000000000 : ℝ)] ![(12162337910407/100000000000000 : ℝ), (42934398837017/100000000000000 : ℝ), (701613488141/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-997655877/5000000000 : ℝ)|^2179 ≤ (12162337910407/100000000000000 : ℝ)^1667
        have hw : |(-997655877/5000000000 : ℝ)|=(997655877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(523703127/1000000000 : ℝ)|^2179 ≤ (42934398837017/100000000000000 : ℝ)^1667
        have hw : |(523703127/1000000000 : ℝ)|=(523703127/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2709893529/5000000000 : ℝ)|^2179 ≤ (701613488141/1562500000000 : ℝ)^1667
        have hw : |(2709893529/5000000000 : ℝ)|=(2709893529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1398_s3_5 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2651482899/5000000000 : ℝ)*x 0 + (-59557413/312500000 : ℝ)*x 1 + (5419787559/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651482899/5000000000 : ℝ)^2179 ≤ (43642330279301/100000000000000 : ℝ)^1667 := by
    have hnat : (2651482899 : ℕ)^2179*100000000000000^1667 ≤ 43642330279301^1667*5000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651482899 5000000000 43642330279301 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (59557413/312500000 : ℝ)^2179 ≤ (5727200523779/50000000000000 : ℝ)^1667 := by
    have hnat : (59557413 : ℕ)^2179*50000000000000^1667 ≤ 5727200523779^1667*312500000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      59557413 312500000 5727200523779 50000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5419787559/10000000000 : ℝ)^2179 ≤ (8980653733343/20000000000000 : ℝ)^1667 := by
    have hnat : (5419787559 : ℕ)^2179*20000000000000^1667 ≤ 8980653733343^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419787559 10000000000 8980653733343 20000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651482899/5000000000 : ℝ), (-59557413/312500000 : ℝ), (5419787559/10000000000 : ℝ)] ![(43642330279301/100000000000000 : ℝ), (5727200523779/50000000000000 : ℝ), (8980653733343/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651482899/5000000000 : ℝ)|^2179 ≤ (43642330279301/100000000000000 : ℝ)^1667
        have hw : |(2651482899/5000000000 : ℝ)|=(2651482899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-59557413/312500000 : ℝ)|^2179 ≤ (5727200523779/50000000000000 : ℝ)^1667
        have hw : |(-59557413/312500000 : ℝ)|=(59557413/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5419787559/10000000000 : ℝ)|^2179 ≤ (8980653733343/20000000000000 : ℝ)^1667
        have hw : |(5419787559/10000000000 : ℝ)|=(5419787559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1398_s3_6 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1325741707/2500000000 : ℝ)*x 0 + (5419786787/10000000000 : ℝ)*x 1 + (-1905836869/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325741707/2500000000 : ℝ)^2179 ≤ (43642341359511/100000000000000 : ℝ)^1667 := by
    have hnat : (1325741707 : ℕ)^2179*100000000000000^1667 ≤ 43642341359511^1667*2500000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325741707 2500000000 43642341359511 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5419786787/10000000000 : ℝ)^2179 ≤ (4490326030617/10000000000000 : ℝ)^1667 := by
    have hnat : (5419786787 : ℕ)^2179*10000000000000^1667 ≤ 4490326030617^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419786787 10000000000 4490326030617 10000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1905836869/10000000000 : ℝ)^2179 ≤ (2863599580371/25000000000000 : ℝ)^1667 := by
    have hnat : (1905836869 : ℕ)^2179*25000000000000^1667 ≤ 2863599580371^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1905836869 10000000000 2863599580371 25000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325741707/2500000000 : ℝ), (5419786787/10000000000 : ℝ), (-1905836869/10000000000 : ℝ)] ![(43642341359511/100000000000000 : ℝ), (4490326030617/10000000000000 : ℝ), (2863599580371/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325741707/2500000000 : ℝ)|^2179 ≤ (43642341359511/100000000000000 : ℝ)^1667
        have hw : |(1325741707/2500000000 : ℝ)|=(1325741707/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5419786787/10000000000 : ℝ)|^2179 ≤ (4490326030617/10000000000000 : ℝ)^1667
        have hw : |(5419786787/10000000000 : ℝ)|=(5419786787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1905836869/10000000000 : ℝ)|^2179 ≤ (2863599580371/25000000000000 : ℝ)^1667
        have hw : |(-1905836869/10000000000 : ℝ)|=(1905836869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1398_s3_7 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2155725657/5000000000 : ℝ)*x 0 + (451096033/1000000000 : ℝ)*x 1 + (412008363/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2155725657/5000000000 : ℝ)^2179 ≤ (8324195553987/25000000000000 : ℝ)^1667 := by
    have hnat : (2155725657 : ℕ)^2179*25000000000000^1667 ≤ 8324195553987^1667*5000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155725657 5000000000 8324195553987 25000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (451096033/1000000000 : ℝ)^2179 ≤ (35324960471899/100000000000000 : ℝ)^1667 := by
    have hnat : (451096033 : ℕ)^2179*100000000000000^1667 ≤ 35324960471899^1667*1000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451096033 1000000000 35324960471899 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (412008363/1000000000 : ℝ)^2179 ≤ (1961141080933/6250000000000 : ℝ)^1667 := by
    have hnat : (412008363 : ℕ)^2179*6250000000000^1667 ≤ 1961141080933^1667*1000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412008363 1000000000 1961141080933 6250000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2155725657/5000000000 : ℝ), (451096033/1000000000 : ℝ), (412008363/1000000000 : ℝ)] ![(8324195553987/25000000000000 : ℝ), (35324960471899/100000000000000 : ℝ), (1961141080933/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2155725657/5000000000 : ℝ)|^2179 ≤ (8324195553987/25000000000000 : ℝ)^1667
        have hw : |(2155725657/5000000000 : ℝ)|=(2155725657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(451096033/1000000000 : ℝ)|^2179 ≤ (35324960471899/100000000000000 : ℝ)^1667
        have hw : |(451096033/1000000000 : ℝ)|=(451096033/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(412008363/1000000000 : ℝ)|^2179 ≤ (1961141080933/6250000000000 : ℝ)^1667
        have hw : |(412008363/1000000000 : ℝ)|=(412008363/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1398_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156939393/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15899/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2549/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (1383/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2993/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15899/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2549/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15899/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2549/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15899/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2549/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15899/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2549/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15899/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2549/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15899/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2549/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2549/25000 : ℝ) ^ (4357/1024 : ℝ) ≤ (6039279267431231/100000000000000000000 : ℝ) := by
    have hpowers : (2549/25000 : ℝ)^4357 ≤ (6039279267431231/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2549 : ℕ)^4357*100000000000000000000^1024 ≤ 6039279267431231^1024*25000^4357 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2549 25000 6039279267431231 100000000000000000000 4357 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2549/25000 : ℝ)) (X := (6039279267431231/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4357 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15899/100000 : ℝ) ^ (4357/1024 : ℝ) ≤ (1249603261082533/3125000000000000000 : ℝ) := by
    have hpowers : (15899/100000 : ℝ)^4357 ≤ (1249603261082533/3125000000000000000 : ℝ)^1024 := by
      have hnat : (15899 : ℕ)^4357*3125000000000000000^1024 ≤ 1249603261082533^1024*100000^4357 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15899 100000 1249603261082533 3125000000000000000 4357 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15899/100000 : ℝ)) (X := (1249603261082533/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4357 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006039279267431231/50000000000000000000 : ℝ) ≤ (10000283862120041/10000000000000000 : ℝ) ^ (4357/1024 : ℝ) := by
    have hpowers : (50006039279267431231/50000000000000000000 : ℝ)^1024 ≤ (10000283862120041/10000000000000000 : ℝ)^4357 := by
      have hnat : (50006039279267431231 : ℕ)^1024*10000000000000000^4357 ≤ 10000283862120041^4357*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006039279267431231 50000000000000000000 10000283862120041 10000000000000000 1024 4357 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000283862120041/10000000000000000 : ℝ)) (X := (50006039279267431231/50000000000000000000 : ℝ)) (by norm_num) 4357 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046026583622072287/100000000000000000000 : ℝ) ≤ (10001081545251449/10000000000000000 : ℝ) ^ (4357/1024 : ℝ) := by
    have hpowers : (100046026583622072287/100000000000000000000 : ℝ)^1024 ≤ (10001081545251449/10000000000000000 : ℝ)^4357 := by
      have hnat : (100046026583622072287 : ℕ)^1024*10000000000000000^4357 ≤ 10001081545251449^4357*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046026583622072287 100000000000000000000 10001081545251449 10000000000000000 1024 4357 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001081545251449/10000000000000000 : ℝ)) (X := (100046026583622072287/100000000000000000000 : ℝ)) (by norm_num) 4357 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1563749603261082533/1562500000000000000 : ℝ) ≤ (10001879228382857/10000000000000000 : ℝ) ^ (4357/1024 : ℝ) := by
    have hpowers : (1563749603261082533/1562500000000000000 : ℝ)^1024 ≤ (10001879228382857/10000000000000000 : ℝ)^4357 := by
      have hnat : (1563749603261082533 : ℕ)^1024*10000000000000000^4357 ≤ 10001879228382857^4357*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1563749603261082533 1562500000000000000 10001879228382857 10000000000000000 1024 4357 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001879228382857/10000000000000000 : ℝ)) (X := (1563749603261082533/1562500000000000000 : ℝ)) (by norm_num) 4357 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6039279267431231/100000000000000000000 : ℝ) ≤ ((19005117503751640629/19010000000000000000 : ℝ)+2*(16618398571/11881250000000 : ℝ)*(2549/25000 : ℝ))^(4357/1024 : ℝ) := by
    rw [show (19005117503751640629/19010000000000000000 : ℝ)+2*(16618398571/11881250000000 : ℝ)*(2549/25000 : ℝ)=(10000283862120041/10000000000000000 : ℝ) by norm_num, show 1+2*(6039279267431231/100000000000000000000 : ℝ)=(50006039279267431231/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1249603261082533/3125000000000000000 : ℝ)+(6039279267431231/100000000000000000000 : ℝ) ≤ ((19005117503751640629/19010000000000000000 : ℝ)+(16618398571/11881250000000 : ℝ)*((15899/100000 : ℝ)+(2549/25000 : ℝ)))^(4357/1024 : ℝ) := by
    rw [show (19005117503751640629/19010000000000000000 : ℝ)+(16618398571/11881250000000 : ℝ)*((15899/100000 : ℝ)+(2549/25000 : ℝ))=(10001081545251449/10000000000000000 : ℝ) by norm_num, show 1+(1249603261082533/3125000000000000000 : ℝ)+(6039279267431231/100000000000000000000 : ℝ)=(100046026583622072287/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1249603261082533/3125000000000000000 : ℝ) ≤ ((19005117503751640629/19010000000000000000 : ℝ)+2*(16618398571/11881250000000 : ℝ)*(15899/100000 : ℝ))^(4357/1024 : ℝ) := by
    rw [show (19005117503751640629/19010000000000000000 : ℝ)+2*(16618398571/11881250000000 : ℝ)*(15899/100000 : ℝ)=(10001879228382857/10000000000000000 : ℝ) by norm_num, show 1+2*(1249603261082533/3125000000000000000 : ℝ)=(1563749603261082533/1562500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (19005117503751640629/19010000000000000000 : ℝ)*(X 1 0+X 2 0)+(16618398571/11881250000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4357/1024 : ℝ)) (lo := (2549/25000 : ℝ)) (hi := (15899/100000 : ℝ)) (c := (19005117503751640629/19010000000000000000 : ℝ)) (alpha := (16618398571/11881250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (19005117503751640629/19010000000000000000 : ℝ)*(X 0 1+X 2 1)+(16618398571/11881250000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4357/1024 : ℝ)) (lo := (2549/25000 : ℝ)) (hi := (15899/100000 : ℝ)) (c := (19005117503751640629/19010000000000000000 : ℝ)) (alpha := (16618398571/11881250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (19005117503751640629/19010000000000000000 : ℝ)*(X 0 2+X 1 2)+(16618398571/11881250000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4357/1024 : ℝ)) (lo := (2549/25000 : ℝ)) (hi := (15899/100000 : ℝ)) (c := (19005117503751640629/19010000000000000000 : ℝ)) (alpha := (16618398571/11881250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-498823653/2500000000 : ℝ)*X 0 0+(1355134341/2500000000 : ℝ)*X 0 1+(5236285729/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350717227/10000000000 : ℝ)*X 1 0+(-2089339187/10000000000 : ℝ)*X 1 1+(327267803/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((214028647/400000000 : ℝ)*X 2 0+(1047257147/2000000000 : ℝ)*X 2 1+(-417867883/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4311413509/10000000000 : ℝ)*X 0 0+(4118481451/10000000000 : ℝ)*X 0 1+(4512555627/10000000000 : ℝ)*X 0 2+(4311413509/10000000000 : ℝ)*X 1 0+(4118481451/10000000000 : ℝ)*X 1 1+(4512555627/10000000000 : ℝ)*X 1 2+(4311413509/10000000000 : ℝ)*X 2 0+(4118481451/10000000000 : ℝ)*X 2 1+(4512555627/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-997655877/5000000000 : ℝ)*X 0 0+(523703127/1000000000 : ℝ)*X 0 1+(2709893529/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2651482899/5000000000 : ℝ)*X 1 0+(-59557413/312500000 : ℝ)*X 1 1+(5419787559/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1325741707/2500000000 : ℝ)*X 2 0+(5419786787/10000000000 : ℝ)*X 2 1+(-1905836869/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2155725657/5000000000 : ℝ)*X 0 0+(451096033/1000000000 : ℝ)*X 0 1+(412008363/1000000000 : ℝ)*X 0 2+(2155725657/5000000000 : ℝ)*X 1 0+(451096033/1000000000 : ℝ)*X 1 1+(412008363/1000000000 : ℝ)*X 1 2+(2155725657/5000000000 : ℝ)*X 2 0+(451096033/1000000000 : ℝ)*X 2 1+(412008363/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2846447018296970348076941721/475250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1079312511/100000000000000 : ℝ)*(base19) + (53687369/50000000000000 : ℝ)*(base23) + (6338307/5000000000000 : ℝ)*(upper2) + (51359613/100000000000000 : ℝ)*(upper4) + (29412847/20000000000000 : ℝ)*(lower5) + (1991243487592617/50000000000000 : ℝ)*(major0) + (1991243487592617/50000000000000 : ℝ)*(major1) + (1991243487592617/50000000000000 : ℝ)*(major2) + (1356844072088331/25000000000000 : ℝ)*(sp0) + (2713688585486373/50000000000000 : ℝ)*(sp1) + (5427373011371367/100000000000000 : ℝ)*(sp2) + (317199437554951/12500000000000 : ℝ)*(sp3) + (1961931933/100000000000000 : ℝ)*(sp4) + (320721197/6250000000000 : ℝ)*(sp6) + (317199437554951/12500000000000 : ℝ)*(f.failure) + (5427378250285257/100000000000000 : ℝ)*(f.sum) + (37450098286157/4752500000000000000000000000 : ℝ)*base65 + (11834145061501836093/950500000000000000000000000000000 : ℝ)*base67 + (6001965134163907/950500000000000000000000000000000 : ℝ)*base70 + (9625462736621836093/950500000000000000000000000000000 : ℝ)*base71 + (29896569817147/4752500000000000000000000000 : ℝ)*base73 + (6449932206383163907/950500000000000000000000000000000 : ℝ)*base76 + (4294758626702336093/950500000000000000000000000000000 : ℝ)*base77 + (20118521018890336093/950500000000000000000000000000000 : ℝ)*base79 + (36857240847209/9505000000000000000000000000 : ℝ)*base81 + (10915257/1250000000000000000000 : ℝ)*base90 + (10915257/1250000000000000000000 : ℝ)*base92 + (10915257/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (521667242454170915520485469/95050000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1247995449/50000000000000 : ℝ)*(base19) + (397683529/10000000000000 : ℝ)*(base23) + (478279297/100000000000000 : ℝ)*(upper3) + (27225201/25000000000000 : ℝ)*(lower4) + (74927957/25000000000000 : ℝ)*(upper5) + (803014013359987/20000000000000 : ℝ)*(major0) + (803014013359987/20000000000000 : ℝ)*(major1) + (803014013359987/20000000000000 : ℝ)*(major2) + (12793733077/25000000000000 : ℝ)*(sp1) + (9349873939/12500000000000 : ℝ)*(sp2) + (273589143702389/5000000000000 : ℝ)*(sp4) + (218869168124983/4000000000000 : ℝ)*(sp5) + (2735852049110489/50000000000000 : ℝ)*(sp6) + (9993582330497/390625000000 : ℝ)*(sp7) + (9993582330497/390625000000 : ℝ)*(f.failure) + (273589143702389/5000000000000 : ℝ)*(f.sum) + (198986302837/237625000000000000000000000 : ℝ)*base66 + (3998091316476688177/380200000000000000000000000000000 : ℝ)*base68 + (1513391638924688177/380200000000000000000000000000000 : ℝ)*base70 + (4159361303287488177/380200000000000000000000000000000 : ℝ)*base72 + (764139916033/475250000000000000000000000 : ℝ)*base74 + (3490659899218488177/380200000000000000000000000000000 : ℝ)*base76 + (418599591851088177/380200000000000000000000000000000 : ℝ)*base78 + (4325164045562111823/380200000000000000000000000000000 : ℝ)*base79 + (5522241893883/950500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (20527/19531250000000000000 : ℝ)*base90 + (20527/19531250000000000000 : ℝ)*base92 + (20527/19531250000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1398_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156939393/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15899/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2549/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1383/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2993/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1398_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1398_s4_0 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-12477283/62500000 : ℝ)*x 0 + (67644201/125000000 : ℝ)*x 1 + (1311145661/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (12477283/62500000 : ℝ)^2179 ≤ (3042683168169/25000000000000 : ℝ)^1667 := by
    have hnat : (12477283 : ℕ)^2179*25000000000000^1667 ≤ 3042683168169^1667*62500000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12477283 62500000 3042683168169 25000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (67644201/125000000 : ℝ)^2179 ≤ (11203482085143/25000000000000 : ℝ)^1667 := by
    have hnat : (67644201 : ℕ)^2179*25000000000000^1667 ≤ 11203482085143^1667*125000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67644201 125000000 11203482085143 25000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311145661/2500000000 : ℝ)^2179 ≤ (43015338977733/100000000000000 : ℝ)^1667 := by
    have hnat : (1311145661 : ℕ)^2179*100000000000000^1667 ≤ 43015338977733^1667*2500000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311145661 2500000000 43015338977733 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-12477283/62500000 : ℝ), (67644201/125000000 : ℝ), (1311145661/2500000000 : ℝ)] ![(3042683168169/25000000000000 : ℝ), (11203482085143/25000000000000 : ℝ), (43015338977733/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-12477283/62500000 : ℝ)|^2179 ≤ (3042683168169/25000000000000 : ℝ)^1667
        have hw : |(-12477283/62500000 : ℝ)|=(12477283/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(67644201/125000000 : ℝ)|^2179 ≤ (11203482085143/25000000000000 : ℝ)^1667
        have hw : |(67644201/125000000 : ℝ)|=(67644201/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311145661/2500000000 : ℝ)|^2179 ≤ (43015338977733/100000000000000 : ℝ)^1667
        have hw : |(1311145661/2500000000 : ℝ)|=(1311145661/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1398_s4_1 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5348402651/10000000000 : ℝ)*x 0 + (-208141743/1000000000 : ℝ)*x 1 + (5244583239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348402651/10000000000 : ℝ)^2179 ≤ (8826351682329/20000000000000 : ℝ)^1667 := by
    have hnat : (5348402651 : ℕ)^2179*20000000000000^1667 ≤ 8826351682329^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348402651 10000000000 8826351682329 20000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (208141743/1000000000 : ℝ)^2179 ≤ (6426448111513/50000000000000 : ℝ)^1667 := by
    have hnat : (208141743 : ℕ)^2179*50000000000000^1667 ≤ 6426448111513^1667*1000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208141743 1000000000 6426448111513 50000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244583239/10000000000 : ℝ)^2179 ≤ (4301534535671/10000000000000 : ℝ)^1667 := by
    have hnat : (5244583239 : ℕ)^2179*10000000000000^1667 ≤ 4301534535671^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244583239 10000000000 4301534535671 10000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348402651/10000000000 : ℝ), (-208141743/1000000000 : ℝ), (5244583239/10000000000 : ℝ)] ![(8826351682329/20000000000000 : ℝ), (6426448111513/50000000000000 : ℝ), (4301534535671/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348402651/10000000000 : ℝ)|^2179 ≤ (8826351682329/20000000000000 : ℝ)^1667
        have hw : |(5348402651/10000000000 : ℝ)|=(5348402651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-208141743/1000000000 : ℝ)|^2179 ≤ (6426448111513/50000000000000 : ℝ)^1667
        have hw : |(-208141743/1000000000 : ℝ)|=(208141743/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244583239/10000000000 : ℝ)|^2179 ≤ (4301534535671/10000000000000 : ℝ)^1667
        have hw : |(5244583239/10000000000 : ℝ)|=(5244583239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1398_s4_2 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2674201549/5000000000 : ℝ)*x 0 + (131114573/250000000 : ℝ)*x 1 + (-260177157/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674201549/5000000000 : ℝ)^2179 ≤ (22065881616429/50000000000000 : ℝ)^1667 := by
    have hnat : (2674201549 : ℕ)^2179*50000000000000^1667 ≤ 22065881616429^1667*5000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674201549 5000000000 22065881616429 50000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131114573/250000000 : ℝ)^2179 ≤ (43015341936721/100000000000000 : ℝ)^1667 := by
    have hnat : (131114573 : ℕ)^2179*100000000000000^1667 ≤ 43015341936721^1667*250000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131114573 250000000 43015341936721 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (260177157/1250000000 : ℝ)^2179 ≤ (2570578963711/20000000000000 : ℝ)^1667 := by
    have hnat : (260177157 : ℕ)^2179*20000000000000^1667 ≤ 2570578963711^1667*1250000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260177157 1250000000 2570578963711 20000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674201549/5000000000 : ℝ), (131114573/250000000 : ℝ), (-260177157/1250000000 : ℝ)] ![(22065881616429/50000000000000 : ℝ), (43015341936721/100000000000000 : ℝ), (2570578963711/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674201549/5000000000 : ℝ)|^2179 ≤ (22065881616429/50000000000000 : ℝ)^1667
        have hw : |(2674201549/5000000000 : ℝ)|=(2674201549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(131114573/250000000 : ℝ)|^2179 ≤ (43015341936721/100000000000000 : ℝ)^1667
        have hw : |(131114573/250000000 : ℝ)|=(131114573/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-260177157/1250000000 : ℝ)|^2179 ≤ (2570578963711/20000000000000 : ℝ)^1667
        have hw : |(-260177157/1250000000 : ℝ)|=(260177157/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1398_s4_3 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2156034451/5000000000 : ℝ)*x 0 + (2068449693/5000000000 : ℝ)*x 1 + (4493977087/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2156034451/5000000000 : ℝ)^2179 ≤ (6660603363811/20000000000000 : ℝ)^1667 := by
    have hnat : (2156034451 : ℕ)^2179*20000000000000^1667 ≤ 6660603363811^1667*5000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2156034451 5000000000 6660603363811 20000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2068449693/5000000000 : ℝ)^2179 ≤ (15772882093609/50000000000000 : ℝ)^1667 := by
    have hnat : (2068449693 : ℕ)^2179*50000000000000^1667 ≤ 15772882093609^1667*5000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2068449693 5000000000 15772882093609 50000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4493977087/10000000000 : ℝ)^2179 ≤ (7030243796273/20000000000000 : ℝ)^1667 := by
    have hnat : (4493977087 : ℕ)^2179*20000000000000^1667 ≤ 7030243796273^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4493977087 10000000000 7030243796273 20000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2156034451/5000000000 : ℝ), (2068449693/5000000000 : ℝ), (4493977087/10000000000 : ℝ)] ![(6660603363811/20000000000000 : ℝ), (15772882093609/50000000000000 : ℝ), (7030243796273/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2156034451/5000000000 : ℝ)|^2179 ≤ (6660603363811/20000000000000 : ℝ)^1667
        have hw : |(2156034451/5000000000 : ℝ)|=(2156034451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2068449693/5000000000 : ℝ)|^2179 ≤ (15772882093609/50000000000000 : ℝ)^1667
        have hw : |(2068449693/5000000000 : ℝ)|=(2068449693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4493977087/10000000000 : ℝ)|^2179 ≤ (7030243796273/20000000000000 : ℝ)^1667
        have hw : |(4493977087/10000000000 : ℝ)|=(4493977087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1398_s4_4 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-998188651/5000000000 : ℝ)*x 0 + (524519531/1000000000 : ℝ)*x 1 + (541092041/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (998188651/5000000000 : ℝ)^2179 ≤ (12170828474873/100000000000000 : ℝ)^1667 := by
    have hnat : (998188651 : ℕ)^2179*100000000000000^1667 ≤ 12170828474873^1667*5000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      998188651 5000000000 12170828474873 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524519531/1000000000 : ℝ)^2179 ≤ (5377738433607/12500000000000 : ℝ)^1667 := by
    have hnat : (524519531 : ℕ)^2179*12500000000000^1667 ≤ 5377738433607^1667*1000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524519531 1000000000 5377738433607 12500000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (541092041/1000000000 : ℝ)^2179 ≤ (22403632020651/50000000000000 : ℝ)^1667 := by
    have hnat : (541092041 : ℕ)^2179*50000000000000^1667 ≤ 22403632020651^1667*1000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541092041 1000000000 22403632020651 50000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-998188651/5000000000 : ℝ), (524519531/1000000000 : ℝ), (541092041/1000000000 : ℝ)] ![(12170828474873/100000000000000 : ℝ), (5377738433607/12500000000000 : ℝ), (22403632020651/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-998188651/5000000000 : ℝ)|^2179 ≤ (12170828474873/100000000000000 : ℝ)^1667
        have hw : |(-998188651/5000000000 : ℝ)|=(998188651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524519531/1000000000 : ℝ)|^2179 ≤ (5377738433607/12500000000000 : ℝ)^1667
        have hw : |(524519531/1000000000 : ℝ)|=(524519531/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(541092041/1000000000 : ℝ)|^2179 ≤ (22403632020651/50000000000000 : ℝ)^1667
        have hw : |(541092041/1000000000 : ℝ)|=(541092041/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1398_s4_5 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (106102709/200000000 : ℝ)*x 0 + (-1915079407/10000000000 : ℝ)*x 1 + (1082184107/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106102709/200000000 : ℝ)^2179 ≤ (43665671743779/100000000000000 : ℝ)^1667 := by
    have hnat : (106102709 : ℕ)^2179*100000000000000^1667 ≤ 43665671743779^1667*200000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106102709 200000000 43665671743779 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1915079407/10000000000 : ℝ)^2179 ≤ (11527062838481/100000000000000 : ℝ)^1667 := by
    have hnat : (1915079407 : ℕ)^2179*100000000000000^1667 ≤ 11527062838481^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1915079407 10000000000 11527062838481 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082184107/2000000000 : ℝ)^2179 ≤ (1400227043573/3125000000000 : ℝ)^1667 := by
    have hnat : (1082184107 : ℕ)^2179*3125000000000^1667 ≤ 1400227043573^1667*2000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082184107 2000000000 1400227043573 3125000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106102709/200000000 : ℝ), (-1915079407/10000000000 : ℝ), (1082184107/2000000000 : ℝ)] ![(43665671743779/100000000000000 : ℝ), (11527062838481/100000000000000 : ℝ), (1400227043573/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106102709/200000000 : ℝ)|^2179 ≤ (43665671743779/100000000000000 : ℝ)^1667
        have hw : |(106102709/200000000 : ℝ)|=(106102709/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1915079407/10000000000 : ℝ)|^2179 ≤ (11527062838481/100000000000000 : ℝ)^1667
        have hw : |(-1915079407/10000000000 : ℝ)|=(1915079407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082184107/2000000000 : ℝ)|^2179 ≤ (1400227043573/3125000000000 : ℝ)^1667
        have hw : |(1082184107/2000000000 : ℝ)|=(1082184107/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1398_s4_6 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305135411/10000000000 : ℝ)*x 0 + (33818253/62500000 : ℝ)*x 1 + (-957539769/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305135411/10000000000 : ℝ)^2179 ≤ (8733134264837/20000000000000 : ℝ)^1667 := by
    have hnat : (5305135411 : ℕ)^2179*20000000000000^1667 ≤ 8733134264837^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305135411 10000000000 8733134264837 20000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (33818253/62500000 : ℝ)^2179 ≤ (44807264799001/100000000000000 : ℝ)^1667 := by
    have hnat : (33818253 : ℕ)^2179*100000000000000^1667 ≤ 44807264799001^1667*62500000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33818253 62500000 44807264799001 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (957539769/5000000000 : ℝ)^2179 ≤ (11527063869163/100000000000000 : ℝ)^1667 := by
    have hnat : (957539769 : ℕ)^2179*100000000000000^1667 ≤ 11527063869163^1667*5000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      957539769 5000000000 11527063869163 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305135411/10000000000 : ℝ), (33818253/62500000 : ℝ), (-957539769/5000000000 : ℝ)] ![(8733134264837/20000000000000 : ℝ), (44807264799001/100000000000000 : ℝ), (11527063869163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305135411/10000000000 : ℝ)|^2179 ≤ (8733134264837/20000000000000 : ℝ)^1667
        have hw : |(5305135411/10000000000 : ℝ)|=(5305135411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(33818253/62500000 : ℝ)|^2179 ≤ (44807264799001/100000000000000 : ℝ)^1667
        have hw : |(33818253/62500000 : ℝ)|=(33818253/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-957539769/5000000000 : ℝ)|^2179 ≤ (11527063869163/100000000000000 : ℝ)^1667
        have hw : |(-957539769/5000000000 : ℝ)|=(957539769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1398_s4_7 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4312095051/10000000000 : ℝ)*x 0 + (1123166777/2500000000 : ℝ)*x 1 + (2069108247/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4312095051/10000000000 : ℝ)^2179 ≤ (1332131232059/4000000000000 : ℝ)^1667 := by
    have hnat : (4312095051 : ℕ)^2179*4000000000000^1667 ≤ 1332131232059^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4312095051 10000000000 1332131232059 4000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1123166777/2500000000 : ℝ)^2179 ≤ (35137826037223/100000000000000 : ℝ)^1667 := by
    have hnat : (1123166777 : ℕ)^2179*100000000000000^1667 ≤ 35137826037223^1667*2500000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123166777 2500000000 35137826037223 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2069108247/5000000000 : ℝ)^2179 ≤ (1972430821737/6250000000000 : ℝ)^1667 := by
    have hnat : (2069108247 : ℕ)^2179*6250000000000^1667 ≤ 1972430821737^1667*5000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069108247 5000000000 1972430821737 6250000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4312095051/10000000000 : ℝ), (1123166777/2500000000 : ℝ), (2069108247/5000000000 : ℝ)] ![(1332131232059/4000000000000 : ℝ), (35137826037223/100000000000000 : ℝ), (1972430821737/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4312095051/10000000000 : ℝ)|^2179 ≤ (1332131232059/4000000000000 : ℝ)^1667
        have hw : |(4312095051/10000000000 : ℝ)|=(4312095051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1123166777/2500000000 : ℝ)|^2179 ≤ (35137826037223/100000000000000 : ℝ)^1667
        have hw : |(1123166777/2500000000 : ℝ)|=(1123166777/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2069108247/5000000000 : ℝ)|^2179 ≤ (1972430821737/6250000000000 : ℝ)^1667
        have hw : |(2069108247/5000000000 : ℝ)|=(2069108247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1398_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156939393/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2993/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1383/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (11241/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1847/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2993/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1383/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2993/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1383/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2993/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1383/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2993/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1383/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2993/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1383/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2993/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1383/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1383/12500 : ℝ) ^ (4357/1024 : ℝ) ≤ (4274923199635161/50000000000000000000 : ℝ) := by
    have hpowers : (1383/12500 : ℝ)^4357 ≤ (4274923199635161/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1383 : ℕ)^4357*50000000000000000000^1024 ≤ 4274923199635161^1024*12500^4357 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1383 12500 4274923199635161 50000000000000000000 4357 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1383/12500 : ℝ)) (X := (4274923199635161/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4357 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2993/20000 : ℝ) ^ (4357/1024 : ℝ) ≤ (241456082223943/781250000000000000 : ℝ) := by
    have hpowers : (2993/20000 : ℝ)^4357 ≤ (241456082223943/781250000000000000 : ℝ)^1024 := by
      have hnat : (2993 : ℕ)^4357*781250000000000000^1024 ≤ 241456082223943^1024*20000^4357 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2993 20000 241456082223943 781250000000000000 4357 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2993/20000 : ℝ)) (X := (241456082223943/781250000000000000 : ℝ)) (by norm_num) (by norm_num) 4357 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004274923199635161/25000000000000000000 : ℝ) ≤ (10000401857707291/10000000000000000 : ℝ) ^ (4357/1024 : ℝ) := by
    have hpowers : (25004274923199635161/25000000000000000000 : ℝ)^1024 ≤ (10000401857707291/10000000000000000 : ℝ)^4357 := by
      have hnat : (25004274923199635161 : ℕ)^1024*10000000000000000^4357 ≤ 10000401857707291^4357*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004274923199635161 25000000000000000000 10000401857707291 10000000000000000 1024 4357 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000401857707291/10000000000000000 : ℝ)) (X := (25004274923199635161/25000000000000000000 : ℝ)) (by norm_num) 4357 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50019728112461967513/50000000000000000000 : ℝ) ≤ (10000927176458107/10000000000000000 : ℝ) ^ (4357/1024 : ℝ) := by
    have hpowers : (50019728112461967513/50000000000000000000 : ℝ)^1024 ≤ (10000927176458107/10000000000000000 : ℝ)^4357 := by
      have hnat : (50019728112461967513 : ℕ)^1024*10000000000000000^4357 ≤ 10000927176458107^4357*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50019728112461967513 50000000000000000000 10000927176458107 10000000000000000 1024 4357 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000927176458107/10000000000000000 : ℝ)) (X := (50019728112461967513/50000000000000000000 : ℝ)) (by norm_num) 4357 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (390866456082223943/390625000000000000 : ℝ) ≤ (10001452495208923/10000000000000000 : ℝ) ^ (4357/1024 : ℝ) := by
    have hpowers : (390866456082223943/390625000000000000 : ℝ)^1024 ≤ (10001452495208923/10000000000000000 : ℝ)^4357 := by
      have hnat : (390866456082223943 : ℕ)^1024*10000000000000000^4357 ≤ 10001452495208923^4357*390625000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        390866456082223943 390625000000000000 10001452495208923 10000000000000000 1024 4357 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001452495208923/10000000000000000 : ℝ)) (X := (390866456082223943/390625000000000000 : ℝ)) (by norm_num) 4357 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4274923199635161/50000000000000000000 : ℝ) ≤ ((38999943393598085743/39010000000000000000 : ℝ)+2*(16416210963/12190625000000 : ℝ)*(1383/12500 : ℝ))^(4357/1024 : ℝ) := by
    rw [show (38999943393598085743/39010000000000000000 : ℝ)+2*(16416210963/12190625000000 : ℝ)*(1383/12500 : ℝ)=(10000401857707291/10000000000000000 : ℝ) by norm_num, show 1+2*(4274923199635161/50000000000000000000 : ℝ)=(25004274923199635161/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(241456082223943/781250000000000000 : ℝ)+(4274923199635161/50000000000000000000 : ℝ) ≤ ((38999943393598085743/39010000000000000000 : ℝ)+(16416210963/12190625000000 : ℝ)*((2993/20000 : ℝ)+(1383/12500 : ℝ)))^(4357/1024 : ℝ) := by
    rw [show (38999943393598085743/39010000000000000000 : ℝ)+(16416210963/12190625000000 : ℝ)*((2993/20000 : ℝ)+(1383/12500 : ℝ))=(10000927176458107/10000000000000000 : ℝ) by norm_num, show 1+(241456082223943/781250000000000000 : ℝ)+(4274923199635161/50000000000000000000 : ℝ)=(50019728112461967513/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(241456082223943/781250000000000000 : ℝ) ≤ ((38999943393598085743/39010000000000000000 : ℝ)+2*(16416210963/12190625000000 : ℝ)*(2993/20000 : ℝ))^(4357/1024 : ℝ) := by
    rw [show (38999943393598085743/39010000000000000000 : ℝ)+2*(16416210963/12190625000000 : ℝ)*(2993/20000 : ℝ)=(10001452495208923/10000000000000000 : ℝ) by norm_num, show 1+2*(241456082223943/781250000000000000 : ℝ)=(390866456082223943/390625000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (38999943393598085743/39010000000000000000 : ℝ)*(X 1 0+X 2 0)+(16416210963/12190625000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4357/1024 : ℝ)) (lo := (1383/12500 : ℝ)) (hi := (2993/20000 : ℝ)) (c := (38999943393598085743/39010000000000000000 : ℝ)) (alpha := (16416210963/12190625000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (38999943393598085743/39010000000000000000 : ℝ)*(X 0 1+X 2 1)+(16416210963/12190625000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4357/1024 : ℝ)) (lo := (1383/12500 : ℝ)) (hi := (2993/20000 : ℝ)) (c := (38999943393598085743/39010000000000000000 : ℝ)) (alpha := (16416210963/12190625000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (38999943393598085743/39010000000000000000 : ℝ)*(X 0 2+X 1 2)+(16416210963/12190625000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4357/1024 : ℝ)) (lo := (1383/12500 : ℝ)) (hi := (2993/20000 : ℝ)) (c := (38999943393598085743/39010000000000000000 : ℝ)) (alpha := (16416210963/12190625000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-12477283/62500000 : ℝ)*X 0 0+(67644201/125000000 : ℝ)*X 0 1+(1311145661/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348402651/10000000000 : ℝ)*X 1 0+(-208141743/1000000000 : ℝ)*X 1 1+(5244583239/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674201549/5000000000 : ℝ)*X 2 0+(131114573/250000000 : ℝ)*X 2 1+(-260177157/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2156034451/5000000000 : ℝ)*X 0 0+(2068449693/5000000000 : ℝ)*X 0 1+(4493977087/10000000000 : ℝ)*X 0 2+(2156034451/5000000000 : ℝ)*X 1 0+(2068449693/5000000000 : ℝ)*X 1 1+(4493977087/10000000000 : ℝ)*X 1 2+(2156034451/5000000000 : ℝ)*X 2 0+(2068449693/5000000000 : ℝ)*X 2 1+(4493977087/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-998188651/5000000000 : ℝ)*X 0 0+(524519531/1000000000 : ℝ)*X 0 1+(541092041/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((106102709/200000000 : ℝ)*X 1 0+(-1915079407/10000000000 : ℝ)*X 1 1+(1082184107/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305135411/10000000000 : ℝ)*X 2 0+(33818253/62500000 : ℝ)*X 2 1+(-957539769/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4312095051/10000000000 : ℝ)*X 0 0+(1123166777/2500000000 : ℝ)*X 0 1+(2069108247/5000000000 : ℝ)*X 0 2+(4312095051/10000000000 : ℝ)*X 1 0+(1123166777/2500000000 : ℝ)*X 1 1+(2069108247/5000000000 : ℝ)*X 1 2+(4312095051/10000000000 : ℝ)*X 2 0+(1123166777/2500000000 : ℝ)*X 2 1+(2069108247/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (148061715079876182323464827/19505000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (71410599/10000000000000 : ℝ)*(base19) + (193523591/20000000000000 : ℝ)*(base23) + (49125227/20000000000000 : ℝ)*(upper3) + (66076381/50000000000000 : ℝ)*(upper4) + (370571659/100000000000000 : ℝ)*(upper5) + (43951325566221/1000000000000 : ℝ)*(major0) + (43951325566221/1000000000000 : ℝ)*(major1) + (43951325566221/1000000000000 : ℝ)*(major2) + (1497427301061927/25000000000000 : ℝ)*(sp0) + (2994867782295261/50000000000000 : ℝ)*(sp1) + (5989735311078557/100000000000000 : ℝ)*(sp2) + (700129816625719/25000000000000 : ℝ)*(sp3) + (6768612201/25000000000000 : ℝ)*(sp4) + (931501273/10000000000000 : ℝ)*(sp7) + (560105716303121/20000000000000 : ℝ)*(f.failure) + (93589629354633/1562500000000 : ℝ)*(f.sum) + (13303723356107/1950500000000000000000000000 : ℝ)*base66 + (717442257896472797/39010000000000000000000000000000 : ℝ)*base68 + (777857340124152797/39010000000000000000000000000000 : ℝ)*base70 + (565724657491952797/39010000000000000000000000000000 : ℝ)*base72 + (8377648651549/975250000000000000000000000 : ℝ)*base74 + (780283417509812797/39010000000000000000000000000000 : ℝ)*base76 + (502758451245592797/39010000000000000000000000000000 : ℝ)*base78 + (645087780062072797/39010000000000000000000000000000 : ℝ)*base80 + (691269707513/97525000000000000000000000 : ℝ)*base82 + (13745553/2000000000000000000000 : ℝ)*base89 + (13745553/2000000000000000000000 : ℝ)*base91 + (13745553/2000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (24737866631650588330557/9752500000000000000000000000 : ℝ) := by norm_num
    linear_combination (360743373/100000000000000 : ℝ)*(base19) + (357571411/100000000000000 : ℝ)*(base23) + (21992829/50000000000000 : ℝ)*(upper2) + (49997943/100000000000000 : ℝ)*(upper3) + (21599363/20000000000000 : ℝ)*(upper5) + (2213838886502181/50000000000000 : ℝ)*(major0) + (2213838886502181/50000000000000 : ℝ)*(major1) + (2213838886502181/50000000000000 : ℝ)*(major2) + (717578753/6250000000000 : ℝ)*(sp1) + (1591298289/25000000000000 : ℝ)*(sp2) + (3017044718720751/50000000000000 : ℝ)*(sp4) + (1178530780359/19531250000 : ℝ)*(sp5) + (3017041357338467/50000000000000 : ℝ)*(sp6) + (176329126500937/6250000000000 : ℝ)*(sp7) + (176329126500937/6250000000000 : ℝ)*(f.failure) + (3017044718720751/50000000000000 : ℝ)*(f.sum) + (15963872677113/4876250000000000000000000000 : ℝ)*base65 + (15463761808013894517/1950500000000000000000000000000000 : ℝ)*base68 + (5499246476030105483/1950500000000000000000000000000000 : ℝ)*base69 + (14944907516355894517/1950500000000000000000000000000000 : ℝ)*base72 + (1435208276009/609531250000000000000000000 : ℝ)*base74 + (8656613568404105483/1950500000000000000000000000000000 : ℝ)*base75 + (1048733940612894517/1950500000000000000000000000000000 : ℝ)*base78 + (18605722688876105483/1950500000000000000000000000000000 : ℝ)*base79 + (25059129115323/4876250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (4211241/625000000000000000000 : ℝ)*base89 + (4211241/625000000000000000000 : ℝ)*base91 + (4211241/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1398_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156939393/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2993/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1383/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11241/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1847/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1398_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1398_s5_0 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-998268001/5000000000 : ℝ)*x 0 + (5410053869/10000000000 : ℝ)*x 1 + (5245952173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (998268001/5000000000 : ℝ)^2179 ≤ (1217209315699/10000000000000 : ℝ)^1667 := by
    have hnat : (998268001 : ℕ)^2179*10000000000000^1667 ≤ 1217209315699^1667*5000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      998268001 5000000000 1217209315699 10000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5410053869/10000000000 : ℝ)^2179 ≤ (22398942295943/50000000000000 : ℝ)^1667 := by
    have hnat : (5410053869 : ℕ)^2179*50000000000000^1667 ≤ 22398942295943^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410053869 10000000000 22398942295943 50000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245952173/10000000000 : ℝ)^2179 ≤ (672344097573/1562500000000 : ℝ)^1667 := by
    have hnat : (5245952173 : ℕ)^2179*1562500000000^1667 ≤ 672344097573^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245952173 10000000000 672344097573 1562500000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-998268001/5000000000 : ℝ), (5410053869/10000000000 : ℝ), (5245952173/10000000000 : ℝ)] ![(1217209315699/10000000000000 : ℝ), (22398942295943/50000000000000 : ℝ), (672344097573/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-998268001/5000000000 : ℝ)|^2179 ≤ (1217209315699/10000000000000 : ℝ)^1667
        have hw : |(-998268001/5000000000 : ℝ)|=(998268001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5410053869/10000000000 : ℝ)|^2179 ≤ (22398942295943/50000000000000 : ℝ)^1667
        have hw : |(5410053869/10000000000 : ℝ)|=(5410053869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245952173/10000000000 : ℝ)|^2179 ≤ (672344097573/1562500000000 : ℝ)^1667
        have hw : |(5245952173/10000000000 : ℝ)|=(5245952173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1398_s5_1 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2674010047/5000000000 : ℝ)*x 0 + (-2080107343/10000000000 : ℝ)*x 1 + (2622977149/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674010047/5000000000 : ℝ)^2179 ≤ (44127632307843/100000000000000 : ℝ)^1667 := by
    have hnat : (2674010047 : ℕ)^2179*100000000000000^1667 ≤ 44127632307843^1667*5000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674010047 5000000000 44127632307843 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2080107343/10000000000 : ℝ)^2179 ≤ (1605290331781/12500000000000 : ℝ)^1667 := by
    have hnat : (2080107343 : ℕ)^2179*12500000000000^1667 ≤ 1605290331781^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080107343 10000000000 1605290331781 12500000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622977149/5000000000 : ℝ)^2179 ≤ (537875562857/1250000000000 : ℝ)^1667 := by
    have hnat : (2622977149 : ℕ)^2179*1250000000000^1667 ≤ 537875562857^1667*5000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622977149 5000000000 537875562857 1250000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674010047/5000000000 : ℝ), (-2080107343/10000000000 : ℝ), (2622977149/5000000000 : ℝ)] ![(44127632307843/100000000000000 : ℝ), (1605290331781/12500000000000 : ℝ), (537875562857/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674010047/5000000000 : ℝ)|^2179 ≤ (44127632307843/100000000000000 : ℝ)^1667
        have hw : |(2674010047/5000000000 : ℝ)|=(2674010047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2080107343/10000000000 : ℝ)|^2179 ≤ (1605290331781/12500000000000 : ℝ)^1667
        have hw : |(-2080107343/10000000000 : ℝ)|=(2080107343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622977149/5000000000 : ℝ)|^2179 ≤ (537875562857/1250000000000 : ℝ)^1667
        have hw : |(2622977149/5000000000 : ℝ)|=(2622977149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1398_s5_2 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (167125651/312500000 : ℝ)*x 0 + (6557441/12500000 : ℝ)*x 1 + (-2080108347/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167125651/312500000 : ℝ)^2179 ≤ (22063820133761/50000000000000 : ℝ)^1667 := by
    have hnat : (167125651 : ℕ)^2179*50000000000000^1667 ≤ 22063820133761^1667*312500000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167125651 312500000 22063820133761 50000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6557441/12500000 : ℝ)^2179 ≤ (43030028967259/100000000000000 : ℝ)^1667 := by
    have hnat : (6557441 : ℕ)^2179*100000000000000^1667 ≤ 43030028967259^1667*12500000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6557441 12500000 43030028967259 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2080108347/10000000000 : ℝ)^2179 ≤ (12842330756639/100000000000000 : ℝ)^1667 := by
    have hnat : (2080108347 : ℕ)^2179*100000000000000^1667 ≤ 12842330756639^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080108347 10000000000 12842330756639 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167125651/312500000 : ℝ), (6557441/12500000 : ℝ), (-2080108347/10000000000 : ℝ)] ![(22063820133761/50000000000000 : ℝ), (43030028967259/100000000000000 : ℝ), (12842330756639/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167125651/312500000 : ℝ)|^2179 ≤ (22063820133761/50000000000000 : ℝ)^1667
        have hw : |(167125651/312500000 : ℝ)|=(167125651/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6557441/12500000 : ℝ)|^2179 ≤ (43030028967259/100000000000000 : ℝ)^1667
        have hw : |(6557441/12500000 : ℝ)|=(6557441/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2080108347/10000000000 : ℝ)|^2179 ≤ (12842330756639/100000000000000 : ℝ)^1667
        have hw : |(-2080108347/10000000000 : ℝ)|=(2080108347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1398_s5_3 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4312170997/10000000000 : ℝ)*x 0 + (517492381/1250000000 : ℝ)*x 1 + (4490912281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4312170997/10000000000 : ℝ)^2179 ≤ (6660809500627/20000000000000 : ℝ)^1667 := by
    have hnat : (4312170997 : ℕ)^2179*20000000000000^1667 ≤ 6660809500627^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4312170997 10000000000 6660809500627 20000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (517492381/1250000000 : ℝ)^2179 ≤ (15788032769817/50000000000000 : ℝ)^1667 := by
    have hnat : (517492381 : ℕ)^2179*50000000000000^1667 ≤ 15788032769817^1667*1250000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517492381 1250000000 15788032769817 50000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4490912281/10000000000 : ℝ)^2179 ≤ (35119886942093/100000000000000 : ℝ)^1667 := by
    have hnat : (4490912281 : ℕ)^2179*100000000000000^1667 ≤ 35119886942093^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4490912281 10000000000 35119886942093 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4312170997/10000000000 : ℝ), (517492381/1250000000 : ℝ), (4490912281/10000000000 : ℝ)] ![(6660809500627/20000000000000 : ℝ), (15788032769817/50000000000000 : ℝ), (35119886942093/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4312170997/10000000000 : ℝ)|^2179 ≤ (6660809500627/20000000000000 : ℝ)^1667
        have hw : |(4312170997/10000000000 : ℝ)|=(4312170997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(517492381/1250000000 : ℝ)|^2179 ≤ (15788032769817/50000000000000 : ℝ)^1667
        have hw : |(517492381/1250000000 : ℝ)|=(517492381/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4490912281/10000000000 : ℝ)|^2179 ≤ (35119886942093/100000000000000 : ℝ)^1667
        have hw : |(4490912281/10000000000 : ℝ)|=(4490912281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1398_s5_4 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1996547829/10000000000 : ℝ)*x 0 + (5246545117/10000000000 : ℝ)*x 1 + (270472889/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1996547829/10000000000 : ℝ)^2179 ≤ (3043046851931/25000000000000 : ℝ)^1667 := by
    have hnat : (1996547829 : ℕ)^2179*25000000000000^1667 ≤ 3043046851931^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1996547829 10000000000 3043046851931 25000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246545117/10000000000 : ℝ)^2179 ≤ (43036379799161/100000000000000 : ℝ)^1667 := by
    have hnat : (5246545117 : ℕ)^2179*100000000000000^1667 ≤ 43036379799161^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246545117 10000000000 43036379799161 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270472889/500000000 : ℝ)^2179 ≤ (349933068639/781250000000 : ℝ)^1667 := by
    have hnat : (270472889 : ℕ)^2179*781250000000^1667 ≤ 349933068639^1667*500000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270472889 500000000 349933068639 781250000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1996547829/10000000000 : ℝ), (5246545117/10000000000 : ℝ), (270472889/500000000 : ℝ)] ![(3043046851931/25000000000000 : ℝ), (43036379799161/100000000000000 : ℝ), (349933068639/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1996547829/10000000000 : ℝ)|^2179 ≤ (3043046851931/25000000000000 : ℝ)^1667
        have hw : |(-1996547829/10000000000 : ℝ)|=(1996547829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246545117/10000000000 : ℝ)|^2179 ≤ (43036379799161/100000000000000 : ℝ)^1667
        have hw : |(5246545117/10000000000 : ℝ)|=(5246545117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(270472889/500000000 : ℝ)|^2179 ≤ (349933068639/781250000000 : ℝ)^1667
        have hw : |(270472889/500000000 : ℝ)|=(270472889/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1398_s5_5 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305492379/10000000000 : ℝ)*x 0 + (-239575433/1250000000 : ℝ)*x 1 + (5409457779/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305492379/10000000000 : ℝ)^2179 ≤ (8733902384827/20000000000000 : ℝ)^1667 := by
    have hnat : (5305492379 : ℕ)^2179*20000000000000^1667 ≤ 8733902384827^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305492379 10000000000 8733902384827 20000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (239575433/1250000000 : ℝ)^2179 ≤ (11539055284669/100000000000000 : ℝ)^1667 := by
    have hnat : (239575433 : ℕ)^2179*100000000000000^1667 ≤ 11539055284669^1667*1250000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      239575433 1250000000 11539055284669 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5409457779/10000000000 : ℝ)^2179 ≤ (44791432774969/100000000000000 : ℝ)^1667 := by
    have hnat : (5409457779 : ℕ)^2179*100000000000000^1667 ≤ 44791432774969^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409457779 10000000000 44791432774969 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305492379/10000000000 : ℝ), (-239575433/1250000000 : ℝ), (5409457779/10000000000 : ℝ)] ![(8733902384827/20000000000000 : ℝ), (11539055284669/100000000000000 : ℝ), (44791432774969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305492379/10000000000 : ℝ)|^2179 ≤ (8733902384827/20000000000000 : ℝ)^1667
        have hw : |(5305492379/10000000000 : ℝ)|=(5305492379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-239575433/1250000000 : ℝ)|^2179 ≤ (11539055284669/100000000000000 : ℝ)^1667
        have hw : |(-239575433/1250000000 : ℝ)|=(239575433/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5409457779/10000000000 : ℝ)|^2179 ≤ (44791432774969/100000000000000 : ℝ)^1667
        have hw : |(5409457779/10000000000 : ℝ)|=(5409457779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1398_s5_6 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (265274619/500000000 : ℝ)*x 0 + (5409457777/10000000000 : ℝ)*x 1 + (-958301733/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265274619/500000000 : ℝ)^2179 ≤ (21834755967447/50000000000000 : ℝ)^1667 := by
    have hnat : (265274619 : ℕ)^2179*50000000000000^1667 ≤ 21834755967447^1667*500000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265274619 500000000 21834755967447 50000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5409457777/10000000000 : ℝ)^2179 ≤ (22395716376661/50000000000000 : ℝ)^1667 := by
    have hnat : (5409457777 : ℕ)^2179*50000000000000^1667 ≤ 22395716376661^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409457777 10000000000 22395716376661 50000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (958301733/5000000000 : ℝ)^2179 ≤ (11539055300409/100000000000000 : ℝ)^1667 := by
    have hnat : (958301733 : ℕ)^2179*100000000000000^1667 ≤ 11539055300409^1667*5000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      958301733 5000000000 11539055300409 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265274619/500000000 : ℝ), (5409457777/10000000000 : ℝ), (-958301733/5000000000 : ℝ)] ![(21834755967447/50000000000000 : ℝ), (22395716376661/50000000000000 : ℝ), (11539055300409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265274619/500000000 : ℝ)|^2179 ≤ (21834755967447/50000000000000 : ℝ)^1667
        have hw : |(265274619/500000000 : ℝ)|=(265274619/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5409457777/10000000000 : ℝ)|^2179 ≤ (22395716376661/50000000000000 : ℝ)^1667
        have hw : |(5409457777/10000000000 : ℝ)|=(5409457777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-958301733/5000000000 : ℝ)|^2179 ≤ (11539055300409/100000000000000 : ℝ)^1667
        have hw : |(-958301733/5000000000 : ℝ)|=(958301733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1398_s5_7 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (33689027/78125000 : ℝ)*x 0 + (4489647043/10000000000 : ℝ)*x 1 + (129412857/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33689027/78125000 : ℝ)^2179 ≤ (33304294426251/100000000000000 : ℝ)^1667 := by
    have hnat : (33689027 : ℕ)^2179*100000000000000^1667 ≤ 33304294426251^1667*78125000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33689027 78125000 33304294426251 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4489647043/10000000000 : ℝ)^2179 ≤ (17553477055543/50000000000000 : ℝ)^1667 := by
    have hnat : (4489647043 : ℕ)^2179*50000000000000^1667 ≤ 17553477055543^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4489647043 10000000000 17553477055543 50000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (129412857/312500000 : ℝ)^2179 ≤ (31588751450711/100000000000000 : ℝ)^1667 := by
    have hnat : (129412857 : ℕ)^2179*100000000000000^1667 ≤ 31588751450711^1667*312500000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129412857 312500000 31588751450711 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33689027/78125000 : ℝ), (4489647043/10000000000 : ℝ), (129412857/312500000 : ℝ)] ![(33304294426251/100000000000000 : ℝ), (17553477055543/50000000000000 : ℝ), (31588751450711/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33689027/78125000 : ℝ)|^2179 ≤ (33304294426251/100000000000000 : ℝ)^1667
        have hw : |(33689027/78125000 : ℝ)|=(33689027/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4489647043/10000000000 : ℝ)|^2179 ≤ (17553477055543/50000000000000 : ℝ)^1667
        have hw : |(4489647043/10000000000 : ℝ)|=(4489647043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(129412857/312500000 : ℝ)|^2179 ≤ (31588751450711/100000000000000 : ℝ)^1667
        have hw : |(129412857/312500000 : ℝ)|=(129412857/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1398_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156939393/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1847/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11241/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1127/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2949/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1847/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11241/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1847/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11241/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1847/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11241/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1847/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11241/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1847/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11241/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1847/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11241/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11241/100000 : ℝ) ^ (4357/1024 : ℝ) ≤ (1143395028991147/12500000000000000000 : ℝ) := by
    have hpowers : (11241/100000 : ℝ)^4357 ≤ (1143395028991147/12500000000000000000 : ℝ)^1024 := by
      have hnat : (11241 : ℕ)^4357*12500000000000000000^1024 ≤ 1143395028991147^1024*100000^4357 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11241 100000 1143395028991147 12500000000000000000 4357 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11241/100000 : ℝ)) (X := (1143395028991147/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4357 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1847/12500 : ℝ) ^ (4357/1024 : ℝ) ≤ (14639689195670539/50000000000000000000 : ℝ) := by
    have hpowers : (1847/12500 : ℝ)^4357 ≤ (14639689195670539/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1847 : ℕ)^4357*50000000000000000000^1024 ≤ 14639689195670539^1024*12500^4357 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1847 12500 14639689195670539 50000000000000000000 4357 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1847/12500 : ℝ)) (X := (14639689195670539/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4357 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251143395028991147/6250000000000000000 : ℝ) ≤ (5000214965268009/5000000000000000 : ℝ) ^ (4357/1024 : ℝ) := by
    have hpowers : (6251143395028991147/6250000000000000000 : ℝ)^1024 ≤ (5000214965268009/5000000000000000 : ℝ)^4357 := by
      have hnat : (6251143395028991147 : ℕ)^1024*5000000000000000^4357 ≤ 5000214965268009^4357*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251143395028991147 6250000000000000000 5000214965268009 5000000000000000 1024 4357 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000214965268009/5000000000000000 : ℝ)) (X := (6251143395028991147/6250000000000000000 : ℝ)) (by norm_num) 4357 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50019213269311635127/50000000000000000000 : ℝ) ≤ (2500225745888783/2500000000000000 : ℝ) ^ (4357/1024 : ℝ) := by
    have hpowers : (50019213269311635127/50000000000000000000 : ℝ)^1024 ≤ (2500225745888783/2500000000000000 : ℝ)^4357 := by
      have hnat : (50019213269311635127 : ℕ)^1024*2500000000000000^4357 ≤ 2500225745888783^4357*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50019213269311635127 50000000000000000000 2500225745888783 2500000000000000 1024 4357 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500225745888783/2500000000000000 : ℝ)) (X := (50019213269311635127/50000000000000000000 : ℝ)) (by norm_num) 4357 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25014639689195670539/25000000000000000000 : ℝ) ≤ (5000688018287123/5000000000000000 : ℝ) ^ (4357/1024 : ℝ) := by
    have hpowers : (25014639689195670539/25000000000000000000 : ℝ)^1024 ≤ (5000688018287123/5000000000000000 : ℝ)^4357 := by
      have hnat : (25014639689195670539 : ℕ)^1024*5000000000000000^4357 ≤ 5000688018287123^4357*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014639689195670539 25000000000000000000 5000688018287123 5000000000000000 1024 4357 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000688018287123/5000000000000000 : ℝ)) (X := (25014639689195670539/25000000000000000000 : ℝ)) (by norm_num) 4357 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1143395028991147/12500000000000000000 : ℝ) ≤ ((17670442313234551341/17675000000000000000 : ℝ)+2*(236526509557/176750000000000 : ℝ)*(11241/100000 : ℝ))^(4357/1024 : ℝ) := by
    rw [show (17670442313234551341/17675000000000000000 : ℝ)+2*(236526509557/176750000000000 : ℝ)*(11241/100000 : ℝ)=(5000214965268009/5000000000000000 : ℝ) by norm_num, show 1+2*(1143395028991147/12500000000000000000 : ℝ)=(6251143395028991147/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14639689195670539/50000000000000000000 : ℝ)+(1143395028991147/12500000000000000000 : ℝ) ≤ ((17670442313234551341/17675000000000000000 : ℝ)+(236526509557/176750000000000 : ℝ)*((1847/12500 : ℝ)+(11241/100000 : ℝ)))^(4357/1024 : ℝ) := by
    rw [show (17670442313234551341/17675000000000000000 : ℝ)+(236526509557/176750000000000 : ℝ)*((1847/12500 : ℝ)+(11241/100000 : ℝ))=(2500225745888783/2500000000000000 : ℝ) by norm_num, show 1+(14639689195670539/50000000000000000000 : ℝ)+(1143395028991147/12500000000000000000 : ℝ)=(50019213269311635127/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14639689195670539/50000000000000000000 : ℝ) ≤ ((17670442313234551341/17675000000000000000 : ℝ)+2*(236526509557/176750000000000 : ℝ)*(1847/12500 : ℝ))^(4357/1024 : ℝ) := by
    rw [show (17670442313234551341/17675000000000000000 : ℝ)+2*(236526509557/176750000000000 : ℝ)*(1847/12500 : ℝ)=(5000688018287123/5000000000000000 : ℝ) by norm_num, show 1+2*(14639689195670539/50000000000000000000 : ℝ)=(25014639689195670539/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17670442313234551341/17675000000000000000 : ℝ)*(X 1 0+X 2 0)+(236526509557/176750000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4357/1024 : ℝ)) (lo := (11241/100000 : ℝ)) (hi := (1847/12500 : ℝ)) (c := (17670442313234551341/17675000000000000000 : ℝ)) (alpha := (236526509557/176750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17670442313234551341/17675000000000000000 : ℝ)*(X 0 1+X 2 1)+(236526509557/176750000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4357/1024 : ℝ)) (lo := (11241/100000 : ℝ)) (hi := (1847/12500 : ℝ)) (c := (17670442313234551341/17675000000000000000 : ℝ)) (alpha := (236526509557/176750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17670442313234551341/17675000000000000000 : ℝ)*(X 0 2+X 1 2)+(236526509557/176750000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4357/1024 : ℝ)) (lo := (11241/100000 : ℝ)) (hi := (1847/12500 : ℝ)) (c := (17670442313234551341/17675000000000000000 : ℝ)) (alpha := (236526509557/176750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-998268001/5000000000 : ℝ)*X 0 0+(5410053869/10000000000 : ℝ)*X 0 1+(5245952173/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674010047/5000000000 : ℝ)*X 1 0+(-2080107343/10000000000 : ℝ)*X 1 1+(2622977149/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((167125651/312500000 : ℝ)*X 2 0+(6557441/12500000 : ℝ)*X 2 1+(-2080108347/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4312170997/10000000000 : ℝ)*X 0 0+(517492381/1250000000 : ℝ)*X 0 1+(4490912281/10000000000 : ℝ)*X 0 2+(4312170997/10000000000 : ℝ)*X 1 0+(517492381/1250000000 : ℝ)*X 1 1+(4490912281/10000000000 : ℝ)*X 1 2+(4312170997/10000000000 : ℝ)*X 2 0+(517492381/1250000000 : ℝ)*X 2 1+(4490912281/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1996547829/10000000000 : ℝ)*X 0 0+(5246545117/10000000000 : ℝ)*X 0 1+(270472889/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305492379/10000000000 : ℝ)*X 1 0+(-239575433/1250000000 : ℝ)*X 1 1+(5409457779/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((265274619/500000000 : ℝ)*X 2 0+(5409457777/10000000000 : ℝ)*X 2 1+(-958301733/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((33689027/78125000 : ℝ)*X 0 0+(4489647043/10000000000 : ℝ)*X 0 1+(129412857/312500000 : ℝ)*X 0 2+(33689027/78125000 : ℝ)*X 1 0+(4489647043/10000000000 : ℝ)*X 1 1+(129412857/312500000 : ℝ)*X 1 2+(33689027/78125000 : ℝ)*X 2 0+(4489647043/10000000000 : ℝ)*X 2 1+(129412857/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (32983848094762241797833/3535000000000000000000000000 : ℝ) := by norm_num
    linear_combination (164052131/20000000000000 : ℝ)*(base19) + (216822377/10000000000000 : ℝ)*(base23) + (243631033/50000000000000 : ℝ)*(upper3) + (3000251/1000000000000 : ℝ)*(lower4) + (447160085098967/10000000000000 : ℝ)*(major0) + (447160085098967/10000000000000 : ℝ)*(major1) + (447160085098967/10000000000000 : ℝ)*(major2) + (7617343539313/125000000000 : ℝ)*(sp0) + (3046973629952407/50000000000000 : ℝ)*(sp1) + (380871195296147/6250000000000 : ℝ)*(sp2) + (2849232844833737/100000000000000 : ℝ)*(sp3) + (7324871507/10000000000000 : ℝ)*(sp4) + (1696800837/25000000000000 : ℝ)*(sp6) + (4093191691/20000000000000 : ℝ)*(sp7) + (5564947872641/195312500000 : ℝ)*(f.failure) + (609394808016547/10000000000000 : ℝ)*(f.sum) + (2113175511389/3535000000000000000000000000 : ℝ)*base66 + (44283437447887821/25250000000000000000000000000000 : ℝ)*base67 + (206898333776387821/25250000000000000000000000000000 : ℝ)*base69 + (47435469334387821/25250000000000000000000000000000 : ℝ)*base71 + (4426088186889/3535000000000000000000000000 : ℝ)*base74 + (475804267216612179/25250000000000000000000000000000 : ℝ)*base76 + (244719771512612179/25250000000000000000000000000000 : ℝ)*base78 + (92733470753612179/25250000000000000000000000000000 : ℝ)*base80 + (20323245843301/3535000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (37481/9765625000000000000 : ℝ)*base90 + (37481/9765625000000000000 : ℝ)*base92 + (37481/9765625000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (294990704889199199633015481/110468750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3673551/800000000000 : ℝ)*(base19) + (497790717/100000000000000 : ℝ)*(base23) + (13400477/25000000000000 : ℝ)*(upper3) + (4352503/25000000000000 : ℝ)*(lower4) + (55760097/100000000000000 : ℝ)*(upper5) + (1126028568378097/25000000000000 : ℝ)*(major0) + (1126028568378097/25000000000000 : ℝ)*(major1) + (1126028568378097/25000000000000 : ℝ)*(major2) + (2394125691/25000000000000 : ℝ)*(sp1) + (5076644481/50000000000000 : ℝ)*(sp2) + (1534564490851957/25000000000000 : ℝ)*(sp4) + (1534561981927797/25000000000000 : ℝ)*(sp5) + (6138247312328149/100000000000000 : ℝ)*(sp6) + (286997049460513/10000000000000 : ℝ)*(sp7) + (286997049460513/10000000000000 : ℝ)*(f.failure) + (1534564490851957/25000000000000 : ℝ)*(f.sum) + (12092646854333/4418750000000000000000000000 : ℝ)*base65 + (21313649073495989/63125000000000000000000000000000 : ℝ)*base68 + (1006391930257245989/63125000000000000000000000000000 : ℝ)*base70 + (464966071500254011/63125000000000000000000000000000 : ℝ)*base71 + (10723170275341/8837500000000000000000000000 : ℝ)*base73 + (357410703809745989/63125000000000000000000000000000 : ℝ)*base76 + (400167415084745989/63125000000000000000000000000000 : ℝ)*base78 + (546771356696620989/63125000000000000000000000000000 : ℝ)*base80 + (1121568259037/276171875000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (7688609/1000000000000000000000 : ℝ)*base89 + (7688609/1000000000000000000000 : ℝ)*base91 + (7688609/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1398_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156939393/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1847/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11241/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1127/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2949/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1398_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1398_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156939393/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15899/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2549/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1127/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2949/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1398_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1398_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1398_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156939393/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15899/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2549/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1127/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2949/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1398_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
