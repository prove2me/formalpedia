-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1348_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:06:41.023983+00:00
-- url     : https://prove2.me/submissions/38ff3135-ac8b-41cc-aad4-9599095d4fa8

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
theorem support_rectangle_w1348_s3_0 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1018548909/5000000000 : ℝ)*x 0 + (5426410603/10000000000 : ℝ)*x 1 + (1307973823/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1018548909/5000000000 : ℝ)^1077 ≤ (1550463453771/12500000000000 : ℝ)^821 := by
    have hnat : (1018548909 : ℕ)^1077*12500000000000^821 ≤ 1550463453771^821*5000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1018548909 5000000000 1550463453771 12500000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5426410603/10000000000 : ℝ)^1077 ≤ (44846623709181/100000000000000 : ℝ)^821 := by
    have hnat : (5426410603 : ℕ)^1077*100000000000000^821 ≤ 44846623709181^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426410603 10000000000 44846623709181 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1307973823/2500000000 : ℝ)^1077 ≤ (42749668642641/100000000000000 : ℝ)^821 := by
    have hnat : (1307973823 : ℕ)^1077*100000000000000^821 ≤ 42749668642641^821*2500000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307973823 2500000000 42749668642641 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1018548909/5000000000 : ℝ), (5426410603/10000000000 : ℝ), (1307973823/2500000000 : ℝ)] ![(1550463453771/12500000000000 : ℝ), (44846623709181/100000000000000 : ℝ), (42749668642641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1018548909/5000000000 : ℝ)|^1077 ≤ (1550463453771/12500000000000 : ℝ)^821
        have hw : |(-1018548909/5000000000 : ℝ)|=(1018548909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5426410603/10000000000 : ℝ)|^1077 ≤ (44846623709181/100000000000000 : ℝ)^821
        have hw : |(5426410603/10000000000 : ℝ)|=(5426410603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1307973823/2500000000 : ℝ)|^1077 ≤ (42749668642641/100000000000000 : ℝ)^821
        have hw : |(1307973823/2500000000 : ℝ)|=(1307973823/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_s3_1 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2676235613/5000000000 : ℝ)*x 0 + (-2136494497/10000000000 : ℝ)*x 1 + (5231895219/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676235613/5000000000 : ℝ)^1077 ≤ (22023358864739/50000000000000 : ℝ)^821 := by
    have hnat : (2676235613 : ℕ)^1077*50000000000000^821 ≤ 22023358864739^821*5000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676235613 5000000000 22023358864739 50000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2136494497/10000000000 : ℝ)^1077 ≤ (13203614395369/100000000000000 : ℝ)^821 := by
    have hnat : (2136494497 : ℕ)^1077*100000000000000^821 ≤ 13203614395369^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2136494497 10000000000 13203614395369 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5231895219/10000000000 : ℝ)^1077 ≤ (5343708482521/12500000000000 : ℝ)^821 := by
    have hnat : (5231895219 : ℕ)^1077*12500000000000^821 ≤ 5343708482521^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5231895219 10000000000 5343708482521 12500000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676235613/5000000000 : ℝ), (-2136494497/10000000000 : ℝ), (5231895219/10000000000 : ℝ)] ![(22023358864739/50000000000000 : ℝ), (13203614395369/100000000000000 : ℝ), (5343708482521/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676235613/5000000000 : ℝ)|^1077 ≤ (22023358864739/50000000000000 : ℝ)^821
        have hw : |(2676235613/5000000000 : ℝ)|=(2676235613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2136494497/10000000000 : ℝ)|^1077 ≤ (13203614395369/100000000000000 : ℝ)^821
        have hw : |(-2136494497/10000000000 : ℝ)|=(2136494497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5231895219/10000000000 : ℝ)|^1077 ≤ (5343708482521/12500000000000 : ℝ)^821
        have hw : |(5231895219/10000000000 : ℝ)|=(5231895219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_s3_2 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2676235831/5000000000 : ℝ)*x 0 + (5231894481/10000000000 : ℝ)*x 1 + (-2136494893/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676235831/5000000000 : ℝ)^1077 ≤ (44046722436197/100000000000000 : ℝ)^821 := by
    have hnat : (2676235831 : ℕ)^1077*100000000000000^821 ≤ 44046722436197^821*5000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676235831 5000000000 44046722436197 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5231894481/10000000000 : ℝ)^1077 ≤ (10687414987423/25000000000000 : ℝ)^821 := by
    have hnat : (5231894481 : ℕ)^1077*25000000000000^821 ≤ 10687414987423^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5231894481 10000000000 10687414987423 25000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2136494893/10000000000 : ℝ)^1077 ≤ (13203617605767/100000000000000 : ℝ)^821 := by
    have hnat : (2136494893 : ℕ)^1077*100000000000000^821 ≤ 13203617605767^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2136494893 10000000000 13203617605767 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676235831/5000000000 : ℝ), (5231894481/10000000000 : ℝ), (-2136494893/10000000000 : ℝ)] ![(44046722436197/100000000000000 : ℝ), (10687414987423/25000000000000 : ℝ), (13203617605767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676235831/5000000000 : ℝ)|^1077 ≤ (44046722436197/100000000000000 : ℝ)^821
        have hw : |(2676235831/5000000000 : ℝ)|=(2676235831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5231894481/10000000000 : ℝ)|^1077 ≤ (10687414987423/25000000000000 : ℝ)^821
        have hw : |(5231894481/10000000000 : ℝ)|=(5231894481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2136494893/10000000000 : ℝ)|^1077 ≤ (13203617605767/100000000000000 : ℝ)^821
        have hw : |(-2136494893/10000000000 : ℝ)|=(2136494893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_s3_3 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4324024919/10000000000 : ℝ)*x 0 + (4124340479/10000000000 : ℝ)*x 1 + (4532687959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4324024919/10000000000 : ℝ)^1077 ≤ (3329298341759/10000000000000 : ℝ)^821 := by
    have hnat : (4324024919 : ℕ)^1077*10000000000000^821 ≤ 3329298341759^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4324024919 10000000000 3329298341759 10000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4124340479/10000000000 : ℝ)^1077 ≤ (31290775829787/100000000000000 : ℝ)^821 := by
    have hnat : (4124340479 : ℕ)^1077*100000000000000^821 ≤ 31290775829787^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4124340479 10000000000 31290775829787 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4532687959/10000000000 : ℝ)^1077 ≤ (35416240739391/100000000000000 : ℝ)^821 := by
    have hnat : (4532687959 : ℕ)^1077*100000000000000^821 ≤ 35416240739391^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4532687959 10000000000 35416240739391 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4324024919/10000000000 : ℝ), (4124340479/10000000000 : ℝ), (4532687959/10000000000 : ℝ)] ![(3329298341759/10000000000000 : ℝ), (31290775829787/100000000000000 : ℝ), (35416240739391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4324024919/10000000000 : ℝ)|^1077 ≤ (3329298341759/10000000000000 : ℝ)^821
        have hw : |(4324024919/10000000000 : ℝ)|=(4324024919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4124340479/10000000000 : ℝ)|^1077 ≤ (31290775829787/100000000000000 : ℝ)^821
        have hw : |(4124340479/10000000000 : ℝ)|=(4124340479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4532687959/10000000000 : ℝ)|^1077 ≤ (35416240739391/100000000000000 : ℝ)^821
        have hw : |(4532687959/10000000000 : ℝ)|=(4532687959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_s3_4 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2037116229/10000000000 : ℝ)*x 0 + (209308117/400000000 : ℝ)*x 1 + (1356399627/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2037116229/10000000000 : ℝ)^1077 ≤ (6201927344341/50000000000000 : ℝ)^821 := by
    have hnat : (2037116229 : ℕ)^1077*50000000000000^821 ≤ 6201927344341^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2037116229 10000000000 6201927344341 50000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209308117/400000000 : ℝ)^1077 ≤ (42758325709327/100000000000000 : ℝ)^821 := by
    have hnat : (209308117 : ℕ)^1077*100000000000000^821 ≤ 42758325709327^821*400000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209308117 400000000 42758325709327 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1356399627/2500000000 : ℝ)^1077 ≤ (22418909790579/50000000000000 : ℝ)^821 := by
    have hnat : (1356399627 : ℕ)^1077*50000000000000^821 ≤ 22418909790579^821*2500000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356399627 2500000000 22418909790579 50000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2037116229/10000000000 : ℝ), (209308117/400000000 : ℝ), (1356399627/2500000000 : ℝ)] ![(6201927344341/50000000000000 : ℝ), (42758325709327/100000000000000 : ℝ), (22418909790579/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2037116229/10000000000 : ℝ)|^1077 ≤ (6201927344341/50000000000000 : ℝ)^821
        have hw : |(-2037116229/10000000000 : ℝ)|=(2037116229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(209308117/400000000 : ℝ)|^1077 ≤ (42758325709327/100000000000000 : ℝ)^821
        have hw : |(209308117/400000000 : ℝ)|=(209308117/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1356399627/2500000000 : ℝ)|^1077 ≤ (22418909790579/50000000000000 : ℝ)^821
        have hw : |(1356399627/2500000000 : ℝ)|=(1356399627/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_s3_5 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5302332489/10000000000 : ℝ)*x 0 + (-194279101/1000000000 : ℝ)*x 1 + (2712799437/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302332489/10000000000 : ℝ)^1077 ≤ (21753125448097/50000000000000 : ℝ)^821 := by
    have hnat : (5302332489 : ℕ)^1077*50000000000000^821 ≤ 21753125448097^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302332489 10000000000 21753125448097 50000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (194279101/1000000000 : ℝ)^1077 ≤ (11655925544321/100000000000000 : ℝ)^821 := by
    have hnat : (194279101 : ℕ)^1077*100000000000000^821 ≤ 11655925544321^821*1000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      194279101 1000000000 11655925544321 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2712799437/5000000000 : ℝ)^1077 ≤ (11209455887241/25000000000000 : ℝ)^821 := by
    have hnat : (2712799437 : ℕ)^1077*25000000000000^821 ≤ 11209455887241^821*5000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712799437 5000000000 11209455887241 25000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302332489/10000000000 : ℝ), (-194279101/1000000000 : ℝ), (2712799437/5000000000 : ℝ)] ![(21753125448097/50000000000000 : ℝ), (11655925544321/100000000000000 : ℝ), (11209455887241/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302332489/10000000000 : ℝ)|^1077 ≤ (21753125448097/50000000000000 : ℝ)^821
        have hw : |(5302332489/10000000000 : ℝ)|=(5302332489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-194279101/1000000000 : ℝ)|^1077 ≤ (11655925544321/100000000000000 : ℝ)^821
        have hw : |(-194279101/1000000000 : ℝ)|=(194279101/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2712799437/5000000000 : ℝ)|^1077 ≤ (11209455887241/25000000000000 : ℝ)^821
        have hw : |(2712799437/5000000000 : ℝ)|=(2712799437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_s3_6 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (331395841/625000000 : ℝ)*x 0 + (5425598237/10000000000 : ℝ)*x 1 + (-485697641/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (331395841/625000000 : ℝ)^1077 ≤ (10876565326147/25000000000000 : ℝ)^821 := by
    have hnat : (331395841 : ℕ)^1077*25000000000000^821 ≤ 10876565326147^821*625000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331395841 625000000 10876565326147 25000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5425598237/10000000000 : ℝ)^1077 ≤ (44837816643247/100000000000000 : ℝ)^821 := by
    have hnat : (5425598237 : ℕ)^1077*100000000000000^821 ≤ 44837816643247^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425598237 10000000000 44837816643247 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (485697641/2500000000 : ℝ)^1077 ≤ (11655922034151/100000000000000 : ℝ)^821 := by
    have hnat : (485697641 : ℕ)^1077*100000000000000^821 ≤ 11655922034151^821*2500000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      485697641 2500000000 11655922034151 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(331395841/625000000 : ℝ), (5425598237/10000000000 : ℝ), (-485697641/2500000000 : ℝ)] ![(10876565326147/25000000000000 : ℝ), (44837816643247/100000000000000 : ℝ), (11655922034151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(331395841/625000000 : ℝ)|^1077 ≤ (10876565326147/25000000000000 : ℝ)^821
        have hw : |(331395841/625000000 : ℝ)|=(331395841/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5425598237/10000000000 : ℝ)|^1077 ≤ (44837816643247/100000000000000 : ℝ)^821
        have hw : |(5425598237/10000000000 : ℝ)|=(5425598237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-485697641/2500000000 : ℝ)|^1077 ≤ (11655922034151/100000000000000 : ℝ)^821
        have hw : |(-485697641/2500000000 : ℝ)|=(485697641/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_s3_7 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2162032329/5000000000 : ℝ)*x 0 + (1132748113/2500000000 : ℝ)*x 1 + (41260461/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2162032329/5000000000 : ℝ)^1077 ≤ (16646692398287/50000000000000 : ℝ)^821 := by
    have hnat : (2162032329 : ℕ)^1077*50000000000000^821 ≤ 16646692398287^821*5000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2162032329 5000000000 16646692398287 50000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1132748113/2500000000 : ℝ)^1077 ≤ (8849715748383/25000000000000 : ℝ)^821 := by
    have hnat : (1132748113 : ℕ)^1077*25000000000000^821 ≤ 8849715748383^821*2500000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1132748113 2500000000 8849715748383 25000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41260461/100000000 : ℝ)^1077 ≤ (15653876101203/50000000000000 : ℝ)^821 := by
    have hnat : (41260461 : ℕ)^1077*50000000000000^821 ≤ 15653876101203^821*100000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41260461 100000000 15653876101203 50000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2162032329/5000000000 : ℝ), (1132748113/2500000000 : ℝ), (41260461/100000000 : ℝ)] ![(16646692398287/50000000000000 : ℝ), (8849715748383/25000000000000 : ℝ), (15653876101203/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2162032329/5000000000 : ℝ)|^1077 ≤ (16646692398287/50000000000000 : ℝ)^821
        have hw : |(2162032329/5000000000 : ℝ)|=(2162032329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1132748113/2500000000 : ℝ)|^1077 ≤ (8849715748383/25000000000000 : ℝ)^821
        have hw : |(1132748113/2500000000 : ℝ)|=(1132748113/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(41260461/100000000 : ℝ)|^1077 ≤ (15653876101203/50000000000000 : ℝ)^821
        have hw : |(41260461/100000000 : ℝ)|=(41260461/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1348_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154965091/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16081/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9891/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10887/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3751/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16081/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9891/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16081/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9891/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16081/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9891/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16081/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9891/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16081/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9891/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16081/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9891/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9891/100000 : ℝ) ^ (4307/1024 : ℝ) ≤ (5941900037233539/100000000000000000000 : ℝ) := by
    have hpowers : (9891/100000 : ℝ)^4307 ≤ (5941900037233539/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9891 : ℕ)^4307*100000000000000000000^1024 ≤ 5941900037233539^1024*100000^4307 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9891 100000 5941900037233539 100000000000000000000 4307 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9891/100000 : ℝ)) (X := (5941900037233539/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4307 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16081/100000 : ℝ) ^ (4307/1024 : ℝ) ≤ (45889073743697079/100000000000000000000 : ℝ) := by
    have hpowers : (16081/100000 : ℝ)^4307 ≤ (45889073743697079/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16081 : ℕ)^4307*100000000000000000000^1024 ≤ 45889073743697079^1024*100000^4307 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16081 100000 45889073743697079 100000000000000000000 4307 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16081/100000 : ℝ)) (X := (45889073743697079/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4307 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005941900037233539/50000000000000000000 : ℝ) ≤ (5000141263758487/5000000000000000 : ℝ) ^ (4307/1024 : ℝ) := by
    have hpowers : (50005941900037233539/50000000000000000000 : ℝ)^1024 ≤ (5000141263758487/5000000000000000 : ℝ)^4307 := by
      have hnat : (50005941900037233539 : ℕ)^1024*5000000000000000^4307 ≤ 5000141263758487^4307*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005941900037233539 50000000000000000000 5000141263758487 5000000000000000 1024 4307 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000141263758487/5000000000000000 : ℝ)) (X := (50005941900037233539/50000000000000000000 : ℝ)) (by norm_num) 4307 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025915486890465309/50000000000000000000 : ℝ) ≤ (10001232050984803/10000000000000000 : ℝ) ^ (4307/1024 : ℝ) := by
    have hpowers : (50025915486890465309/50000000000000000000 : ℝ)^1024 ≤ (10001232050984803/10000000000000000 : ℝ)^4307 := by
      have hnat : (50025915486890465309 : ℕ)^1024*10000000000000000^4307 ≤ 10001232050984803^4307*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025915486890465309 50000000000000000000 10001232050984803 10000000000000000 1024 4307 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001232050984803/10000000000000000 : ℝ)) (X := (50025915486890465309/50000000000000000000 : ℝ)) (by norm_num) 4307 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50045889073743697079/50000000000000000000 : ℝ) ≤ (1250272696806579/1250000000000000 : ℝ) ^ (4307/1024 : ℝ) := by
    have hpowers : (50045889073743697079/50000000000000000000 : ℝ)^1024 ≤ (1250272696806579/1250000000000000 : ℝ)^4307 := by
      have hnat : (50045889073743697079 : ℕ)^1024*1250000000000000^4307 ≤ 1250272696806579^4307*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50045889073743697079 50000000000000000000 1250272696806579 1250000000000000 1024 4307 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250272696806579/1250000000000000 : ℝ)) (X := (50045889073743697079/50000000000000000000 : ℝ)) (by norm_num) 4307 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5941900037233539/100000000000000000000 : ℝ) ≤ ((30941482686044737891/30950000000000000000 : ℝ)+2*(949523467829/619000000000000 : ℝ)*(9891/100000 : ℝ))^(4307/1024 : ℝ) := by
    rw [show (30941482686044737891/30950000000000000000 : ℝ)+2*(949523467829/619000000000000 : ℝ)*(9891/100000 : ℝ)=(5000141263758487/5000000000000000 : ℝ) by norm_num, show 1+2*(5941900037233539/100000000000000000000 : ℝ)=(50005941900037233539/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(45889073743697079/100000000000000000000 : ℝ)+(5941900037233539/100000000000000000000 : ℝ) ≤ ((30941482686044737891/30950000000000000000 : ℝ)+(949523467829/619000000000000 : ℝ)*((16081/100000 : ℝ)+(9891/100000 : ℝ)))^(4307/1024 : ℝ) := by
    rw [show (30941482686044737891/30950000000000000000 : ℝ)+(949523467829/619000000000000 : ℝ)*((16081/100000 : ℝ)+(9891/100000 : ℝ))=(10001232050984803/10000000000000000 : ℝ) by norm_num, show 1+(45889073743697079/100000000000000000000 : ℝ)+(5941900037233539/100000000000000000000 : ℝ)=(50025915486890465309/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(45889073743697079/100000000000000000000 : ℝ) ≤ ((30941482686044737891/30950000000000000000 : ℝ)+2*(949523467829/619000000000000 : ℝ)*(16081/100000 : ℝ))^(4307/1024 : ℝ) := by
    rw [show (30941482686044737891/30950000000000000000 : ℝ)+2*(949523467829/619000000000000 : ℝ)*(16081/100000 : ℝ)=(1250272696806579/1250000000000000 : ℝ) by norm_num, show 1+2*(45889073743697079/100000000000000000000 : ℝ)=(50045889073743697079/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (30941482686044737891/30950000000000000000 : ℝ)*(X 1 0+X 2 0)+(949523467829/619000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4307/1024 : ℝ)) (lo := (9891/100000 : ℝ)) (hi := (16081/100000 : ℝ)) (c := (30941482686044737891/30950000000000000000 : ℝ)) (alpha := (949523467829/619000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (30941482686044737891/30950000000000000000 : ℝ)*(X 0 1+X 2 1)+(949523467829/619000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4307/1024 : ℝ)) (lo := (9891/100000 : ℝ)) (hi := (16081/100000 : ℝ)) (c := (30941482686044737891/30950000000000000000 : ℝ)) (alpha := (949523467829/619000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (30941482686044737891/30950000000000000000 : ℝ)*(X 0 2+X 1 2)+(949523467829/619000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4307/1024 : ℝ)) (lo := (9891/100000 : ℝ)) (hi := (16081/100000 : ℝ)) (c := (30941482686044737891/30950000000000000000 : ℝ)) (alpha := (949523467829/619000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1018548909/5000000000 : ℝ)*X 0 0+(5426410603/10000000000 : ℝ)*X 0 1+(1307973823/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676235613/5000000000 : ℝ)*X 1 0+(-2136494497/10000000000 : ℝ)*X 1 1+(5231895219/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676235831/5000000000 : ℝ)*X 2 0+(5231894481/10000000000 : ℝ)*X 2 1+(-2136494893/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4324024919/10000000000 : ℝ)*X 0 0+(4124340479/10000000000 : ℝ)*X 0 1+(4532687959/10000000000 : ℝ)*X 0 2+(4324024919/10000000000 : ℝ)*X 1 0+(4124340479/10000000000 : ℝ)*X 1 1+(4532687959/10000000000 : ℝ)*X 1 2+(4324024919/10000000000 : ℝ)*X 2 0+(4124340479/10000000000 : ℝ)*X 2 1+(4532687959/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2037116229/10000000000 : ℝ)*X 0 0+(209308117/400000000 : ℝ)*X 0 1+(1356399627/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5302332489/10000000000 : ℝ)*X 1 0+(-194279101/1000000000 : ℝ)*X 1 1+(2712799437/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((331395841/625000000 : ℝ)*X 2 0+(5425598237/10000000000 : ℝ)*X 2 1+(-485697641/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2162032329/5000000000 : ℝ)*X 0 0+(1132748113/2500000000 : ℝ)*X 0 1+(41260461/100000000 : ℝ)*X 0 2+(2162032329/5000000000 : ℝ)*X 1 0+(1132748113/2500000000 : ℝ)*X 1 1+(41260461/100000000 : ℝ)*X 1 2+(2162032329/5000000000 : ℝ)*X 2 0+(1132748113/2500000000 : ℝ)*X 2 1+(41260461/100000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3186776808373486722666149787/386875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1216009741/50000000000000 : ℝ)*(base19) + (21660487/781250000000 : ℝ)*(base23) + (64541369/10000000000000 : ℝ)*(upper3) + (41885443/100000000000000 : ℝ)*(upper4) + (119450793/50000000000000 : ℝ)*(upper5) + (1897493042494981/50000000000000 : ℝ)*(major0) + (1897493042494981/50000000000000 : ℝ)*(major1) + (1897493042494981/50000000000000 : ℝ)*(major2) + (5141017621481173/100000000000000 : ℝ)*(sp0) + (5141039797678511/100000000000000 : ℝ)*(sp1) + (5141039457155657/100000000000000 : ℝ)*(sp2) + (2448908745244603/100000000000000 : ℝ)*(sp3) + (24608216819/100000000000000 : ℝ)*(sp4) + (4184092623/20000000000000 : ℝ)*(sp7) + (1224464832853859/50000000000000 : ℝ)*(f.failure) + (642630278712249/12500000000000 : ℝ)*(f.sum) + (54717161049299/15475000000000000000000000000 : ℝ)*base65 + (9326715800367975071/1547500000000000000000000000000000 : ℝ)*base67 + (28132532154252975071/1547500000000000000000000000000000 : ℝ)*base69 + (8653227393772975071/1547500000000000000000000000000000 : ℝ)*base71 + (17823806237501/15475000000000000000000000000 : ℝ)*base74 + (21621123614055475071/1547500000000000000000000000000000 : ℝ)*base75 + (15633276517992975071/1547500000000000000000000000000000 : ℝ)*base77 + (9659029549974524929/1547500000000000000000000000000000 : ℝ)*base80 + (79839874715149/15475000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (50363831/5000000000000000000000 : ℝ)*base90 + (50363831/5000000000000000000000 : ℝ)*base92 + (50363831/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11569391009041452220977/1934375000000000000000000000 : ℝ) := by norm_num
    linear_combination (1191754543/100000000000000 : ℝ)*(base19) + (2766173783/100000000000000 : ℝ)*(base23) + (295244953/100000000000000 : ℝ)*(upper3) + (105399863/50000000000000 : ℝ)*(lower4) + (245320193/100000000000000 : ℝ)*(upper5) + (1913404890323143/50000000000000 : ℝ)*(major0) + (1913404890323143/50000000000000 : ℝ)*(major1) + (1913404890323143/50000000000000 : ℝ)*(major2) + (22697114439/100000000000000 : ℝ)*(sp1) + (47170171201/100000000000000 : ℝ)*(sp2) + (5184153654553479/100000000000000 : ℝ)*(sp4) + (5184129765684497/100000000000000 : ℝ)*(sp5) + (2592051859104247/50000000000000 : ℝ)*(sp6) + (15434160671089/625000000000 : ℝ)*(sp7) + (15434160671089/625000000000 : ℝ)*(f.failure) + (5184153654553479/100000000000000 : ℝ)*(f.sum) + (10989313975557/3868750000000000000000000000 : ℝ)*base66 + (3840558578808838587/1547500000000000000000000000000000 : ℝ)*base68 + (9325245243783661413/1547500000000000000000000000000000 : ℝ)*base69 + (7732215620878838587/1547500000000000000000000000000000 : ℝ)*base72 + (13190554171889/7737500000000000000000000000 : ℝ)*base74 + (259682210598838587/1547500000000000000000000000000000 : ℝ)*base76 + (14834627021868661413/1547500000000000000000000000000000 : ℝ)*base77 + (3820122462701161413/1547500000000000000000000000000000 : ℝ)*base79 + (17883906889161/7737500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (795901/62500000000000000000 : ℝ)*base90 + (795901/62500000000000000000 : ℝ)*base92 + (795901/62500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1348_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154965091/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16081/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9891/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10887/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3751/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1348_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1348_s4_0 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2038512981/10000000000 : ℝ)*x 0 + (5414852977/10000000000 : ℝ)*x 1 + (52425233/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2038512981/10000000000 : ℝ)^1077 ≤ (12415012502869/100000000000000 : ℝ)^821 := by
    have hnat : (2038512981 : ℕ)^1077*100000000000000^821 ≤ 12415012502869^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2038512981 10000000000 12415012502869 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414852977/10000000000 : ℝ)^1077 ≤ (5590170407147/12500000000000 : ℝ)^821 := by
    have hnat : (5414852977 : ℕ)^1077*12500000000000^821 ≤ 5590170407147^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414852977 10000000000 5590170407147 12500000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (52425233/100000000 : ℝ)^1077 ≤ (21431812110137/50000000000000 : ℝ)^821 := by
    have hnat : (52425233 : ℕ)^1077*50000000000000^821 ≤ 21431812110137^821*100000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52425233 100000000 21431812110137 50000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2038512981/10000000000 : ℝ), (5414852977/10000000000 : ℝ), (52425233/100000000 : ℝ)] ![(12415012502869/100000000000000 : ℝ), (5590170407147/12500000000000 : ℝ), (21431812110137/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2038512981/10000000000 : ℝ)|^1077 ≤ (12415012502869/100000000000000 : ℝ)^821
        have hw : |(-2038512981/10000000000 : ℝ)|=(2038512981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414852977/10000000000 : ℝ)|^1077 ≤ (5590170407147/12500000000000 : ℝ)^821
        have hw : |(5414852977/10000000000 : ℝ)|=(5414852977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(52425233/100000000 : ℝ)|^1077 ≤ (21431812110137/50000000000000 : ℝ)^821
        have hw : |(52425233/100000000 : ℝ)|=(52425233/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_s4_1 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5349522083/10000000000 : ℝ)*x 0 + (-2126357461/10000000000 : ℝ)*x 1 + (5242523143/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349522083/10000000000 : ℝ)^1077 ≤ (44014883798227/100000000000000 : ℝ)^821 := by
    have hnat : (5349522083 : ℕ)^1077*100000000000000^821 ≤ 44014883798227^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349522083 10000000000 44014883798227 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2126357461/10000000000 : ℝ)^1077 ≤ (1312149365489/10000000000000 : ℝ)^821 := by
    have hnat : (2126357461 : ℕ)^1077*10000000000000^821 ≤ 1312149365489^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126357461 10000000000 1312149365489 10000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242523143/10000000000 : ℝ)^1077 ≤ (10715905634089/25000000000000 : ℝ)^821 := by
    have hnat : (5242523143 : ℕ)^1077*25000000000000^821 ≤ 10715905634089^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242523143 10000000000 10715905634089 25000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349522083/10000000000 : ℝ), (-2126357461/10000000000 : ℝ), (5242523143/10000000000 : ℝ)] ![(44014883798227/100000000000000 : ℝ), (1312149365489/10000000000000 : ℝ), (10715905634089/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349522083/10000000000 : ℝ)|^1077 ≤ (44014883798227/100000000000000 : ℝ)^821
        have hw : |(5349522083/10000000000 : ℝ)|=(5349522083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2126357461/10000000000 : ℝ)|^1077 ≤ (1312149365489/10000000000000 : ℝ)^821
        have hw : |(-2126357461/10000000000 : ℝ)|=(2126357461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242523143/10000000000 : ℝ)|^1077 ≤ (10715905634089/25000000000000 : ℝ)^821
        have hw : |(5242523143/10000000000 : ℝ)|=(5242523143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_s4_2 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2139809/4000000 : ℝ)*x 0 + (2621261497/5000000000 : ℝ)*x 1 + (-2126357101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2139809/4000000 : ℝ)^1077 ≤ (44014888299063/100000000000000 : ℝ)^821 := by
    have hnat : (2139809 : ℕ)^1077*100000000000000^821 ≤ 44014888299063^821*4000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2139809 4000000 44014888299063 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621261497/5000000000 : ℝ)^1077 ≤ (10715905234561/25000000000000 : ℝ)^821 := by
    have hnat : (2621261497 : ℕ)^1077*25000000000000^821 ≤ 10715905234561^821*5000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621261497 5000000000 10715905234561 25000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2126357101/10000000000 : ℝ)^1077 ≤ (205023292823/1562500000000 : ℝ)^821 := by
    have hnat : (2126357101 : ℕ)^1077*1562500000000^821 ≤ 205023292823^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126357101 10000000000 205023292823 1562500000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2139809/4000000 : ℝ), (2621261497/5000000000 : ℝ), (-2126357101/10000000000 : ℝ)] ![(44014888299063/100000000000000 : ℝ), (10715905234561/25000000000000 : ℝ), (205023292823/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2139809/4000000 : ℝ)|^1077 ≤ (44014888299063/100000000000000 : ℝ)^821
        have hw : |(2139809/4000000 : ℝ)|=(2139809/4000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621261497/5000000000 : ℝ)|^1077 ≤ (10715905234561/25000000000000 : ℝ)^821
        have hw : |(2621261497/5000000000 : ℝ)|=(2621261497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2126357101/10000000000 : ℝ)|^1077 ≤ (205023292823/1562500000000 : ℝ)^821
        have hw : |(-2126357101/10000000000 : ℝ)|=(2126357101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_s4_3 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4324883361/10000000000 : ℝ)*x 0 + (1036880487/2500000000 : ℝ)*x 1 + (4509294471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4324883361/10000000000 : ℝ)^1077 ≤ (16650827131783/50000000000000 : ℝ)^821 := by
    have hnat : (4324883361 : ℕ)^1077*50000000000000^821 ≤ 16650827131783^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4324883361 10000000000 16650827131783 50000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036880487/2500000000 : ℝ)^1077 ≤ (31521692473861/100000000000000 : ℝ)^821 := by
    have hnat : (1036880487 : ℕ)^1077*100000000000000^821 ≤ 31521692473861^821*2500000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036880487 2500000000 31521692473861 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4509294471/10000000000 : ℝ)^1077 ≤ (8794163309871/25000000000000 : ℝ)^821 := by
    have hnat : (4509294471 : ℕ)^1077*25000000000000^821 ≤ 8794163309871^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4509294471 10000000000 8794163309871 25000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4324883361/10000000000 : ℝ), (1036880487/2500000000 : ℝ), (4509294471/10000000000 : ℝ)] ![(16650827131783/50000000000000 : ℝ), (31521692473861/100000000000000 : ℝ), (8794163309871/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4324883361/10000000000 : ℝ)|^1077 ≤ (16650827131783/50000000000000 : ℝ)^821
        have hw : |(4324883361/10000000000 : ℝ)|=(4324883361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036880487/2500000000 : ℝ)|^1077 ≤ (31521692473861/100000000000000 : ℝ)^821
        have hw : |(1036880487/2500000000 : ℝ)|=(1036880487/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4509294471/10000000000 : ℝ)|^1077 ≤ (8794163309871/25000000000000 : ℝ)^821
        have hw : |(4509294471/10000000000 : ℝ)|=(4509294471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_s4_4 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1019263217/5000000000 : ℝ)*x 0 + (2621578869/5000000000 : ℝ)*x 1 + (2707107481/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1019263217/5000000000 : ℝ)^1077 ≤ (12415119982413/100000000000000 : ℝ)^821 := by
    have hnat : (1019263217 : ℕ)^1077*100000000000000^821 ≤ 12415119982413^821*5000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1019263217 5000000000 12415119982413 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621578869/5000000000 : ℝ)^1077 ≤ (42870429068557/100000000000000 : ℝ)^821 := by
    have hnat : (2621578869 : ℕ)^1077*100000000000000^821 ≤ 42870429068557^821*5000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621578869 5000000000 42870429068557 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707107481/5000000000 : ℝ)^1077 ≤ (4471445093739/10000000000000 : ℝ)^821 := by
    have hnat : (2707107481 : ℕ)^1077*10000000000000^821 ≤ 4471445093739^821*5000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707107481 5000000000 4471445093739 10000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1019263217/5000000000 : ℝ), (2621578869/5000000000 : ℝ), (2707107481/5000000000 : ℝ)] ![(12415119982413/100000000000000 : ℝ), (42870429068557/100000000000000 : ℝ), (4471445093739/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1019263217/5000000000 : ℝ)|^1077 ≤ (12415119982413/100000000000000 : ℝ)^821
        have hw : |(-1019263217/5000000000 : ℝ)|=(1019263217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621578869/5000000000 : ℝ)|^1077 ≤ (42870429068557/100000000000000 : ℝ)^821
        have hw : |(2621578869/5000000000 : ℝ)|=(2621578869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707107481/5000000000 : ℝ)|^1077 ≤ (4471445093739/10000000000000 : ℝ)^821
        have hw : |(2707107481/5000000000 : ℝ)|=(2707107481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_s4_5 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1326275753/2500000000 : ℝ)*x 0 + (-488666481/2500000000 : ℝ)*x 1 + (2707107523/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326275753/2500000000 : ℝ)^1077 ≤ (5442009263237/12500000000000 : ℝ)^821 := by
    have hnat : (1326275753 : ℕ)^1077*12500000000000^821 ≤ 5442009263237^821*2500000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326275753 2500000000 5442009263237 12500000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (488666481/2500000000 : ℝ)^1077 ≤ (5874737017541/50000000000000 : ℝ)^821 := by
    have hnat : (488666481 : ℕ)^1077*50000000000000^821 ≤ 5874737017541^821*2500000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      488666481 2500000000 5874737017541 50000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707107523/5000000000 : ℝ)^1077 ≤ (22357225923719/50000000000000 : ℝ)^821 := by
    have hnat : (2707107523 : ℕ)^1077*50000000000000^821 ≤ 22357225923719^821*5000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707107523 5000000000 22357225923719 50000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326275753/2500000000 : ℝ), (-488666481/2500000000 : ℝ), (2707107523/5000000000 : ℝ)] ![(5442009263237/12500000000000 : ℝ), (5874737017541/50000000000000 : ℝ), (22357225923719/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326275753/2500000000 : ℝ)|^1077 ≤ (5442009263237/12500000000000 : ℝ)^821
        have hw : |(1326275753/2500000000 : ℝ)|=(1326275753/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-488666481/2500000000 : ℝ)|^1077 ≤ (5874737017541/50000000000000 : ℝ)^821
        have hw : |(-488666481/2500000000 : ℝ)|=(488666481/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707107523/5000000000 : ℝ)|^1077 ≤ (22357225923719/50000000000000 : ℝ)^821
        have hw : |(2707107523/5000000000 : ℝ)|=(2707107523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_s4_6 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2652551627/5000000000 : ℝ)*x 0 + (5414214921/10000000000 : ℝ)*x 1 + (-488666441/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652551627/5000000000 : ℝ)^1077 ≤ (43536076711109/100000000000000 : ℝ)^821 := by
    have hnat : (2652551627 : ℕ)^1077*100000000000000^821 ≤ 43536076711109^821*5000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652551627 5000000000 43536076711109 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414214921/10000000000 : ℝ)^1077 ≤ (111786126233/250000000000 : ℝ)^821 := by
    have hnat : (5414214921 : ℕ)^1077*250000000000^821 ≤ 111786126233^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414214921 10000000000 111786126233 250000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (488666441/2500000000 : ℝ)^1077 ≤ (11749472773433/100000000000000 : ℝ)^821 := by
    have hnat : (488666441 : ℕ)^1077*100000000000000^821 ≤ 11749472773433^821*2500000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      488666441 2500000000 11749472773433 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652551627/5000000000 : ℝ), (5414214921/10000000000 : ℝ), (-488666441/2500000000 : ℝ)] ![(43536076711109/100000000000000 : ℝ), (111786126233/250000000000 : ℝ), (11749472773433/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652551627/5000000000 : ℝ)|^1077 ≤ (43536076711109/100000000000000 : ℝ)^821
        have hw : |(2652551627/5000000000 : ℝ)|=(2652551627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414214921/10000000000 : ℝ)|^1077 ≤ (111786126233/250000000000 : ℝ)^821
        have hw : |(5414214921/10000000000 : ℝ)|=(5414214921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-488666441/2500000000 : ℝ)|^1077 ≤ (11749472773433/100000000000000 : ℝ)^821
        have hw : |(-488666441/2500000000 : ℝ)|=(488666441/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_s4_7 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (540613829/1250000000 : ℝ)*x 0 + (2253981299/5000000000 : ℝ)*x 1 + (3319089/8000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540613829/1250000000 : ℝ)^1077 ≤ (4162741215993/12500000000000 : ℝ)^821 := by
    have hnat : (540613829 : ℕ)^1077*12500000000000^821 ≤ 4162741215993^821*1250000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540613829 1250000000 4162741215993 12500000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2253981299/5000000000 : ℝ)^1077 ≤ (7032604864909/20000000000000 : ℝ)^821 := by
    have hnat : (2253981299 : ℕ)^1077*20000000000000^821 ≤ 7032604864909^821*5000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253981299 5000000000 7032604864909 20000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3319089/8000000 : ℝ)^1077 ≤ (31535045932353/100000000000000 : ℝ)^821 := by
    have hnat : (3319089 : ℕ)^1077*100000000000000^821 ≤ 31535045932353^821*8000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3319089 8000000 31535045932353 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(540613829/1250000000 : ℝ), (2253981299/5000000000 : ℝ), (3319089/8000000 : ℝ)] ![(4162741215993/12500000000000 : ℝ), (7032604864909/20000000000000 : ℝ), (31535045932353/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(540613829/1250000000 : ℝ)|^1077 ≤ (4162741215993/12500000000000 : ℝ)^821
        have hw : |(540613829/1250000000 : ℝ)|=(540613829/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2253981299/5000000000 : ℝ)|^1077 ≤ (7032604864909/20000000000000 : ℝ)^821
        have hw : |(2253981299/5000000000 : ℝ)|=(2253981299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3319089/8000000 : ℝ)|^1077 ≤ (31535045932353/100000000000000 : ℝ)^821
        have hw : |(3319089/8000000 : ℝ)|=(3319089/8000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1348_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154965091/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3751/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10887/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5557/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7381/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3751/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10887/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3751/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10887/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3751/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10887/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3751/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10887/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3751/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10887/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3751/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10887/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10887/100000 : ℝ) ^ (4307/1024 : ℝ) ≤ (8895765305544889/100000000000000000000 : ℝ) := by
    have hpowers : (10887/100000 : ℝ)^4307 ≤ (8895765305544889/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10887 : ℕ)^4307*100000000000000000000^1024 ≤ 8895765305544889^1024*100000^4307 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10887 100000 8895765305544889 100000000000000000000 4307 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10887/100000 : ℝ)) (X := (8895765305544889/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4307 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3751/25000 : ℝ) ^ (4307/1024 : ℝ) ≤ (34283237251734551/100000000000000000000 : ℝ) := by
    have hpowers : (3751/25000 : ℝ)^4307 ≤ (34283237251734551/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3751 : ℕ)^4307*100000000000000000000^1024 ≤ 34283237251734551^1024*25000^4307 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3751 25000 34283237251734551 100000000000000000000 4307 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3751/25000 : ℝ)) (X := (34283237251734551/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4307 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008895765305544889/50000000000000000000 : ℝ) ≤ (5000211484700691/5000000000000000 : ℝ) ^ (4307/1024 : ℝ) := by
    have hpowers : (50008895765305544889/50000000000000000000 : ℝ)^1024 ≤ (5000211484700691/5000000000000000 : ℝ)^4307 := by
      have hnat : (50008895765305544889 : ℕ)^1024*5000000000000000^4307 ≤ 5000211484700691^4307*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008895765305544889 50000000000000000000 5000211484700691 5000000000000000 1024 4307 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000211484700691/5000000000000000 : ℝ)) (X := (50008895765305544889/50000000000000000000 : ℝ)) (by norm_num) 4307 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (1250539737531965993/1250000000000000000 : ℝ) ≤ (10001026422664357/10000000000000000 : ℝ) ^ (4307/1024 : ℝ) := by
    have hpowers : (1250539737531965993/1250000000000000000 : ℝ)^1024 ≤ (10001026422664357/10000000000000000 : ℝ)^4307 := by
      have hnat : (1250539737531965993 : ℕ)^1024*10000000000000000^4307 ≤ 10001026422664357^4307*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250539737531965993 1250000000000000000 10001026422664357 10000000000000000 1024 4307 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001026422664357/10000000000000000 : ℝ)) (X := (1250539737531965993/1250000000000000000 : ℝ)) (by norm_num) 4307 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034283237251734551/50000000000000000000 : ℝ) ≤ (2500407468981833/2500000000000000 : ℝ) ^ (4307/1024 : ℝ) := by
    have hpowers : (50034283237251734551/50000000000000000000 : ℝ)^1024 ≤ (2500407468981833/2500000000000000 : ℝ)^4307 := by
      have hnat : (50034283237251734551 : ℕ)^1024*2500000000000000^4307 ≤ 2500407468981833^4307*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034283237251734551 50000000000000000000 2500407468981833 2500000000000000 1024 4307 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500407468981833/2500000000000000 : ℝ)) (X := (50034283237251734551/50000000000000000000 : ℝ)) (by norm_num) 4307 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8895765305544889/100000000000000000000 : ℝ) ≤ ((10289650443419368011/10292500000000000000 : ℝ)+2*(24138130519/16468000000000 : ℝ)*(10887/100000 : ℝ))^(4307/1024 : ℝ) := by
    rw [show (10289650443419368011/10292500000000000000 : ℝ)+2*(24138130519/16468000000000 : ℝ)*(10887/100000 : ℝ)=(5000211484700691/5000000000000000 : ℝ) by norm_num, show 1+2*(8895765305544889/100000000000000000000 : ℝ)=(50008895765305544889/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34283237251734551/100000000000000000000 : ℝ)+(8895765305544889/100000000000000000000 : ℝ) ≤ ((10289650443419368011/10292500000000000000 : ℝ)+(24138130519/16468000000000 : ℝ)*((3751/25000 : ℝ)+(10887/100000 : ℝ)))^(4307/1024 : ℝ) := by
    rw [show (10289650443419368011/10292500000000000000 : ℝ)+(24138130519/16468000000000 : ℝ)*((3751/25000 : ℝ)+(10887/100000 : ℝ))=(10001026422664357/10000000000000000 : ℝ) by norm_num, show 1+(34283237251734551/100000000000000000000 : ℝ)+(8895765305544889/100000000000000000000 : ℝ)=(1250539737531965993/1250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34283237251734551/100000000000000000000 : ℝ) ≤ ((10289650443419368011/10292500000000000000 : ℝ)+2*(24138130519/16468000000000 : ℝ)*(3751/25000 : ℝ))^(4307/1024 : ℝ) := by
    rw [show (10289650443419368011/10292500000000000000 : ℝ)+2*(24138130519/16468000000000 : ℝ)*(3751/25000 : ℝ)=(2500407468981833/2500000000000000 : ℝ) by norm_num, show 1+2*(34283237251734551/100000000000000000000 : ℝ)=(50034283237251734551/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (10289650443419368011/10292500000000000000 : ℝ)*(X 1 0+X 2 0)+(24138130519/16468000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4307/1024 : ℝ)) (lo := (10887/100000 : ℝ)) (hi := (3751/25000 : ℝ)) (c := (10289650443419368011/10292500000000000000 : ℝ)) (alpha := (24138130519/16468000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (10289650443419368011/10292500000000000000 : ℝ)*(X 0 1+X 2 1)+(24138130519/16468000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4307/1024 : ℝ)) (lo := (10887/100000 : ℝ)) (hi := (3751/25000 : ℝ)) (c := (10289650443419368011/10292500000000000000 : ℝ)) (alpha := (24138130519/16468000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (10289650443419368011/10292500000000000000 : ℝ)*(X 0 2+X 1 2)+(24138130519/16468000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4307/1024 : ℝ)) (lo := (10887/100000 : ℝ)) (hi := (3751/25000 : ℝ)) (c := (10289650443419368011/10292500000000000000 : ℝ)) (alpha := (24138130519/16468000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2038512981/10000000000 : ℝ)*X 0 0+(5414852977/10000000000 : ℝ)*X 0 1+(52425233/100000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349522083/10000000000 : ℝ)*X 1 0+(-2126357461/10000000000 : ℝ)*X 1 1+(5242523143/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2139809/4000000 : ℝ)*X 2 0+(2621261497/5000000000 : ℝ)*X 2 1+(-2126357101/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4324883361/10000000000 : ℝ)*X 0 0+(1036880487/2500000000 : ℝ)*X 0 1+(4509294471/10000000000 : ℝ)*X 0 2+(4324883361/10000000000 : ℝ)*X 1 0+(1036880487/2500000000 : ℝ)*X 1 1+(4509294471/10000000000 : ℝ)*X 1 2+(4324883361/10000000000 : ℝ)*X 2 0+(1036880487/2500000000 : ℝ)*X 2 1+(4509294471/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1019263217/5000000000 : ℝ)*X 0 0+(2621578869/5000000000 : ℝ)*X 0 1+(2707107481/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326275753/2500000000 : ℝ)*X 1 0+(-488666481/2500000000 : ℝ)*X 1 1+(2707107523/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652551627/5000000000 : ℝ)*X 2 0+(5414214921/10000000000 : ℝ)*X 2 1+(-488666441/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((540613829/1250000000 : ℝ)*X 0 0+(2253981299/5000000000 : ℝ)*X 0 1+(3319089/8000000 : ℝ)*X 0 2+(540613829/1250000000 : ℝ)*X 1 0+(2253981299/5000000000 : ℝ)*X 1 1+(3319089/8000000 : ℝ)*X 1 2+(540613829/1250000000 : ℝ)*X 2 0+(2253981299/5000000000 : ℝ)*X 2 1+(3319089/8000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2347620044916686386328298729/257312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2358137009/100000000000000 : ℝ)*(base19) + (270085823/12500000000000 : ℝ)*(base23) + (347608217/100000000000000 : ℝ)*(lower2) + (31824519/20000000000000 : ℝ)*(upper3) + (4694689/2500000000000 : ℝ)*(upper5) + (2141783702466387/50000000000000 : ℝ)*(major0) + (2141783702466387/50000000000000 : ℝ)*(major1) + (2141783702466387/50000000000000 : ℝ)*(major2) + (5802869308681161/100000000000000 : ℝ)*(sp0) + (5802917718867597/100000000000000 : ℝ)*(sp1) + (2901458958159011/50000000000000 : ℝ)*(sp2) + (691047291742917/25000000000000 : ℝ)*(sp3) + (10153664689/20000000000000 : ℝ)*(sp4) + (5052353757/20000000000000 : ℝ)*(sp7) + (1382107214370227/50000000000000 : ℝ)*(f.failure) + (2901460038502303/50000000000000 : ℝ)*(f.sum) + (5289148023481/4117000000000000000000000000 : ℝ)*base65 + (503441869429046257/514625000000000000000000000000000 : ℝ)*base67 + (3809980639624171257/514625000000000000000000000000000 : ℝ)*base69 + (7550059742815796257/514625000000000000000000000000000 : ℝ)*base71 + (5395452092279/4117000000000000000000000000 : ℝ)*base74 + (3722771769847953743/514625000000000000000000000000000 : ℝ)*base76 + (2434764205499171257/514625000000000000000000000000000 : ℝ)*base77 + (2393055036925578743/514625000000000000000000000000000 : ℝ)*base80 + (3813789535111/2058500000000000000000000000 : ℝ)*base82 + (34745657/5000000000000000000000 : ℝ)*base89 + (34745657/5000000000000000000000 : ℝ)*base91 + (34745657/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (207028997582161212025134387/64328125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (94268463/50000000000000 : ℝ)*(base19) + (450946541/100000000000000 : ℝ)*(base23) + (784547/2000000000000 : ℝ)*(lower2) + (2711307/2000000000000 : ℝ)*(upper3) + (1898941/6250000000000 : ℝ)*(upper5) + (539420631330837/12500000000000 : ℝ)*(major0) + (539420631330837/12500000000000 : ℝ)*(major1) + (539420631330837/12500000000000 : ℝ)*(major2) + (1664380063/20000000000000 : ℝ)*(sp2) + (748943673/100000000000000 : ℝ)*(sp3) + (2922998166904623/50000000000000 : ℝ)*(sp4) + (2283592244247/39062500000 : ℝ)*(sp5) + (5845987560962389/100000000000000 : ℝ)*(sp6) + (2784732911262867/100000000000000 : ℝ)*(sp7) + (139236683010327/5000000000000 : ℝ)*(f.failure) + (2922998166904623/50000000000000 : ℝ)*(f.sum) + (13188721122559/4117000000000000000000000000 : ℝ)*base65 + (1366767140925467707/128656250000000000000000000000000 : ℝ)*base67 + (442636326052373957/128656250000000000000000000000000 : ℝ)*base69 + (445597947640373957/128656250000000000000000000000000 : ℝ)*base71 + (690353742069/411700000000000000000000000 : ℝ)*base73 + (1656612504928748957/128656250000000000000000000000000 : ℝ)*base75 + (868507320780311457/128656250000000000000000000000000 : ℝ)*base77 + (2701433719918373957/128656250000000000000000000000000 : ℝ)*base79 + (10060511281177/2058500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (2505243/500000000000000000000 : ℝ)*base90 + (2505243/500000000000000000000 : ℝ)*base92 + (2505243/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1348_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154965091/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3751/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10887/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5557/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7381/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1348_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1348_s5_0 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2038756121/10000000000 : ℝ)*x 0 + (2706382119/5000000000 : ℝ)*x 1 + (262222593/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2038756121/10000000000 : ℝ)^1077 ≤ (2483391009239/20000000000000 : ℝ)^821 := by
    have hnat : (2038756121 : ℕ)^1077*20000000000000^821 ≤ 2483391009239^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2038756121 10000000000 2483391009239 20000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2706382119/5000000000 : ℝ)^1077 ≤ (44698734590517/100000000000000 : ℝ)^821 := by
    have hnat : (2706382119 : ℕ)^1077*100000000000000^821 ≤ 44698734590517^821*5000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706382119 5000000000 44698734590517 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262222593/500000000 : ℝ)^1077 ≤ (10721077586097/25000000000000 : ℝ)^821 := by
    have hnat : (262222593 : ℕ)^1077*25000000000000^821 ≤ 10721077586097^821*500000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262222593 500000000 10721077586097 25000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2038756121/10000000000 : ℝ), (2706382119/5000000000 : ℝ), (262222593/500000000 : ℝ)] ![(2483391009239/20000000000000 : ℝ), (44698734590517/100000000000000 : ℝ), (10721077586097/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2038756121/10000000000 : ℝ)|^1077 ≤ (2483391009239/20000000000000 : ℝ)^821
        have hw : |(-2038756121/10000000000 : ℝ)|=(2038756121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2706382119/5000000000 : ℝ)|^1077 ≤ (44698734590517/100000000000000 : ℝ)^821
        have hw : |(2706382119/5000000000 : ℝ)|=(2706382119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(262222593/500000000 : ℝ)|^1077 ≤ (10721077586097/25000000000000 : ℝ)^821
        have hw : |(262222593/500000000 : ℝ)|=(262222593/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_s5_1 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (534898747/1000000000 : ℝ)*x 0 + (-531128597/2500000000 : ℝ)*x 1 + (163889121/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534898747/1000000000 : ℝ)^1077 ≤ (22004556805737/50000000000000 : ℝ)^821 := by
    have hnat : (534898747 : ℕ)^1077*50000000000000^821 ≤ 22004556805737^821*1000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534898747 1000000000 22004556805737 50000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (531128597/2500000000 : ℝ)^1077 ≤ (6553287951533/50000000000000 : ℝ)^821 := by
    have hnat : (531128597 : ℕ)^1077*50000000000000^821 ≤ 6553287951533^821*2500000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531128597 2500000000 6553287951533 50000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (163889121/312500000 : ℝ)^1077 ≤ (4288431047311/10000000000000 : ℝ)^821 := by
    have hnat : (163889121 : ℕ)^1077*10000000000000^821 ≤ 4288431047311^821*312500000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163889121 312500000 4288431047311 10000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534898747/1000000000 : ℝ), (-531128597/2500000000 : ℝ), (163889121/312500000 : ℝ)] ![(22004556805737/50000000000000 : ℝ), (6553287951533/50000000000000 : ℝ), (4288431047311/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534898747/1000000000 : ℝ)|^1077 ≤ (22004556805737/50000000000000 : ℝ)^821
        have hw : |(534898747/1000000000 : ℝ)|=(534898747/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-531128597/2500000000 : ℝ)|^1077 ≤ (6553287951533/50000000000000 : ℝ)^821
        have hw : |(-531128597/2500000000 : ℝ)|=(531128597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(163889121/312500000 : ℝ)|^1077 ≤ (4288431047311/10000000000000 : ℝ)^821
        have hw : |(163889121/312500000 : ℝ)|=(163889121/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_s5_2 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (8357793/15625000 : ℝ)*x 0 + (8391123/16000000 : ℝ)*x 1 + (-2124514317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8357793/15625000 : ℝ)^1077 ≤ (22004557075563/50000000000000 : ℝ)^821 := by
    have hnat : (8357793 : ℕ)^1077*50000000000000^821 ≤ 22004557075563^821*15625000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8357793 15625000 22004557075563 50000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8391123/16000000 : ℝ)^1077 ≤ (4288431050529/10000000000000 : ℝ)^821 := by
    have hnat : (8391123 : ℕ)^1077*10000000000000^821 ≤ 4288431050529^821*16000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8391123 16000000 4288431050529 10000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2124514317/10000000000 : ℝ)^1077 ≤ (13106575328473/100000000000000 : ℝ)^821 := by
    have hnat : (2124514317 : ℕ)^1077*100000000000000^821 ≤ 13106575328473^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124514317 10000000000 13106575328473 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8357793/15625000 : ℝ), (8391123/16000000 : ℝ), (-2124514317/10000000000 : ℝ)] ![(22004557075563/50000000000000 : ℝ), (4288431050529/10000000000000 : ℝ), (13106575328473/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8357793/15625000 : ℝ)|^1077 ≤ (22004557075563/50000000000000 : ℝ)^821
        have hw : |(8357793/15625000 : ℝ)|=(8357793/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8391123/16000000 : ℝ)|^1077 ≤ (4288431050529/10000000000000 : ℝ)^821
        have hw : |(8391123/16000000 : ℝ)|=(8391123/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2124514317/10000000000 : ℝ)|^1077 ≤ (13106575328473/100000000000000 : ℝ)^821
        have hw : |(-2124514317/10000000000 : ℝ)|=(2124514317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_s5_3 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2162513707/5000000000 : ℝ)*x 0 + (1037930327/2500000000 : ℝ)*x 1 + (4505059747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2162513707/5000000000 : ℝ)^1077 ≤ (832577733727/2500000000000 : ℝ)^821 := by
    have hnat : (2162513707 : ℕ)^1077*2500000000000^821 ≤ 832577733727^821*5000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2162513707 5000000000 832577733727 2500000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1037930327/2500000000 : ℝ)^1077 ≤ (31563566529217/100000000000000 : ℝ)^821 := by
    have hnat : (1037930327 : ℕ)^1077*100000000000000^821 ≤ 31563566529217^821*2500000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037930327 2500000000 31563566529217 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4505059747/10000000000 : ℝ)^1077 ≤ (17566662054601/50000000000000 : ℝ)^821 := by
    have hnat : (4505059747 : ℕ)^1077*50000000000000^821 ≤ 17566662054601^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4505059747 10000000000 17566662054601 50000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2162513707/5000000000 : ℝ), (1037930327/2500000000 : ℝ), (4505059747/10000000000 : ℝ)] ![(832577733727/2500000000000 : ℝ), (31563566529217/100000000000000 : ℝ), (17566662054601/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2162513707/5000000000 : ℝ)|^1077 ≤ (832577733727/2500000000000 : ℝ)^821
        have hw : |(2162513707/5000000000 : ℝ)|=(2162513707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1037930327/2500000000 : ℝ)|^1077 ≤ (31563566529217/100000000000000 : ℝ)^821
        have hw : |(1037930327/2500000000 : ℝ)|=(1037930327/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4505059747/10000000000 : ℝ)|^1077 ≤ (17566662054601/50000000000000 : ℝ)^821
        have hw : |(4505059747/10000000000 : ℝ)|=(4505059747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_s5_4 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-407753671/2000000000 : ℝ)*x 0 + (524505727/1000000000 : ℝ)*x 1 + (2706077859/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (407753671/2000000000 : ℝ)^1077 ≤ (2483410558091/20000000000000 : ℝ)^821 := by
    have hnat : (407753671 : ℕ)^1077*20000000000000^821 ≤ 2483410558091^821*2000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      407753671 2000000000 2483410558091 20000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524505727/1000000000 : ℝ)^1077 ≤ (42890804583567/100000000000000 : ℝ)^821 := by
    have hnat : (524505727 : ℕ)^1077*100000000000000^821 ≤ 42890804583567^821*1000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524505727 1000000000 42890804583567 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2706077859/5000000000 : ℝ)^1077 ≤ (44692142610111/100000000000000 : ℝ)^821 := by
    have hnat : (2706077859 : ℕ)^1077*100000000000000^821 ≤ 44692142610111^821*5000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706077859 5000000000 44692142610111 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-407753671/2000000000 : ℝ), (524505727/1000000000 : ℝ), (2706077859/5000000000 : ℝ)] ![(2483410558091/20000000000000 : ℝ), (42890804583567/100000000000000 : ℝ), (44692142610111/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-407753671/2000000000 : ℝ)|^1077 ≤ (2483410558091/20000000000000 : ℝ)^821
        have hw : |(-407753671/2000000000 : ℝ)|=(407753671/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524505727/1000000000 : ℝ)|^1077 ≤ (42890804583567/100000000000000 : ℝ)^821
        have hw : |(524505727/1000000000 : ℝ)|=(524505727/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2706077859/5000000000 : ℝ)|^1077 ≤ (44692142610111/100000000000000 : ℝ)^821
        have hw : |(2706077859/5000000000 : ℝ)|=(2706077859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_s5_5 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305604223/10000000000 : ℝ)*x 0 + (-978405237/5000000000 : ℝ)*x 1 + (5412155729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305604223/10000000000 : ℝ)^1077 ≤ (8708293979031/20000000000000 : ℝ)^821 := by
    have hnat : (5305604223 : ℕ)^1077*20000000000000^821 ≤ 8708293979031^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305604223 10000000000 8708293979031 20000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (978405237/5000000000 : ℝ)^1077 ≤ (11766387355193/100000000000000 : ℝ)^821 := by
    have hnat : (978405237 : ℕ)^1077*100000000000000^821 ≤ 11766387355193^821*5000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      978405237 5000000000 11766387355193 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5412155729/10000000000 : ℝ)^1077 ≤ (4469214272927/10000000000000 : ℝ)^821 := by
    have hnat : (5412155729 : ℕ)^1077*10000000000000^821 ≤ 4469214272927^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412155729 10000000000 4469214272927 10000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305604223/10000000000 : ℝ), (-978405237/5000000000 : ℝ), (5412155729/10000000000 : ℝ)] ![(8708293979031/20000000000000 : ℝ), (11766387355193/100000000000000 : ℝ), (4469214272927/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305604223/10000000000 : ℝ)|^1077 ≤ (8708293979031/20000000000000 : ℝ)^821
        have hw : |(5305604223/10000000000 : ℝ)|=(5305604223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-978405237/5000000000 : ℝ)|^1077 ≤ (11766387355193/100000000000000 : ℝ)^821
        have hw : |(-978405237/5000000000 : ℝ)|=(978405237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5412155729/10000000000 : ℝ)|^1077 ≤ (4469214272927/10000000000000 : ℝ)^821
        have hw : |(5412155729/10000000000 : ℝ)|=(5412155729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_s5_6 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305604209/10000000000 : ℝ)*x 0 + (270607787/500000000 : ℝ)*x 1 + (-978405239/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305604209/10000000000 : ℝ)^1077 ≤ (8708293948887/20000000000000 : ℝ)^821 := by
    have hnat : (5305604209 : ℕ)^1077*20000000000000^821 ≤ 8708293948887^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305604209 10000000000 8708293948887 20000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (270607787/500000000 : ℝ)^1077 ≤ (44692142848429/100000000000000 : ℝ)^821 := by
    have hnat : (270607787 : ℕ)^1077*100000000000000^821 ≤ 44692142848429^821*500000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270607787 500000000 44692142848429 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (978405239/5000000000 : ℝ)^1077 ≤ (2353277477349/20000000000000 : ℝ)^821 := by
    have hnat : (978405239 : ℕ)^1077*20000000000000^821 ≤ 2353277477349^821*5000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      978405239 5000000000 2353277477349 20000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305604209/10000000000 : ℝ), (270607787/500000000 : ℝ), (-978405239/5000000000 : ℝ)] ![(8708293948887/20000000000000 : ℝ), (44692142848429/100000000000000 : ℝ), (2353277477349/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305604209/10000000000 : ℝ)|^1077 ≤ (8708293948887/20000000000000 : ℝ)^821
        have hw : |(5305604209/10000000000 : ℝ)|=(5305604209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(270607787/500000000 : ℝ)|^1077 ≤ (44692142848429/100000000000000 : ℝ)^821
        have hw : |(270607787/500000000 : ℝ)|=(270607787/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-978405239/5000000000 : ℝ)|^1077 ≤ (2353277477349/20000000000000 : ℝ)^821
        have hw : |(-978405239/5000000000 : ℝ)|=(978405239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_s5_7 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4325053071/10000000000 : ℝ)*x 0 + (4503788931/10000000000 : ℝ)*x 1 + (10382497/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4325053071/10000000000 : ℝ)^1077 ≤ (33303368513119/100000000000000 : ℝ)^821 := by
    have hnat : (4325053071 : ℕ)^1077*100000000000000^821 ≤ 33303368513119^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4325053071 10000000000 33303368513119 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4503788931/10000000000 : ℝ)^1077 ≤ (8780080941589/25000000000000 : ℝ)^821 := by
    have hnat : (4503788931 : ℕ)^1077*25000000000000^821 ≤ 8780080941589^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4503788931 10000000000 8780080941589 25000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (10382497/25000000 : ℝ)^1077 ≤ (15788153851587/50000000000000 : ℝ)^821 := by
    have hnat : (10382497 : ℕ)^1077*50000000000000^821 ≤ 15788153851587^821*25000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10382497 25000000 15788153851587 50000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4325053071/10000000000 : ℝ), (4503788931/10000000000 : ℝ), (10382497/25000000 : ℝ)] ![(33303368513119/100000000000000 : ℝ), (8780080941589/25000000000000 : ℝ), (15788153851587/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4325053071/10000000000 : ℝ)|^1077 ≤ (33303368513119/100000000000000 : ℝ)^821
        have hw : |(4325053071/10000000000 : ℝ)|=(4325053071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4503788931/10000000000 : ℝ)|^1077 ≤ (8780080941589/25000000000000 : ℝ)^821
        have hw : |(4503788931/10000000000 : ℝ)|=(4503788931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(10382497/25000000 : ℝ)|^1077 ≤ (15788153851587/50000000000000 : ℝ)^821
        have hw : |(10382497/25000000 : ℝ)|=(10382497/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1348_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154965091/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7381/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5557/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2789/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14719/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7381/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5557/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7381/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5557/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7381/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5557/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7381/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5557/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7381/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5557/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7381/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5557/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5557/50000 : ℝ) ^ (4307/1024 : ℝ) ≤ (4851194598036323/50000000000000000000 : ℝ) := by
    have hpowers : (5557/50000 : ℝ)^4307 ≤ (4851194598036323/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5557 : ℕ)^4307*50000000000000000000^1024 ≤ 4851194598036323^1024*50000^4307 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5557 50000 4851194598036323 50000000000000000000 4307 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5557/50000 : ℝ)) (X := (4851194598036323/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4307 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7381/50000 : ℝ) ^ (4307/1024 : ℝ) ≤ (8004224971405693/25000000000000000000 : ℝ) := by
    have hpowers : (7381/50000 : ℝ)^4307 ≤ (8004224971405693/25000000000000000000 : ℝ)^1024 := by
      have hnat : (7381 : ℕ)^4307*25000000000000000000^1024 ≤ 8004224971405693^1024*50000^4307 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7381 50000 8004224971405693 25000000000000000000 4307 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7381/50000 : ℝ)) (X := (8004224971405693/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4307 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004851194598036323/25000000000000000000 : ℝ) ≤ (2500115329833379/2500000000000000 : ℝ) ^ (4307/1024 : ℝ) := by
    have hpowers : (25004851194598036323/25000000000000000000 : ℝ)^1024 ≤ (2500115329833379/2500000000000000 : ℝ)^4307 := by
      have hnat : (25004851194598036323 : ℕ)^1024*2500000000000000^4307 ≤ 2500115329833379^4307*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004851194598036323 25000000000000000000 2500115329833379 2500000000000000 1024 4307 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500115329833379/2500000000000000 : ℝ)) (X := (25004851194598036323/25000000000000000000 : ℝ)) (by norm_num) 4307 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50020859644540847709/50000000000000000000 : ℝ) ≤ (1000099172883737/1000000000000000 : ℝ) ^ (4307/1024 : ℝ) := by
    have hpowers : (50020859644540847709/50000000000000000000 : ℝ)^1024 ≤ (1000099172883737/1000000000000000 : ℝ)^4307 := by
      have hnat : (50020859644540847709 : ℕ)^1024*1000000000000000^4307 ≤ 1000099172883737^4307*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020859644540847709 50000000000000000000 1000099172883737 1000000000000000 1024 4307 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000099172883737/1000000000000000 : ℝ)) (X := (50020859644540847709/50000000000000000000 : ℝ)) (by norm_num) 4307 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508004224971405693/12500000000000000000 : ℝ) ≤ (1250190267292653/1250000000000000 : ℝ) ^ (4307/1024 : ℝ) := by
    have hpowers : (12508004224971405693/12500000000000000000 : ℝ)^1024 ≤ (1250190267292653/1250000000000000 : ℝ)^4307 := by
      have hnat : (12508004224971405693 : ℕ)^1024*1250000000000000^4307 ≤ 1250190267292653^4307*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508004224971405693 12500000000000000000 1250190267292653 1250000000000000 1024 4307 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250190267292653/1250000000000000 : ℝ)) (X := (12508004224971405693/12500000000000000000 : ℝ)) (by norm_num) 4307 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4851194598036323/50000000000000000000 : ℝ) ≤ ((4558736618809624957/4560000000000000000 : ℝ)+2*(265204751927/182400000000000 : ℝ)*(5557/50000 : ℝ))^(4307/1024 : ℝ) := by
    rw [show (4558736618809624957/4560000000000000000 : ℝ)+2*(265204751927/182400000000000 : ℝ)*(5557/50000 : ℝ)=(2500115329833379/2500000000000000 : ℝ) by norm_num, show 1+2*(4851194598036323/50000000000000000000 : ℝ)=(25004851194598036323/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8004224971405693/25000000000000000000 : ℝ)+(4851194598036323/50000000000000000000 : ℝ) ≤ ((4558736618809624957/4560000000000000000 : ℝ)+(265204751927/182400000000000 : ℝ)*((7381/50000 : ℝ)+(5557/50000 : ℝ)))^(4307/1024 : ℝ) := by
    rw [show (4558736618809624957/4560000000000000000 : ℝ)+(265204751927/182400000000000 : ℝ)*((7381/50000 : ℝ)+(5557/50000 : ℝ))=(1000099172883737/1000000000000000 : ℝ) by norm_num, show 1+(8004224971405693/25000000000000000000 : ℝ)+(4851194598036323/50000000000000000000 : ℝ)=(50020859644540847709/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8004224971405693/25000000000000000000 : ℝ) ≤ ((4558736618809624957/4560000000000000000 : ℝ)+2*(265204751927/182400000000000 : ℝ)*(7381/50000 : ℝ))^(4307/1024 : ℝ) := by
    rw [show (4558736618809624957/4560000000000000000 : ℝ)+2*(265204751927/182400000000000 : ℝ)*(7381/50000 : ℝ)=(1250190267292653/1250000000000000 : ℝ) by norm_num, show 1+2*(8004224971405693/25000000000000000000 : ℝ)=(12508004224971405693/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4558736618809624957/4560000000000000000 : ℝ)*(X 1 0+X 2 0)+(265204751927/182400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4307/1024 : ℝ)) (lo := (5557/50000 : ℝ)) (hi := (7381/50000 : ℝ)) (c := (4558736618809624957/4560000000000000000 : ℝ)) (alpha := (265204751927/182400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4558736618809624957/4560000000000000000 : ℝ)*(X 0 1+X 2 1)+(265204751927/182400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4307/1024 : ℝ)) (lo := (5557/50000 : ℝ)) (hi := (7381/50000 : ℝ)) (c := (4558736618809624957/4560000000000000000 : ℝ)) (alpha := (265204751927/182400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4558736618809624957/4560000000000000000 : ℝ)*(X 0 2+X 1 2)+(265204751927/182400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4307/1024 : ℝ)) (lo := (5557/50000 : ℝ)) (hi := (7381/50000 : ℝ)) (c := (4558736618809624957/4560000000000000000 : ℝ)) (alpha := (265204751927/182400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2038756121/10000000000 : ℝ)*X 0 0+(2706382119/5000000000 : ℝ)*X 0 1+(262222593/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534898747/1000000000 : ℝ)*X 1 0+(-531128597/2500000000 : ℝ)*X 1 1+(163889121/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((8357793/15625000 : ℝ)*X 2 0+(8391123/16000000 : ℝ)*X 2 1+(-2124514317/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2162513707/5000000000 : ℝ)*X 0 0+(1037930327/2500000000 : ℝ)*X 0 1+(4505059747/10000000000 : ℝ)*X 0 2+(2162513707/5000000000 : ℝ)*X 1 0+(1037930327/2500000000 : ℝ)*X 1 1+(4505059747/10000000000 : ℝ)*X 1 2+(2162513707/5000000000 : ℝ)*X 2 0+(1037930327/2500000000 : ℝ)*X 2 1+(4505059747/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-407753671/2000000000 : ℝ)*X 0 0+(524505727/1000000000 : ℝ)*X 0 1+(2706077859/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305604223/10000000000 : ℝ)*X 1 0+(-978405237/5000000000 : ℝ)*X 1 1+(5412155729/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305604209/10000000000 : ℝ)*X 2 0+(270607787/500000000 : ℝ)*X 2 1+(-978405239/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4325053071/10000000000 : ℝ)*X 0 0+(4503788931/10000000000 : ℝ)*X 0 1+(10382497/25000000 : ℝ)*X 0 2+(4325053071/10000000000 : ℝ)*X 1 0+(4503788931/10000000000 : ℝ)*X 1 1+(10382497/25000000 : ℝ)*X 1 2+(4325053071/10000000000 : ℝ)*X 2 0+(4503788931/10000000000 : ℝ)*X 2 1+(10382497/25000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (173907541079491888420960089/76000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (477690241/100000000000000 : ℝ)*(base19) + (264261577/50000000000000 : ℝ)*(base23) + (1258153/50000000000000 : ℝ)*(lower2) + (7639703/25000000000000 : ℝ)*(upper3) + (30874363/25000000000000 : ℝ)*(upper5) + (4385755550928723/100000000000000 : ℝ)*(major0) + (4385755550928723/100000000000000 : ℝ)*(major1) + (4385755550928723/100000000000000 : ℝ)*(major2) + (1485335440106661/25000000000000 : ℝ)*(sp0) + (5941353431455509/100000000000000 : ℝ)*(sp1) + (1485338345155649/25000000000000 : ℝ)*(sp2) + (707538250145277/25000000000000 : ℝ)*(sp3) + (12148719107/100000000000000 : ℝ)*(sp4) + (4115855343/100000000000000 : ℝ)*(sp7) + (707539279109113/25000000000000 : ℝ)*(f.failure) + (23765415636583/400000000000 : ℝ)*(f.sum) + (20989091252167/3040000000000000000000000000 : ℝ)*base65 + (921401820681821637/152000000000000000000000000000000 : ℝ)*base67 + (630615000734178363/152000000000000000000000000000000 : ℝ)*base70 + (182134235209821637/152000000000000000000000000000000 : ℝ)*base71 + (17001711887207/3040000000000000000000000000 : ℝ)*base73 + (1039180819601821637/152000000000000000000000000000000 : ℝ)*base75 + (1043893722329821637/152000000000000000000000000000000 : ℝ)*base77 + (87232534694178363/152000000000000000000000000000000 : ℝ)*base80 + (2038080888647/3040000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (19974283/2500000000000000000000 : ℝ)*base89 + (19974283/2500000000000000000000 : ℝ)*base91 + (19974283/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9226621627296639462921007/1000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (412690091/25000000000000 : ℝ)*(base19) + (864977113/50000000000000 : ℝ)*(base23) + (100826239/50000000000000 : ℝ)*(upper3) + (2637937/6250000000000 : ℝ)*(lower4) + (9380057/5000000000000 : ℝ)*(upper5) + (2208800509692131/50000000000000 : ℝ)*(major0) + (2208800509692131/50000000000000 : ℝ)*(major1) + (2208800509692131/50000000000000 : ℝ)*(major2) + (1676388433/5000000000000 : ℝ)*(sp1) + (7083035909/20000000000000 : ℝ)*(sp2) + (1196898904595977/20000000000000 : ℝ)*(sp4) + (2992229672225431/50000000000000 : ℝ)*(sp5) + (2992228688923057/50000000000000 : ℝ)*(sp6) + (285070720823457/10000000000000 : ℝ)*(sp7) + (285070720823457/10000000000000 : ℝ)*(f.failure) + (1196898904595977/20000000000000 : ℝ)*(f.sum) + (180020823223/240000000000000000000000000 : ℝ)*base65 + (55187937490263831/4000000000000000000000000000000 : ℝ)*base67 + (30811578250263831/4000000000000000000000000000000 : ℝ)*base69 + (56660792386263831/4000000000000000000000000000000 : ℝ)*base71 + (529266253543/240000000000000000000000000 : ℝ)*base73 + (61390371701736169/4000000000000000000000000000000 : ℝ)*base76 + (32200425186263831/4000000000000000000000000000000 : ℝ)*base77 + (74885228350263831/4000000000000000000000000000000 : ℝ)*base79 + (366306164297/240000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (11060413/1000000000000000000000 : ℝ)*base90 + (11060413/1000000000000000000000 : ℝ)*base92 + (11060413/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1348_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154965091/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7381/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5557/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2789/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14719/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1348_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1348_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154965091/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16081/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9891/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2789/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14719/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1348_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1348_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1348_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154965091/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16081/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9891/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2789/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14719/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1348_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
