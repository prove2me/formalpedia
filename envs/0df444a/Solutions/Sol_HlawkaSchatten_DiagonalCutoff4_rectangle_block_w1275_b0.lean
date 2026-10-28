-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1275_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:20:36.034801+00:00
-- url     : https://prove2.me/submissions/c173b583-d76d-408b-9b75-5aa923df9041

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
theorem support_rectangle_w1275_s0_0 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1849426749/10000000000 : ℝ)*x 0 + (188323753/312500000 : ℝ)*x 1 + (1198668481/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1849426749/10000000000 : ℝ)^4235 ≤ (5398368407043/50000000000000 : ℝ)^3211 := by
    have hnat : (1849426749 : ℕ)^4235*50000000000000^3211 ≤ 5398368407043^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1849426749 10000000000 5398368407043 50000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (188323753/312500000 : ℝ)^4235 ≤ (51275961703879/100000000000000 : ℝ)^3211 := by
    have hnat : (188323753 : ℕ)^4235*100000000000000^3211 ≤ 51275961703879^3211*312500000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      188323753 312500000 51275961703879 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1198668481/2500000000 : ℝ)^4235 ≤ (18963650734017/50000000000000 : ℝ)^3211 := by
    have hnat : (1198668481 : ℕ)^4235*50000000000000^3211 ≤ 18963650734017^3211*2500000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1198668481 2500000000 18963650734017 50000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1849426749/10000000000 : ℝ), (188323753/312500000 : ℝ), (1198668481/2500000000 : ℝ)] ![(5398368407043/50000000000000 : ℝ), (51275961703879/100000000000000 : ℝ), (18963650734017/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1849426749/10000000000 : ℝ)|^4235 ≤ (5398368407043/50000000000000 : ℝ)^3211
        have hw : |(-1849426749/10000000000 : ℝ)|=(1849426749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(188323753/312500000 : ℝ)|^4235 ≤ (51275961703879/100000000000000 : ℝ)^3211
        have hw : |(188323753/312500000 : ℝ)|=(188323753/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1198668481/2500000000 : ℝ)|^4235 ≤ (18963650734017/50000000000000 : ℝ)^3211
        have hw : |(1198668481/2500000000 : ℝ)|=(1198668481/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_s0_1 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2754663451/5000000000 : ℝ)*x 0 + (-2552992917/10000000000 : ℝ)*x 1 + (4794673899/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2754663451/5000000000 : ℝ)^4235 ≤ (45554773542937/100000000000000 : ℝ)^3211 := by
    have hnat : (2754663451 : ℕ)^4235*100000000000000^3211 ≤ 45554773542937^3211*5000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2754663451 5000000000 45554773542937 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2552992917/10000000000 : ℝ)^4235 ≤ (16517925236981/100000000000000 : ℝ)^3211 := by
    have hnat : (2552992917 : ℕ)^4235*100000000000000^3211 ≤ 16517925236981^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2552992917 10000000000 16517925236981 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4794673899/10000000000 : ℝ)^4235 ≤ (37927301207211/100000000000000 : ℝ)^3211 := by
    have hnat : (4794673899 : ℕ)^4235*100000000000000^3211 ≤ 37927301207211^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4794673899 10000000000 37927301207211 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2754663451/5000000000 : ℝ), (-2552992917/10000000000 : ℝ), (4794673899/10000000000 : ℝ)] ![(45554773542937/100000000000000 : ℝ), (16517925236981/100000000000000 : ℝ), (37927301207211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2754663451/5000000000 : ℝ)|^4235 ≤ (45554773542937/100000000000000 : ℝ)^3211
        have hw : |(2754663451/5000000000 : ℝ)|=(2754663451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2552992917/10000000000 : ℝ)|^4235 ≤ (16517925236981/100000000000000 : ℝ)^3211
        have hw : |(-2552992917/10000000000 : ℝ)|=(2552992917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4794673899/10000000000 : ℝ)|^4235 ≤ (37927301207211/100000000000000 : ℝ)^3211
        have hw : |(4794673899/10000000000 : ℝ)|=(4794673899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_s0_2 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (344332933/625000000 : ℝ)*x 0 + (4794673897/10000000000 : ℝ)*x 1 + (-2552992887/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (344332933/625000000 : ℝ)^4235 ≤ (22777386913241/50000000000000 : ℝ)^3211 := by
    have hnat : (344332933 : ℕ)^4235*50000000000000^3211 ≤ 22777386913241^3211*625000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      344332933 625000000 22777386913241 50000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4794673897/10000000000 : ℝ)^4235 ≤ (7585460237269/20000000000000 : ℝ)^3211 := by
    have hnat : (4794673897 : ℕ)^4235*20000000000000^3211 ≤ 7585460237269^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4794673897 10000000000 7585460237269 20000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2552992887/10000000000 : ℝ)^4235 ≤ (16517924980981/100000000000000 : ℝ)^3211 := by
    have hnat : (2552992887 : ℕ)^4235*100000000000000^3211 ≤ 16517924980981^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2552992887 10000000000 16517924980981 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(344332933/625000000 : ℝ), (4794673897/10000000000 : ℝ), (-2552992887/10000000000 : ℝ)] ![(22777386913241/50000000000000 : ℝ), (7585460237269/20000000000000 : ℝ), (16517924980981/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(344332933/625000000 : ℝ)|^4235 ≤ (22777386913241/50000000000000 : ℝ)^3211
        have hw : |(344332933/625000000 : ℝ)|=(344332933/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4794673897/10000000000 : ℝ)|^4235 ≤ (7585460237269/20000000000000 : ℝ)^3211
        have hw : |(4794673897/10000000000 : ℝ)|=(4794673897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2552992887/10000000000 : ℝ)|^4235 ≤ (16517924980981/100000000000000 : ℝ)^3211
        have hw : |(-2552992887/10000000000 : ℝ)|=(2552992887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_s0_3 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (837791479/2000000000 : ℝ)*x 0 + (3110591749/10000000000 : ℝ)*x 1 + (2812782667/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (837791479/2000000000 : ℝ)^4235 ≤ (31739063232567/100000000000000 : ℝ)^3211 := by
    have hnat : (837791479 : ℕ)^4235*100000000000000^3211 ≤ 31739063232567^3211*2000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      837791479 2000000000 31739063232567 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3110591749/10000000000 : ℝ)^4235 ≤ (21434272230351/100000000000000 : ℝ)^3211 := by
    have hnat : (3110591749 : ℕ)^4235*100000000000000^3211 ≤ 21434272230351^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3110591749 10000000000 21434272230351 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2812782667/5000000000 : ℝ)^4235 ≤ (2341333225919/5000000000000 : ℝ)^3211 := by
    have hnat : (2812782667 : ℕ)^4235*5000000000000^3211 ≤ 2341333225919^3211*5000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2812782667 5000000000 2341333225919 5000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(837791479/2000000000 : ℝ), (3110591749/10000000000 : ℝ), (2812782667/5000000000 : ℝ)] ![(31739063232567/100000000000000 : ℝ), (21434272230351/100000000000000 : ℝ), (2341333225919/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(837791479/2000000000 : ℝ)|^4235 ≤ (31739063232567/100000000000000 : ℝ)^3211
        have hw : |(837791479/2000000000 : ℝ)|=(837791479/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3110591749/10000000000 : ℝ)|^4235 ≤ (21434272230351/100000000000000 : ℝ)^3211
        have hw : |(3110591749/10000000000 : ℝ)|=(3110591749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2812782667/5000000000 : ℝ)|^4235 ≤ (2341333225919/5000000000000 : ℝ)^3211
        have hw : |(2812782667/5000000000 : ℝ)|=(2812782667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_s0_4 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-463561287/2500000000 : ℝ)*x 0 + (4826487603/10000000000 : ℝ)*x 1 + (749177021/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (463561287/2500000000 : ℝ)^4235 ≤ (5416925994997/50000000000000 : ℝ)^3211 := by
    have hnat : (463561287 : ℕ)^4235*50000000000000^3211 ≤ 5416925994997^3211*2500000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      463561287 2500000000 5416925994997 50000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4826487603/10000000000 : ℝ)^4235 ≤ (38259561743189/100000000000000 : ℝ)^3211 := by
    have hnat : (4826487603 : ℕ)^4235*100000000000000^3211 ≤ 38259561743189^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4826487603 10000000000 38259561743189 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (749177021/1250000000 : ℝ)^4235 ≤ (50906586252459/100000000000000 : ℝ)^3211 := by
    have hnat : (749177021 : ℕ)^4235*100000000000000^3211 ≤ 50906586252459^3211*1250000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      749177021 1250000000 50906586252459 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-463561287/2500000000 : ℝ), (4826487603/10000000000 : ℝ), (749177021/1250000000 : ℝ)] ![(5416925994997/50000000000000 : ℝ), (38259561743189/100000000000000 : ℝ), (50906586252459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-463561287/2500000000 : ℝ)|^4235 ≤ (5416925994997/50000000000000 : ℝ)^3211
        have hw : |(-463561287/2500000000 : ℝ)|=(463561287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4826487603/10000000000 : ℝ)|^4235 ≤ (38259561743189/100000000000000 : ℝ)^3211
        have hw : |(4826487603/10000000000 : ℝ)|=(4826487603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(749177021/1250000000 : ℝ)|^4235 ≤ (50906586252459/100000000000000 : ℝ)^3211
        have hw : |(749177021/1250000000 : ℝ)|=(749177021/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_s0_5 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1293535523/2500000000 : ℝ)*x 0 + (-270849659/2000000000 : ℝ)*x 1 + (1498354649/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1293535523/2500000000 : ℝ)^4235 ≤ (41935354912467/100000000000000 : ℝ)^3211 := by
    have hnat : (1293535523 : ℕ)^4235*100000000000000^3211 ≤ 41935354912467^3211*2500000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1293535523 2500000000 41935354912467 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (270849659/2000000000 : ℝ)^4235 ≤ (7158031620229/100000000000000 : ℝ)^3211 := by
    have hnat : (270849659 : ℕ)^4235*100000000000000^3211 ≤ 7158031620229^3211*2000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270849659 2000000000 7158031620229 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1498354649/2500000000 : ℝ)^4235 ≤ (50906613451987/100000000000000 : ℝ)^3211 := by
    have hnat : (1498354649 : ℕ)^4235*100000000000000^3211 ≤ 50906613451987^3211*2500000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1498354649 2500000000 50906613451987 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1293535523/2500000000 : ℝ), (-270849659/2000000000 : ℝ), (1498354649/2500000000 : ℝ)] ![(41935354912467/100000000000000 : ℝ), (7158031620229/100000000000000 : ℝ), (50906613451987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1293535523/2500000000 : ℝ)|^4235 ≤ (41935354912467/100000000000000 : ℝ)^3211
        have hw : |(1293535523/2500000000 : ℝ)|=(1293535523/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-270849659/2000000000 : ℝ)|^4235 ≤ (7158031620229/100000000000000 : ℝ)^3211
        have hw : |(-270849659/2000000000 : ℝ)|=(270849659/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1498354649/2500000000 : ℝ)|^4235 ≤ (50906613451987/100000000000000 : ℝ)^3211
        have hw : |(1498354649/2500000000 : ℝ)|=(1498354649/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_s0_6 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2587071617/5000000000 : ℝ)*x 0 + (2996708293/5000000000 : ℝ)*x 1 + (-1354249773/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2587071617/5000000000 : ℝ)^4235 ≤ (41935367119811/100000000000000 : ℝ)^3211 := by
    have hnat : (2587071617 : ℕ)^4235*100000000000000^3211 ≤ 41935367119811^3211*5000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587071617 5000000000 41935367119811 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2996708293/5000000000 : ℝ)^4235 ≤ (1272664773377/2500000000000 : ℝ)^3211 := by
    have hnat : (2996708293 : ℕ)^4235*2500000000000^3211 ≤ 1272664773377^3211*5000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2996708293 5000000000 1272664773377 2500000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1354249773/10000000000 : ℝ)^4235 ≤ (1431608384737/20000000000000 : ℝ)^3211 := by
    have hnat : (1354249773 : ℕ)^4235*20000000000000^3211 ≤ 1431608384737^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354249773 10000000000 1431608384737 20000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2587071617/5000000000 : ℝ), (2996708293/5000000000 : ℝ), (-1354249773/10000000000 : ℝ)] ![(41935367119811/100000000000000 : ℝ), (1272664773377/2500000000000 : ℝ), (1431608384737/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2587071617/5000000000 : ℝ)|^4235 ≤ (41935367119811/100000000000000 : ℝ)^3211
        have hw : |(2587071617/5000000000 : ℝ)|=(2587071617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2996708293/5000000000 : ℝ)|^4235 ≤ (1272664773377/2500000000000 : ℝ)^3211
        have hw : |(2996708293/5000000000 : ℝ)|=(2996708293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1354249773/10000000000 : ℝ)|^4235 ≤ (1431608384737/20000000000000 : ℝ)^3211
        have hw : |(-1354249773/10000000000 : ℝ)|=(1354249773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_s0_7 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2099399679/5000000000 : ℝ)*x 0 + (5560611257/10000000000 : ℝ)*x 1 + (3177853671/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2099399679/5000000000 : ℝ)^4235 ≤ (3979681501759/12500000000000 : ℝ)^3211 := by
    have hnat : (2099399679 : ℕ)^4235*12500000000000^3211 ≤ 3979681501759^3211*5000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2099399679 5000000000 3979681501759 12500000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5560611257/10000000000 : ℝ)^4235 ≤ (90068139003/195312500000 : ℝ)^3211 := by
    have hnat : (5560611257 : ℕ)^4235*195312500000^3211 ≤ 90068139003^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5560611257 10000000000 90068139003 195312500000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3177853671/10000000000 : ℝ)^4235 ≤ (22047660803667/100000000000000 : ℝ)^3211 := by
    have hnat : (3177853671 : ℕ)^4235*100000000000000^3211 ≤ 22047660803667^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3177853671 10000000000 22047660803667 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2099399679/5000000000 : ℝ), (5560611257/10000000000 : ℝ), (3177853671/10000000000 : ℝ)] ![(3979681501759/12500000000000 : ℝ), (90068139003/195312500000 : ℝ), (22047660803667/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2099399679/5000000000 : ℝ)|^4235 ≤ (3979681501759/12500000000000 : ℝ)^3211
        have hw : |(2099399679/5000000000 : ℝ)|=(2099399679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5560611257/10000000000 : ℝ)|^4235 ≤ (90068139003/195312500000 : ℝ)^3211
        have hw : |(5560611257/10000000000 : ℝ)|=(5560611257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3177853671/10000000000 : ℝ)|^4235 ≤ (22047660803667/100000000000000 : ℝ)^3211
        have hw : |(3177853671/10000000000 : ℝ)|=(3177853671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1275_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19011843/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (899/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27361/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2/5 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2/5 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2/5 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2/5 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2/5 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2/5 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
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
  have hpowlo : (0 : ℝ) ^ (2117/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2117 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2117*1^512 ≤ 0^512*1^2117 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2117 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2117 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2117/512 : ℝ) ≤ (565654621842374423/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2117 ≤ (565654621842374423/25000000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2117*25000000000000000000^512 ≤ 565654621842374423^512*5^2117 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 565654621842374423 25000000000000000000 2117 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (565654621842374423/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2117 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2117/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2117 := by
      have hnat : (1 : ℕ)^512*1^2117 ≤ 1^2117*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2117 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2117 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (25565654621842374423/25000000000000000000 : ℝ) ≤ (628391161662629/625000000000000 : ℝ) ^ (2117/512 : ℝ) := by
    have hpowers : (25565654621842374423/25000000000000000000 : ℝ)^512 ≤ (628391161662629/625000000000000 : ℝ)^2117 := by
      have hnat : (25565654621842374423 : ℕ)^512*625000000000000^2117 ≤ 628391161662629^2117*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25565654621842374423 25000000000000000000 628391161662629 625000000000000 512 2117 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (628391161662629/625000000000000 : ℝ)) (X := (25565654621842374423/25000000000000000000 : ℝ)) (by norm_num) 2117 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (13065654621842374423/12500000000000000000 : ℝ) ≤ (315891161662629/312500000000000 : ℝ) ^ (2117/512 : ℝ) := by
    have hpowers : (13065654621842374423/12500000000000000000 : ℝ)^512 ≤ (315891161662629/312500000000000 : ℝ)^2117 := by
      have hnat : (13065654621842374423 : ℕ)^512*312500000000000^2117 ≤ 315891161662629^2117*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13065654621842374423 12500000000000000000 315891161662629 312500000000000 512 2117 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (315891161662629/312500000000000 : ℝ)) (X := (13065654621842374423/12500000000000000000 : ℝ)) (by norm_num) 2117 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(3391161662629/250000000000000 : ℝ)*(0 : ℝ))^(2117/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(3391161662629/250000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(565654621842374423/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(3391161662629/250000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2117/512 : ℝ) := by
    rw [show (1 : ℝ)+(3391161662629/250000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(628391161662629/625000000000000 : ℝ) by norm_num, show 1+(565654621842374423/25000000000000000000 : ℝ)+(0 : ℝ)=(25565654621842374423/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(565654621842374423/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(3391161662629/250000000000000 : ℝ)*(2/5 : ℝ))^(2117/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(3391161662629/250000000000000 : ℝ)*(2/5 : ℝ)=(315891161662629/312500000000000 : ℝ) by norm_num, show 1+2*(565654621842374423/25000000000000000000 : ℝ)=(13065654621842374423/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(3391161662629/250000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2117/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (3391161662629/250000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(3391161662629/250000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2117/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (3391161662629/250000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(3391161662629/250000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2117/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (3391161662629/250000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1849426749/10000000000 : ℝ)*X 0 0+(188323753/312500000 : ℝ)*X 0 1+(1198668481/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2754663451/5000000000 : ℝ)*X 1 0+(-2552992917/10000000000 : ℝ)*X 1 1+(4794673899/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((344332933/625000000 : ℝ)*X 2 0+(4794673897/10000000000 : ℝ)*X 2 1+(-2552992887/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((837791479/2000000000 : ℝ)*X 0 0+(3110591749/10000000000 : ℝ)*X 0 1+(2812782667/5000000000 : ℝ)*X 0 2+(837791479/2000000000 : ℝ)*X 1 0+(3110591749/10000000000 : ℝ)*X 1 1+(2812782667/5000000000 : ℝ)*X 1 2+(837791479/2000000000 : ℝ)*X 2 0+(3110591749/10000000000 : ℝ)*X 2 1+(2812782667/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-463561287/2500000000 : ℝ)*X 0 0+(4826487603/10000000000 : ℝ)*X 0 1+(749177021/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1293535523/2500000000 : ℝ)*X 1 0+(-270849659/2000000000 : ℝ)*X 1 1+(1498354649/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2587071617/5000000000 : ℝ)*X 2 0+(2996708293/5000000000 : ℝ)*X 2 1+(-1354249773/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2099399679/5000000000 : ℝ)*X 0 0+(5560611257/10000000000 : ℝ)*X 0 1+(3177853671/10000000000 : ℝ)*X 0 2+(2099399679/5000000000 : ℝ)*X 1 0+(5560611257/10000000000 : ℝ)*X 1 1+(3177853671/10000000000 : ℝ)*X 1 2+(2099399679/5000000000 : ℝ)*X 2 0+(5560611257/10000000000 : ℝ)*X 2 1+(3177853671/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5755832737387443552537/781250000000000000000000000 : ℝ) := by norm_num
    linear_combination (81308619/100000000000000 : ℝ)*(base1) + (357265521/20000000000000 : ℝ)*(base19) + (2237699/125000000000 : ℝ)*(base23) + (204527007/100000000000000 : ℝ)*(upper3) + (213270351/100000000000000 : ℝ)*(upper5) + (151191290306357/25000000000000 : ℝ)*(major0) + (151191290306357/25000000000000 : ℝ)*(major1) + (151191290306357/25000000000000 : ℝ)*(major2) + (811900478396559/100000000000000 : ℝ)*(sp0) + (162380863848991/20000000000000 : ℝ)*(sp1) + (811904315413359/100000000000000 : ℝ)*(sp2) + (397621128139447/100000000000000 : ℝ)*(sp3) + (285424231/5000000000000 : ℝ)*(sp4) + (690462007/25000000000000 : ℝ)*(sp7) + (198811985648047/50000000000000 : ℝ)*(f.failure) + (10148826319657/1250000000000 : ℝ)*(f.sum) + (4258493851303/3125000000000000000000000000 : ℝ)*base65 + (19004796486197/6250000000000000000000000000 : ℝ)*base68 + (26033608270053/6250000000000000000000000000 : ℝ)*base69 + (1029524461197/6250000000000000000000000000 : ℝ)*base72 + (6675230957553/3125000000000000000000000000 : ℝ)*base73 + (11903678411197/6250000000000000000000000000 : ℝ)*base76 + (15968277151303/6250000000000000000000000000 : ℝ)*base77 + (21026987895053/6250000000000000000000000000 : ℝ)*base79 + (144519055601/24414062500000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (2179379/625000000000000000000 : ℝ)*base90 + (2179379/625000000000000000000 : ℝ)*base92 + (2179379/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (23927581214286740000871/6250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (273509801/100000000000000 : ℝ)*(base1) + (706072939/100000000000000 : ℝ)*(base19) + (859167649/100000000000000 : ℝ)*(base23) + (139055039/100000000000000 : ℝ)*(upper3) + (319158248881333/50000000000000 : ℝ)*(major0) + (319158248881333/50000000000000 : ℝ)*(major1) + (319158248881333/50000000000000 : ℝ)*(major2) + (39203581/2500000000000 : ℝ)*(sp1) + (202346563/20000000000000 : ℝ)*(sp2) + (236786211/50000000000000 : ℝ)*(sp3) + (428474836218309/50000000000000 : ℝ)*(sp4) + (856947124710637/100000000000000 : ℝ)*(sp5) + (856947528026353/100000000000000 : ℝ)*(sp6) + (419682721902521/100000000000000 : ℝ)*(sp7) + (52460433623093/12500000000000 : ℝ)*(f.failure) + (26779668716463/3125000000000 : ℝ)*(f.sum) + (2306147154457/6250000000000000000000000000 : ℝ)*base65 + (52812793558043/12500000000000000000000000000 : ℝ)*base68 + (57130190233043/12500000000000000000000000000 : ℝ)*base70 + (11874614345543/12500000000000000000000000000 : ℝ)*base72 + (6538023070543/6250000000000000000000000000 : ℝ)*base74 + (874077416957/12500000000000000000000000000 : ℝ)*base75 + (47201024820543/12500000000000000000000000000 : ℝ)*base78 + (117236221795543/12500000000000000000000000000 : ℝ)*base80 + (908922023207/6250000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (334601/156250000000000000000 : ℝ)*base90 + (334601/156250000000000000000 : ℝ)*base92 + (334601/156250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1275_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19011843/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (899/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27361/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1275_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1275_s1_0 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-510983529/2500000000 : ℝ)*x 0 + (5673539893/10000000000 : ℝ)*x 1 + (313935861/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (510983529/2500000000 : ℝ)^4235 ≤ (492756291121/4000000000000 : ℝ)^3211 := by
    have hnat : (510983529 : ℕ)^4235*4000000000000^3211 ≤ 492756291121^3211*2500000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      510983529 2500000000 492756291121 4000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5673539893/10000000000 : ℝ)^4235 ≤ (47354064566843/100000000000000 : ℝ)^3211 := by
    have hnat : (5673539893 : ℕ)^4235*100000000000000^3211 ≤ 47354064566843^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5673539893 10000000000 47354064566843 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (313935861/625000000 : ℝ)^4235 ≤ (40327028148467/100000000000000 : ℝ)^3211 := by
    have hnat : (313935861 : ℕ)^4235*100000000000000^3211 ≤ 40327028148467^3211*625000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      313935861 625000000 40327028148467 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-510983529/2500000000 : ℝ), (5673539893/10000000000 : ℝ), (313935861/625000000 : ℝ)] ![(492756291121/4000000000000 : ℝ), (47354064566843/100000000000000 : ℝ), (40327028148467/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-510983529/2500000000 : ℝ)|^4235 ≤ (492756291121/4000000000000 : ℝ)^3211
        have hw : |(-510983529/2500000000 : ℝ)|=(510983529/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5673539893/10000000000 : ℝ)|^4235 ≤ (47354064566843/100000000000000 : ℝ)^3211
        have hw : |(5673539893/10000000000 : ℝ)|=(5673539893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(313935861/625000000 : ℝ)|^4235 ≤ (40327028148467/100000000000000 : ℝ)^3211
        have hw : |(313935861/625000000 : ℝ)|=(313935861/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_s1_1 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (676599669/1250000000 : ℝ)*x 0 + (-59829377/250000000 : ℝ)*x 1 + (627871703/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (676599669/1250000000 : ℝ)^4235 ≤ (44505016383293/100000000000000 : ℝ)^3211 := by
    have hnat : (676599669 : ℕ)^4235*100000000000000^3211 ≤ 44505016383293^3211*1250000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676599669 1250000000 44505016383293 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (59829377/250000000 : ℝ)^4235 ≤ (15167957069451/100000000000000 : ℝ)^3211 := by
    have hnat : (59829377 : ℕ)^4235*100000000000000^3211 ≤ 15167957069451^3211*250000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      59829377 250000000 15167957069451 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (627871703/1250000000 : ℝ)^4235 ≤ (10081756634741/25000000000000 : ℝ)^3211 := by
    have hnat : (627871703 : ℕ)^4235*25000000000000^3211 ≤ 10081756634741^3211*1250000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      627871703 1250000000 10081756634741 25000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(676599669/1250000000 : ℝ), (-59829377/250000000 : ℝ), (627871703/1250000000 : ℝ)] ![(44505016383293/100000000000000 : ℝ), (15167957069451/100000000000000 : ℝ), (10081756634741/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(676599669/1250000000 : ℝ)|^4235 ≤ (44505016383293/100000000000000 : ℝ)^3211
        have hw : |(676599669/1250000000 : ℝ)|=(676599669/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-59829377/250000000 : ℝ)|^4235 ≤ (15167957069451/100000000000000 : ℝ)^3211
        have hw : |(-59829377/250000000 : ℝ)|=(59829377/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(627871703/1250000000 : ℝ)|^4235 ≤ (10081756634741/25000000000000 : ℝ)^3211
        have hw : |(627871703/1250000000 : ℝ)|=(627871703/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_s1_2 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2706398591/5000000000 : ℝ)*x 0 + (200918951/400000000 : ℝ)*x 1 + (-598293777/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2706398591/5000000000 : ℝ)^4235 ≤ (44505014539767/100000000000000 : ℝ)^3211 := by
    have hnat : (2706398591 : ℕ)^4235*100000000000000^3211 ≤ 44505014539767^3211*5000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706398591 5000000000 44505014539767 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (200918951/400000000 : ℝ)^4235 ≤ (20163514068939/50000000000000 : ℝ)^3211 := by
    have hnat : (200918951 : ℕ)^4235*50000000000000^3211 ≤ 20163514068939^3211*400000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200918951 400000000 20163514068939 50000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (598293777/2500000000 : ℝ)^4235 ≤ (1516795730351/10000000000000 : ℝ)^3211 := by
    have hnat : (598293777 : ℕ)^4235*10000000000000^3211 ≤ 1516795730351^3211*2500000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      598293777 2500000000 1516795730351 10000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2706398591/5000000000 : ℝ), (200918951/400000000 : ℝ), (-598293777/2500000000 : ℝ)] ![(44505014539767/100000000000000 : ℝ), (20163514068939/50000000000000 : ℝ), (1516795730351/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2706398591/5000000000 : ℝ)|^4235 ≤ (44505014539767/100000000000000 : ℝ)^3211
        have hw : |(2706398591/5000000000 : ℝ)|=(2706398591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(200918951/400000000 : ℝ)|^4235 ≤ (20163514068939/50000000000000 : ℝ)^3211
        have hw : |(200918951/400000000 : ℝ)|=(200918951/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-598293777/2500000000 : ℝ)|^4235 ≤ (1516795730351/10000000000000 : ℝ)^3211
        have hw : |(-598293777/2500000000 : ℝ)|=(598293777/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_s1_3 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2152053287/5000000000 : ℝ)*x 0 + (3688832243/10000000000 : ℝ)*x 1 + (2508609933/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2152053287/5000000000 : ℝ)^4235 ≤ (32894775792713/100000000000000 : ℝ)^3211 := by
    have hnat : (2152053287 : ℕ)^4235*100000000000000^3211 ≤ 32894775792713^3211*5000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2152053287 5000000000 32894775792713 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3688832243/10000000000 : ℝ)^4235 ≤ (13419556074737/50000000000000 : ℝ)^3211 := by
    have hnat : (3688832243 : ℕ)^4235*50000000000000^3211 ≤ 13419556074737^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3688832243 10000000000 13419556074737 50000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2508609933/5000000000 : ℝ)^4235 ≤ (10066528010843/25000000000000 : ℝ)^3211 := by
    have hnat : (2508609933 : ℕ)^4235*25000000000000^3211 ≤ 10066528010843^3211*5000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2508609933 5000000000 10066528010843 25000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2152053287/5000000000 : ℝ), (3688832243/10000000000 : ℝ), (2508609933/5000000000 : ℝ)] ![(32894775792713/100000000000000 : ℝ), (13419556074737/50000000000000 : ℝ), (10066528010843/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2152053287/5000000000 : ℝ)|^4235 ≤ (32894775792713/100000000000000 : ℝ)^3211
        have hw : |(2152053287/5000000000 : ℝ)|=(2152053287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3688832243/10000000000 : ℝ)|^4235 ≤ (13419556074737/50000000000000 : ℝ)^3211
        have hw : |(3688832243/10000000000 : ℝ)|=(3688832243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2508609933/5000000000 : ℝ)|^4235 ≤ (10066528010843/25000000000000 : ℝ)^3211
        have hw : |(2508609933/5000000000 : ℝ)|=(2508609933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_s1_4 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-511152277/2500000000 : ℝ)*x 0 + (2515782841/5000000000 : ℝ)*x 1 + (1416195861/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (511152277/2500000000 : ℝ)^4235 ≤ (2464854628983/20000000000000 : ℝ)^3211 := by
    have hnat : (511152277 : ℕ)^4235*20000000000000^3211 ≤ 2464854628983^3211*2500000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      511152277 2500000000 2464854628983 20000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2515782841/5000000000 : ℝ)^4235 ≤ (808360625543/2000000000000 : ℝ)^3211 := by
    have hnat : (2515782841 : ℕ)^4235*2000000000000^3211 ≤ 808360625543^3211*5000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2515782841 5000000000 808360625543 2000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1416195861/2500000000 : ℝ)^4235 ≤ (9451539113379/20000000000000 : ℝ)^3211 := by
    have hnat : (1416195861 : ℕ)^4235*20000000000000^3211 ≤ 9451539113379^3211*2500000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1416195861 2500000000 9451539113379 20000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-511152277/2500000000 : ℝ), (2515782841/5000000000 : ℝ), (1416195861/2500000000 : ℝ)] ![(2464854628983/20000000000000 : ℝ), (808360625543/2000000000000 : ℝ), (9451539113379/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-511152277/2500000000 : ℝ)|^4235 ≤ (2464854628983/20000000000000 : ℝ)^3211
        have hw : |(-511152277/2500000000 : ℝ)|=(511152277/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2515782841/5000000000 : ℝ)|^4235 ≤ (808360625543/2000000000000 : ℝ)^3211
        have hw : |(2515782841/5000000000 : ℝ)|=(2515782841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1416195861/2500000000 : ℝ)|^4235 ≤ (9451539113379/20000000000000 : ℝ)^3211
        have hw : |(1416195861/2500000000 : ℝ)|=(1416195861/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_s1_5 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5244972233/10000000000 : ℝ)*x 0 + (-350273049/2000000000 : ℝ)*x 1 + (1132956747/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5244972233/10000000000 : ℝ)^4235 ≤ (42694137225853/100000000000000 : ℝ)^3211 := by
    have hnat : (5244972233 : ℕ)^4235*100000000000000^3211 ≤ 42694137225853^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244972233 10000000000 42694137225853 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (350273049/2000000000 : ℝ)^4235 ≤ (5024081993531/50000000000000 : ℝ)^3211 := by
    have hnat : (350273049 : ℕ)^4235*50000000000000^3211 ≤ 5024081993531^3211*2000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      350273049 2000000000 5024081993531 50000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1132956747/2000000000 : ℝ)^4235 ≤ (47257698768703/100000000000000 : ℝ)^3211 := by
    have hnat : (1132956747 : ℕ)^4235*100000000000000^3211 ≤ 47257698768703^3211*2000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1132956747 2000000000 47257698768703 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5244972233/10000000000 : ℝ), (-350273049/2000000000 : ℝ), (1132956747/2000000000 : ℝ)] ![(42694137225853/100000000000000 : ℝ), (5024081993531/50000000000000 : ℝ), (47257698768703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5244972233/10000000000 : ℝ)|^4235 ≤ (42694137225853/100000000000000 : ℝ)^3211
        have hw : |(5244972233/10000000000 : ℝ)|=(5244972233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-350273049/2000000000 : ℝ)|^4235 ≤ (5024081993531/50000000000000 : ℝ)^3211
        have hw : |(-350273049/2000000000 : ℝ)|=(350273049/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1132956747/2000000000 : ℝ)|^4235 ≤ (47257698768703/100000000000000 : ℝ)^3211
        have hw : |(1132956747/2000000000 : ℝ)|=(1132956747/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_s1_6 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (655621519/1250000000 : ℝ)*x 0 + (2832391747/5000000000 : ℝ)*x 1 + (-1751365711/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (655621519/1250000000 : ℝ)^4235 ≤ (21347068178123/50000000000000 : ℝ)^3211 := by
    have hnat : (655621519 : ℕ)^4235*50000000000000^3211 ≤ 21347068178123^3211*1250000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655621519 1250000000 21347068178123 50000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2832391747/5000000000 : ℝ)^4235 ≤ (47257696117033/100000000000000 : ℝ)^3211 := by
    have hnat : (2832391747 : ℕ)^4235*100000000000000^3211 ≤ 47257696117033^3211*5000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2832391747 5000000000 47257696117033 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1751365711/10000000000 : ℝ)^4235 ≤ (10048167513279/100000000000000 : ℝ)^3211 := by
    have hnat : (1751365711 : ℕ)^4235*100000000000000^3211 ≤ 10048167513279^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1751365711 10000000000 10048167513279 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(655621519/1250000000 : ℝ), (2832391747/5000000000 : ℝ), (-1751365711/10000000000 : ℝ)] ![(21347068178123/50000000000000 : ℝ), (47257696117033/100000000000000 : ℝ), (10048167513279/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(655621519/1250000000 : ℝ)|^4235 ≤ (21347068178123/50000000000000 : ℝ)^3211
        have hw : |(655621519/1250000000 : ℝ)|=(655621519/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2832391747/5000000000 : ℝ)|^4235 ≤ (47257696117033/100000000000000 : ℝ)^3211
        have hw : |(2832391747/5000000000 : ℝ)|=(2832391747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1751365711/10000000000 : ℝ)|^4235 ≤ (10048167513279/100000000000000 : ℝ)^3211
        have hw : |(-1751365711/10000000000 : ℝ)|=(1751365711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_s1_7 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (861096913/2000000000 : ℝ)*x 0 + (999935237/2000000000 : ℝ)*x 1 + (741342349/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (861096913/2000000000 : ℝ)^4235 ≤ (32908666538803/100000000000000 : ℝ)^3211 := by
    have hnat : (861096913 : ℕ)^4235*100000000000000^3211 ≤ 32908666538803^3211*2000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      861096913 2000000000 32908666538803 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (999935237/2000000000 : ℝ)^4235 ≤ (40080516308119/100000000000000 : ℝ)^3211 := by
    have hnat : (999935237 : ℕ)^4235*100000000000000^3211 ≤ 40080516308119^3211*2000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      999935237 2000000000 40080516308119 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (741342349/2000000000 : ℝ)^4235 ≤ (27010817138593/100000000000000 : ℝ)^3211 := by
    have hnat : (741342349 : ℕ)^4235*100000000000000^3211 ≤ 27010817138593^3211*2000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      741342349 2000000000 27010817138593 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(861096913/2000000000 : ℝ), (999935237/2000000000 : ℝ), (741342349/2000000000 : ℝ)] ![(32908666538803/100000000000000 : ℝ), (40080516308119/100000000000000 : ℝ), (27010817138593/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(861096913/2000000000 : ℝ)|^4235 ≤ (32908666538803/100000000000000 : ℝ)^3211
        have hw : |(861096913/2000000000 : ℝ)|=(861096913/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(999935237/2000000000 : ℝ)|^4235 ≤ (40080516308119/100000000000000 : ℝ)^3211
        have hw : |(999935237/2000000000 : ℝ)|=(999935237/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(741342349/2000000000 : ℝ)|^4235 ≤ (27010817138593/100000000000000 : ℝ)^3211
        have hw : |(741342349/2000000000 : ℝ)|=(741342349/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1275_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19011843/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27361/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (899/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (6237/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (19989/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27361/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (899/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27361/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (899/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27361/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (899/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27361/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (899/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27361/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (899/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27361/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (899/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
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
  have hpowlo : (899/100000 : ℝ) ^ (2117/512 : ℝ) ≤ (346159227407/100000000000000000000 : ℝ) := by
    have hpowers : (899/100000 : ℝ)^2117 ≤ (346159227407/100000000000000000000 : ℝ)^512 := by
      have hnat : (899 : ℕ)^2117*100000000000000000000^512 ≤ 346159227407^512*100000^2117 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        899 100000 346159227407 100000000000000000000 2117 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (899/100000 : ℝ)) (X := (346159227407/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2117 512 (by norm_num) hpowers
    exact h
  have hpowhi : (27361/100000 : ℝ) ^ (2117/512 : ℝ) ≤ (470622408394934893/100000000000000000000 : ℝ) := by
    have hpowers : (27361/100000 : ℝ)^2117 ≤ (470622408394934893/100000000000000000000 : ℝ)^512 := by
      have hnat : (27361 : ℕ)^2117*100000000000000000000^512 ≤ 470622408394934893^512*100000^2117 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27361 100000 470622408394934893 100000000000000000000 2117 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27361/100000 : ℝ)) (X := (470622408394934893/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2117 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000346159227407/50000000000000000000 : ℝ) ≤ (5000000008371919/5000000000000000 : ℝ) ^ (2117/512 : ℝ) := by
    have hpowers : (50000000346159227407/50000000000000000000 : ℝ)^512 ≤ (5000000008371919/5000000000000000 : ℝ)^2117 := by
      have hnat : (50000000346159227407 : ℕ)^512*5000000000000000^2117 ≤ 5000000008371919^2117*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000346159227407 50000000000000000000 5000000008371919 5000000000000000 512 2117 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000008371919/5000000000000000 : ℝ)) (X := (50000000346159227407/50000000000000000000 : ℝ)) (by norm_num) 2117 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (1004706227545541623/1000000000000000000 : ℝ) ≤ (2502840460076781/2500000000000000 : ℝ) ^ (2117/512 : ℝ) := by
    have hpowers : (1004706227545541623/1000000000000000000 : ℝ)^512 ≤ (2502840460076781/2500000000000000 : ℝ)^2117 := by
      have hnat : (1004706227545541623 : ℕ)^512*2500000000000000^2117 ≤ 2502840460076781^2117*1000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1004706227545541623 1000000000000000000 2502840460076781 2500000000000000 512 2117 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2502840460076781/2500000000000000 : ℝ)) (X := (1004706227545541623/1000000000000000000 : ℝ)) (by norm_num) 2117 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50470622408394934893/50000000000000000000 : ℝ) ≤ (1002272366387041/1000000000000000 : ℝ) ^ (2117/512 : ℝ) := by
    have hpowers : (50470622408394934893/50000000000000000000 : ℝ)^512 ≤ (1002272366387041/1000000000000000 : ℝ)^2117 := by
      have hnat : (50470622408394934893 : ℕ)^512*1000000000000000^2117 ≤ 1002272366387041^2117*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50470622408394934893 50000000000000000000 1002272366387041 1000000000000000 512 2117 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1002272366387041/1000000000000000 : ℝ)) (X := (50470622408394934893/50000000000000000000 : ℝ)) (by norm_num) 2117 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(346159227407/100000000000000000000 : ℝ) ≤ ((2067184155346161351/2067343750000000000 : ℝ)+2*(5680911781643/1323100000000000 : ℝ)*(899/100000 : ℝ))^(2117/512 : ℝ) := by
    rw [show (2067184155346161351/2067343750000000000 : ℝ)+2*(5680911781643/1323100000000000 : ℝ)*(899/100000 : ℝ)=(5000000008371919/5000000000000000 : ℝ) by norm_num, show 1+2*(346159227407/100000000000000000000 : ℝ)=(50000000346159227407/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(470622408394934893/100000000000000000000 : ℝ)+(346159227407/100000000000000000000 : ℝ) ≤ ((2067184155346161351/2067343750000000000 : ℝ)+(5680911781643/1323100000000000 : ℝ)*((27361/100000 : ℝ)+(899/100000 : ℝ)))^(2117/512 : ℝ) := by
    rw [show (2067184155346161351/2067343750000000000 : ℝ)+(5680911781643/1323100000000000 : ℝ)*((27361/100000 : ℝ)+(899/100000 : ℝ))=(2502840460076781/2500000000000000 : ℝ) by norm_num, show 1+(470622408394934893/100000000000000000000 : ℝ)+(346159227407/100000000000000000000 : ℝ)=(1004706227545541623/1000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(470622408394934893/100000000000000000000 : ℝ) ≤ ((2067184155346161351/2067343750000000000 : ℝ)+2*(5680911781643/1323100000000000 : ℝ)*(27361/100000 : ℝ))^(2117/512 : ℝ) := by
    rw [show (2067184155346161351/2067343750000000000 : ℝ)+2*(5680911781643/1323100000000000 : ℝ)*(27361/100000 : ℝ)=(1002272366387041/1000000000000000 : ℝ) by norm_num, show 1+2*(470622408394934893/100000000000000000000 : ℝ)=(50470622408394934893/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2067184155346161351/2067343750000000000 : ℝ)*(X 1 0+X 2 0)+(5680911781643/1323100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2117/512 : ℝ)) (lo := (899/100000 : ℝ)) (hi := (27361/100000 : ℝ)) (c := (2067184155346161351/2067343750000000000 : ℝ)) (alpha := (5680911781643/1323100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2067184155346161351/2067343750000000000 : ℝ)*(X 0 1+X 2 1)+(5680911781643/1323100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2117/512 : ℝ)) (lo := (899/100000 : ℝ)) (hi := (27361/100000 : ℝ)) (c := (2067184155346161351/2067343750000000000 : ℝ)) (alpha := (5680911781643/1323100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2067184155346161351/2067343750000000000 : ℝ)*(X 0 2+X 1 2)+(5680911781643/1323100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2117/512 : ℝ)) (lo := (899/100000 : ℝ)) (hi := (27361/100000 : ℝ)) (c := (2067184155346161351/2067343750000000000 : ℝ)) (alpha := (5680911781643/1323100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-510983529/2500000000 : ℝ)*X 0 0+(5673539893/10000000000 : ℝ)*X 0 1+(313935861/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((676599669/1250000000 : ℝ)*X 1 0+(-59829377/250000000 : ℝ)*X 1 1+(627871703/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2706398591/5000000000 : ℝ)*X 2 0+(200918951/400000000 : ℝ)*X 2 1+(-598293777/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2152053287/5000000000 : ℝ)*X 0 0+(3688832243/10000000000 : ℝ)*X 0 1+(2508609933/5000000000 : ℝ)*X 0 2+(2152053287/5000000000 : ℝ)*X 1 0+(3688832243/10000000000 : ℝ)*X 1 1+(2508609933/5000000000 : ℝ)*X 1 2+(2152053287/5000000000 : ℝ)*X 2 0+(3688832243/10000000000 : ℝ)*X 2 1+(2508609933/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-511152277/2500000000 : ℝ)*X 0 0+(2515782841/5000000000 : ℝ)*X 0 1+(1416195861/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5244972233/10000000000 : ℝ)*X 1 0+(-350273049/2000000000 : ℝ)*X 1 1+(1132956747/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((655621519/1250000000 : ℝ)*X 2 0+(2832391747/5000000000 : ℝ)*X 2 1+(-1751365711/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((861096913/2000000000 : ℝ)*X 0 0+(999935237/2000000000 : ℝ)*X 0 1+(741342349/2000000000 : ℝ)*X 0 2+(861096913/2000000000 : ℝ)*X 1 0+(999935237/2000000000 : ℝ)*X 1 1+(741342349/2000000000 : ℝ)*X 1 2+(861096913/2000000000 : ℝ)*X 2 0+(999935237/2000000000 : ℝ)*X 2 1+(741342349/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (860790517385636860762930551/103367187500000000000000000000000 : ℝ) := by norm_num
    linear_combination (46364831/50000000000000 : ℝ)*(base1) + (108774501/6250000000000 : ℝ)*(base19) + (1692114989/100000000000000 : ℝ)*(base23) + (195687327/100000000000000 : ℝ)*(upper3) + (10795767/6250000000000 : ℝ)*(upper5) + (1144971696371439/100000000000000 : ℝ)*(major0) + (1144971696371439/100000000000000 : ℝ)*(major1) + (1144971696371439/100000000000000 : ℝ)*(major2) + (1537132230733917/100000000000000 : ℝ)*(sp0) + (768569877513707/50000000000000 : ℝ)*(sp1) + (38428495082611/2500000000000 : ℝ)*(sp2) + (752796834000409/100000000000000 : ℝ)*(sp3) + (374296607/4000000000000 : ℝ)*(sp4) + (93860199/2000000000000 : ℝ)*(sp7) + (376400809870011/50000000000000 : ℝ)*(f.failure) + (1537141495419429/100000000000000 : ℝ)*(f.sum) + (3007392967543/66155000000000000000000000000 : ℝ)*base66 + (1309854449024026197/413468750000000000000000000000000 : ℝ)*base68 + (3682051961571151197/413468750000000000000000000000000 : ℝ)*base70 + (3336767106035151197/413468750000000000000000000000000 : ℝ)*base72 + (28901115947321/33077500000000000000000000000 : ℝ)*base73 + (5178728228357526197/413468750000000000000000000000000 : ℝ)*base76 + (1513310326151197/413468750000000000000000000000000 : ℝ)*base78 + (3351309171200244947/413468750000000000000000000000000 : ℝ)*base80 + (400263152095443/66155000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (5790273/625000000000000000000 : ℝ)*base89 + (5790273/625000000000000000000 : ℝ)*base91 + (5790273/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (956639473263927877620316347/103367187500000000000000000000000 : ℝ) := by norm_num
    linear_combination (8706951/12500000000000 : ℝ)*(base1) + (1818994027/100000000000000 : ℝ)*(base19) + (1762786049/100000000000000 : ℝ)*(base23) + (28862827/12500000000000 : ℝ)*(upper3) + (205826153/100000000000000 : ℝ)*(upper5) + (588162989264413/50000000000000 : ℝ)*(major0) + (588162989264413/50000000000000 : ℝ)*(major1) + (588162989264413/50000000000000 : ℝ)*(major2) + (4395131601/50000000000000 : ℝ)*(sp1) + (3897915509/50000000000000 : ℝ)*(sp2) + (789617565453451/50000000000000 : ℝ)*(sp4) + (789612225997033/50000000000000 : ℝ)*(sp5) + (789612751317113/50000000000000 : ℝ)*(sp6) + (12084633088413/1562500000000 : ℝ)*(sp7) + (19335414682851/2500000000000 : ℝ)*(f.failure) + (789617530625647/50000000000000 : ℝ)*(f.sum) + (44235035662099/33077500000000000000000000000 : ℝ)*base65 + (511936694364788301/206734375000000000000000000000000 : ℝ)*base67 + (245882941030975801/206734375000000000000000000000000 : ℝ)*base69 + (997251837626117949/206734375000000000000000000000000 : ℝ)*base72 + (24764364066167/16538750000000000000000000000 : ℝ)*base73 + (560829749534180449/206734375000000000000000000000000 : ℝ)*base76 + (2564521961800038301/206734375000000000000000000000000 : ℝ)*base77 + (2771609272484632051/206734375000000000000000000000000 : ℝ)*base79 + (6711447837277/4134687500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (120607/31250000000000000000 : ℝ)*base90 + (120607/31250000000000000000 : ℝ)*base92 + (120607/31250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1275_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19011843/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27361/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (899/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6237/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (19989/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1275_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1275_s2_0 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-104512741/500000000 : ℝ)*x 0 + (5499588023/10000000000 : ℝ)*x 1 + (1291842151/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (104512741/500000000 : ℝ)^4235 ≤ (12688439330631/100000000000000 : ℝ)^3211 := by
    have hnat : (104512741 : ℕ)^4235*100000000000000^3211 ≤ 12688439330631^3211*500000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104512741 500000000 12688439330631 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5499588023/10000000000 : ℝ)^4235 ≤ (45448595442807/100000000000000 : ℝ)^3211 := by
    have hnat : (5499588023 : ℕ)^4235*100000000000000^3211 ≤ 45448595442807^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5499588023 10000000000 45448595442807 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1291842151/2500000000 : ℝ)^4235 ≤ (41862965215931/100000000000000 : ℝ)^3211 := by
    have hnat : (1291842151 : ℕ)^4235*100000000000000^3211 ≤ 41862965215931^3211*2500000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1291842151 2500000000 41862965215931 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-104512741/500000000 : ℝ), (5499588023/10000000000 : ℝ), (1291842151/2500000000 : ℝ)] ![(12688439330631/100000000000000 : ℝ), (45448595442807/100000000000000 : ℝ), (41862965215931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-104512741/500000000 : ℝ)|^4235 ≤ (12688439330631/100000000000000 : ℝ)^3211
        have hw : |(-104512741/500000000 : ℝ)|=(104512741/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5499588023/10000000000 : ℝ)|^4235 ≤ (45448595442807/100000000000000 : ℝ)^3211
        have hw : |(5499588023/10000000000 : ℝ)|=(5499588023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1291842151/2500000000 : ℝ)|^4235 ≤ (41862965215931/100000000000000 : ℝ)^3211
        have hw : |(1291842151/2500000000 : ℝ)|=(1291842151/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_s2_1 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (268543621/500000000 : ℝ)*x 0 + (-1131301301/5000000000 : ℝ)*x 1 + (1291842433/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268543621/500000000 : ℝ)^4235 ≤ (11012733403031/25000000000000 : ℝ)^3211 := by
    have hnat : (268543621 : ℕ)^4235*25000000000000^3211 ≤ 11012733403031^3211*500000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268543621 500000000 11012733403031 25000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1131301301/5000000000 : ℝ)^4235 ≤ (440190284637/3125000000000 : ℝ)^3211 := by
    have hnat : (1131301301 : ℕ)^4235*3125000000000^3211 ≤ 440190284637^3211*5000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1131301301 5000000000 440190284637 3125000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1291842433/2500000000 : ℝ)^4235 ≤ (41862977268587/100000000000000 : ℝ)^3211 := by
    have hnat : (1291842433 : ℕ)^4235*100000000000000^3211 ≤ 41862977268587^3211*2500000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1291842433 2500000000 41862977268587 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268543621/500000000 : ℝ), (-1131301301/5000000000 : ℝ), (1291842433/2500000000 : ℝ)] ![(11012733403031/25000000000000 : ℝ), (440190284637/3125000000000 : ℝ), (41862977268587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268543621/500000000 : ℝ)|^4235 ≤ (11012733403031/25000000000000 : ℝ)^3211
        have hw : |(268543621/500000000 : ℝ)|=(268543621/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1131301301/5000000000 : ℝ)|^4235 ≤ (440190284637/3125000000000 : ℝ)^3211
        have hw : |(-1131301301/5000000000 : ℝ)|=(1131301301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1291842433/2500000000 : ℝ)|^4235 ≤ (41862977268587/100000000000000 : ℝ)^3211
        have hw : |(1291842433/2500000000 : ℝ)|=(1291842433/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_s2_2 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (537087307/1000000000 : ℝ)*x 0 + (2583684421/5000000000 : ℝ)*x 1 + (-2262602903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537087307/1000000000 : ℝ)^4235 ≤ (22025470321721/50000000000000 : ℝ)^3211 := by
    have hnat : (537087307 : ℕ)^4235*50000000000000^3211 ≤ 22025470321721^3211*1000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537087307 1000000000 22025470321721 50000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2583684421/5000000000 : ℝ)^4235 ≤ (10465741939739/25000000000000 : ℝ)^3211 := by
    have hnat : (2583684421 : ℕ)^4235*25000000000000^3211 ≤ 10465741939739^3211*5000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2583684421 5000000000 10465741939739 25000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2262602903/10000000000 : ℝ)^4235 ≤ (1408609157989/10000000000000 : ℝ)^3211 := by
    have hnat : (2262602903 : ℕ)^4235*10000000000000^3211 ≤ 1408609157989^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2262602903 10000000000 1408609157989 10000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537087307/1000000000 : ℝ), (2583684421/5000000000 : ℝ), (-2262602903/10000000000 : ℝ)] ![(22025470321721/50000000000000 : ℝ), (10465741939739/25000000000000 : ℝ), (1408609157989/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537087307/1000000000 : ℝ)|^4235 ≤ (22025470321721/50000000000000 : ℝ)^3211
        have hw : |(537087307/1000000000 : ℝ)|=(537087307/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2583684421/5000000000 : ℝ)|^4235 ≤ (10465741939739/25000000000000 : ℝ)^3211
        have hw : |(2583684421/5000000000 : ℝ)|=(2583684421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2262602903/10000000000 : ℝ)|^4235 ≤ (1408609157989/10000000000000 : ℝ)^3211
        have hw : |(-2262602903/10000000000 : ℝ)|=(2262602903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_s2_3 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4336237627/10000000000 : ℝ)*x 0 + (4009794091/10000000000 : ℝ)*x 1 + (1172039071/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4336237627/10000000000 : ℝ)^4235 ≤ (16609519532417/50000000000000 : ℝ)^3211 := by
    have hnat : (4336237627 : ℕ)^4235*50000000000000^3211 ≤ 16609519532417^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4336237627 10000000000 16609519532417 50000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4009794091/10000000000 : ℝ)^4235 ≤ (936281034347/3125000000000 : ℝ)^3211 := by
    have hnat : (4009794091 : ℕ)^4235*3125000000000^3211 ≤ 936281034347^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4009794091 10000000000 936281034347 3125000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1172039071/2500000000 : ℝ)^4235 ≤ (18409983913323/50000000000000 : ℝ)^3211 := by
    have hnat : (1172039071 : ℕ)^4235*50000000000000^3211 ≤ 18409983913323^3211*2500000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1172039071 2500000000 18409983913323 50000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4336237627/10000000000 : ℝ), (4009794091/10000000000 : ℝ), (1172039071/2500000000 : ℝ)] ![(16609519532417/50000000000000 : ℝ), (936281034347/3125000000000 : ℝ), (18409983913323/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4336237627/10000000000 : ℝ)|^4235 ≤ (16609519532417/50000000000000 : ℝ)^3211
        have hw : |(4336237627/10000000000 : ℝ)|=(4336237627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4009794091/10000000000 : ℝ)|^4235 ≤ (936281034347/3125000000000 : ℝ)^3211
        have hw : |(4009794091/10000000000 : ℝ)|=(4009794091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1172039071/2500000000 : ℝ)|^4235 ≤ (18409983913323/50000000000000 : ℝ)^3211
        have hw : |(1172039071/2500000000 : ℝ)|=(1172039071/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_s2_4 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1045171871/5000000000 : ℝ)*x 0 + (1033923819/2000000000 : ℝ)*x 1 + (5497316189/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1045171871/5000000000 : ℝ)^4235 ≤ (12689151255643/100000000000000 : ℝ)^3211 := by
    have hnat : (1045171871 : ℕ)^4235*100000000000000^3211 ≤ 12689151255643^3211*5000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045171871 5000000000 12689151255643 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1033923819/2000000000 : ℝ)^4235 ≤ (10471753333417/25000000000000 : ℝ)^3211 := by
    have hnat : (1033923819 : ℕ)^4235*25000000000000^3211 ≤ 10471753333417^3211*2000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033923819 2000000000 10471753333417 25000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5497316189/10000000000 : ℝ)^4235 ≤ (5677979424917/12500000000000 : ℝ)^3211 := by
    have hnat : (5497316189 : ℕ)^4235*12500000000000^3211 ≤ 5677979424917^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5497316189 10000000000 5677979424917 12500000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1045171871/5000000000 : ℝ), (1033923819/2000000000 : ℝ), (5497316189/10000000000 : ℝ)] ![(12689151255643/100000000000000 : ℝ), (10471753333417/25000000000000 : ℝ), (5677979424917/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1045171871/5000000000 : ℝ)|^4235 ≤ (12689151255643/100000000000000 : ℝ)^3211
        have hw : |(-1045171871/5000000000 : ℝ)|=(1045171871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1033923819/2000000000 : ℝ)|^4235 ≤ (10471753333417/25000000000000 : ℝ)^3211
        have hw : |(1033923819/2000000000 : ℝ)|=(1033923819/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5497316189/10000000000 : ℝ)|^4235 ≤ (5677979424917/12500000000000 : ℝ)^3211
        have hw : |(5497316189/10000000000 : ℝ)|=(5497316189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_s2_5 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2642948441/5000000000 : ℝ)*x 0 + (-966327723/5000000000 : ℝ)*x 1 + (2748658177/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642948441/5000000000 : ℝ)^4235 ≤ (4313404552753/10000000000000 : ℝ)^3211 := by
    have hnat : (2642948441 : ℕ)^4235*10000000000000^3211 ≤ 4313404552753^3211*5000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642948441 5000000000 4313404552753 10000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (966327723/5000000000 : ℝ)^4235 ≤ (11442117260461/100000000000000 : ℝ)^3211 := by
    have hnat : (966327723 : ℕ)^4235*100000000000000^3211 ≤ 11442117260461^3211*5000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      966327723 5000000000 11442117260461 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2748658177/5000000000 : ℝ)^4235 ≤ (709747456211/1562500000000 : ℝ)^3211 := by
    have hnat : (2748658177 : ℕ)^4235*1562500000000^3211 ≤ 709747456211^3211*5000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2748658177 5000000000 709747456211 1562500000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642948441/5000000000 : ℝ), (-966327723/5000000000 : ℝ), (2748658177/5000000000 : ℝ)] ![(4313404552753/10000000000000 : ℝ), (11442117260461/100000000000000 : ℝ), (709747456211/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642948441/5000000000 : ℝ)|^4235 ≤ (4313404552753/10000000000000 : ℝ)^3211
        have hw : |(2642948441/5000000000 : ℝ)|=(2642948441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-966327723/5000000000 : ℝ)|^4235 ≤ (11442117260461/100000000000000 : ℝ)^3211
        have hw : |(-966327723/5000000000 : ℝ)|=(966327723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2748658177/5000000000 : ℝ)|^4235 ≤ (709747456211/1562500000000 : ℝ)^3211
        have hw : |(2748658177/5000000000 : ℝ)|=(2748658177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_s2_6 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (211435883/400000000 : ℝ)*x 0 + (5497316199/10000000000 : ℝ)*x 1 + (-386531079/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211435883/400000000 : ℝ)^4235 ≤ (431340476047/1000000000000 : ℝ)^3211 := by
    have hnat : (211435883 : ℕ)^4235*1000000000000^3211 ≤ 431340476047^3211*400000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211435883 400000000 431340476047 1000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5497316199/10000000000 : ℝ)^4235 ≤ (11355958877079/25000000000000 : ℝ)^3211 := by
    have hnat : (5497316199 : ℕ)^4235*25000000000000^3211 ≤ 11355958877079^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5497316199 10000000000 11355958877079 25000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (386531079/2000000000 : ℝ)^4235 ≤ (11442116862229/100000000000000 : ℝ)^3211 := by
    have hnat : (386531079 : ℕ)^4235*100000000000000^3211 ≤ 11442116862229^3211*2000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      386531079 2000000000 11442116862229 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(211435883/400000000 : ℝ), (5497316199/10000000000 : ℝ), (-386531079/2000000000 : ℝ)] ![(431340476047/1000000000000 : ℝ), (11355958877079/25000000000000 : ℝ), (11442116862229/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(211435883/400000000 : ℝ)|^4235 ≤ (431340476047/1000000000000 : ℝ)^3211
        have hw : |(211435883/400000000 : ℝ)|=(211435883/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5497316199/10000000000 : ℝ)|^4235 ≤ (11355958877079/25000000000000 : ℝ)^3211
        have hw : |(5497316199/10000000000 : ℝ)|=(5497316199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-386531079/2000000000 : ℝ)|^4235 ≤ (11442116862229/100000000000000 : ℝ)^3211
        have hw : |(-386531079/2000000000 : ℝ)|=(386531079/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_s2_7 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4336419773/10000000000 : ℝ)*x 0 + (2341780207/5000000000 : ℝ)*x 1 + (2007218241/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4336419773/10000000000 : ℝ)^4235 ≤ (8305219863479/25000000000000 : ℝ)^3211 := by
    have hnat : (4336419773 : ℕ)^4235*25000000000000^3211 ≤ 8305219863479^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4336419773 10000000000 8305219863479 25000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2341780207/5000000000 : ℝ)^4235 ≤ (36772369217543/100000000000000 : ℝ)^3211 := by
    have hnat : (2341780207 : ℕ)^4235*100000000000000^3211 ≤ 36772369217543^3211*5000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2341780207 5000000000 36772369217543 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2007218241/5000000000 : ℝ)^4235 ≤ (15003375658567/50000000000000 : ℝ)^3211 := by
    have hnat : (2007218241 : ℕ)^4235*50000000000000^3211 ≤ 15003375658567^3211*5000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2007218241 5000000000 15003375658567 50000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4336419773/10000000000 : ℝ), (2341780207/5000000000 : ℝ), (2007218241/5000000000 : ℝ)] ![(8305219863479/25000000000000 : ℝ), (36772369217543/100000000000000 : ℝ), (15003375658567/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4336419773/10000000000 : ℝ)|^4235 ≤ (8305219863479/25000000000000 : ℝ)^3211
        have hw : |(4336419773/10000000000 : ℝ)|=(4336419773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2341780207/5000000000 : ℝ)|^4235 ≤ (36772369217543/100000000000000 : ℝ)^3211
        have hw : |(2341780207/5000000000 : ℝ)|=(2341780207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2007218241/5000000000 : ℝ)|^4235 ≤ (15003375658567/50000000000000 : ℝ)^3211
        have hw : |(2007218241/5000000000 : ℝ)|=(2007218241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1275_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19011843/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19989/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6237/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9377/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16397/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (19989/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6237/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (19989/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6237/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (19989/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6237/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (19989/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6237/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (19989/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6237/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (19989/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6237/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6237/100000 : ℝ) ^ (2117/512 : ℝ) ≤ (520567599179307/50000000000000000000 : ℝ) := by
    have hpowers : (6237/100000 : ℝ)^2117 ≤ (520567599179307/50000000000000000000 : ℝ)^512 := by
      have hnat : (6237 : ℕ)^2117*50000000000000000000^512 ≤ 520567599179307^512*100000^2117 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6237 100000 520567599179307 50000000000000000000 2117 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6237/100000 : ℝ)) (X := (520567599179307/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2117 512 (by norm_num) hpowers
    exact h
  have hpowhi : (19989/100000 : ℝ) ^ (2117/512 : ℝ) ≤ (64254707000467/50000000000000000 : ℝ) := by
    have hpowers : (19989/100000 : ℝ)^2117 ≤ (64254707000467/50000000000000000 : ℝ)^512 := by
      have hnat : (19989 : ℕ)^2117*50000000000000000^512 ≤ 64254707000467^512*100000^2117 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19989 100000 64254707000467 50000000000000000 2117 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19989/100000 : ℝ)) (X := (64254707000467/50000000000000000 : ℝ)) (by norm_num) (by norm_num) 2117 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000520567599179307/25000000000000000000 : ℝ) ≤ (10000050359661217/10000000000000000 : ℝ) ^ (2117/512 : ℝ) := by
    have hpowers : (25000520567599179307/25000000000000000000 : ℝ)^512 ≤ (10000050359661217/10000000000000000 : ℝ)^2117 := by
      have hnat : (25000520567599179307 : ℕ)^512*10000000000000000^2117 ≤ 10000050359661217^2117*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000520567599179307 25000000000000000000 10000050359661217 10000000000000000 512 2117 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000050359661217/10000000000000000 : ℝ)) (X := (25000520567599179307/25000000000000000000 : ℝ)) (by norm_num) 2117 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50064775274599646307/50000000000000000000 : ℝ) ≤ (5001565832115767/5000000000000000 : ℝ) ^ (2117/512 : ℝ) := by
    have hpowers : (50064775274599646307/50000000000000000000 : ℝ)^512 ≤ (5001565832115767/5000000000000000 : ℝ)^2117 := by
      have hnat : (50064775274599646307 : ℕ)^512*5000000000000000^2117 ≤ 5001565832115767^2117*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50064775274599646307 50000000000000000000 5001565832115767 5000000000000000 512 2117 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001565832115767/5000000000000000 : ℝ)) (X := (50064775274599646307/50000000000000000000 : ℝ)) (by norm_num) 2117 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25064254707000467/25000000000000000 : ℝ) ≤ (10006212968801851/10000000000000000 : ℝ) ^ (2117/512 : ℝ) := by
    have hpowers : (25064254707000467/25000000000000000 : ℝ)^512 ≤ (10006212968801851/10000000000000000 : ℝ)^2117 := by
      have hnat : (25064254707000467 : ℕ)^512*10000000000000000^2117 ≤ 10006212968801851^2117*25000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25064254707000467 25000000000000000 10006212968801851 10000000000000000 512 2117 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006212968801851/10000000000000000 : ℝ)) (X := (25064254707000467/25000000000000000 : ℝ)) (by norm_num) 2117 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(520567599179307/50000000000000000000 : ℝ) ≤ ((7637903130713940107/7640000000000000000 : ℝ)+2*(1027101523439/458400000000000 : ℝ)*(6237/100000 : ℝ))^(2117/512 : ℝ) := by
    rw [show (7637903130713940107/7640000000000000000 : ℝ)+2*(1027101523439/458400000000000 : ℝ)*(6237/100000 : ℝ)=(10000050359661217/10000000000000000 : ℝ) by norm_num, show 1+2*(520567599179307/50000000000000000000 : ℝ)=(25000520567599179307/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(64254707000467/50000000000000000 : ℝ)+(520567599179307/50000000000000000000 : ℝ) ≤ ((7637903130713940107/7640000000000000000 : ℝ)+(1027101523439/458400000000000 : ℝ)*((19989/100000 : ℝ)+(6237/100000 : ℝ)))^(2117/512 : ℝ) := by
    rw [show (7637903130713940107/7640000000000000000 : ℝ)+(1027101523439/458400000000000 : ℝ)*((19989/100000 : ℝ)+(6237/100000 : ℝ))=(5001565832115767/5000000000000000 : ℝ) by norm_num, show 1+(64254707000467/50000000000000000 : ℝ)+(520567599179307/50000000000000000000 : ℝ)=(50064775274599646307/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(64254707000467/50000000000000000 : ℝ) ≤ ((7637903130713940107/7640000000000000000 : ℝ)+2*(1027101523439/458400000000000 : ℝ)*(19989/100000 : ℝ))^(2117/512 : ℝ) := by
    rw [show (7637903130713940107/7640000000000000000 : ℝ)+2*(1027101523439/458400000000000 : ℝ)*(19989/100000 : ℝ)=(10006212968801851/10000000000000000 : ℝ) by norm_num, show 1+2*(64254707000467/50000000000000000 : ℝ)=(25064254707000467/25000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7637903130713940107/7640000000000000000 : ℝ)*(X 1 0+X 2 0)+(1027101523439/458400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2117/512 : ℝ)) (lo := (6237/100000 : ℝ)) (hi := (19989/100000 : ℝ)) (c := (7637903130713940107/7640000000000000000 : ℝ)) (alpha := (1027101523439/458400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7637903130713940107/7640000000000000000 : ℝ)*(X 0 1+X 2 1)+(1027101523439/458400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2117/512 : ℝ)) (lo := (6237/100000 : ℝ)) (hi := (19989/100000 : ℝ)) (c := (7637903130713940107/7640000000000000000 : ℝ)) (alpha := (1027101523439/458400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7637903130713940107/7640000000000000000 : ℝ)*(X 0 2+X 1 2)+(1027101523439/458400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2117/512 : ℝ)) (lo := (6237/100000 : ℝ)) (hi := (19989/100000 : ℝ)) (c := (7637903130713940107/7640000000000000000 : ℝ)) (alpha := (1027101523439/458400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-104512741/500000000 : ℝ)*X 0 0+(5499588023/10000000000 : ℝ)*X 0 1+(1291842151/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((268543621/500000000 : ℝ)*X 1 0+(-1131301301/5000000000 : ℝ)*X 1 1+(1291842433/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((537087307/1000000000 : ℝ)*X 2 0+(2583684421/5000000000 : ℝ)*X 2 1+(-2262602903/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4336237627/10000000000 : ℝ)*X 0 0+(4009794091/10000000000 : ℝ)*X 0 1+(1172039071/2500000000 : ℝ)*X 0 2+(4336237627/10000000000 : ℝ)*X 1 0+(4009794091/10000000000 : ℝ)*X 1 1+(1172039071/2500000000 : ℝ)*X 1 2+(4336237627/10000000000 : ℝ)*X 2 0+(4009794091/10000000000 : ℝ)*X 2 1+(1172039071/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1045171871/5000000000 : ℝ)*X 0 0+(1033923819/2000000000 : ℝ)*X 0 1+(5497316189/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2642948441/5000000000 : ℝ)*X 1 0+(-966327723/5000000000 : ℝ)*X 1 1+(2748658177/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((211435883/400000000 : ℝ)*X 2 0+(5497316199/10000000000 : ℝ)*X 2 1+(-386531079/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4336419773/10000000000 : ℝ)*X 0 0+(2341780207/5000000000 : ℝ)*X 0 1+(2007218241/5000000000 : ℝ)*X 0 2+(4336419773/10000000000 : ℝ)*X 1 0+(2341780207/5000000000 : ℝ)*X 1 1+(2007218241/5000000000 : ℝ)*X 1 2+(4336419773/10000000000 : ℝ)*X 2 0+(2341780207/5000000000 : ℝ)*X 2 1+(2007218241/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (62890358284835809873671849/11937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (232126299/12500000000000 : ℝ)*(base19) + (1092762917/50000000000000 : ℝ)*(base23) + (11636003/2500000000000 : ℝ)*(upper3) + (4803833/25000000000000 : ℝ)*(upper4) + (19593413/6250000000000 : ℝ)*(upper5) + (140133749308269/6250000000000 : ℝ)*(major0) + (140133749308269/6250000000000 : ℝ)*(major1) + (140133749308269/6250000000000 : ℝ)*(major2) + (1505041598239267/50000000000000 : ℝ)*(sp0) + (3010104722708377/100000000000000 : ℝ)*(sp1) + (602020878838587/20000000000000 : ℝ)*(sp2) + (147415486478471/10000000000000 : ℝ)*(sp3) + (5845810059/25000000000000 : ℝ)*(sp4) + (4589437761/25000000000000 : ℝ)*(sp7) + (737086611267877/50000000000000 : ℝ)*(f.failure) + (301010657971877/10000000000000 : ℝ)*(f.sum) + (63156088441/59687500000000000000000000 : ℝ)*base66 + (385821691931305217/47750000000000000000000000000000 : ℝ)*base68 + (488088175396305217/47750000000000000000000000000000 : ℝ)*base70 + (152702037394805217/47750000000000000000000000000000 : ℝ)*base72 + (660192856817/477500000000000000000000000 : ℝ)*base73 + (477684301492305217/47750000000000000000000000000000 : ℝ)*base76 + (594079072147305217/47750000000000000000000000000000 : ℝ)*base78 + (106259889446694783/47750000000000000000000000000000 : ℝ)*base79 + (2809407377171/955000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (8467311/625000000000000000000 : ℝ)*base89 + (8467311/625000000000000000000 : ℝ)*base91 + (8467311/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (30408917619619396855777/7640000000000000000000000000 : ℝ) := by norm_num
    linear_combination (145367871/20000000000000 : ℝ)*(base19) + (1003313341/100000000000000 : ℝ)*(base23) + (17816681/12500000000000 : ℝ)*(upper3) + (14272023/25000000000000 : ℝ)*(lower4) + (7022503/25000000000000 : ℝ)*(upper5) + (2273044463550863/100000000000000 : ℝ)*(major0) + (2273044463550863/100000000000000 : ℝ)*(major1) + (2273044463550863/100000000000000 : ℝ)*(major2) + (111329873/1562500000000 : ℝ)*(sp1) + (10674007077/100000000000000 : ℝ)*(sp2) + (762899086497431/25000000000000 : ℝ)*(sp4) + (3051588494038497/100000000000000 : ℝ)*(sp5) + (1525792334334653/50000000000000 : ℝ)*(sp6) + (1494492448437839/100000000000000 : ℝ)*(sp7) + (1494492448437839/100000000000000 : ℝ)*(f.failure) + (762899086497431/25000000000000 : ℝ)*(f.sum) + (68123450952023/22920000000000000000000000000 : ℝ)*base66 + (6656012402291337023/2292000000000000000000000000000000 : ℝ)*base67 + (3016683953244662977/2292000000000000000000000000000000 : ℝ)*base70 + (2703465896088662977/2292000000000000000000000000000000 : ℝ)*base72 + (15538527937057/22920000000000000000000000000 : ℝ)*base73 + (4340305715796662977/2292000000000000000000000000000000 : ℝ)*base76 + (1979640766079337023/2292000000000000000000000000000000 : ℝ)*base77 + (9495793645475337023/2292000000000000000000000000000000 : ℝ)*base79 + (122558649393383/22920000000000000000000000000 : ℝ)*base82 + (2827277/1250000000000000000000 : ℝ)*base89 + (2827277/1250000000000000000000 : ℝ)*base91 + (2827277/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1275_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19011843/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19989/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6237/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9377/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16397/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1275_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1275_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19011843/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9377/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16397/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1275_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1275_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1275_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19011843/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9377/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16397/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1275_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
