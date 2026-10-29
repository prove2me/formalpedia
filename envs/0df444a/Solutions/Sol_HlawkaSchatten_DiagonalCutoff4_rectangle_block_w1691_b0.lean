-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1691_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:39:25.032685+00:00
-- url     : https://prove2.me/submissions/d9211f3f-64c4-42cf-9ab5-3e9196a6535f

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
theorem support_rectangle_w1691_s0_0 (p : ℝ) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1394455043/10000000000 : ℝ)*x 0 + (5737529569/10000000000 : ℝ)*x 1 + (617379371/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1394455043/10000000000 : ℝ)^5151 ≤ (427643971649/5000000000000 : ℝ)^4127 := by
    have hnat : (1394455043 : ℕ)^5151*5000000000000^4127 ≤ 427643971649^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1394455043 10000000000 427643971649 5000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5737529569/10000000000 : ℝ)^5151 ≤ (9997450248301/20000000000000 : ℝ)^4127 := by
    have hnat : (5737529569 : ℕ)^5151*20000000000000^4127 ≤ 9997450248301^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5737529569 10000000000 9997450248301 20000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (617379371/1250000000 : ℝ)^5151 ≤ (8291973861603/20000000000000 : ℝ)^4127 := by
    have hnat : (617379371 : ℕ)^5151*20000000000000^4127 ≤ 8291973861603^4127*1250000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      617379371 1250000000 8291973861603 20000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5151/1024 : ℝ)) 5151 4127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1394455043/10000000000 : ℝ), (5737529569/10000000000 : ℝ), (617379371/1250000000 : ℝ)] ![(427643971649/5000000000000 : ℝ), (9997450248301/20000000000000 : ℝ), (8291973861603/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1394455043/10000000000 : ℝ)|^5151 ≤ (427643971649/5000000000000 : ℝ)^4127
        have hw : |(-1394455043/10000000000 : ℝ)|=(1394455043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5737529569/10000000000 : ℝ)|^5151 ≤ (9997450248301/20000000000000 : ℝ)^4127
        have hw : |(5737529569/10000000000 : ℝ)|=(5737529569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(617379371/1250000000 : ℝ)|^5151 ≤ (8291973861603/20000000000000 : ℝ)^4127
        have hw : |(617379371/1250000000 : ℝ)|=(617379371/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1691_s0_1 (p : ℝ) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (541786721/1000000000 : ℝ)*x 0 + (-914824453/5000000000 : ℝ)*x 1 + (4939036119/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (541786721/1000000000 : ℝ)^5151 ≤ (23267798148651/50000000000000 : ℝ)^4127 := by
    have hnat : (541786721 : ℕ)^5151*50000000000000^4127 ≤ 23267798148651^4127*1000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541786721 1000000000 23267798148651 50000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (914824453/5000000000 : ℝ)^5151 ≤ (6002261158301/50000000000000 : ℝ)^4127 := by
    have hnat : (914824453 : ℕ)^5151*50000000000000^4127 ≤ 6002261158301^4127*5000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      914824453 5000000000 6002261158301 50000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4939036119/10000000000 : ℝ)^5151 ≤ (5182485170901/12500000000000 : ℝ)^4127 := by
    have hnat : (4939036119 : ℕ)^5151*12500000000000^4127 ≤ 5182485170901^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4939036119 10000000000 5182485170901 12500000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5151/1024 : ℝ)) 5151 4127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(541786721/1000000000 : ℝ), (-914824453/5000000000 : ℝ), (4939036119/10000000000 : ℝ)] ![(23267798148651/50000000000000 : ℝ), (6002261158301/50000000000000 : ℝ), (5182485170901/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(541786721/1000000000 : ℝ)|^5151 ≤ (23267798148651/50000000000000 : ℝ)^4127
        have hw : |(541786721/1000000000 : ℝ)|=(541786721/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-914824453/5000000000 : ℝ)|^5151 ≤ (6002261158301/50000000000000 : ℝ)^4127
        have hw : |(-914824453/5000000000 : ℝ)|=(914824453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4939036119/10000000000 : ℝ)|^5151 ≤ (5182485170901/12500000000000 : ℝ)^4127
        have hw : |(4939036119/10000000000 : ℝ)|=(4939036119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1691_s0_2 (p : ℝ) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5417869541/10000000000 : ℝ)*x 0 + (4939035067/10000000000 : ℝ)*x 1 + (-914823601/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5417869541/10000000000 : ℝ)^5151 ≤ (46535621286729/100000000000000 : ℝ)^4127 := by
    have hnat : (5417869541 : ℕ)^5151*100000000000000^4127 ≤ 46535621286729^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417869541 10000000000 46535621286729 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4939035067/10000000000 : ℝ)^5151 ≤ (10364967586313/25000000000000 : ℝ)^4127 := by
    have hnat : (4939035067 : ℕ)^5151*25000000000000^4127 ≤ 10364967586313^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4939035067 10000000000 10364967586313 25000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (914823601/5000000000 : ℝ)^5151 ≤ (12004508362441/100000000000000 : ℝ)^4127 := by
    have hnat : (914823601 : ℕ)^5151*100000000000000^4127 ≤ 12004508362441^4127*5000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      914823601 5000000000 12004508362441 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5151/1024 : ℝ)) 5151 4127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5417869541/10000000000 : ℝ), (4939035067/10000000000 : ℝ), (-914823601/5000000000 : ℝ)] ![(46535621286729/100000000000000 : ℝ), (10364967586313/25000000000000 : ℝ), (12004508362441/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5417869541/10000000000 : ℝ)|^5151 ≤ (46535621286729/100000000000000 : ℝ)^4127
        have hw : |(5417869541/10000000000 : ℝ)|=(5417869541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4939035067/10000000000 : ℝ)|^5151 ≤ (10364967586313/25000000000000 : ℝ)^4127
        have hw : |(4939035067/10000000000 : ℝ)|=(4939035067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-914823601/5000000000 : ℝ)|^5151 ≤ (12004508362441/100000000000000 : ℝ)^4127
        have hw : |(-914823601/5000000000 : ℝ)|=(914823601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1691_s0_3 (p : ℝ) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (405576879/1000000000 : ℝ)*x 0 + (121920423/400000000 : ℝ)*x 1 + (5262956927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (405576879/1000000000 : ℝ)^5151 ≤ (16210539955509/50000000000000 : ℝ)^4127 := by
    have hnat : (405576879 : ℕ)^5151*50000000000000^4127 ≤ 16210539955509^4127*1000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      405576879 1000000000 16210539955509 50000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (121920423/400000000 : ℝ)^5151 ≤ (22698101859587/100000000000000 : ℝ)^4127 := by
    have hnat : (121920423 : ℕ)^5151*100000000000000^4127 ≤ 22698101859587^4127*400000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      121920423 400000000 22698101859587 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5262956927/10000000000 : ℝ)^5151 ≤ (8976163642209/20000000000000 : ℝ)^4127 := by
    have hnat : (5262956927 : ℕ)^5151*20000000000000^4127 ≤ 8976163642209^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262956927 10000000000 8976163642209 20000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5151/1024 : ℝ)) 5151 4127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(405576879/1000000000 : ℝ), (121920423/400000000 : ℝ), (5262956927/10000000000 : ℝ)] ![(16210539955509/50000000000000 : ℝ), (22698101859587/100000000000000 : ℝ), (8976163642209/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(405576879/1000000000 : ℝ)|^5151 ≤ (16210539955509/50000000000000 : ℝ)^4127
        have hw : |(405576879/1000000000 : ℝ)|=(405576879/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(121920423/400000000 : ℝ)|^5151 ≤ (22698101859587/100000000000000 : ℝ)^4127
        have hw : |(121920423/400000000 : ℝ)|=(121920423/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5262956927/10000000000 : ℝ)|^5151 ≤ (8976163642209/20000000000000 : ℝ)^4127
        have hw : |(5262956927/10000000000 : ℝ)|=(5262956927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1691_s0_4 (p : ℝ) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-43638957/312500000 : ℝ)*x 0 + (4959057773/10000000000 : ℝ)*x 1 + (357301019/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (43638957/312500000 : ℝ)^5151 ≤ (2142032094553/25000000000000 : ℝ)^4127 := by
    have hnat : (43638957 : ℕ)^5151*25000000000000^4127 ≤ 2142032094553^4127*312500000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43638957 312500000 2142032094553 25000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4959057773/10000000000 : ℝ)^5151 ≤ (1041743912961/2500000000000 : ℝ)^4127 := by
    have hnat : (4959057773 : ℕ)^5151*2500000000000^4127 ≤ 1041743912961^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4959057773 10000000000 1041743912961 2500000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (357301019/625000000 : ℝ)^5151 ≤ (24881057546791/50000000000000 : ℝ)^4127 := by
    have hnat : (357301019 : ℕ)^5151*50000000000000^4127 ≤ 24881057546791^4127*625000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      357301019 625000000 24881057546791 50000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5151/1024 : ℝ)) 5151 4127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-43638957/312500000 : ℝ), (4959057773/10000000000 : ℝ), (357301019/625000000 : ℝ)] ![(2142032094553/25000000000000 : ℝ), (1041743912961/2500000000000 : ℝ), (24881057546791/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-43638957/312500000 : ℝ)|^5151 ≤ (2142032094553/25000000000000 : ℝ)^4127
        have hw : |(-43638957/312500000 : ℝ)|=(43638957/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4959057773/10000000000 : ℝ)|^5151 ≤ (1041743912961/2500000000000 : ℝ)^4127
        have hw : |(4959057773/10000000000 : ℝ)|=(4959057773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(357301019/625000000 : ℝ)|^5151 ≤ (24881057546791/50000000000000 : ℝ)^4127
        have hw : |(357301019/625000000 : ℝ)|=(357301019/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1691_s0_5 (p : ℝ) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (650122851/1250000000 : ℝ)*x 0 + (-1051867887/10000000000 : ℝ)*x 1 + (57168163/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (650122851/1250000000 : ℝ)^5151 ≤ (44222157756129/100000000000000 : ℝ)^4127 := by
    have hnat : (650122851 : ℕ)^5151*100000000000000^4127 ≤ 44222157756129^4127*1250000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      650122851 1250000000 44222157756129 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1051867887/10000000000 : ℝ)^5151 ≤ (6015727184447/100000000000000 : ℝ)^4127 := by
    have hnat : (1051867887 : ℕ)^5151*100000000000000^4127 ≤ 6015727184447^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051867887 10000000000 6015727184447 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (57168163/100000000 : ℝ)^5151 ≤ (398096920401/800000000000 : ℝ)^4127 := by
    have hnat : (57168163 : ℕ)^5151*800000000000^4127 ≤ 398096920401^4127*100000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      57168163 100000000 398096920401 800000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5151/1024 : ℝ)) 5151 4127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(650122851/1250000000 : ℝ), (-1051867887/10000000000 : ℝ), (57168163/100000000 : ℝ)] ![(44222157756129/100000000000000 : ℝ), (6015727184447/100000000000000 : ℝ), (398096920401/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(650122851/1250000000 : ℝ)|^5151 ≤ (44222157756129/100000000000000 : ℝ)^4127
        have hw : |(650122851/1250000000 : ℝ)|=(650122851/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1051867887/10000000000 : ℝ)|^5151 ≤ (6015727184447/100000000000000 : ℝ)^4127
        have hw : |(-1051867887/10000000000 : ℝ)|=(1051867887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(57168163/100000000 : ℝ)|^5151 ≤ (398096920401/800000000000 : ℝ)^4127
        have hw : |(57168163/100000000 : ℝ)|=(57168163/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1691_s0_6 (p : ℝ) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5200982847/10000000000 : ℝ)*x 0 + (1429204089/2500000000 : ℝ)*x 1 + (-1051867743/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5200982847/10000000000 : ℝ)^5151 ≤ (44222158170011/100000000000000 : ℝ)^4127 := by
    have hnat : (5200982847 : ℕ)^5151*100000000000000^4127 ≤ 44222158170011^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5200982847 10000000000 44222158170011 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1429204089/2500000000 : ℝ)^5151 ≤ (24881057829263/50000000000000 : ℝ)^4127 := by
    have hnat : (1429204089 : ℕ)^5151*50000000000000^4127 ≤ 24881057829263^4127*2500000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1429204089 2500000000 24881057829263 50000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1051867743/10000000000 : ℝ)^5151 ≤ (6015726156557/100000000000000 : ℝ)^4127 := by
    have hnat : (1051867743 : ℕ)^5151*100000000000000^4127 ≤ 6015726156557^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051867743 10000000000 6015726156557 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5151/1024 : ℝ)) 5151 4127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5200982847/10000000000 : ℝ), (1429204089/2500000000 : ℝ), (-1051867743/10000000000 : ℝ)] ![(44222158170011/100000000000000 : ℝ), (24881057829263/50000000000000 : ℝ), (6015726156557/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5200982847/10000000000 : ℝ)|^5151 ≤ (44222158170011/100000000000000 : ℝ)^4127
        have hw : |(5200982847/10000000000 : ℝ)|=(5200982847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1429204089/2500000000 : ℝ)|^5151 ≤ (24881057829263/50000000000000 : ℝ)^4127
        have hw : |(1429204089/2500000000 : ℝ)|=(1429204089/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1051867743/10000000000 : ℝ)|^5151 ≤ (6015726156557/100000000000000 : ℝ)^4127
        have hw : |(-1051867743/10000000000 : ℝ)|=(1051867743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1691_s0_7 (p : ℝ) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4061293529/10000000000 : ℝ)*x 0 + (32546337/62500000 : ℝ)*x 1 + (1552733117/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4061293529/10000000000 : ℝ)^5151 ≤ (6495242198121/20000000000000 : ℝ)^4127 := by
    have hnat : (4061293529 : ℕ)^5151*20000000000000^4127 ≤ 6495242198121^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4061293529 10000000000 6495242198121 20000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32546337/62500000 : ℝ)^5151 ≤ (2214520871917/5000000000000 : ℝ)^4127 := by
    have hnat : (32546337 : ℕ)^5151*5000000000000^4127 ≤ 2214520871917^4127*62500000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32546337 62500000 2214520871917 5000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1552733117/5000000000 : ℝ)^5151 ≤ (11616685779953/50000000000000 : ℝ)^4127 := by
    have hnat : (1552733117 : ℕ)^5151*50000000000000^4127 ≤ 11616685779953^4127*5000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1552733117 5000000000 11616685779953 50000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5151/1024 : ℝ)) 5151 4127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4061293529/10000000000 : ℝ), (32546337/62500000 : ℝ), (1552733117/5000000000 : ℝ)] ![(6495242198121/20000000000000 : ℝ), (2214520871917/5000000000000 : ℝ), (11616685779953/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4061293529/10000000000 : ℝ)|^5151 ≤ (6495242198121/20000000000000 : ℝ)^4127
        have hw : |(4061293529/10000000000 : ℝ)|=(4061293529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(32546337/62500000 : ℝ)|^5151 ≤ (2214520871917/5000000000000 : ℝ)^4127
        have hw : |(32546337/62500000 : ℝ)|=(32546337/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1552733117/5000000000 : ℝ)|^5151 ≤ (11616685779953/50000000000000 : ℝ)^4127
        have hw : |(1552733117/5000000000 : ℝ)|=(1552733117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1691_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (94347533/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (683/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (22601/100000 : ℝ)*pair X 0 0 := by
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
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (5143/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5143 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5143*1^1024 ≤ 0^1024*1^5143 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5143 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5143 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5143/1024 : ℝ) ≤ (100314069945103337/10000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5143 ≤ (100314069945103337/10000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5143*10000000000000000000^1024 ≤ 100314069945103337^1024*5^5143 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 100314069945103337 10000000000000000000 5143 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (100314069945103337/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5143 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5143/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5143 := by
      have hnat : (1 : ℕ)^1024*1^5143 ≤ 1^5143*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5143 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10100314069945103337/10000000000000000000 : ℝ) ≤ (500994666900767/500000000000000 : ℝ) ^ (5143/1024 : ℝ) := by
    have hpowers : (10100314069945103337/10000000000000000000 : ℝ)^1024 ≤ (500994666900767/500000000000000 : ℝ)^5143 := by
      have hnat : (10100314069945103337 : ℕ)^1024*500000000000000^5143 ≤ 500994666900767^5143*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10100314069945103337 10000000000000000000 500994666900767 500000000000000 1024 5143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500994666900767/500000000000000 : ℝ)) (X := (10100314069945103337/10000000000000000000 : ℝ)) (by norm_num) 5143 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5100314069945103337/5000000000000000000 : ℝ) ≤ (250994666900767/250000000000000 : ℝ) ^ (5143/1024 : ℝ) := by
    have hpowers : (5100314069945103337/5000000000000000000 : ℝ)^1024 ≤ (250994666900767/250000000000000 : ℝ)^5143 := by
      have hnat : (5100314069945103337 : ℕ)^1024*250000000000000^5143 ≤ 250994666900767^5143*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5100314069945103337 5000000000000000000 250994666900767 250000000000000 1024 5143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250994666900767/250000000000000 : ℝ)) (X := (5100314069945103337/5000000000000000000 : ℝ)) (by norm_num) 5143 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(994666900767/200000000000000 : ℝ)*(0 : ℝ))^(5143/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(994666900767/200000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(100314069945103337/10000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(994666900767/200000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5143/1024 : ℝ) := by
    rw [show (1 : ℝ)+(994666900767/200000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(500994666900767/500000000000000 : ℝ) by norm_num, show 1+(100314069945103337/10000000000000000000 : ℝ)+(0 : ℝ)=(10100314069945103337/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(100314069945103337/10000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(994666900767/200000000000000 : ℝ)*(2/5 : ℝ))^(5143/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(994666900767/200000000000000 : ℝ)*(2/5 : ℝ)=(250994666900767/250000000000000 : ℝ) by norm_num, show 1+2*(100314069945103337/10000000000000000000 : ℝ)=(5100314069945103337/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(994666900767/200000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5143/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (994666900767/200000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(994666900767/200000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5143/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (994666900767/200000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(994666900767/200000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5143/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (994666900767/200000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1394455043/10000000000 : ℝ)*X 0 0+(5737529569/10000000000 : ℝ)*X 0 1+(617379371/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1691_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((541786721/1000000000 : ℝ)*X 1 0+(-914824453/5000000000 : ℝ)*X 1 1+(4939036119/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1691_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5417869541/10000000000 : ℝ)*X 2 0+(4939035067/10000000000 : ℝ)*X 2 1+(-914823601/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1691_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((405576879/1000000000 : ℝ)*X 0 0+(121920423/400000000 : ℝ)*X 0 1+(5262956927/10000000000 : ℝ)*X 0 2+(405576879/1000000000 : ℝ)*X 1 0+(121920423/400000000 : ℝ)*X 1 1+(5262956927/10000000000 : ℝ)*X 1 2+(405576879/1000000000 : ℝ)*X 2 0+(121920423/400000000 : ℝ)*X 2 1+(5262956927/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1691_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-43638957/312500000 : ℝ)*X 0 0+(4959057773/10000000000 : ℝ)*X 0 1+(357301019/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1691_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((650122851/1250000000 : ℝ)*X 1 0+(-1051867887/10000000000 : ℝ)*X 1 1+(57168163/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1691_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5200982847/10000000000 : ℝ)*X 2 0+(1429204089/2500000000 : ℝ)*X 2 1+(-1051867743/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1691_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4061293529/10000000000 : ℝ)*X 0 0+(32546337/62500000 : ℝ)*X 0 1+(1552733117/5000000000 : ℝ)*X 0 2+(4061293529/10000000000 : ℝ)*X 1 0+(32546337/62500000 : ℝ)*X 1 1+(1552733117/5000000000 : ℝ)*X 1 2+(4061293529/10000000000 : ℝ)*X 2 0+(32546337/62500000 : ℝ)*X 2 1+(1552733117/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1691_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4096371858037967952681/400000000000000000000000000 : ℝ) := by norm_num
    linear_combination (33779381/100000000000000 : ℝ)*(base1) + (102784751/6250000000000 : ℝ)*(base19) + (26118673/1250000000000 : ℝ)*(base23) + (93887241/100000000000000 : ℝ)*(base24) + (220969799/50000000000000 : ℝ)*(upper5) + (34077229277619/4000000000000 : ℝ)*(major0) + (34077229277619/4000000000000 : ℝ)*(major1) + (34077229277619/4000000000000 : ℝ)*(major2) + (156545423188221/12500000000000 : ℝ)*(sp0) + (1252374046995243/100000000000000 : ℝ)*(sp1) + (1252373508170179/100000000000000 : ℝ)*(sp2) + (225741112369771/50000000000000 : ℝ)*(sp3) + (12339824873/100000000000000 : ℝ)*(sp4) + (3172446439/100000000000000 : ℝ)*(sp7) + (225742715482681/50000000000000 : ℝ)*(f.failure) + (1252375691551259/100000000000000 : ℝ)*(f.sum) + (490158779773/400000000000000000000000000 : ℝ)*base65 + (1330336447027/800000000000000000000000000 : ℝ)*base68 + (1688291347027/800000000000000000000000000 : ℝ)*base70 + (401408519027/800000000000000000000000000 : ℝ)*base72 + (325953684973/400000000000000000000000000 : ℝ)*base73 + (3424222972173/800000000000000000000000000 : ℝ)*base75 + (1499757166227/800000000000000000000000000 : ℝ)*base78 + (2334516584627/800000000000000000000000000 : ℝ)*base80 + (1092743432973/400000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (18424027/2500000000000000000000 : ℝ)*base90 + (18424027/2500000000000000000000 : ℝ)*base92 + (18424027/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13842589799387634074493/2000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (74371711/5000000000000 : ℝ)*(base19) + (757822339/50000000000000 : ℝ)*(base23) + (787387/2000000000000 : ℝ)*(base32) + (122711667/50000000000000 : ℝ)*(upper3) + (40129249/20000000000000 : ℝ)*(upper5) + (897715343183407/100000000000000 : ℝ)*(major0) + (897715343183407/100000000000000 : ℝ)*(major1) + (897715343183407/100000000000000 : ℝ)*(major2) + (1005796249/20000000000000 : ℝ)*(sp1) + (341757419/6250000000000 : ℝ)*(sp2) + (1319681215248431/100000000000000 : ℝ)*(sp4) + (659837349416483/50000000000000 : ℝ)*(sp5) + (1319674231485049/100000000000000 : ℝ)*(sp6) + (475749201039197/100000000000000 : ℝ)*(sp7) + (475749240408547/100000000000000 : ℝ)*(f.failure) + (1319681215248431/100000000000000 : ℝ)*(f.sum) + (2638257283169/10000000000000000000000000000 : ℝ)*base65 + (127239821913169/20000000000000000000000000000 : ℝ)*base67 + (68336487533169/20000000000000000000000000000 : ℝ)*base69 + (10191273846831/20000000000000000000000000000 : ℝ)*base72 + (59217435693169/10000000000000000000000000000 : ℝ)*base73 + (106666188913169/20000000000000000000000000000 : ℝ)*base75 + (3012238373169/20000000000000000000000000000 : ℝ)*base77 + (127426812933169/20000000000000000000000000000 : ℝ)*base79 + (33374015143169/10000000000000000000000000000 : ℝ)*base81 + (28435449/5000000000000000000000 : ℝ)*base90 + (28435449/5000000000000000000000 : ℝ)*base92 + (28435449/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1691_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (94347533/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (683/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (22601/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1691_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1691_s1_0 (p : ℝ) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-92394489/625000000 : ℝ)*x 0 + (5504503433/10000000000 : ℝ)*x 1 + (2558572869/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (92394489/625000000 : ℝ)^5151 ≤ (9199551198479/100000000000000 : ℝ)^4127 := by
    have hnat : (92394489 : ℕ)^5151*100000000000000^4127 ≤ 9199551198479^4127*625000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      92394489 625000000 9199551198479 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5504503433/10000000000 : ℝ)^5151 ≤ (9493242587331/20000000000000 : ℝ)^4127 := by
    have hnat : (5504503433 : ℕ)^5151*20000000000000^4127 ≤ 9493242587331^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5504503433 10000000000 9493242587331 20000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2558572869/5000000000 : ℝ)^5151 ≤ (433342358463/1000000000000 : ℝ)^4127 := by
    have hnat : (2558572869 : ℕ)^5151*1000000000000^4127 ≤ 433342358463^4127*5000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2558572869 5000000000 433342358463 1000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5151/1024 : ℝ)) 5151 4127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-92394489/625000000 : ℝ), (5504503433/10000000000 : ℝ), (2558572869/5000000000 : ℝ)] ![(9199551198479/100000000000000 : ℝ), (9493242587331/20000000000000 : ℝ), (433342358463/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-92394489/625000000 : ℝ)|^5151 ≤ (9199551198479/100000000000000 : ℝ)^4127
        have hw : |(-92394489/625000000 : ℝ)|=(92394489/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5504503433/10000000000 : ℝ)|^5151 ≤ (9493242587331/20000000000000 : ℝ)^4127
        have hw : |(5504503433/10000000000 : ℝ)|=(5504503433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2558572869/5000000000 : ℝ)|^5151 ≤ (433342358463/1000000000000 : ℝ)^4127
        have hw : |(2558572869/5000000000 : ℝ)|=(2558572869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1691_s1_1 (p : ℝ) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5355787039/10000000000 : ℝ)*x 0 + (-420093973/2500000000 : ℝ)*x 1 + (5117145411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5355787039/10000000000 : ℝ)^5151 ≤ (9174203243257/20000000000000 : ℝ)^4127 := by
    have hnat : (5355787039 : ℕ)^5151*20000000000000^4127 ≤ 9174203243257^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355787039 10000000000 9174203243257 20000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (420093973/2500000000 : ℝ)^5151 ≤ (10794751383727/100000000000000 : ℝ)^4127 := by
    have hnat : (420093973 : ℕ)^5151*100000000000000^4127 ≤ 10794751383727^4127*2500000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420093973 2500000000 10794751383727 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5117145411/10000000000 : ℝ)^5151 ≤ (21667116195013/50000000000000 : ℝ)^4127 := by
    have hnat : (5117145411 : ℕ)^5151*50000000000000^4127 ≤ 21667116195013^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5117145411 10000000000 21667116195013 50000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5151/1024 : ℝ)) 5151 4127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5355787039/10000000000 : ℝ), (-420093973/2500000000 : ℝ), (5117145411/10000000000 : ℝ)] ![(9174203243257/20000000000000 : ℝ), (10794751383727/100000000000000 : ℝ), (21667116195013/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5355787039/10000000000 : ℝ)|^5151 ≤ (9174203243257/20000000000000 : ℝ)^4127
        have hw : |(5355787039/10000000000 : ℝ)|=(5355787039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-420093973/2500000000 : ℝ)|^5151 ≤ (10794751383727/100000000000000 : ℝ)^4127
        have hw : |(-420093973/2500000000 : ℝ)|=(420093973/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5117145411/10000000000 : ℝ)|^5151 ≤ (21667116195013/50000000000000 : ℝ)^4127
        have hw : |(5117145411/10000000000 : ℝ)|=(5117145411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1691_s1_2 (p : ℝ) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677893101/5000000000 : ℝ)*x 0 + (5117146139/10000000000 : ℝ)*x 1 + (-1680376049/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677893101/5000000000 : ℝ)^5151 ≤ (4587100726887/10000000000000 : ℝ)^4127 := by
    have hnat : (2677893101 : ℕ)^5151*10000000000000^4127 ≤ 4587100726887^4127*5000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677893101 5000000000 4587100726887 10000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5117146139/10000000000 : ℝ)^5151 ≤ (5416780010591/12500000000000 : ℝ)^4127 := by
    have hnat : (5117146139 : ℕ)^5151*12500000000000^4127 ≤ 5416780010591^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5117146139 10000000000 5416780010591 12500000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1680376049/10000000000 : ℝ)^5151 ≤ (2158950528509/20000000000000 : ℝ)^4127 := by
    have hnat : (1680376049 : ℕ)^5151*20000000000000^4127 ≤ 2158950528509^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1680376049 10000000000 2158950528509 20000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5151/1024 : ℝ)) 5151 4127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677893101/5000000000 : ℝ), (5117146139/10000000000 : ℝ), (-1680376049/10000000000 : ℝ)] ![(4587100726887/10000000000000 : ℝ), (5416780010591/12500000000000 : ℝ), (2158950528509/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677893101/5000000000 : ℝ)|^5151 ≤ (4587100726887/10000000000000 : ℝ)^4127
        have hw : |(2677893101/5000000000 : ℝ)|=(2677893101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5117146139/10000000000 : ℝ)|^5151 ≤ (5416780010591/12500000000000 : ℝ)^4127
        have hw : |(5117146139/10000000000 : ℝ)|=(5117146139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1680376049/10000000000 : ℝ)|^5151 ≤ (2158950528509/20000000000000 : ℝ)^4127
        have hw : |(-1680376049/10000000000 : ℝ)|=(1680376049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1691_s1_3 (p : ℝ) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4125672253/10000000000 : ℝ)*x 0 + (722337409/2000000000 : ℝ)*x 1 + (585772369/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4125672253/10000000000 : ℝ)^5151 ≤ (33120009989961/100000000000000 : ℝ)^4127 := by
    have hnat : (4125672253 : ℕ)^5151*100000000000000^4127 ≤ 33120009989961^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4125672253 10000000000 33120009989961 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (722337409/2000000000 : ℝ)^5151 ≤ (5610456520667/20000000000000 : ℝ)^4127 := by
    have hnat : (722337409 : ℕ)^5151*20000000000000^4127 ≤ 5610456520667^4127*2000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      722337409 2000000000 5610456520667 20000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (585772369/1250000000 : ℝ)^5151 ≤ (38827707395417/100000000000000 : ℝ)^4127 := by
    have hnat : (585772369 : ℕ)^5151*100000000000000^4127 ≤ 38827707395417^4127*1250000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      585772369 1250000000 38827707395417 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5151/1024 : ℝ)) 5151 4127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4125672253/10000000000 : ℝ), (722337409/2000000000 : ℝ), (585772369/1250000000 : ℝ)] ![(33120009989961/100000000000000 : ℝ), (5610456520667/20000000000000 : ℝ), (38827707395417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4125672253/10000000000 : ℝ)|^5151 ≤ (33120009989961/100000000000000 : ℝ)^4127
        have hw : |(4125672253/10000000000 : ℝ)|=(4125672253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(722337409/2000000000 : ℝ)|^5151 ≤ (5610456520667/20000000000000 : ℝ)^4127
        have hw : |(722337409/2000000000 : ℝ)|=(722337409/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(585772369/1250000000 : ℝ)|^5151 ≤ (38827707395417/100000000000000 : ℝ)^4127
        have hw : |(585772369/1250000000 : ℝ)|=(585772369/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1691_s1_4 (p : ℝ) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-739267943/5000000000 : ℝ)*x 0 + (1024370023/2000000000 : ℝ)*x 1 + (2749860361/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (739267943/5000000000 : ℝ)^5151 ≤ (9201291538251/100000000000000 : ℝ)^4127 := by
    have hnat : (739267943 : ℕ)^5151*100000000000000^4127 ≤ 9201291538251^4127*5000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      739267943 5000000000 9201291538251 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1024370023/2000000000 : ℝ)^5151 ≤ (4338396511519/10000000000000 : ℝ)^4127 := by
    have hnat : (1024370023 : ℕ)^5151*10000000000000^4127 ≤ 4338396511519^4127*2000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1024370023 2000000000 4338396511519 10000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2749860361/5000000000 : ℝ)^5151 ≤ (47414743332339/100000000000000 : ℝ)^4127 := by
    have hnat : (2749860361 : ℕ)^5151*100000000000000^4127 ≤ 47414743332339^4127*5000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2749860361 5000000000 47414743332339 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5151/1024 : ℝ)) 5151 4127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-739267943/5000000000 : ℝ), (1024370023/2000000000 : ℝ), (2749860361/5000000000 : ℝ)] ![(9201291538251/100000000000000 : ℝ), (4338396511519/10000000000000 : ℝ), (47414743332339/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-739267943/5000000000 : ℝ)|^5151 ≤ (9201291538251/100000000000000 : ℝ)^4127
        have hw : |(-739267943/5000000000 : ℝ)|=(739267943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1024370023/2000000000 : ℝ)|^5151 ≤ (4338396511519/10000000000000 : ℝ)^4127
        have hw : |(1024370023/2000000000 : ℝ)|=(1024370023/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2749860361/5000000000 : ℝ)|^5151 ≤ (47414743332339/100000000000000 : ℝ)^4127
        have hw : |(2749860361/5000000000 : ℝ)|=(2749860361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1691_s1_5 (p : ℝ) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5252148553/10000000000 : ℝ)*x 0 + (-1297802647/10000000000 : ℝ)*x 1 + (5499720799/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5252148553/10000000000 : ℝ)^5151 ≤ (44765807662617/100000000000000 : ℝ)^4127 := by
    have hnat : (5252148553 : ℕ)^5151*100000000000000^4127 ≤ 44765807662617^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252148553 10000000000 44765807662617 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1297802647/10000000000 : ℝ)^5151 ≤ (1954862040669/25000000000000 : ℝ)^4127 := by
    have hnat : (1297802647 : ℕ)^5151*25000000000000^4127 ≤ 1954862040669^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1297802647 10000000000 1954862040669 25000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5499720799/10000000000 : ℝ)^5151 ≤ (47414744160893/100000000000000 : ℝ)^4127 := by
    have hnat : (5499720799 : ℕ)^5151*100000000000000^4127 ≤ 47414744160893^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5499720799 10000000000 47414744160893 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5151/1024 : ℝ)) 5151 4127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5252148553/10000000000 : ℝ), (-1297802647/10000000000 : ℝ), (5499720799/10000000000 : ℝ)] ![(44765807662617/100000000000000 : ℝ), (1954862040669/25000000000000 : ℝ), (47414744160893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5252148553/10000000000 : ℝ)|^5151 ≤ (44765807662617/100000000000000 : ℝ)^4127
        have hw : |(5252148553/10000000000 : ℝ)|=(5252148553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1297802647/10000000000 : ℝ)|^5151 ≤ (1954862040669/25000000000000 : ℝ)^4127
        have hw : |(-1297802647/10000000000 : ℝ)|=(1297802647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5499720799/10000000000 : ℝ)|^5151 ≤ (47414744160893/100000000000000 : ℝ)^4127
        have hw : |(5499720799/10000000000 : ℝ)|=(5499720799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1691_s1_6 (p : ℝ) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5252149749/10000000000 : ℝ)*x 0 + (5499720501/10000000000 : ℝ)*x 1 + (-648900691/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5252149749/10000000000 : ℝ)^5151 ≤ (699465943529/1562500000000 : ℝ)^4127 := by
    have hnat : (5252149749 : ℕ)^5151*1562500000000^4127 ≤ 699465943529^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252149749 10000000000 699465943529 1562500000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5499720501/10000000000 : ℝ)^5151 ≤ (47414740954283/100000000000000 : ℝ)^4127 := by
    have hnat : (5499720501 : ℕ)^5151*100000000000000^4127 ≤ 47414740954283^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5499720501 10000000000 47414740954283 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (648900691/5000000000 : ℝ)^5151 ≤ (7819438649731/100000000000000 : ℝ)^4127 := by
    have hnat : (648900691 : ℕ)^5151*100000000000000^4127 ≤ 7819438649731^4127*5000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      648900691 5000000000 7819438649731 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5151/1024 : ℝ)) 5151 4127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5252149749/10000000000 : ℝ), (5499720501/10000000000 : ℝ), (-648900691/5000000000 : ℝ)] ![(699465943529/1562500000000 : ℝ), (47414740954283/100000000000000 : ℝ), (7819438649731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5252149749/10000000000 : ℝ)|^5151 ≤ (699465943529/1562500000000 : ℝ)^4127
        have hw : |(5252149749/10000000000 : ℝ)|=(5252149749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5499720501/10000000000 : ℝ)|^5151 ≤ (47414740954283/100000000000000 : ℝ)^4127
        have hw : |(5499720501/10000000000 : ℝ)|=(5499720501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-648900691/5000000000 : ℝ)|^5151 ≤ (7819438649731/100000000000000 : ℝ)^4127
        have hw : |(-648900691/5000000000 : ℝ)|=(648900691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1691_s1_7 (p : ℝ) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2063147283/5000000000 : ℝ)*x 0 + (2336564097/5000000000 : ℝ)*x 1 + (1812477471/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2063147283/5000000000 : ℝ)^5151 ≤ (33126245468889/100000000000000 : ℝ)^4127 := by
    have hnat : (2063147283 : ℕ)^5151*100000000000000^4127 ≤ 33126245468889^4127*5000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063147283 5000000000 33126245468889 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2336564097/5000000000 : ℝ)^5151 ≤ (9673197688949/25000000000000 : ℝ)^4127 := by
    have hnat : (2336564097 : ℕ)^5151*25000000000000^4127 ≤ 9673197688949^4127*5000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2336564097 5000000000 9673197688949 25000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1812477471/5000000000 : ℝ)^5151 ≤ (28180963764027/100000000000000 : ℝ)^4127 := by
    have hnat : (1812477471 : ℕ)^5151*100000000000000^4127 ≤ 28180963764027^4127*5000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1812477471 5000000000 28180963764027 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5151/1024 : ℝ)) 5151 4127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2063147283/5000000000 : ℝ), (2336564097/5000000000 : ℝ), (1812477471/5000000000 : ℝ)] ![(33126245468889/100000000000000 : ℝ), (9673197688949/25000000000000 : ℝ), (28180963764027/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2063147283/5000000000 : ℝ)|^5151 ≤ (33126245468889/100000000000000 : ℝ)^4127
        have hw : |(2063147283/5000000000 : ℝ)|=(2063147283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2336564097/5000000000 : ℝ)|^5151 ≤ (9673197688949/25000000000000 : ℝ)^4127
        have hw : |(2336564097/5000000000 : ℝ)|=(2336564097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1812477471/5000000000 : ℝ)|^5151 ≤ (28180963764027/100000000000000 : ℝ)^4127
        have hw : |(1812477471/5000000000 : ℝ)|=(1812477471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1691_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (94347533/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (22601/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (683/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (4721/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2211/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (22601/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (683/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (22601/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (683/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (22601/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (683/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (22601/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (683/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (22601/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (683/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (22601/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (683/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (683/12500 : ℝ) ^ (5143/1024 : ℝ) ≤ (22812178660331/50000000000000000000 : ℝ) := by
    have hpowers : (683/12500 : ℝ)^5143 ≤ (22812178660331/50000000000000000000 : ℝ)^1024 := by
      have hnat : (683 : ℕ)^5143*50000000000000000000^1024 ≤ 22812178660331^1024*12500^5143 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        683 12500 22812178660331 50000000000000000000 5143 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (683/12500 : ℝ)) (X := (22812178660331/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5143 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (22601/100000 : ℝ) ^ (5143/1024 : ℝ) ≤ (57033677833271927/100000000000000000000 : ℝ) := by
    have hpowers : (22601/100000 : ℝ)^5143 ≤ (57033677833271927/100000000000000000000 : ℝ)^1024 := by
      have hnat : (22601 : ℕ)^5143*100000000000000000000^1024 ≤ 57033677833271927^1024*100000^5143 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22601 100000 57033677833271927 100000000000000000000 5143 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (22601/100000 : ℝ)) (X := (57033677833271927/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5143 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000022812178660331/25000000000000000000 : ℝ) ≤ (5000000908406083/5000000000000000 : ℝ) ^ (5143/1024 : ℝ) := by
    have hpowers : (25000022812178660331/25000000000000000000 : ℝ)^1024 ≤ (5000000908406083/5000000000000000 : ℝ)^5143 := by
      have hnat : (25000022812178660331 : ℕ)^1024*5000000000000000^5143 ≤ 5000000908406083^5143*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000022812178660331 25000000000000000000 5000000908406083 5000000000000000 1024 5143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000908406083/5000000000000000 : ℝ)) (X := (25000022812178660331/25000000000000000000 : ℝ)) (by norm_num) 5143 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100057079302190592589/100000000000000000000 : ℝ) ≤ (10001136221079907/10000000000000000 : ℝ) ^ (5143/1024 : ℝ) := by
    have hpowers : (100057079302190592589/100000000000000000000 : ℝ)^1024 ≤ (10001136221079907/10000000000000000 : ℝ)^5143 := by
      have hnat : (100057079302190592589 : ℕ)^1024*10000000000000000^5143 ≤ 10001136221079907^5143*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100057079302190592589 100000000000000000000 10001136221079907 10000000000000000 1024 5143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001136221079907/10000000000000000 : ℝ)) (X := (100057079302190592589/100000000000000000000 : ℝ)) (by norm_num) 5143 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50057033677833271927/50000000000000000000 : ℝ) ≤ (156285478521057/156250000000000 : ℝ) ^ (5143/1024 : ℝ) := by
    have hpowers : (50057033677833271927/50000000000000000000 : ℝ)^1024 ≤ (156285478521057/156250000000000 : ℝ)^5143 := by
      have hnat : (50057033677833271927 : ℕ)^1024*156250000000000^5143 ≤ 156285478521057^5143*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50057033677833271927 50000000000000000000 156285478521057 156250000000000 1024 5143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156285478521057/156250000000000 : ℝ)) (X := (50057033677833271927/50000000000000000000 : ℝ)) (by norm_num) 5143 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(22812178660331/50000000000000000000 : ℝ) ≤ ((85678817182436107547/85685000000000000000 : ℝ)+2*(1134404267741/1713700000000000 : ℝ)*(683/12500 : ℝ))^(5143/1024 : ℝ) := by
    rw [show (85678817182436107547/85685000000000000000 : ℝ)+2*(1134404267741/1713700000000000 : ℝ)*(683/12500 : ℝ)=(5000000908406083/5000000000000000 : ℝ) by norm_num, show 1+2*(22812178660331/50000000000000000000 : ℝ)=(25000022812178660331/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(57033677833271927/100000000000000000000 : ℝ)+(22812178660331/50000000000000000000 : ℝ) ≤ ((85678817182436107547/85685000000000000000 : ℝ)+(1134404267741/1713700000000000 : ℝ)*((22601/100000 : ℝ)+(683/12500 : ℝ)))^(5143/1024 : ℝ) := by
    rw [show (85678817182436107547/85685000000000000000 : ℝ)+(1134404267741/1713700000000000 : ℝ)*((22601/100000 : ℝ)+(683/12500 : ℝ))=(10001136221079907/10000000000000000 : ℝ) by norm_num, show 1+(57033677833271927/100000000000000000000 : ℝ)+(22812178660331/50000000000000000000 : ℝ)=(100057079302190592589/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(57033677833271927/100000000000000000000 : ℝ) ≤ ((85678817182436107547/85685000000000000000 : ℝ)+2*(1134404267741/1713700000000000 : ℝ)*(22601/100000 : ℝ))^(5143/1024 : ℝ) := by
    rw [show (85678817182436107547/85685000000000000000 : ℝ)+2*(1134404267741/1713700000000000 : ℝ)*(22601/100000 : ℝ)=(156285478521057/156250000000000 : ℝ) by norm_num, show 1+2*(57033677833271927/100000000000000000000 : ℝ)=(50057033677833271927/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (85678817182436107547/85685000000000000000 : ℝ)*(X 1 0+X 2 0)+(1134404267741/1713700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5143/1024 : ℝ)) (lo := (683/12500 : ℝ)) (hi := (22601/100000 : ℝ)) (c := (85678817182436107547/85685000000000000000 : ℝ)) (alpha := (1134404267741/1713700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (85678817182436107547/85685000000000000000 : ℝ)*(X 0 1+X 2 1)+(1134404267741/1713700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5143/1024 : ℝ)) (lo := (683/12500 : ℝ)) (hi := (22601/100000 : ℝ)) (c := (85678817182436107547/85685000000000000000 : ℝ)) (alpha := (1134404267741/1713700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (85678817182436107547/85685000000000000000 : ℝ)*(X 0 2+X 1 2)+(1134404267741/1713700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5143/1024 : ℝ)) (lo := (683/12500 : ℝ)) (hi := (22601/100000 : ℝ)) (c := (85678817182436107547/85685000000000000000 : ℝ)) (alpha := (1134404267741/1713700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-92394489/625000000 : ℝ)*X 0 0+(5504503433/10000000000 : ℝ)*X 0 1+(2558572869/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1691_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5355787039/10000000000 : ℝ)*X 1 0+(-420093973/2500000000 : ℝ)*X 1 1+(5117145411/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1691_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2677893101/5000000000 : ℝ)*X 2 0+(5117146139/10000000000 : ℝ)*X 2 1+(-1680376049/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1691_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4125672253/10000000000 : ℝ)*X 0 0+(722337409/2000000000 : ℝ)*X 0 1+(585772369/1250000000 : ℝ)*X 0 2+(4125672253/10000000000 : ℝ)*X 1 0+(722337409/2000000000 : ℝ)*X 1 1+(585772369/1250000000 : ℝ)*X 1 2+(4125672253/10000000000 : ℝ)*X 2 0+(722337409/2000000000 : ℝ)*X 2 1+(585772369/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1691_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-739267943/5000000000 : ℝ)*X 0 0+(1024370023/2000000000 : ℝ)*X 0 1+(2749860361/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1691_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5252148553/10000000000 : ℝ)*X 1 0+(-1297802647/10000000000 : ℝ)*X 1 1+(5499720799/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1691_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5252149749/10000000000 : ℝ)*X 2 0+(5499720501/10000000000 : ℝ)*X 2 1+(-648900691/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1691_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2063147283/5000000000 : ℝ)*X 0 0+(2336564097/5000000000 : ℝ)*X 0 1+(1812477471/5000000000 : ℝ)*X 0 2+(2063147283/5000000000 : ℝ)*X 1 0+(2336564097/5000000000 : ℝ)*X 1 1+(1812477471/5000000000 : ℝ)*X 1 2+(2063147283/5000000000 : ℝ)*X 2 0+(2336564097/5000000000 : ℝ)*X 2 1+(1812477471/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1691_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (34490688306159639277323599307/4284250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1207860209/100000000000000 : ℝ)*(base19) + (152803637/20000000000000 : ℝ)*(base23) + (228110409/100000000000000 : ℝ)*(upper3) + (5407881/25000000000000 : ℝ)*(upper4) + (48515271/100000000000000 : ℝ)*(upper5) + (1756145349156009/100000000000000 : ℝ)*(major0) + (1756145349156009/100000000000000 : ℝ)*(major1) + (1756145349156009/100000000000000 : ℝ)*(major2) + (258160418517069/10000000000000 : ℝ)*(sp0) + (2581610224294353/100000000000000 : ℝ)*(sp1) + (2581610668136377/100000000000000 : ℝ)*(sp2) + (46533768609337/5000000000000 : ℝ)*(sp3) + (113234123/1562500000000 : ℝ)*(sp4) + (725123623/20000000000000 : ℝ)*(sp7) + (186135799560971/20000000000000 : ℝ)*(f.failure) + (1290805716077281/50000000000000 : ℝ)*(f.sum) + (533607001047561/85685000000000000000000000000 : ℝ)*base66 + (35454753989821250077/8568500000000000000000000000000000 : ℝ)*base68 + (51617892159670250077/8568500000000000000000000000000000 : ℝ)*base70 + (91172602697385750077/8568500000000000000000000000000000 : ℝ)*base72 + (185996143997879/85685000000000000000000000000 : ℝ)*base73 + (27565678056781750077/8568500000000000000000000000000000 : ℝ)*base76 + (7823199174895250077/8568500000000000000000000000000000 : ℝ)*base78 + (60206360183501750077/8568500000000000000000000000000000 : ℝ)*base80 + (1149865836409/1338828125000000000000000000 : ℝ)*base82 + (6934543/1000000000000000000000 : ℝ)*base89 + (6934543/1000000000000000000000 : ℝ)*base91 + (6934543/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (43507081564316458522461/5355312500000000000000000000 : ℝ) := by norm_num
    linear_combination (6299067/1250000000000 : ℝ)*(base23) + (38322581/50000000000000 : ℝ)*(lower2) + (5094351/25000000000000 : ℝ)*(upper3) + (24442737/100000000000000 : ℝ)*(upper4) + (4239217/1562500000000 : ℝ)*(upper5) + (900114404118109/50000000000000 : ℝ)*(major0) + (900114404118109/50000000000000 : ℝ)*(major1) + (900114404118109/50000000000000 : ℝ)*(major2) + (950354459/20000000000000 : ℝ)*(sp2) + (81816049/20000000000000 : ℝ)*(sp3) + (1323208036736923/50000000000000 : ℝ)*(sp4) + (1323208036736923/50000000000000 : ℝ)*(sp5) + (2646410817776191/100000000000000 : ℝ)*(sp6) + (190808172623017/20000000000000 : ℝ)*(sp7) + (95404127219533/10000000000000 : ℝ)*(f.failure) + (1323208036736923/50000000000000 : ℝ)*(f.sum) + (199622961139323/85685000000000000000000000000 : ℝ)*base65 + (34281609338481468623/4284250000000000000000000000000000 : ℝ)*base67 + (18667930458375781377/4284250000000000000000000000000000 : ℝ)*base70 + (29422455282597468623/4284250000000000000000000000000000 : ℝ)*base71 + (313889939663733/85685000000000000000000000000 : ℝ)*base73 + (8632015462239281377/4284250000000000000000000000000000 : ℝ)*base76 + (367883491429281377/4284250000000000000000000000000000 : ℝ)*base78 + (38333574132575968623/4284250000000000000000000000000000 : ℝ)*base79 + (134172583413167/85685000000000000000000000000 : ℝ)*base82 + (2037911/500000000000000000000 : ℝ)*base90 + (2037911/500000000000000000000 : ℝ)*base92 + (2037911/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1691_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (94347533/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (22601/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (683/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4721/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2211/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1691_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1691_s2_0 (p : ℝ) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1483528223/10000000000 : ℝ)*x 0 + (5483563779/10000000000 : ℝ)*x 1 + (5134615567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1483528223/10000000000 : ℝ)^5151 ≤ (4620042548849/50000000000000 : ℝ)^4127 := by
    have hnat : (1483528223 : ℕ)^5151*50000000000000^4127 ≤ 4620042548849^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1483528223 10000000000 4620042548849 50000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5483563779/10000000000 : ℝ)^5151 ≤ (11810237750029/25000000000000 : ℝ)^4127 := by
    have hnat : (5483563779 : ℕ)^5151*25000000000000^4127 ≤ 11810237750029^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5483563779 10000000000 11810237750029 25000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5134615567/10000000000 : ℝ)^5151 ≤ (1359967621649/3125000000000 : ℝ)^4127 := by
    have hnat : (5134615567 : ℕ)^5151*3125000000000^4127 ≤ 1359967621649^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5134615567 10000000000 1359967621649 3125000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5151/1024 : ℝ)) 5151 4127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1483528223/10000000000 : ℝ), (5483563779/10000000000 : ℝ), (5134615567/10000000000 : ℝ)] ![(4620042548849/50000000000000 : ℝ), (11810237750029/25000000000000 : ℝ), (1359967621649/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1483528223/10000000000 : ℝ)|^5151 ≤ (4620042548849/50000000000000 : ℝ)^4127
        have hw : |(-1483528223/10000000000 : ℝ)|=(1483528223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5483563779/10000000000 : ℝ)|^5151 ≤ (11810237750029/25000000000000 : ℝ)^4127
        have hw : |(5483563779/10000000000 : ℝ)|=(5483563779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5134615567/10000000000 : ℝ)|^5151 ≤ (1359967621649/3125000000000 : ℝ)^4127
        have hw : |(5134615567/10000000000 : ℝ)|=(5134615567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1691_s2_1 (p : ℝ) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675084851/5000000000 : ℝ)*x 0 + (-332961321/2000000000 : ℝ)*x 1 + (80228367/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675084851/5000000000 : ℝ)^5151 ≤ (45810975468437/100000000000000 : ℝ)^4127 := by
    have hnat : (2675084851 : ℕ)^5151*100000000000000^4127 ≤ 45810975468437^4127*5000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675084851 5000000000 45810975468437 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (332961321/2000000000 : ℝ)^5151 ≤ (5335030731821/50000000000000 : ℝ)^4127 := by
    have hnat : (332961321 : ℕ)^5151*50000000000000^4127 ≤ 5335030731821^4127*2000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332961321 2000000000 5335030731821 50000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (80228367/156250000 : ℝ)^5151 ≤ (43518963057059/100000000000000 : ℝ)^4127 := by
    have hnat : (80228367 : ℕ)^5151*100000000000000^4127 ≤ 43518963057059^4127*156250000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80228367 156250000 43518963057059 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5151/1024 : ℝ)) 5151 4127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675084851/5000000000 : ℝ), (-332961321/2000000000 : ℝ), (80228367/156250000 : ℝ)] ![(45810975468437/100000000000000 : ℝ), (5335030731821/50000000000000 : ℝ), (43518963057059/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675084851/5000000000 : ℝ)|^5151 ≤ (45810975468437/100000000000000 : ℝ)^4127
        have hw : |(2675084851/5000000000 : ℝ)|=(2675084851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-332961321/2000000000 : ℝ)|^5151 ≤ (5335030731821/50000000000000 : ℝ)^4127
        have hw : |(-332961321/2000000000 : ℝ)|=(332961321/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(80228367/156250000 : ℝ)|^5151 ≤ (43518963057059/100000000000000 : ℝ)^4127
        have hw : |(80228367/156250000 : ℝ)|=(80228367/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1691_s2_2 (p : ℝ) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350169789/10000000000 : ℝ)*x 0 + (1026923091/2000000000 : ℝ)*x 1 + (-416201633/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350169789/10000000000 : ℝ)^5151 ≤ (45810976398213/100000000000000 : ℝ)^4127 := by
    have hnat : (5350169789 : ℕ)^5151*100000000000000^4127 ≤ 45810976398213^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350169789 10000000000 45810976398213 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1026923091/2000000000 : ℝ)^5151 ≤ (21759481353983/50000000000000 : ℝ)^4127 := by
    have hnat : (1026923091 : ℕ)^5151*50000000000000^4127 ≤ 21759481353983^4127*2000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026923091 2000000000 21759481353983 50000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (416201633/2500000000 : ℝ)^5151 ≤ (5335030439841/50000000000000 : ℝ)^4127 := by
    have hnat : (416201633 : ℕ)^5151*50000000000000^4127 ≤ 5335030439841^4127*2500000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416201633 2500000000 5335030439841 50000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5151/1024 : ℝ)) 5151 4127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350169789/10000000000 : ℝ), (1026923091/2000000000 : ℝ), (-416201633/2500000000 : ℝ)] ![(45810976398213/100000000000000 : ℝ), (21759481353983/50000000000000 : ℝ), (5335030439841/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350169789/10000000000 : ℝ)|^5151 ≤ (45810976398213/100000000000000 : ℝ)^4127
        have hw : |(5350169789/10000000000 : ℝ)|=(5350169789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1026923091/2000000000 : ℝ)|^5151 ≤ (21759481353983/50000000000000 : ℝ)^4127
        have hw : |(1026923091/2000000000 : ℝ)|=(1026923091/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-416201633/2500000000 : ℝ)|^5151 ≤ (5335030439841/50000000000000 : ℝ)^4127
        have hw : |(-416201633/2500000000 : ℝ)|=(416201633/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1691_s2_3 (p : ℝ) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (825937207/2000000000 : ℝ)*x 0 + (229036649/625000000 : ℝ)*x 1 + (4632534387/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (825937207/2000000000 : ℝ)^5151 ≤ (16580115779053/50000000000000 : ℝ)^4127 := by
    have hnat : (825937207 : ℕ)^5151*50000000000000^4127 ≤ 16580115779053^4127*2000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      825937207 2000000000 16580115779053 50000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (229036649/625000000 : ℝ)^5151 ≤ (892688487317/3125000000000 : ℝ)^4127 := by
    have hnat : (229036649 : ℕ)^5151*3125000000000^4127 ≤ 892688487317^4127*625000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      229036649 625000000 892688487317 3125000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4632534387/10000000000 : ℝ)^5151 ≤ (19136868412317/50000000000000 : ℝ)^4127 := by
    have hnat : (4632534387 : ℕ)^5151*50000000000000^4127 ≤ 19136868412317^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4632534387 10000000000 19136868412317 50000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5151/1024 : ℝ)) 5151 4127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(825937207/2000000000 : ℝ), (229036649/625000000 : ℝ), (4632534387/10000000000 : ℝ)] ![(16580115779053/50000000000000 : ℝ), (892688487317/3125000000000 : ℝ), (19136868412317/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(825937207/2000000000 : ℝ)|^5151 ≤ (16580115779053/50000000000000 : ℝ)^4127
        have hw : |(825937207/2000000000 : ℝ)|=(825937207/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(229036649/625000000 : ℝ)|^5151 ≤ (892688487317/3125000000000 : ℝ)^4127
        have hw : |(229036649/625000000 : ℝ)|=(229036649/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4632534387/10000000000 : ℝ)|^5151 ≤ (19136868412317/50000000000000 : ℝ)^4127
        have hw : |(4632534387/10000000000 : ℝ)|=(4632534387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1691_s2_4 (p : ℝ) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-741846047/5000000000 : ℝ)*x 0 + (1284609279/2500000000 : ℝ)*x 1 + (1095936981/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (741846047/5000000000 : ℝ)^5151 ≤ (1155169878363/12500000000000 : ℝ)^4127 := by
    have hnat : (741846047 : ℕ)^5151*12500000000000^4127 ≤ 1155169878363^4127*5000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      741846047 5000000000 1155169878363 12500000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1284609279/2500000000 : ℝ)^5151 ≤ (43559394216489/100000000000000 : ℝ)^4127 := by
    have hnat : (1284609279 : ℕ)^5151*100000000000000^4127 ≤ 43559394216489^4127*2500000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1284609279 2500000000 43559394216489 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1095936981/2000000000 : ℝ)^5151 ≤ (47199246745299/100000000000000 : ℝ)^4127 := by
    have hnat : (1095936981 : ℕ)^5151*100000000000000^4127 ≤ 47199246745299^4127*2000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095936981 2000000000 47199246745299 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5151/1024 : ℝ)) 5151 4127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-741846047/5000000000 : ℝ), (1284609279/2500000000 : ℝ), (1095936981/2000000000 : ℝ)] ![(1155169878363/12500000000000 : ℝ), (43559394216489/100000000000000 : ℝ), (47199246745299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-741846047/5000000000 : ℝ)|^5151 ≤ (1155169878363/12500000000000 : ℝ)^4127
        have hw : |(-741846047/5000000000 : ℝ)|=(741846047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1284609279/2500000000 : ℝ)|^5151 ≤ (43559394216489/100000000000000 : ℝ)^4127
        have hw : |(1284609279/2500000000 : ℝ)|=(1284609279/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1095936981/2000000000 : ℝ)|^5151 ≤ (47199246745299/100000000000000 : ℝ)^4127
        have hw : |(1095936981/2000000000 : ℝ)|=(1095936981/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1691_s2_5 (p : ℝ) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5256867083/10000000000 : ℝ)*x 0 + (-1319737157/10000000000 : ℝ)*x 1 + (5479684987/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256867083/10000000000 : ℝ)^5151 ≤ (44816009731593/100000000000000 : ℝ)^4127 := by
    have hnat : (5256867083 : ℕ)^5151*100000000000000^4127 ≤ 44816009731593^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256867083 10000000000 44816009731593 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1319737157/10000000000 : ℝ)^5151 ≤ (3992371314943/50000000000000 : ℝ)^4127 := by
    have hnat : (1319737157 : ℕ)^5151*50000000000000^4127 ≤ 3992371314943^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319737157 10000000000 3992371314943 50000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5479684987/10000000000 : ℝ)^5151 ≤ (5899905953357/12500000000000 : ℝ)^4127 := by
    have hnat : (5479684987 : ℕ)^5151*12500000000000^4127 ≤ 5899905953357^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5479684987 10000000000 5899905953357 12500000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5151/1024 : ℝ)) 5151 4127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256867083/10000000000 : ℝ), (-1319737157/10000000000 : ℝ), (5479684987/10000000000 : ℝ)] ![(44816009731593/100000000000000 : ℝ), (3992371314943/50000000000000 : ℝ), (5899905953357/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256867083/10000000000 : ℝ)|^5151 ≤ (44816009731593/100000000000000 : ℝ)^4127
        have hw : |(5256867083/10000000000 : ℝ)|=(5256867083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1319737157/10000000000 : ℝ)|^5151 ≤ (3992371314943/50000000000000 : ℝ)^4127
        have hw : |(-1319737157/10000000000 : ℝ)|=(1319737157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5479684987/10000000000 : ℝ)|^5151 ≤ (5899905953357/12500000000000 : ℝ)^4127
        have hw : |(5479684987/10000000000 : ℝ)|=(5479684987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1691_s2_6 (p : ℝ) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (20534637/39062500 : ℝ)*x 0 + (5479684993/10000000000 : ℝ)*x 1 + (-329934291/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20534637/39062500 : ℝ)^5151 ≤ (44816009614547/100000000000000 : ℝ)^4127 := by
    have hnat : (20534637 : ℕ)^5151*100000000000000^4127 ≤ 44816009614547^4127*39062500^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20534637 39062500 44816009614547 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5479684993/10000000000 : ℝ)^5151 ≤ (294995298071/625000000000 : ℝ)^4127 := by
    have hnat : (5479684993 : ℕ)^5151*625000000000^4127 ≤ 294995298071^4127*10000000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5479684993 10000000000 294995298071 625000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (329934291/2500000000 : ℝ)^5151 ≤ (3992371341373/50000000000000 : ℝ)^4127 := by
    have hnat : (329934291 : ℕ)^5151*50000000000000^4127 ≤ 3992371341373^4127*2500000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329934291 2500000000 3992371341373 50000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5151/1024 : ℝ)) 5151 4127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(20534637/39062500 : ℝ), (5479684993/10000000000 : ℝ), (-329934291/2500000000 : ℝ)] ![(44816009614547/100000000000000 : ℝ), (294995298071/625000000000 : ℝ), (3992371341373/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(20534637/39062500 : ℝ)|^5151 ≤ (44816009614547/100000000000000 : ℝ)^4127
        have hw : |(20534637/39062500 : ℝ)|=(20534637/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5479684993/10000000000 : ℝ)|^5151 ≤ (294995298071/625000000000 : ℝ)^4127
        have hw : |(5479684993/10000000000 : ℝ)|=(5479684993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-329934291/2500000000 : ℝ)|^5151 ≤ (3992371341373/50000000000000 : ℝ)^4127
        have hw : |(-329934291/2500000000 : ℝ)|=(329934291/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1691_s2_7 (p : ℝ) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1032535231/2500000000 : ℝ)*x 0 + (231096689/500000000 : ℝ)*x 1 + (22970913/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1032535231/2500000000 : ℝ)^5151 ≤ (4145598818947/12500000000000 : ℝ)^4127 := by
    have hnat : (1032535231 : ℕ)^5151*12500000000000^4127 ≤ 4145598818947^4127*2500000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1032535231 2500000000 4145598818947 12500000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (231096689/500000000 : ℝ)^5151 ≤ (38164455323971/100000000000000 : ℝ)^4127 := by
    have hnat : (231096689 : ℕ)^5151*100000000000000^4127 ≤ 38164455323971^4127*500000000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      231096689 500000000 38164455323971 100000000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (22970913/62500000 : ℝ)^5151 ≤ (179192213209/625000000000 : ℝ)^4127 := by
    have hnat : (22970913 : ℕ)^5151*625000000000^4127 ≤ 179192213209^4127*62500000^5151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22970913 62500000 179192213209 625000000000 5151 4127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5151/1024 : ℝ)) 5151 4127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1032535231/2500000000 : ℝ), (231096689/500000000 : ℝ), (22970913/62500000 : ℝ)] ![(4145598818947/12500000000000 : ℝ), (38164455323971/100000000000000 : ℝ), (179192213209/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1032535231/2500000000 : ℝ)|^5151 ≤ (4145598818947/12500000000000 : ℝ)^4127
        have hw : |(1032535231/2500000000 : ℝ)|=(1032535231/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(231096689/500000000 : ℝ)|^5151 ≤ (38164455323971/100000000000000 : ℝ)^4127
        have hw : |(231096689/500000000 : ℝ)|=(231096689/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(22970913/62500000 : ℝ)|^5151 ≤ (179192213209/625000000000 : ℝ)^4127
        have hw : |(22970913/62500000 : ℝ)|=(22970913/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1691_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (94347533/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2211/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4721/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (4911/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (69/400 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2211/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4721/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2211/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4721/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2211/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4721/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2211/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4721/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2211/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4721/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2211/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4721/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4721/50000 : ℝ) ^ (5143/1024 : ℝ) ≤ (711703262961641/100000000000000000000 : ℝ) := by
    have hpowers : (4721/50000 : ℝ)^5143 ≤ (711703262961641/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4721 : ℕ)^5143*100000000000000000000^1024 ≤ 711703262961641^1024*50000^5143 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4721 50000 711703262961641 100000000000000000000 5143 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4721/50000 : ℝ)) (X := (711703262961641/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5143 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2211/12500 : ℝ) ^ (5143/1024 : ℝ) ≤ (16653127488500551/100000000000000000000 : ℝ) := by
    have hpowers : (2211/12500 : ℝ)^5143 ≤ (16653127488500551/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2211 : ℕ)^5143*100000000000000000000^1024 ≤ 16653127488500551^1024*12500^5143 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2211 12500 16653127488500551 100000000000000000000 5143 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2211/12500 : ℝ)) (X := (16653127488500551/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5143 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000711703262961641/50000000000000000000 : ℝ) ≤ (2500007085164177/2500000000000000 : ℝ) ^ (5143/1024 : ℝ) := by
    have hpowers : (50000711703262961641/50000000000000000000 : ℝ)^1024 ≤ (2500007085164177/2500000000000000 : ℝ)^5143 := by
      have hnat : (50000711703262961641 : ℕ)^1024*2500000000000000^5143 ≤ 2500007085164177^5143*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000711703262961641 50000000000000000000 2500007085164177 2500000000000000 1024 5143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500007085164177/2500000000000000 : ℝ)) (X := (50000711703262961641/50000000000000000000 : ℝ)) (by norm_num) 5143 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6251085301921966387/6250000000000000000 : ℝ) ≤ (5000172859715541/5000000000000000 : ℝ) ^ (5143/1024 : ℝ) := by
    have hpowers : (6251085301921966387/6250000000000000000 : ℝ)^1024 ≤ (5000172859715541/5000000000000000 : ℝ)^5143 := by
      have hnat : (6251085301921966387 : ℕ)^1024*5000000000000000^5143 ≤ 5000172859715541^5143*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251085301921966387 6250000000000000000 5000172859715541 5000000000000000 1024 5143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000172859715541/5000000000000000 : ℝ)) (X := (6251085301921966387/6250000000000000000 : ℝ)) (by norm_num) 5143 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50016653127488500551/50000000000000000000 : ℝ) ≤ (625041443637841/625000000000000 : ℝ) ^ (5143/1024 : ℝ) := by
    have hpowers : (50016653127488500551/50000000000000000000 : ℝ)^1024 ≤ (625041443637841/625000000000000 : ℝ)^5143 := by
      have hnat : (50016653127488500551 : ℕ)^1024*625000000000000^5143 ≤ 625041443637841^5143*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50016653127488500551 50000000000000000000 625041443637841 625000000000000 1024 5143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625041443637841/625000000000000 : ℝ)) (X := (50016653127488500551/50000000000000000000 : ℝ)) (by norm_num) 5143 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(711703262961641/100000000000000000000 : ℝ) ≤ ((1288347504941873993/1288437500000000000 : ℝ)+2*(158689387187/412300000000000 : ℝ)*(4721/50000 : ℝ))^(5143/1024 : ℝ) := by
    rw [show (1288347504941873993/1288437500000000000 : ℝ)+2*(158689387187/412300000000000 : ℝ)*(4721/50000 : ℝ)=(2500007085164177/2500000000000000 : ℝ) by norm_num, show 1+2*(711703262961641/100000000000000000000 : ℝ)=(50000711703262961641/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16653127488500551/100000000000000000000 : ℝ)+(711703262961641/100000000000000000000 : ℝ) ≤ ((1288347504941873993/1288437500000000000 : ℝ)+(158689387187/412300000000000 : ℝ)*((2211/12500 : ℝ)+(4721/50000 : ℝ)))^(5143/1024 : ℝ) := by
    rw [show (1288347504941873993/1288437500000000000 : ℝ)+(158689387187/412300000000000 : ℝ)*((2211/12500 : ℝ)+(4721/50000 : ℝ))=(5000172859715541/5000000000000000 : ℝ) by norm_num, show 1+(16653127488500551/100000000000000000000 : ℝ)+(711703262961641/100000000000000000000 : ℝ)=(6251085301921966387/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16653127488500551/100000000000000000000 : ℝ) ≤ ((1288347504941873993/1288437500000000000 : ℝ)+2*(158689387187/412300000000000 : ℝ)*(2211/12500 : ℝ))^(5143/1024 : ℝ) := by
    rw [show (1288347504941873993/1288437500000000000 : ℝ)+2*(158689387187/412300000000000 : ℝ)*(2211/12500 : ℝ)=(625041443637841/625000000000000 : ℝ) by norm_num, show 1+2*(16653127488500551/100000000000000000000 : ℝ)=(50016653127488500551/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1288347504941873993/1288437500000000000 : ℝ)*(X 1 0+X 2 0)+(158689387187/412300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5143/1024 : ℝ)) (lo := (4721/50000 : ℝ)) (hi := (2211/12500 : ℝ)) (c := (1288347504941873993/1288437500000000000 : ℝ)) (alpha := (158689387187/412300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1288347504941873993/1288437500000000000 : ℝ)*(X 0 1+X 2 1)+(158689387187/412300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5143/1024 : ℝ)) (lo := (4721/50000 : ℝ)) (hi := (2211/12500 : ℝ)) (c := (1288347504941873993/1288437500000000000 : ℝ)) (alpha := (158689387187/412300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1288347504941873993/1288437500000000000 : ℝ)*(X 0 2+X 1 2)+(158689387187/412300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5143/1024 : ℝ)) (lo := (4721/50000 : ℝ)) (hi := (2211/12500 : ℝ)) (c := (1288347504941873993/1288437500000000000 : ℝ)) (alpha := (158689387187/412300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1483528223/10000000000 : ℝ)*X 0 0+(5483563779/10000000000 : ℝ)*X 0 1+(5134615567/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1691_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675084851/5000000000 : ℝ)*X 1 0+(-332961321/2000000000 : ℝ)*X 1 1+(80228367/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1691_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350169789/10000000000 : ℝ)*X 2 0+(1026923091/2000000000 : ℝ)*X 2 1+(-416201633/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1691_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((825937207/2000000000 : ℝ)*X 0 0+(229036649/625000000 : ℝ)*X 0 1+(4632534387/10000000000 : ℝ)*X 0 2+(825937207/2000000000 : ℝ)*X 1 0+(229036649/625000000 : ℝ)*X 1 1+(4632534387/10000000000 : ℝ)*X 1 2+(825937207/2000000000 : ℝ)*X 2 0+(229036649/625000000 : ℝ)*X 2 1+(4632534387/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1691_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-741846047/5000000000 : ℝ)*X 0 0+(1284609279/2500000000 : ℝ)*X 0 1+(1095936981/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1691_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5256867083/10000000000 : ℝ)*X 1 0+(-1319737157/10000000000 : ℝ)*X 1 1+(5479684987/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1691_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((20534637/39062500 : ℝ)*X 2 0+(5479684993/10000000000 : ℝ)*X 2 1+(-329934291/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1691_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1032535231/2500000000 : ℝ)*X 0 0+(231096689/500000000 : ℝ)*X 0 1+(22970913/62500000 : ℝ)*X 0 2+(1032535231/2500000000 : ℝ)*X 1 0+(231096689/500000000 : ℝ)*X 1 1+(22970913/62500000 : ℝ)*X 1 2+(1032535231/2500000000 : ℝ)*X 2 0+(231096689/500000000 : ℝ)*X 2 1+(22970913/62500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1691_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4165885527027077377533789/644218750000000000000000000000 : ℝ) := by norm_num
    linear_combination (254224583/25000000000000 : ℝ)*(base19) + (103468773/10000000000000 : ℝ)*(base23) + (240853/1562500000000 : ℝ)*(lower2) + (62302859/50000000000000 : ℝ)*(upper3) + (154413467/100000000000000 : ℝ)*(upper5) + (4873618014043/250000000000 : ℝ)*(major0) + (4873618014043/250000000000 : ℝ)*(major1) + (4873618014043/250000000000 : ℝ)*(major2) + (2865763732774281/100000000000000 : ℝ)*(sp0) + (1432886393372433/50000000000000 : ℝ)*(sp1) + (716443192238867/25000000000000 : ℝ)*(sp2) + (516558430298267/50000000000000 : ℝ)*(sp3) + (10070868917/100000000000000 : ℝ)*(sp4) + (1765721167/50000000000000 : ℝ)*(sp7) + (258280098009717/25000000000000 : ℝ)*(f.failure) + (1432886901821599/50000000000000 : ℝ)*(f.sum) + (2123049032691/824600000000000000000000000 : ℝ)*base66 + (2991668951281219/368125000000000000000000000000 : ℝ)*base68 + (342364253649047/184062500000000000000000000000 : ℝ)*base70 + (10340103234047/184062500000000000000000000000 : ℝ)*base72 + (2792853657411/2061500000000000000000000000 : ℝ)*base73 + (2924697515912797/184062500000000000000000000000 : ℝ)*base76 + (2348431985259047/184062500000000000000000000000 : ℝ)*base78 + (1138283123451711/92031250000000000000000000000 : ℝ)*base80 + (8413630800917/2061500000000000000000000000 : ℝ)*base81 + (8978161/1250000000000000000000 : ℝ)*base89 + (8978161/1250000000000000000000 : ℝ)*base91 + (8978161/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (173215095618747434281749/20615000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1120500597/100000000000000 : ℝ)*(base19) + (1244967149/100000000000000 : ℝ)*(base23) + (686949/390625000000 : ℝ)*(upper3) + (29584853/50000000000000 : ℝ)*(lower4) + (85899287/50000000000000 : ℝ)*(upper5) + (249177961271637/12500000000000 : ℝ)*(major0) + (249177961271637/12500000000000 : ℝ)*(major1) + (249177961271637/12500000000000 : ℝ)*(major2) + (10278279517/100000000000000 : ℝ)*(sp1) + (5647381533/50000000000000 : ℝ)*(sp2) + (1465210562790877/50000000000000 : ℝ)*(sp4) + (73260243170041/2500000000000 : ℝ)*(sp5) + (1465204292925769/50000000000000 : ℝ)*(sp6) + (1056425974685049/100000000000000 : ℝ)*(sp7) + (1056425974685049/100000000000000 : ℝ)*(f.failure) + (1465210562790877/50000000000000 : ℝ)*(f.sum) + (8545653774369/2576875000000000000000000000 : ℝ)*base65 + (1747576889918887/2300781250000000000000000000000 : ℝ)*base68 + (26480623880884649/4601562500000000000000000000000 : ℝ)*base70 + (738197919427851/4601562500000000000000000000000 : ℝ)*base71 + (16944915028627/20615000000000000000000000000 : ℝ)*base73 + (6020934296264131/1150390625000000000000000000000 : ℝ)*base76 + (315039354709101/4601562500000000000000000000000 : ℝ)*base77 + (15956077097581113/2300781250000000000000000000000 : ℝ)*base79 + (6392645666661/2576875000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (25134117/5000000000000000000000 : ℝ)*base89 + (25134117/5000000000000000000000 : ℝ)*base91 + (25134117/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1691_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (94347533/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2211/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4721/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4911/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (69/400 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1691_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1691_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (94347533/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4911/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (69/400 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1691_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1691_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1691_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5143/1024 : ℝ) ≤ p) (hpb : p ≤ (5151/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (94347533/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4911/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (69/400 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1691_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
