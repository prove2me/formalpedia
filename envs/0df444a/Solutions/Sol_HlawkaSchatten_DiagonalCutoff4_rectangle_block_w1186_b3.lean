-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1186_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:51:29.24466+00:00
-- url     : https://prove2.me/submissions/38e2f0f1-6299-4af8-868d-c8069d8409ab

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
theorem support_rectangle_w1186_s9_0 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344568611/10000000000 : ℝ)*x 0 + (329154311/625000000 : ℝ)*x 1 + (-22097769/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344568611/10000000000 : ℝ)^8379 ≤ (43641108655807/100000000000000 : ℝ)^6331 := by
    have hnat : (5344568611 : ℕ)^8379*100000000000000^6331 ≤ 43641108655807^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344568611 10000000000 43641108655807 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (329154311/625000000 : ℝ)^8379 ≤ (42799091581853/100000000000000 : ℝ)^6331 := by
    have hnat : (329154311 : ℕ)^8379*100000000000000^6331 ≤ 42799091581853^6331*625000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329154311 625000000 42799091581853 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (22097769/100000000 : ℝ)^8379 ≤ (1694974968397/12500000000000 : ℝ)^6331 := by
    have hnat : (22097769 : ℕ)^8379*12500000000000^6331 ≤ 1694974968397^6331*100000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22097769 100000000 1694974968397 12500000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344568611/10000000000 : ℝ), (329154311/625000000 : ℝ), (-22097769/100000000 : ℝ)] ![(43641108655807/100000000000000 : ℝ), (42799091581853/100000000000000 : ℝ), (1694974968397/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344568611/10000000000 : ℝ)|^8379 ≤ (43641108655807/100000000000000 : ℝ)^6331
        have hw : |(5344568611/10000000000 : ℝ)|=(5344568611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(329154311/625000000 : ℝ)|^8379 ≤ (42799091581853/100000000000000 : ℝ)^6331
        have hw : |(329154311/625000000 : ℝ)|=(329154311/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-22097769/100000000 : ℝ)|^8379 ≤ (1694974968397/12500000000000 : ℝ)^6331
        have hw : |(-22097769/100000000 : ℝ)|=(22097769/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s9_1 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4358513519/10000000000 : ℝ)*x 0 + (4234176093/10000000000 : ℝ)*x 1 + (4486446293/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4358513519/10000000000 : ℝ)^8379 ≤ (832930661747/2500000000000 : ℝ)^6331 := by
    have hnat : (4358513519 : ℕ)^8379*2500000000000^6331 ≤ 832930661747^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4358513519 10000000000 832930661747 2500000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4234176093/10000000000 : ℝ)^8379 ≤ (32065150876643/100000000000000 : ℝ)^6331 := by
    have hnat : (4234176093 : ℕ)^8379*100000000000000^6331 ≤ 32065150876643^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4234176093 10000000000 32065150876643 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4486446293/10000000000 : ℝ)^8379 ≤ (1384704905587/4000000000000 : ℝ)^6331 := by
    have hnat : (4486446293 : ℕ)^8379*4000000000000^6331 ≤ 1384704905587^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4486446293 10000000000 1384704905587 4000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4358513519/10000000000 : ℝ), (4234176093/10000000000 : ℝ), (4486446293/10000000000 : ℝ)] ![(832930661747/2500000000000 : ℝ), (32065150876643/100000000000000 : ℝ), (1384704905587/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4358513519/10000000000 : ℝ)|^8379 ≤ (832930661747/2500000000000 : ℝ)^6331
        have hw : |(4358513519/10000000000 : ℝ)|=(4358513519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4234176093/10000000000 : ℝ)|^8379 ≤ (32065150876643/100000000000000 : ℝ)^6331
        have hw : |(4234176093/10000000000 : ℝ)|=(4234176093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4486446293/10000000000 : ℝ)|^8379 ≤ (1384704905587/4000000000000 : ℝ)^6331
        have hw : |(4486446293/10000000000 : ℝ)|=(4486446293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s9_2 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2146027479/10000000000 : ℝ)*x 0 + (526678521/1000000000 : ℝ)*x 1 + (5391868183/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2146027479/10000000000 : ℝ)^8379 ≤ (13044504247641/100000000000000 : ℝ)^6331 := by
    have hnat : (2146027479 : ℕ)^8379*100000000000000^6331 ≤ 13044504247641^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2146027479 10000000000 13044504247641 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526678521/1000000000 : ℝ)^8379 ≤ (42802492903297/100000000000000 : ℝ)^6331 := by
    have hnat : (526678521 : ℕ)^8379*100000000000000^6331 ≤ 42802492903297^6331*1000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526678521 1000000000 42802492903297 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391868183/10000000000 : ℝ)^8379 ≤ (22076501418159/50000000000000 : ℝ)^6331 := by
    have hnat : (5391868183 : ℕ)^8379*50000000000000^6331 ≤ 22076501418159^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391868183 10000000000 22076501418159 50000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2146027479/10000000000 : ℝ), (526678521/1000000000 : ℝ), (5391868183/10000000000 : ℝ)] ![(13044504247641/100000000000000 : ℝ), (42802492903297/100000000000000 : ℝ), (22076501418159/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2146027479/10000000000 : ℝ)|^8379 ≤ (13044504247641/100000000000000 : ℝ)^6331
        have hw : |(-2146027479/10000000000 : ℝ)|=(2146027479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526678521/1000000000 : ℝ)|^8379 ≤ (42802492903297/100000000000000 : ℝ)^6331
        have hw : |(526678521/1000000000 : ℝ)|=(526678521/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391868183/10000000000 : ℝ)|^8379 ≤ (22076501418159/50000000000000 : ℝ)^6331
        have hw : |(5391868183/10000000000 : ℝ)|=(5391868183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s9_3 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312615703/10000000000 : ℝ)*x 0 + (-2084377779/10000000000 : ℝ)*x 1 + (5391868153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312615703/10000000000 : ℝ)^8379 ≤ (8659225932431/20000000000000 : ℝ)^6331 := by
    have hnat : (5312615703 : ℕ)^8379*20000000000000^6331 ≤ 8659225932431^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312615703 10000000000 8659225932431 20000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2084377779/10000000000 : ℝ)^8379 ≤ (6275433904653/50000000000000 : ℝ)^6331 := by
    have hnat : (2084377779 : ℕ)^8379*50000000000000^6331 ≤ 6275433904653^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084377779 10000000000 6275433904653 50000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391868153/10000000000 : ℝ)^8379 ≤ (2759562656949/6250000000000 : ℝ)^6331 := by
    have hnat : (5391868153 : ℕ)^8379*6250000000000^6331 ≤ 2759562656949^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391868153 10000000000 2759562656949 6250000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312615703/10000000000 : ℝ), (-2084377779/10000000000 : ℝ), (5391868153/10000000000 : ℝ)] ![(8659225932431/20000000000000 : ℝ), (6275433904653/50000000000000 : ℝ), (2759562656949/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312615703/10000000000 : ℝ)|^8379 ≤ (8659225932431/20000000000000 : ℝ)^6331
        have hw : |(5312615703/10000000000 : ℝ)|=(5312615703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2084377779/10000000000 : ℝ)|^8379 ≤ (6275433904653/50000000000000 : ℝ)^6331
        have hw : |(-2084377779/10000000000 : ℝ)|=(2084377779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391868153/10000000000 : ℝ)|^8379 ≤ (2759562656949/6250000000000 : ℝ)^6331
        have hw : |(5391868153/10000000000 : ℝ)|=(5391868153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s9_4 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312616027/10000000000 : ℝ)*x 0 + (1347967053/2500000000 : ℝ)*x 1 + (-2084377261/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312616027/10000000000 : ℝ)^8379 ≤ (2164806657841/5000000000000 : ℝ)^6331 := by
    have hnat : (5312616027 : ℕ)^8379*5000000000000^6331 ≤ 2164806657841^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312616027 10000000000 2164806657841 5000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1347967053/2500000000 : ℝ)^8379 ≤ (22076501575307/50000000000000 : ℝ)^6331 := by
    have hnat : (1347967053 : ℕ)^8379*50000000000000^6331 ≤ 22076501575307^6331*2500000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347967053 2500000000 22076501575307 50000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2084377261/10000000000 : ℝ)^8379 ≤ (12550863681237/100000000000000 : ℝ)^6331 := by
    have hnat : (2084377261 : ℕ)^8379*100000000000000^6331 ≤ 12550863681237^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084377261 10000000000 12550863681237 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312616027/10000000000 : ℝ), (1347967053/2500000000 : ℝ), (-2084377261/10000000000 : ℝ)] ![(2164806657841/5000000000000 : ℝ), (22076501575307/50000000000000 : ℝ), (12550863681237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312616027/10000000000 : ℝ)|^8379 ≤ (2164806657841/5000000000000 : ℝ)^6331
        have hw : |(5312616027/10000000000 : ℝ)|=(5312616027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1347967053/2500000000 : ℝ)|^8379 ≤ (22076501575307/50000000000000 : ℝ)^6331
        have hw : |(1347967053/2500000000 : ℝ)|=(1347967053/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2084377261/10000000000 : ℝ)|^8379 ≤ (12550863681237/100000000000000 : ℝ)^6331
        have hw : |(-2084377261/10000000000 : ℝ)|=(2084377261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s9_5 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4358523357/10000000000 : ℝ)*x 0 + (2242905919/5000000000 : ℝ)*x 1 + (4234812577/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4358523357/10000000000 : ℝ)^8379 ≤ (6663465200127/20000000000000 : ℝ)^6331 := by
    have hnat : (4358523357 : ℕ)^8379*20000000000000^6331 ≤ 6663465200127^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4358523357 10000000000 6663465200127 20000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2242905919/5000000000 : ℝ)^8379 ≤ (1384445747047/4000000000000 : ℝ)^6331 := by
    have hnat : (2242905919 : ℕ)^8379*4000000000000^6331 ≤ 1384445747047^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242905919 5000000000 1384445747047 4000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4234812577/10000000000 : ℝ)^8379 ≤ (32071530312843/100000000000000 : ℝ)^6331 := by
    have hnat : (4234812577 : ℕ)^8379*100000000000000^6331 ≤ 32071530312843^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4234812577 10000000000 32071530312843 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4358523357/10000000000 : ℝ), (2242905919/5000000000 : ℝ), (4234812577/10000000000 : ℝ)] ![(6663465200127/20000000000000 : ℝ), (1384445747047/4000000000000 : ℝ), (32071530312843/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4358523357/10000000000 : ℝ)|^8379 ≤ (6663465200127/20000000000000 : ℝ)^6331
        have hw : |(4358523357/10000000000 : ℝ)|=(4358523357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2242905919/5000000000 : ℝ)|^8379 ≤ (1384445747047/4000000000000 : ℝ)^6331
        have hw : |(2242905919/5000000000 : ℝ)|=(2242905919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4234812577/10000000000 : ℝ)|^8379 ≤ (32071530312843/100000000000000 : ℝ)^6331
        have hw : |(4234812577/10000000000 : ℝ)|=(4234812577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1186_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150332923/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7037/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1141/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (1141/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14073/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7037/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1141/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7037/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1141/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7037/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1141/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7037/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1141/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7037/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1141/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7037/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1141/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1141/10000 : ℝ) ^ (4189/1024 : ℝ) ≤ (13916337902369687/100000000000000000000 : ℝ) := by
    have hpowers : (1141/10000 : ℝ)^4189 ≤ (13916337902369687/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1141 : ℕ)^4189*100000000000000000000^1024 ≤ 13916337902369687^1024*10000^4189 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1141 10000 13916337902369687 100000000000000000000 4189 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1141/10000 : ℝ)) (X := (13916337902369687/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4189 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7037/50000 : ℝ) ^ (4189/1024 : ℝ) ≤ (8208602223295037/25000000000000000000 : ℝ) := by
    have hpowers : (7037/50000 : ℝ)^4189 ≤ (8208602223295037/25000000000000000000 : ℝ)^1024 := by
      have hnat : (7037 : ℕ)^4189*25000000000000000000^1024 ≤ 8208602223295037^1024*50000^4189 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7037 50000 8208602223295037 25000000000000000000 4189 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7037/50000 : ℝ)) (X := (8208602223295037/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4189 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013916337902369687/50000000000000000000 : ℝ) ≤ (5000340148768349/5000000000000000 : ℝ) ^ (4189/1024 : ℝ) := by
    have hpowers : (50013916337902369687/50000000000000000000 : ℝ)^1024 ≤ (5000340148768349/5000000000000000 : ℝ)^4189 := by
      have hnat : (50013916337902369687 : ℕ)^1024*5000000000000000^4189 ≤ 5000340148768349^4189*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013916337902369687 50000000000000000000 5000340148768349 5000000000000000 1024 4189 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000340148768349/5000000000000000 : ℝ)) (X := (50013916337902369687/50000000000000000000 : ℝ)) (by norm_num) 4189 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009350149359109967/20000000000000000000 : ℝ) ≤ (2500285654763029/2500000000000000 : ℝ) ^ (4189/1024 : ℝ) := by
    have hpowers : (20009350149359109967/20000000000000000000 : ℝ)^1024 ≤ (2500285654763029/2500000000000000 : ℝ)^4189 := by
      have hnat : (20009350149359109967 : ℕ)^1024*2500000000000000^4189 ≤ 2500285654763029^4189*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009350149359109967 20000000000000000000 2500285654763029 2500000000000000 1024 4189 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500285654763029/2500000000000000 : ℝ)) (X := (20009350149359109967/20000000000000000000 : ℝ)) (by norm_num) 4189 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508208602223295037/12500000000000000000 : ℝ) ≤ (5000802470283767/5000000000000000 : ℝ) ^ (4189/1024 : ℝ) := by
    have hpowers : (12508208602223295037/12500000000000000000 : ℝ)^1024 ≤ (5000802470283767/5000000000000000 : ℝ)^4189 := by
      have hnat : (12508208602223295037 : ℕ)^1024*5000000000000000^4189 ≤ 5000802470283767^4189*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508208602223295037 12500000000000000000 5000802470283767 5000000000000000 1024 4189 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000802470283767/5000000000000000 : ℝ)) (X := (12508208602223295037/12500000000000000000 : ℝ)) (by norm_num) 4189 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13916337902369687/100000000000000000000 : ℝ) ≤ ((1109635922318996863/1110000000000000000 : ℝ)+2*(77053585903/44400000000000 : ℝ)*(1141/10000 : ℝ))^(4189/1024 : ℝ) := by
    rw [show (1109635922318996863/1110000000000000000 : ℝ)+2*(77053585903/44400000000000 : ℝ)*(1141/10000 : ℝ)=(5000340148768349/5000000000000000 : ℝ) by norm_num, show 1+2*(13916337902369687/100000000000000000000 : ℝ)=(50013916337902369687/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8208602223295037/25000000000000000000 : ℝ)+(13916337902369687/100000000000000000000 : ℝ) ≤ ((1109635922318996863/1110000000000000000 : ℝ)+(77053585903/44400000000000 : ℝ)*((7037/50000 : ℝ)+(1141/10000 : ℝ)))^(4189/1024 : ℝ) := by
    rw [show (1109635922318996863/1110000000000000000 : ℝ)+(77053585903/44400000000000 : ℝ)*((7037/50000 : ℝ)+(1141/10000 : ℝ))=(2500285654763029/2500000000000000 : ℝ) by norm_num, show 1+(8208602223295037/25000000000000000000 : ℝ)+(13916337902369687/100000000000000000000 : ℝ)=(20009350149359109967/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8208602223295037/25000000000000000000 : ℝ) ≤ ((1109635922318996863/1110000000000000000 : ℝ)+2*(77053585903/44400000000000 : ℝ)*(7037/50000 : ℝ))^(4189/1024 : ℝ) := by
    rw [show (1109635922318996863/1110000000000000000 : ℝ)+2*(77053585903/44400000000000 : ℝ)*(7037/50000 : ℝ)=(5000802470283767/5000000000000000 : ℝ) by norm_num, show 1+2*(8208602223295037/25000000000000000000 : ℝ)=(12508208602223295037/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1109635922318996863/1110000000000000000 : ℝ)*(X 1 0+X 2 0)+(77053585903/44400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4189/1024 : ℝ)) (lo := (1141/10000 : ℝ)) (hi := (7037/50000 : ℝ)) (c := (1109635922318996863/1110000000000000000 : ℝ)) (alpha := (77053585903/44400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1109635922318996863/1110000000000000000 : ℝ)*(X 0 1+X 2 1)+(77053585903/44400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4189/1024 : ℝ)) (lo := (1141/10000 : ℝ)) (hi := (7037/50000 : ℝ)) (c := (1109635922318996863/1110000000000000000 : ℝ)) (alpha := (77053585903/44400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1109635922318996863/1110000000000000000 : ℝ)*(X 0 2+X 1 2)+(77053585903/44400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4189/1024 : ℝ)) (lo := (1141/10000 : ℝ)) (hi := (7037/50000 : ℝ)) (c := (1109635922318996863/1110000000000000000 : ℝ)) (alpha := (77053585903/44400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((5344568611/10000000000 : ℝ)*X 2 0+(329154311/625000000 : ℝ)*X 2 1+(-22097769/100000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s9_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((4358513519/10000000000 : ℝ)*X 0 0+(4234176093/10000000000 : ℝ)*X 0 1+(4486446293/10000000000 : ℝ)*X 0 2+(4358513519/10000000000 : ℝ)*X 1 0+(4234176093/10000000000 : ℝ)*X 1 1+(4486446293/10000000000 : ℝ)*X 1 2+(4358513519/10000000000 : ℝ)*X 2 0+(4234176093/10000000000 : ℝ)*X 2 1+(4486446293/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s9_1 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((-2146027479/10000000000 : ℝ)*X 0 0+(526678521/1000000000 : ℝ)*X 0 1+(5391868183/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s9_2 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5312615703/10000000000 : ℝ)*X 1 0+(-2084377779/10000000000 : ℝ)*X 1 1+(5391868153/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s9_3 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((5312616027/10000000000 : ℝ)*X 2 0+(1347967053/2500000000 : ℝ)*X 2 1+(-2084377261/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s9_4 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4358523357/10000000000 : ℝ)*X 0 0+(2242905919/5000000000 : ℝ)*X 0 1+(4234812577/10000000000 : ℝ)*X 0 2+(4358523357/10000000000 : ℝ)*X 1 0+(2242905919/5000000000 : ℝ)*X 1 1+(4234812577/10000000000 : ℝ)*X 1 2+(4358523357/10000000000 : ℝ)*X 2 0+(2242905919/5000000000 : ℝ)*X 2 1+(4234812577/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s9_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2707378422919872516890801/2312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (320200111/100000000000000 : ℝ)*(base19) + (704343883/50000000000000 : ℝ)*(base23) + (1386137/20000000000000 : ℝ)*(lower1) + (58318839/50000000000000 : ℝ)*(upper3) + (39295029/25000000000000 : ℝ)*(lower4) + (1497346457276027/25000000000000 : ℝ)*(major0) + (1497346457276027/25000000000000 : ℝ)*(major1) + (1497346457276027/25000000000000 : ℝ)*(major2) + (50720036117/100000000000000 : ℝ)*(sp0) + (611746177/100000000000000 : ℝ)*(sp1) + (7994690348373003/100000000000000 : ℝ)*(sp2) + (1998672507043223/25000000000000 : ℝ)*(sp3) + (49966488872807/625000000000 : ℝ)*(sp4) + (3187264527251/80000000000 : ℝ)*(sp5) + (1992040635404963/50000000000000 : ℝ)*(f.failure) + (7994690348373003/100000000000000 : ℝ)*(f.sum) + (2279756019701/555000000000000000000000000 : ℝ)*base65 + (468394266077621699/27750000000000000000000000000000 : ℝ)*base68 + (399588545367371699/27750000000000000000000000000000 : ℝ)*base70 + (459250477297121699/27750000000000000000000000000000 : ℝ)*base72 + (505953932117/277500000000000000000000000 : ℝ)*base74 + (79376992091621699/27750000000000000000000000000000 : ℝ)*base76 + (26517528137628301/27750000000000000000000000000000 : ℝ)*base77 + (910676374633121699/27750000000000000000000000000000 : ℝ)*base80 + (31801729703/69375000000000000000000000 : ℝ)*base82 + (23503151/5000000000000000000000 : ℝ)*base90 + (23503151/5000000000000000000000 : ℝ)*base92 + (23503151/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1186_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150332923/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7037/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1141/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1141/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14073/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1186_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1186_box_0 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1010282733/5000000000 : ℝ)*x 0 + (2687836403/5000000000 : ℝ)*x 1 + (5375672841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1010282733/5000000000 : ℝ)^8379 ≤ (1204486756739/10000000000000 : ℝ)^6331 := by
    have hnat : (1010282733 : ℕ)^8379*10000000000000^6331 ≤ 1204486756739^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1010282733 5000000000 1204486756739 10000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2687836403/5000000000 : ℝ)^8379 ≤ (21988783011009/50000000000000 : ℝ)^6331 := by
    have hnat : (2687836403 : ℕ)^8379*50000000000000^6331 ≤ 21988783011009^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687836403 5000000000 21988783011009 50000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5375672841/10000000000 : ℝ)^8379 ≤ (10994391600243/25000000000000 : ℝ)^6331 := by
    have hnat : (5375672841 : ℕ)^8379*25000000000000^6331 ≤ 10994391600243^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375672841 10000000000 10994391600243 25000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1010282733/5000000000 : ℝ), (2687836403/5000000000 : ℝ), (5375672841/10000000000 : ℝ)] ![(1204486756739/10000000000000 : ℝ), (21988783011009/50000000000000 : ℝ), (10994391600243/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1010282733/5000000000 : ℝ)|^8379 ≤ (1204486756739/10000000000000 : ℝ)^6331
        have hw : |(-1010282733/5000000000 : ℝ)|=(1010282733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2687836403/5000000000 : ℝ)|^8379 ≤ (21988783011009/50000000000000 : ℝ)^6331
        have hw : |(2687836403/5000000000 : ℝ)|=(2687836403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5375672841/10000000000 : ℝ)|^8379 ≤ (10994391600243/25000000000000 : ℝ)^6331
        have hw : |(5375672841/10000000000 : ℝ)|=(5375672841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_box_1 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1324092581/2500000000 : ℝ)*x 0 + (-1064110001/5000000000 : ℝ)*x 1 + (1075134561/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1324092581/2500000000 : ℝ)^8379 ≤ (43120993673839/100000000000000 : ℝ)^6331 := by
    have hnat : (1324092581 : ℕ)^8379*100000000000000^6331 ≤ 43120993673839^6331*2500000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1324092581 2500000000 43120993673839 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1064110001/5000000000 : ℝ)^8379 ≤ (12901440301013/100000000000000 : ℝ)^6331 := by
    have hnat : (1064110001 : ℕ)^8379*100000000000000^6331 ≤ 12901440301013^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064110001 5000000000 12901440301013 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1075134561/2000000000 : ℝ)^8379 ≤ (43977566011191/100000000000000 : ℝ)^6331 := by
    have hnat : (1075134561 : ℕ)^8379*100000000000000^6331 ≤ 43977566011191^6331*2000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075134561 2000000000 43977566011191 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1324092581/2500000000 : ℝ), (-1064110001/5000000000 : ℝ), (1075134561/2000000000 : ℝ)] ![(43120993673839/100000000000000 : ℝ), (12901440301013/100000000000000 : ℝ), (43977566011191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1324092581/2500000000 : ℝ)|^8379 ≤ (43120993673839/100000000000000 : ℝ)^6331
        have hw : |(1324092581/2500000000 : ℝ)|=(1324092581/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1064110001/5000000000 : ℝ)|^8379 ≤ (12901440301013/100000000000000 : ℝ)^6331
        have hw : |(-1064110001/5000000000 : ℝ)|=(1064110001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1075134561/2000000000 : ℝ)|^8379 ≤ (43977566011191/100000000000000 : ℝ)^6331
        have hw : |(1075134561/2000000000 : ℝ)|=(1075134561/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_box_2 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2648184957/5000000000 : ℝ)*x 0 + (5375673111/10000000000 : ℝ)*x 1 + (-1064110069/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2648184957/5000000000 : ℝ)^8379 ≤ (43120989255957/100000000000000 : ℝ)^6331 := by
    have hnat : (2648184957 : ℕ)^8379*100000000000000^6331 ≤ 43120989255957^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2648184957 5000000000 43120989255957 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5375673111/10000000000 : ℝ)^8379 ≤ (4397756932433/10000000000000 : ℝ)^6331 := by
    have hnat : (5375673111 : ℕ)^8379*10000000000000^6331 ≤ 4397756932433^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375673111 10000000000 4397756932433 10000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1064110069/5000000000 : ℝ)^8379 ≤ (12901441392153/100000000000000 : ℝ)^6331 := by
    have hnat : (1064110069 : ℕ)^8379*100000000000000^6331 ≤ 12901441392153^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064110069 5000000000 12901441392153 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2648184957/5000000000 : ℝ), (5375673111/10000000000 : ℝ), (-1064110069/5000000000 : ℝ)] ![(43120989255957/100000000000000 : ℝ), (4397756932433/10000000000000 : ℝ), (12901441392153/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2648184957/5000000000 : ℝ)|^8379 ≤ (43120989255957/100000000000000 : ℝ)^6331
        have hw : |(2648184957/5000000000 : ℝ)|=(2648184957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5375673111/10000000000 : ℝ)|^8379 ≤ (4397756932433/10000000000000 : ℝ)^6331
        have hw : |(5375673111/10000000000 : ℝ)|=(5375673111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1064110069/5000000000 : ℝ)|^8379 ≤ (12901441392153/100000000000000 : ℝ)^6331
        have hw : |(-1064110069/5000000000 : ℝ)|=(1064110069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_box_3 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4465597181/10000000000 : ℝ)*x 0 + (269190601/625000000 : ℝ)*x 1 + (4307049651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4465597181/10000000000 : ℝ)^8379 ≤ (4300608728733/12500000000000 : ℝ)^6331 := by
    have hnat : (4465597181 : ℕ)^8379*12500000000000^6331 ≤ 4300608728733^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4465597181 10000000000 4300608728733 12500000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269190601/625000000 : ℝ)^8379 ≤ (1311902596043/4000000000000 : ℝ)^6331 := by
    have hnat : (269190601 : ℕ)^8379*4000000000000^6331 ≤ 1311902596043^6331*625000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269190601 625000000 1311902596043 4000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4307049651/10000000000 : ℝ)^8379 ≤ (32797565253811/100000000000000 : ℝ)^6331 := by
    have hnat : (4307049651 : ℕ)^8379*100000000000000^6331 ≤ 32797565253811^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4307049651 10000000000 32797565253811 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4465597181/10000000000 : ℝ), (269190601/625000000 : ℝ), (4307049651/10000000000 : ℝ)] ![(4300608728733/12500000000000 : ℝ), (1311902596043/4000000000000 : ℝ), (32797565253811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4465597181/10000000000 : ℝ)|^8379 ≤ (4300608728733/12500000000000 : ℝ)^6331
        have hw : |(4465597181/10000000000 : ℝ)|=(4465597181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269190601/625000000 : ℝ)|^8379 ≤ (1311902596043/4000000000000 : ℝ)^6331
        have hw : |(269190601/625000000 : ℝ)|=(269190601/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4307049651/10000000000 : ℝ)|^8379 ≤ (32797565253811/100000000000000 : ℝ)^6331
        have hw : |(4307049651/10000000000 : ℝ)|=(4307049651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_box_4 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-568217281/2500000000 : ℝ)*x 0 + (5281675901/10000000000 : ℝ)*x 1 + (2640838133/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (568217281/2500000000 : ℝ)^8379 ≤ (14074540813913/100000000000000 : ℝ)^6331 := by
    have hnat : (568217281 : ℕ)^8379*100000000000000^6331 ≤ 14074540813913^6331*2500000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      568217281 2500000000 14074540813913 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5281675901/10000000000 : ℝ)^8379 ≤ (42962727619009/100000000000000 : ℝ)^6331 := by
    have hnat : (5281675901 : ℕ)^8379*100000000000000^6331 ≤ 42962727619009^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281675901 10000000000 42962727619009 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2640838133/5000000000 : ℝ)^8379 ≤ (42962731548469/100000000000000 : ℝ)^6331 := by
    have hnat : (2640838133 : ℕ)^8379*100000000000000^6331 ≤ 42962731548469^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640838133 5000000000 42962731548469 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-568217281/2500000000 : ℝ), (5281675901/10000000000 : ℝ), (2640838133/5000000000 : ℝ)] ![(14074540813913/100000000000000 : ℝ), (42962727619009/100000000000000 : ℝ), (42962731548469/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-568217281/2500000000 : ℝ)|^8379 ≤ (14074540813913/100000000000000 : ℝ)^6331
        have hw : |(-568217281/2500000000 : ℝ)|=(568217281/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5281675901/10000000000 : ℝ)|^8379 ≤ (42962727619009/100000000000000 : ℝ)^6331
        have hw : |(5281675901/10000000000 : ℝ)|=(5281675901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2640838133/5000000000 : ℝ)|^8379 ≤ (42962731548469/100000000000000 : ℝ)^6331
        have hw : |(2640838133/5000000000 : ℝ)|=(2640838133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_box_5 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2681356473/5000000000 : ℝ)*x 0 + (-1082661911/5000000000 : ℝ)*x 1 + (2640838303/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681356473/5000000000 : ℝ)^8379 ≤ (21918650549769/50000000000000 : ℝ)^6331 := by
    have hnat : (2681356473 : ℕ)^8379*50000000000000^6331 ≤ 21918650549769^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681356473 5000000000 21918650549769 50000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082661911/5000000000 : ℝ)^8379 ≤ (13199963676599/100000000000000 : ℝ)^6331 := by
    have hnat : (1082661911 : ℕ)^8379*100000000000000^6331 ≤ 13199963676599^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082661911 5000000000 13199963676599 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2640838303/5000000000 : ℝ)^8379 ≤ (10740683802197/25000000000000 : ℝ)^6331 := by
    have hnat : (2640838303 : ℕ)^8379*25000000000000^6331 ≤ 10740683802197^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640838303 5000000000 10740683802197 25000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681356473/5000000000 : ℝ), (-1082661911/5000000000 : ℝ), (2640838303/5000000000 : ℝ)] ![(21918650549769/50000000000000 : ℝ), (13199963676599/100000000000000 : ℝ), (10740683802197/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681356473/5000000000 : ℝ)|^8379 ≤ (21918650549769/50000000000000 : ℝ)^6331
        have hw : |(2681356473/5000000000 : ℝ)|=(2681356473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1082661911/5000000000 : ℝ)|^8379 ≤ (13199963676599/100000000000000 : ℝ)^6331
        have hw : |(-1082661911/5000000000 : ℝ)|=(1082661911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2640838303/5000000000 : ℝ)|^8379 ≤ (10740683802197/25000000000000 : ℝ)^6331
        have hw : |(2640838303/5000000000 : ℝ)|=(2640838303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_box_6 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (214508519/400000000 : ℝ)*x 0 + (330104779/625000000 : ℝ)*x 1 + (-541330993/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214508519/400000000 : ℝ)^8379 ≤ (43837301413283/100000000000000 : ℝ)^6331 := by
    have hnat : (214508519 : ℕ)^8379*100000000000000^6331 ≤ 43837301413283^6331*400000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214508519 400000000 43837301413283 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (330104779/625000000 : ℝ)^8379 ≤ (21481366840033/50000000000000 : ℝ)^6331 := by
    have hnat : (330104779 : ℕ)^8379*50000000000000^6331 ≤ 21481366840033^6331*625000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330104779 625000000 21481366840033 50000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (541330993/2500000000 : ℝ)^8379 ≤ (13199964886809/100000000000000 : ℝ)^6331 := by
    have hnat : (541330993 : ℕ)^8379*100000000000000^6331 ≤ 13199964886809^6331*2500000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541330993 2500000000 13199964886809 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214508519/400000000 : ℝ), (330104779/625000000 : ℝ), (-541330993/2500000000 : ℝ)] ![(43837301413283/100000000000000 : ℝ), (21481366840033/50000000000000 : ℝ), (13199964886809/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214508519/400000000 : ℝ)|^8379 ≤ (43837301413283/100000000000000 : ℝ)^6331
        have hw : |(214508519/400000000 : ℝ)|=(214508519/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(330104779/625000000 : ℝ)|^8379 ≤ (21481366840033/50000000000000 : ℝ)^6331
        have hw : |(330104779/625000000 : ℝ)|=(330104779/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-541330993/2500000000 : ℝ)|^8379 ≤ (13199964886809/100000000000000 : ℝ)^6331
        have hw : |(-541330993/2500000000 : ℝ)|=(541330993/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_box_7 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2125525077/5000000000 : ℝ)*x 0 + (176572097/400000000 : ℝ)*x 1 + (275893929/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2125525077/5000000000 : ℝ)^8379 ≤ (251831119189/781250000000 : ℝ)^6331 := by
    have hnat : (2125525077 : ℕ)^8379*781250000000^6331 ≤ 251831119189^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125525077 5000000000 251831119189 781250000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (176572097/400000000 : ℝ)^8379 ≤ (16941403068337/50000000000000 : ℝ)^6331 := by
    have hnat : (176572097 : ℕ)^8379*50000000000000^6331 ≤ 16941403068337^6331*400000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      176572097 400000000 16941403068337 50000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (275893929/625000000 : ℝ)^8379 ≤ (16941405298167/50000000000000 : ℝ)^6331 := by
    have hnat : (275893929 : ℕ)^8379*50000000000000^6331 ≤ 16941405298167^6331*625000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275893929 625000000 16941405298167 50000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2125525077/5000000000 : ℝ), (176572097/400000000 : ℝ), (275893929/625000000 : ℝ)] ![(251831119189/781250000000 : ℝ), (16941403068337/50000000000000 : ℝ), (16941405298167/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2125525077/5000000000 : ℝ)|^8379 ≤ (251831119189/781250000000 : ℝ)^6331
        have hw : |(2125525077/5000000000 : ℝ)|=(2125525077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(176572097/400000000 : ℝ)|^8379 ≤ (16941403068337/50000000000000 : ℝ)^6331
        have hw : |(176572097/400000000 : ℝ)|=(176572097/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(275893929/625000000 : ℝ)|^8379 ≤ (16941405298167/50000000000000 : ℝ)^6331
        have hw : |(275893929/625000000 : ℝ)|=(275893929/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_box_8 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-69376843/312500000 : ℝ)*x 0 + (1304416459/2500000000 : ℝ)*x 1 + (5385284207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (69376843/312500000 : ℝ)^8379 ≤ (2728673237963/20000000000000 : ℝ)^6331 := by
    have hnat : (69376843 : ℕ)^8379*20000000000000^6331 ≤ 2728673237963^6331*312500000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69376843 312500000 2728673237963 20000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1304416459/2500000000 : ℝ)^8379 ≤ (8454994524863/20000000000000 : ℝ)^6331 := by
    have hnat : (1304416459 : ℕ)^8379*20000000000000^6331 ≤ 8454994524863^6331*2500000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304416459 2500000000 8454994524863 20000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5385284207/10000000000 : ℝ)^8379 ≤ (22040830581807/50000000000000 : ℝ)^6331 := by
    have hnat : (5385284207 : ℕ)^8379*50000000000000^6331 ≤ 22040830581807^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385284207 10000000000 22040830581807 50000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-69376843/312500000 : ℝ), (1304416459/2500000000 : ℝ), (5385284207/10000000000 : ℝ)] ![(2728673237963/20000000000000 : ℝ), (8454994524863/20000000000000 : ℝ), (22040830581807/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-69376843/312500000 : ℝ)|^8379 ≤ (2728673237963/20000000000000 : ℝ)^6331
        have hw : |(-69376843/312500000 : ℝ)|=(69376843/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1304416459/2500000000 : ℝ)|^8379 ≤ (8454994524863/20000000000000 : ℝ)^6331
        have hw : |(1304416459/2500000000 : ℝ)|=(1304416459/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5385284207/10000000000 : ℝ)|^8379 ≤ (22040830581807/50000000000000 : ℝ)^6331
        have hw : |(5385284207/10000000000 : ℝ)|=(5385284207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_box_9 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2644791589/5000000000 : ℝ)*x 0 + (-212435803/1000000000 : ℝ)*x 1 + (2692642067/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644791589/5000000000 : ℝ)^8379 ≤ (43047875146901/100000000000000 : ℝ)^6331 := by
    have hnat : (2644791589 : ℕ)^8379*100000000000000^6331 ≤ 43047875146901^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644791589 5000000000 43047875146901 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (212435803/1000000000 : ℝ)^8379 ≤ (514818578321/4000000000000 : ℝ)^6331 := by
    have hnat : (212435803 : ℕ)^8379*4000000000000^6331 ≤ 514818578321^6331*1000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212435803 1000000000 514818578321 4000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2692642067/5000000000 : ℝ)^8379 ≤ (1377551886649/3125000000000 : ℝ)^6331 := by
    have hnat : (2692642067 : ℕ)^8379*3125000000000^6331 ≤ 1377551886649^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692642067 5000000000 1377551886649 3125000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644791589/5000000000 : ℝ), (-212435803/1000000000 : ℝ), (2692642067/5000000000 : ℝ)] ![(43047875146901/100000000000000 : ℝ), (514818578321/4000000000000 : ℝ), (1377551886649/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644791589/5000000000 : ℝ)|^8379 ≤ (43047875146901/100000000000000 : ℝ)^6331
        have hw : |(2644791589/5000000000 : ℝ)|=(2644791589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-212435803/1000000000 : ℝ)|^8379 ≤ (514818578321/4000000000000 : ℝ)^6331
        have hw : |(-212435803/1000000000 : ℝ)|=(212435803/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2692642067/5000000000 : ℝ)|^8379 ≤ (1377551886649/3125000000000 : ℝ)^6331
        have hw : |(2692642067/5000000000 : ℝ)|=(2692642067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_box_10 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2644791593/5000000000 : ℝ)*x 0 + (5385284219/10000000000 : ℝ)*x 1 + (-424871581/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644791593/5000000000 : ℝ)^8379 ≤ (10761968808267/25000000000000 : ℝ)^6331 := by
    have hnat : (2644791593 : ℕ)^8379*25000000000000^6331 ≤ 10761968808267^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644791593 5000000000 10761968808267 25000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5385284219/10000000000 : ℝ)^8379 ≤ (2755103830851/6250000000000 : ℝ)^6331 := by
    have hnat : (5385284219 : ℕ)^8379*6250000000000^6331 ≤ 2755103830851^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385284219 10000000000 2755103830851 6250000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (424871581/2000000000 : ℝ)^8379 ≤ (804403965983/6250000000000 : ℝ)^6331 := by
    have hnat : (424871581 : ℕ)^8379*6250000000000^6331 ≤ 804403965983^6331*2000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424871581 2000000000 804403965983 6250000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644791593/5000000000 : ℝ), (5385284219/10000000000 : ℝ), (-424871581/2000000000 : ℝ)] ![(10761968808267/25000000000000 : ℝ), (2755103830851/6250000000000 : ℝ), (804403965983/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644791593/5000000000 : ℝ)|^8379 ≤ (10761968808267/25000000000000 : ℝ)^6331
        have hw : |(2644791593/5000000000 : ℝ)|=(2644791593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5385284219/10000000000 : ℝ)|^8379 ≤ (2755103830851/6250000000000 : ℝ)^6331
        have hw : |(5385284219/10000000000 : ℝ)|=(5385284219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-424871581/2000000000 : ℝ)|^8379 ≤ (804403965983/6250000000000 : ℝ)^6331
        have hw : |(-424871581/2000000000 : ℝ)|=(424871581/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_box_11 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (560907751/1250000000 : ℝ)*x 0 + (4296076643/10000000000 : ℝ)*x 1 + (4296076731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (560907751/1250000000 : ℝ)^8379 ≤ (17312976519907/50000000000000 : ℝ)^6331 := by
    have hnat : (560907751 : ℕ)^8379*50000000000000^6331 ≤ 17312976519907^6331*1250000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560907751 1250000000 17312976519907 50000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4296076643/10000000000 : ℝ)^8379 ≤ (32687023029617/100000000000000 : ℝ)^6331 := by
    have hnat : (4296076643 : ℕ)^8379*100000000000000^6331 ≤ 32687023029617^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4296076643 10000000000 32687023029617 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4296076731/10000000000 : ℝ)^8379 ≤ (6537404783153/20000000000000 : ℝ)^6331 := by
    have hnat : (4296076731 : ℕ)^8379*20000000000000^6331 ≤ 6537404783153^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4296076731 10000000000 6537404783153 20000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(560907751/1250000000 : ℝ), (4296076643/10000000000 : ℝ), (4296076731/10000000000 : ℝ)] ![(17312976519907/50000000000000 : ℝ), (32687023029617/100000000000000 : ℝ), (6537404783153/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(560907751/1250000000 : ℝ)|^8379 ≤ (17312976519907/50000000000000 : ℝ)^6331
        have hw : |(560907751/1250000000 : ℝ)|=(560907751/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4296076643/10000000000 : ℝ)|^8379 ≤ (32687023029617/100000000000000 : ℝ)^6331
        have hw : |(4296076643/10000000000 : ℝ)|=(4296076643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4296076731/10000000000 : ℝ)|^8379 ≤ (6537404783153/20000000000000 : ℝ)^6331
        have hw : |(4296076731/10000000000 : ℝ)|=(4296076731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_box_12 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-518416907/2500000000 : ℝ)*x 0 + (2719218399/5000000000 : ℝ)*x 1 + (659202307/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (518416907/2500000000 : ℝ)^8379 ≤ (6232793502729/50000000000000 : ℝ)^6331 := by
    have hnat : (518416907 : ℕ)^8379*50000000000000^6331 ≤ 6232793502729^6331*2500000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518416907 2500000000 6232793502729 50000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2719218399/5000000000 : ℝ)^8379 ≤ (22329203762919/50000000000000 : ℝ)^6331 := by
    have hnat : (2719218399 : ℕ)^8379*50000000000000^6331 ≤ 22329203762919^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719218399 5000000000 22329203762919 50000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (659202307/1250000000 : ℝ)^8379 ≤ (42876005453641/100000000000000 : ℝ)^6331 := by
    have hnat : (659202307 : ℕ)^8379*100000000000000^6331 ≤ 42876005453641^6331*1250000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659202307 1250000000 42876005453641 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-518416907/2500000000 : ℝ), (2719218399/5000000000 : ℝ), (659202307/1250000000 : ℝ)] ![(6232793502729/50000000000000 : ℝ), (22329203762919/50000000000000 : ℝ), (42876005453641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-518416907/2500000000 : ℝ)|^8379 ≤ (6232793502729/50000000000000 : ℝ)^6331
        have hw : |(-518416907/2500000000 : ℝ)|=(518416907/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2719218399/5000000000 : ℝ)|^8379 ≤ (22329203762919/50000000000000 : ℝ)^6331
        have hw : |(2719218399/5000000000 : ℝ)|=(2719218399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(659202307/1250000000 : ℝ)|^8379 ≤ (42876005453641/100000000000000 : ℝ)^6331
        have hw : |(659202307/1250000000 : ℝ)|=(659202307/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_box_13 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1073679827/2000000000 : ℝ)*x 0 + (-542111639/2500000000 : ℝ)*x 1 + (2636809281/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073679827/2000000000 : ℝ)^8379 ≤ (21949414697421/50000000000000 : ℝ)^6331 := by
    have hnat : (1073679827 : ℕ)^8379*50000000000000^6331 ≤ 21949414697421^6331*2000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073679827 2000000000 21949414697421 50000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (542111639/2500000000 : ℝ)^8379 ≤ (2645032798787/20000000000000 : ℝ)^6331 := by
    have hnat : (542111639 : ℕ)^8379*20000000000000^6331 ≤ 2645032798787^6331*2500000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542111639 2500000000 2645032798787 20000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2636809281/5000000000 : ℝ)^8379 ≤ (10719001648559/25000000000000 : ℝ)^6331 := by
    have hnat : (2636809281 : ℕ)^8379*25000000000000^6331 ≤ 10719001648559^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636809281 5000000000 10719001648559 25000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073679827/2000000000 : ℝ), (-542111639/2500000000 : ℝ), (2636809281/5000000000 : ℝ)] ![(21949414697421/50000000000000 : ℝ), (2645032798787/20000000000000 : ℝ), (10719001648559/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073679827/2000000000 : ℝ)|^8379 ≤ (21949414697421/50000000000000 : ℝ)^6331
        have hw : |(1073679827/2000000000 : ℝ)|=(1073679827/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-542111639/2500000000 : ℝ)|^8379 ≤ (2645032798787/20000000000000 : ℝ)^6331
        have hw : |(-542111639/2500000000 : ℝ)|=(542111639/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2636809281/5000000000 : ℝ)|^8379 ≤ (10719001648559/25000000000000 : ℝ)^6331
        have hw : |(2636809281/5000000000 : ℝ)|=(2636809281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_box_14 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (536839949/1000000000 : ℝ)*x 0 + (527361781/1000000000 : ℝ)*x 1 + (-2168447083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536839949/1000000000 : ℝ)^8379 ≤ (21949416618417/50000000000000 : ℝ)^6331 := by
    have hnat : (536839949 : ℕ)^8379*50000000000000^6331 ≤ 21949416618417^6331*1000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536839949 1000000000 21949416618417 50000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (527361781/1000000000 : ℝ)^8379 ≤ (4287599850247/10000000000000 : ℝ)^6331 := by
    have hnat : (527361781 : ℕ)^8379*10000000000000^6331 ≤ 4287599850247^6331*1000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527361781 1000000000 4287599850247 10000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2168447083/10000000000 : ℝ)^8379 ≤ (826573015487/6250000000000 : ℝ)^6331 := by
    have hnat : (2168447083 : ℕ)^8379*6250000000000^6331 ≤ 826573015487^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2168447083 10000000000 826573015487 6250000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(536839949/1000000000 : ℝ), (527361781/1000000000 : ℝ), (-2168447083/10000000000 : ℝ)] ![(21949416618417/50000000000000 : ℝ), (4287599850247/10000000000000 : ℝ), (826573015487/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(536839949/1000000000 : ℝ)|^8379 ≤ (21949416618417/50000000000000 : ℝ)^6331
        have hw : |(536839949/1000000000 : ℝ)|=(536839949/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(527361781/1000000000 : ℝ)|^8379 ≤ (4287599850247/10000000000000 : ℝ)^6331
        have hw : |(527361781/1000000000 : ℝ)|=(527361781/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2168447083/10000000000 : ℝ)|^8379 ≤ (826573015487/6250000000000 : ℝ)^6331
        have hw : |(-2168447083/10000000000 : ℝ)|=(2168447083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_box_15 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (423242761/1000000000 : ℝ)*x 0 + (4423492119/10000000000 : ℝ)*x 1 + (884698169/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (423242761/1000000000 : ℝ)^8379 ≤ (16023813773067/50000000000000 : ℝ)^6331 := by
    have hnat : (423242761 : ℕ)^8379*50000000000000^6331 ≤ 16023813773067^6331*1000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423242761 1000000000 16023813773067 50000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4423492119/10000000000 : ℝ)^8379 ≤ (679523853841/2000000000000 : ℝ)^6331 := by
    have hnat : (4423492119 : ℕ)^8379*2000000000000^6331 ≤ 679523853841^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4423492119 10000000000 679523853841 2000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (884698169/2000000000 : ℝ)^8379 ≤ (16988089870593/50000000000000 : ℝ)^6331 := by
    have hnat : (884698169 : ℕ)^8379*50000000000000^6331 ≤ 16988089870593^6331*2000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      884698169 2000000000 16988089870593 50000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(423242761/1000000000 : ℝ), (4423492119/10000000000 : ℝ), (884698169/2000000000 : ℝ)] ![(16023813773067/50000000000000 : ℝ), (679523853841/2000000000000 : ℝ), (16988089870593/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(423242761/1000000000 : ℝ)|^8379 ≤ (16023813773067/50000000000000 : ℝ)^6331
        have hw : |(423242761/1000000000 : ℝ)|=(423242761/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4423492119/10000000000 : ℝ)|^8379 ≤ (679523853841/2000000000000 : ℝ)^6331
        have hw : |(4423492119/10000000000 : ℝ)|=(4423492119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(884698169/2000000000 : ℝ)|^8379 ≤ (16988089870593/50000000000000 : ℝ)^6331
        have hw : |(884698169/2000000000 : ℝ)|=(884698169/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1186_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150332923/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14073/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1141/10000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62237/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59333/100000 : ℝ) ∧ (39971/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (41611/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14073/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1141/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14073/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1141/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14073/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1141/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14073/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1141/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14073/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1141/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14073/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1141/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1141/10000 : ℝ) ^ (4189/1024 : ℝ) ≤ (13916337902369687/100000000000000000000 : ℝ) := by
    have hpowers : (1141/10000 : ℝ)^4189 ≤ (13916337902369687/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1141 : ℕ)^4189*100000000000000000000^1024 ≤ 13916337902369687^1024*10000^4189 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1141 10000 13916337902369687 100000000000000000000 4189 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1141/10000 : ℝ)) (X := (13916337902369687/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4189 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14073/100000 : ℝ) ^ (4189/1024 : ℝ) ≤ (16412433062531907/50000000000000000000 : ℝ) := by
    have hpowers : (14073/100000 : ℝ)^4189 ≤ (16412433062531907/50000000000000000000 : ℝ)^1024 := by
      have hnat : (14073 : ℕ)^4189*50000000000000000000^1024 ≤ 16412433062531907^1024*100000^4189 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14073 100000 16412433062531907 50000000000000000000 4189 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14073/100000 : ℝ)) (X := (16412433062531907/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4189 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013916337902369687/50000000000000000000 : ℝ) ≤ (5000340148768349/5000000000000000 : ℝ) ^ (4189/1024 : ℝ) := by
    have hpowers : (50013916337902369687/50000000000000000000 : ℝ)^1024 ≤ (5000340148768349/5000000000000000 : ℝ)^4189 := by
      have hnat : (50013916337902369687 : ℕ)^1024*5000000000000000^4189 ≤ 5000340148768349^4189*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013916337902369687 50000000000000000000 5000340148768349 5000000000000000 1024 4189 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000340148768349/5000000000000000 : ℝ)) (X := (50013916337902369687/50000000000000000000 : ℝ)) (by norm_num) 4189 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046741204027433501/100000000000000000000 : ℝ) ≤ (625071399116359/625000000000000 : ℝ) ^ (4189/1024 : ℝ) := by
    have hpowers : (100046741204027433501/100000000000000000000 : ℝ)^1024 ≤ (625071399116359/625000000000000 : ℝ)^4189 := by
      have hnat : (100046741204027433501 : ℕ)^1024*625000000000000^4189 ≤ 625071399116359^4189*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046741204027433501 100000000000000000000 625071399116359 625000000000000 1024 4189 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625071399116359/625000000000000 : ℝ)) (X := (100046741204027433501/100000000000000000000 : ℝ)) (by norm_num) 4189 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016412433062531907/25000000000000000000 : ℝ) ≤ (1000160447418679/1000000000000000 : ℝ) ^ (4189/1024 : ℝ) := by
    have hpowers : (25016412433062531907/25000000000000000000 : ℝ)^1024 ≤ (1000160447418679/1000000000000000 : ℝ)^4189 := by
      have hnat : (25016412433062531907 : ℕ)^1024*1000000000000000^4189 ≤ 1000160447418679^4189*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016412433062531907 25000000000000000000 1000160447418679 1000000000000000 1024 4189 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000160447418679/1000000000000000 : ℝ)) (X := (25016412433062531907/25000000000000000000 : ℝ)) (by norm_num) 4189 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13916337902369687/100000000000000000000 : ℝ) ≤ ((13310633388381338527/13315000000000000000 : ℝ)+2*(231044162523/133150000000000 : ℝ)*(1141/10000 : ℝ))^(4189/1024 : ℝ) := by
    rw [show (13310633388381338527/13315000000000000000 : ℝ)+2*(231044162523/133150000000000 : ℝ)*(1141/10000 : ℝ)=(5000340148768349/5000000000000000 : ℝ) by norm_num, show 1+2*(13916337902369687/100000000000000000000 : ℝ)=(50013916337902369687/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16412433062531907/50000000000000000000 : ℝ)+(13916337902369687/100000000000000000000 : ℝ) ≤ ((13310633388381338527/13315000000000000000 : ℝ)+(231044162523/133150000000000 : ℝ)*((14073/100000 : ℝ)+(1141/10000 : ℝ)))^(4189/1024 : ℝ) := by
    rw [show (13310633388381338527/13315000000000000000 : ℝ)+(231044162523/133150000000000 : ℝ)*((14073/100000 : ℝ)+(1141/10000 : ℝ))=(625071399116359/625000000000000 : ℝ) by norm_num, show 1+(16412433062531907/50000000000000000000 : ℝ)+(13916337902369687/100000000000000000000 : ℝ)=(100046741204027433501/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16412433062531907/50000000000000000000 : ℝ) ≤ ((13310633388381338527/13315000000000000000 : ℝ)+2*(231044162523/133150000000000 : ℝ)*(14073/100000 : ℝ))^(4189/1024 : ℝ) := by
    rw [show (13310633388381338527/13315000000000000000 : ℝ)+2*(231044162523/133150000000000 : ℝ)*(14073/100000 : ℝ)=(1000160447418679/1000000000000000 : ℝ) by norm_num, show 1+2*(16412433062531907/50000000000000000000 : ℝ)=(25016412433062531907/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13310633388381338527/13315000000000000000 : ℝ)*(X 1 0+X 2 0)+(231044162523/133150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4189/1024 : ℝ)) (lo := (1141/10000 : ℝ)) (hi := (14073/100000 : ℝ)) (c := (13310633388381338527/13315000000000000000 : ℝ)) (alpha := (231044162523/133150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13310633388381338527/13315000000000000000 : ℝ)*(X 0 1+X 2 1)+(231044162523/133150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4189/1024 : ℝ)) (lo := (1141/10000 : ℝ)) (hi := (14073/100000 : ℝ)) (c := (13310633388381338527/13315000000000000000 : ℝ)) (alpha := (231044162523/133150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13310633388381338527/13315000000000000000 : ℝ)*(X 0 2+X 1 2)+(231044162523/133150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4189/1024 : ℝ)) (lo := (1141/10000 : ℝ)) (hi := (14073/100000 : ℝ)) (c := (13310633388381338527/13315000000000000000 : ℝ)) (alpha := (231044162523/133150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1010282733/5000000000 : ℝ)*X 0 0+(2687836403/5000000000 : ℝ)*X 0 1+(5375672841/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1324092581/2500000000 : ℝ)*X 1 0+(-1064110001/5000000000 : ℝ)*X 1 1+(1075134561/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2648184957/5000000000 : ℝ)*X 2 0+(5375673111/10000000000 : ℝ)*X 2 1+(-1064110069/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4465597181/10000000000 : ℝ)*X 0 0+(269190601/625000000 : ℝ)*X 0 1+(4307049651/10000000000 : ℝ)*X 0 2+(4465597181/10000000000 : ℝ)*X 1 0+(269190601/625000000 : ℝ)*X 1 1+(4307049651/10000000000 : ℝ)*X 1 2+(4465597181/10000000000 : ℝ)*X 2 0+(269190601/625000000 : ℝ)*X 2 1+(4307049651/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-568217281/2500000000 : ℝ)*X 0 0+(5281675901/10000000000 : ℝ)*X 0 1+(2640838133/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2681356473/5000000000 : ℝ)*X 1 0+(-1082661911/5000000000 : ℝ)*X 1 1+(2640838303/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((214508519/400000000 : ℝ)*X 2 0+(330104779/625000000 : ℝ)*X 2 1+(-541330993/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2125525077/5000000000 : ℝ)*X 0 0+(176572097/400000000 : ℝ)*X 0 1+(275893929/625000000 : ℝ)*X 0 2+(2125525077/5000000000 : ℝ)*X 1 0+(176572097/400000000 : ℝ)*X 1 1+(275893929/625000000 : ℝ)*X 1 2+(2125525077/5000000000 : ℝ)*X 2 0+(176572097/400000000 : ℝ)*X 2 1+(275893929/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-69376843/312500000 : ℝ)*X 0 0+(1304416459/2500000000 : ℝ)*X 0 1+(5385284207/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2644791589/5000000000 : ℝ)*X 1 0+(-212435803/1000000000 : ℝ)*X 1 1+(2692642067/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2644791593/5000000000 : ℝ)*X 2 0+(5385284219/10000000000 : ℝ)*X 2 1+(-424871581/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((560907751/1250000000 : ℝ)*X 0 0+(4296076643/10000000000 : ℝ)*X 0 1+(4296076731/10000000000 : ℝ)*X 0 2+(560907751/1250000000 : ℝ)*X 1 0+(4296076643/10000000000 : ℝ)*X 1 1+(4296076731/10000000000 : ℝ)*X 1 2+(560907751/1250000000 : ℝ)*X 2 0+(4296076643/10000000000 : ℝ)*X 2 1+(4296076731/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-518416907/2500000000 : ℝ)*X 0 0+(2719218399/5000000000 : ℝ)*X 0 1+(659202307/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1073679827/2000000000 : ℝ)*X 1 0+(-542111639/2500000000 : ℝ)*X 1 1+(2636809281/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((536839949/1000000000 : ℝ)*X 2 0+(527361781/1000000000 : ℝ)*X 2 1+(-2168447083/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((423242761/1000000000 : ℝ)*X 0 0+(4423492119/10000000000 : ℝ)*X 0 1+(884698169/2000000000 : ℝ)*X 0 2+(423242761/1000000000 : ℝ)*X 1 0+(4423492119/10000000000 : ℝ)*X 1 1+(884698169/2000000000 : ℝ)*X 1 2+(423242761/1000000000 : ℝ)*X 2 0+(4423492119/10000000000 : ℝ)*X 2 1+(884698169/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62237/100000 : ℝ) ≤ (-5179077675468615109955955225879/8321875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21427489/25000000000000 : ℝ)*(upper1) + (85651751/50000000000000 : ℝ)*(lower4) + (224244853/100000000000000 : ℝ)*(upper5) + (49463818839553/1250000000000 : ℝ)*(major0) + (49463818839553/1250000000000 : ℝ)*(major1) + (49463818839553/1250000000000 : ℝ)*(major2) + (8406211079/100000000000000 : ℝ)*(sp3) + (662840410814179/12500000000000 : ℝ)*(sp4) + (1325598294592419/25000000000000 : ℝ)*(sp5) + (2651360742728393/50000000000000 : ℝ)*(sp6) + (10528878946527/400000000000 : ℝ)*(sp7) + (2209911/50000000000 : ℝ)*(sp12) + (83631991439/25000000000000 : ℝ)*(sp13) + (3110439323/50000000000000 : ℝ)*(sp14) + (2632228142842829/100000000000000 : ℝ)*(f.failure) + (5302727706335433/100000000000000 : ℝ)*(f.sum) + (748375682371/532600000000000000000000000 : ℝ)*base65 + (232248558204145931/16643750000000000000000000000000 : ℝ)*base67 + (93171640686739681/16643750000000000000000000000000 : ℝ)*base69 + (227981821228727181/16643750000000000000000000000000 : ℝ)*base71 + (2795757662317/266300000000000000000000000 : ℝ)*base74 + (113618061215439681/16643750000000000000000000000000 : ℝ)*base75 + (159022731632214681/16643750000000000000000000000000 : ℝ)*base77 + (252513792939670931/16643750000000000000000000000000 : ℝ)*base79 + (3288930482989/2663000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (13159167/10000000000000000000000 : ℝ)*base89 + (13159167/10000000000000000000000 : ℝ)*base91 + (13159167/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (59333/100000 : ℝ) ≤ (19751234179089031733493831114849/33287500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (20729311/25000000000000 : ℝ)*(lower0) + (3235337/10000000000000 : ℝ)*(upper2) + (152014699/100000000000000 : ℝ)*(lower4) + (402199355089471/10000000000000 : ℝ)*(major0) + (402199355089471/10000000000000 : ℝ)*(major1) + (402199355089471/10000000000000 : ℝ)*(major2) + (2674407300240669/50000000000000 : ℝ)*(sp0) + (5348816389066349/100000000000000 : ℝ)*(sp1) + (1069762224699281/20000000000000 : ℝ)*(sp2) + (668847190496817/25000000000000 : ℝ)*(sp3) + (124401317/10000000000000 : ℝ)*(sp5) + (3254791557/50000000000000 : ℝ)*(sp6) + (2277202937/100000000000000 : ℝ)*(sp7) + (3032598181/100000000000000 : ℝ)*(sp12) + (668847759797551/25000000000000 : ℝ)*(f.failure) + (5348817633079519/100000000000000 : ℝ)*(f.sum) + (47370054599321/1331500000000000000000000000 : ℝ)*base65 + (1953114837976200783/133150000000000000000000000000000 : ℝ)*base68 + (391143415243149217/133150000000000000000000000000000 : ℝ)*base69 + (6797097118036349217/133150000000000000000000000000000 : ℝ)*base71 + (12772463454793/2663000000000000000000000000 : ℝ)*base74 + (652480891974499217/133150000000000000000000000000000 : ℝ)*base75 + (2196266980030749217/133150000000000000000000000000000 : ℝ)*base77 + (172766585621049217/133150000000000000000000000000000 : ℝ)*base79 + (3362501032381/1331500000000000000000000000 : ℝ)*base82 + (19928427/2500000000000000000000 : ℝ)*base90 + (19928427/2500000000000000000000 : ℝ)*base92 + (19928427/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (39971/50000 : ℝ) ≤ (66528669690837894894623652091221/83218750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2715229/50000000000000 : ℝ)*(upper0) + (2928039/25000000000000 : ℝ)*(lower1) + (61719557/100000000000000 : ℝ)*(lower3) + (43416107/100000000000000 : ℝ)*(upper4) + (1122366753301691/25000000000000 : ℝ)*(major0) + (1122366753301691/25000000000000 : ℝ)*(major1) + (1122366753301691/25000000000000 : ℝ)*(major2) + (6717144171/100000000000000 : ℝ)*(sp1) + (6365715937/10000000000000 : ℝ)*(sp2) + (8158250967/25000000000000 : ℝ)*(sp3) + (2982968036123029/50000000000000 : ℝ)*(sp8) + (5965929355101887/100000000000000 : ℝ)*(sp9) + (5965872415086687/100000000000000 : ℝ)*(sp10) + (2986317212137349/100000000000000 : ℝ)*(sp11) + (93323432660663/3125000000000 : ℝ)*(f.failure) + (2982968036123029/50000000000000 : ℝ)*(f.sum) + (15455355654209/3328750000000000000000000000 : ℝ)*base66 + (1068541594694275843/332875000000000000000000000000000 : ℝ)*base68 + (3551207765123025843/332875000000000000000000000000000 : ℝ)*base70 + (1059967602499400843/332875000000000000000000000000000 : ℝ)*base72 + (8312789637901/13315000000000000000000000000 : ℝ)*base74 + (1606593460390650843/332875000000000000000000000000000 : ℝ)*base76 + (1390712426191400843/332875000000000000000000000000000 : ℝ)*base78 + (144282464405099157/332875000000000000000000000000000 : ℝ)*base79 + (244707306979/832187500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (1592051/312500000000000000000 : ℝ)*base90 + (1592051/312500000000000000000 : ℝ)*base92 + (1592051/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-41611/50000 : ℝ) ≤ (-69254666381120377650302287370991/83218750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (208218089/20000000000000 : ℝ)*(lower0) + (112143287/20000000000000 : ℝ)*(lower1) + (2561589/6250000000000 : ℝ)*(lower2) + (23126139/10000000000000 : ℝ)*(lower4) + (1131162655259111/25000000000000 : ℝ)*(major0) + (1131162655259111/25000000000000 : ℝ)*(major1) + (1131162655259111/25000000000000 : ℝ)*(major2) + (5918551063/25000000000000 : ℝ)*(sp0) + (915865961483/100000000000000 : ℝ)*(sp5) + (101824598603/6250000000000 : ℝ)*(sp6) + (47400499512877/781250000000 : ℝ)*(sp12) + (379148234118189/6250000000000 : ℝ)*(sp13) + (303282920913743/5000000000000 : ℝ)*(sp14) + (752438409821321/25000000000000 : ℝ)*(sp15) + (752438409821321/25000000000000 : ℝ)*(f.failure) + (6067287611852507/100000000000000 : ℝ)*(f.sum) + (19360057568897/1664375000000000000000000000 : ℝ)*base66 + (2285182558846130503/332875000000000000000000000000000 : ℝ)*base68 + (237815058819369497/332875000000000000000000000000000 : ℝ)*base69 + (4409585393163119497/332875000000000000000000000000000 : ℝ)*base71 + (20961997789617/6657500000000000000000000000 : ℝ)*base73 + (2896547096015119497/332875000000000000000000000000000 : ℝ)*base75 + (2400324916307369497/332875000000000000000000000000000 : ℝ)*base77 + (912934684511869497/332875000000000000000000000000000 : ℝ)*base79 + (11811454746883/1664375000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (6348717/2500000000000000000000 : ℝ)*base90 + (6348717/2500000000000000000000 : ℝ)*base92 + (6348717/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1186_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150332923/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14073/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1141/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62237/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59333/100000 : ℝ) else (39971/50000 : ℝ) ≤ X j i ∧ X j i ≤ (41611/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1186_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1186_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150332923/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7037/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1141/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62237/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59333/100000 : ℝ) else (39971/50000 : ℝ) ≤ X j i ∧ X j i ≤ (41611/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1186_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1186_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150332923/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7037/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1141/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62237/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59333/100000 : ℝ) else (39971/50000 : ℝ) ≤ X j i ∧ X j i ≤ (41611/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1186_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
