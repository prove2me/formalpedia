-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1585_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:31:25.537665+00:00
-- url     : https://prove2.me/submissions/1454dc2d-5f85-46f0-9885-4a4e8a2a8d74

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
theorem support_rectangle_w1585_s0_0 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-322214109/2000000000 : ℝ)*x 0 + (5858790417/10000000000 : ℝ)*x 1 + (977063553/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (322214109/2000000000 : ℝ)^4667 ≤ (2410930899231/25000000000000 : ℝ)^3643 := by
    have hnat : (322214109 : ℕ)^4667*25000000000000^3643 ≤ 2410930899231^3643*2000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      322214109 2000000000 2410930899231 25000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5858790417/10000000000 : ℝ)^4667 ≤ (630161416289/1250000000000 : ℝ)^3643 := by
    have hnat : (5858790417 : ℕ)^4667*1250000000000^3643 ≤ 630161416289^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5858790417 10000000000 630161416289 1250000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (977063553/2000000000 : ℝ)^4667 ≤ (1997168153883/5000000000000 : ℝ)^3643 := by
    have hnat : (977063553 : ℕ)^4667*5000000000000^3643 ≤ 1997168153883^3643*2000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      977063553 2000000000 1997168153883 5000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-322214109/2000000000 : ℝ), (5858790417/10000000000 : ℝ), (977063553/2000000000 : ℝ)] ![(2410930899231/25000000000000 : ℝ), (630161416289/1250000000000 : ℝ), (1997168153883/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-322214109/2000000000 : ℝ)|^4667 ≤ (2410930899231/25000000000000 : ℝ)^3643
        have hw : |(-322214109/2000000000 : ℝ)|=(322214109/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5858790417/10000000000 : ℝ)|^4667 ≤ (630161416289/1250000000000 : ℝ)^3643
        have hw : |(5858790417/10000000000 : ℝ)|=(5858790417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(977063553/2000000000 : ℝ)|^4667 ≤ (1997168153883/5000000000000 : ℝ)^3643
        have hw : |(977063553/2000000000 : ℝ)|=(977063553/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1585_s0_1 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2731143959/5000000000 : ℝ)*x 0 + (-215181779/1000000000 : ℝ)*x 1 + (4885317677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2731143959/5000000000 : ℝ)^4667 ≤ (46084406070503/100000000000000 : ℝ)^3643 := by
    have hnat : (2731143959 : ℕ)^4667*100000000000000^3643 ≤ 46084406070503^3643*5000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2731143959 5000000000 46084406070503 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215181779/1000000000 : ℝ)^4667 ≤ (13972231758157/100000000000000 : ℝ)^3643 := by
    have hnat : (215181779 : ℕ)^4667*100000000000000^3643 ≤ 13972231758157^3643*1000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215181779 1000000000 13972231758157 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4885317677/10000000000 : ℝ)^4667 ≤ (3994336215591/10000000000000 : ℝ)^3643 := by
    have hnat : (4885317677 : ℕ)^4667*10000000000000^3643 ≤ 3994336215591^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4885317677 10000000000 3994336215591 10000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2731143959/5000000000 : ℝ), (-215181779/1000000000 : ℝ), (4885317677/10000000000 : ℝ)] ![(46084406070503/100000000000000 : ℝ), (13972231758157/100000000000000 : ℝ), (3994336215591/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2731143959/5000000000 : ℝ)|^4667 ≤ (46084406070503/100000000000000 : ℝ)^3643
        have hw : |(2731143959/5000000000 : ℝ)|=(2731143959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-215181779/1000000000 : ℝ)|^4667 ≤ (13972231758157/100000000000000 : ℝ)^3643
        have hw : |(-215181779/1000000000 : ℝ)|=(215181779/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4885317677/10000000000 : ℝ)|^4667 ≤ (3994336215591/10000000000000 : ℝ)^3643
        have hw : |(4885317677/10000000000 : ℝ)|=(4885317677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1585_s0_2 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5462287991/10000000000 : ℝ)*x 0 + (977063513/2000000000 : ℝ)*x 1 + (-430363567/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5462287991/10000000000 : ℝ)^4667 ≤ (4608440685951/10000000000000 : ℝ)^3643 := by
    have hnat : (5462287991 : ℕ)^4667*10000000000000^3643 ≤ 4608440685951^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5462287991 10000000000 4608440685951 10000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (977063513/2000000000 : ℝ)^4667 ≤ (19971680491387/50000000000000 : ℝ)^3643 := by
    have hnat : (977063513 : ℕ)^4667*50000000000000^3643 ≤ 19971680491387^3643*2000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      977063513 2000000000 19971680491387 50000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (430363567/2000000000 : ℝ)^4667 ≤ (2794446426497/20000000000000 : ℝ)^3643 := by
    have hnat : (430363567 : ℕ)^4667*20000000000000^3643 ≤ 2794446426497^3643*2000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430363567 2000000000 2794446426497 20000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5462287991/10000000000 : ℝ), (977063513/2000000000 : ℝ), (-430363567/2000000000 : ℝ)] ![(4608440685951/10000000000000 : ℝ), (19971680491387/50000000000000 : ℝ), (2794446426497/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5462287991/10000000000 : ℝ)|^4667 ≤ (4608440685951/10000000000000 : ℝ)^3643
        have hw : |(5462287991/10000000000 : ℝ)|=(5462287991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(977063513/2000000000 : ℝ)|^4667 ≤ (19971680491387/50000000000000 : ℝ)^3643
        have hw : |(977063513/2000000000 : ℝ)|=(977063513/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-430363567/2000000000 : ℝ)|^4667 ≤ (2794446426497/20000000000000 : ℝ)^3643
        have hw : |(-430363567/2000000000 : ℝ)|=(430363567/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1585_s0_3 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4126000619/10000000000 : ℝ)*x 0 + (3094079163/10000000000 : ℝ)*x 1 + (5415521973/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4126000619/10000000000 : ℝ)^4667 ≤ (32170629848533/100000000000000 : ℝ)^3643 := by
    have hnat : (4126000619 : ℕ)^4667*100000000000000^3643 ≤ 32170629848533^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4126000619 10000000000 32170629848533 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3094079163/10000000000 : ℝ)^4667 ≤ (22249815720149/100000000000000 : ℝ)^3643 := by
    have hnat : (3094079163 : ℕ)^4667*100000000000000^3643 ≤ 22249815720149^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3094079163 10000000000 22249815720149 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5415521973/10000000000 : ℝ)^4667 ≤ (22789777209199/50000000000000 : ℝ)^3643 := by
    have hnat : (5415521973 : ℕ)^4667*50000000000000^3643 ≤ 22789777209199^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415521973 10000000000 22789777209199 50000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4126000619/10000000000 : ℝ), (3094079163/10000000000 : ℝ), (5415521973/10000000000 : ℝ)] ![(32170629848533/100000000000000 : ℝ), (22249815720149/100000000000000 : ℝ), (22789777209199/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4126000619/10000000000 : ℝ)|^4667 ≤ (32170629848533/100000000000000 : ℝ)^3643
        have hw : |(4126000619/10000000000 : ℝ)|=(4126000619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3094079163/10000000000 : ℝ)|^4667 ≤ (22249815720149/100000000000000 : ℝ)^3643
        have hw : |(3094079163/10000000000 : ℝ)|=(3094079163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5415521973/10000000000 : ℝ)|^4667 ≤ (22789777209199/50000000000000 : ℝ)^3643
        have hw : |(5415521973/10000000000 : ℝ)|=(5415521973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1585_s0_4 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1614013457/10000000000 : ℝ)*x 0 + (2454883557/5000000000 : ℝ)*x 1 + (1166695799/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1614013457/10000000000 : ℝ)^4667 ≤ (9666297025903/100000000000000 : ℝ)^3643 := by
    have hnat : (1614013457 : ℕ)^4667*100000000000000^3643 ≤ 9666297025903^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1614013457 10000000000 9666297025903 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2454883557/5000000000 : ℝ)^4667 ≤ (40199636009827/100000000000000 : ℝ)^3643 := by
    have hnat : (2454883557 : ℕ)^4667*100000000000000^3643 ≤ 40199636009827^3643*5000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2454883557 5000000000 40199636009827 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1166695799/2000000000 : ℝ)^4667 ≤ (78334479621/156250000000 : ℝ)^3643 := by
    have hnat : (1166695799 : ℕ)^4667*156250000000^3643 ≤ 78334479621^3643*2000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1166695799 2000000000 78334479621 156250000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1614013457/10000000000 : ℝ), (2454883557/5000000000 : ℝ), (1166695799/2000000000 : ℝ)] ![(9666297025903/100000000000000 : ℝ), (40199636009827/100000000000000 : ℝ), (78334479621/156250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1614013457/10000000000 : ℝ)|^4667 ≤ (9666297025903/100000000000000 : ℝ)^3643
        have hw : |(-1614013457/10000000000 : ℝ)|=(1614013457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2454883557/5000000000 : ℝ)|^4667 ≤ (40199636009827/100000000000000 : ℝ)^3643
        have hw : |(2454883557/5000000000 : ℝ)|=(2454883557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1166695799/2000000000 : ℝ)|^4667 ≤ (78334479621/156250000000 : ℝ)^3643
        have hw : |(1166695799/2000000000 : ℝ)|=(1166695799/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1585_s0_5 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2598074993/5000000000 : ℝ)*x 0 + (-1203656057/10000000000 : ℝ)*x 1 + (145836977/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2598074993/5000000000 : ℝ)^4667 ≤ (84429366139/195312500000 : ℝ)^3643 := by
    have hnat : (2598074993 : ℕ)^4667*195312500000^3643 ≤ 84429366139^3643*5000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598074993 5000000000 84429366139 195312500000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1203656057/10000000000 : ℝ)^4667 ≤ (829762079371/12500000000000 : ℝ)^3643 := by
    have hnat : (1203656057 : ℕ)^4667*12500000000000^3643 ≤ 829762079371^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1203656057 10000000000 829762079371 12500000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (145836977/250000000 : ℝ)^4667 ≤ (25067033946641/50000000000000 : ℝ)^3643 := by
    have hnat : (145836977 : ℕ)^4667*50000000000000^3643 ≤ 25067033946641^3643*250000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      145836977 250000000 25067033946641 50000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2598074993/5000000000 : ℝ), (-1203656057/10000000000 : ℝ), (145836977/250000000 : ℝ)] ![(84429366139/195312500000 : ℝ), (829762079371/12500000000000 : ℝ), (25067033946641/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2598074993/5000000000 : ℝ)|^4667 ≤ (84429366139/195312500000 : ℝ)^3643
        have hw : |(2598074993/5000000000 : ℝ)|=(2598074993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1203656057/10000000000 : ℝ)|^4667 ≤ (829762079371/12500000000000 : ℝ)^3643
        have hw : |(-1203656057/10000000000 : ℝ)|=(1203656057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(145836977/250000000 : ℝ)|^4667 ≤ (25067033946641/50000000000000 : ℝ)^3643
        have hw : |(145836977/250000000 : ℝ)|=(145836977/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1585_s0_6 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5196149947/10000000000 : ℝ)*x 0 + (2916739489/5000000000 : ℝ)*x 1 + (-1203656273/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5196149947/10000000000 : ℝ)^4667 ≤ (43227835047521/100000000000000 : ℝ)^3643 := by
    have hnat : (5196149947 : ℕ)^4667*100000000000000^3643 ≤ 43227835047521^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196149947 10000000000 43227835047521 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2916739489/5000000000 : ℝ)^4667 ≤ (50134066770271/100000000000000 : ℝ)^3643 := by
    have hnat : (2916739489 : ℕ)^4667*100000000000000^3643 ≤ 50134066770271^3643*5000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2916739489 5000000000 50134066770271 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1203656273/10000000000 : ℝ)^4667 ≤ (1327619632207/20000000000000 : ℝ)^3643 := by
    have hnat : (1203656273 : ℕ)^4667*20000000000000^3643 ≤ 1327619632207^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1203656273 10000000000 1327619632207 20000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5196149947/10000000000 : ℝ), (2916739489/5000000000 : ℝ), (-1203656273/10000000000 : ℝ)] ![(43227835047521/100000000000000 : ℝ), (50134066770271/100000000000000 : ℝ), (1327619632207/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5196149947/10000000000 : ℝ)|^4667 ≤ (43227835047521/100000000000000 : ℝ)^3643
        have hw : |(5196149947/10000000000 : ℝ)|=(5196149947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2916739489/5000000000 : ℝ)|^4667 ≤ (50134066770271/100000000000000 : ℝ)^3643
        have hw : |(2916739489/5000000000 : ℝ)|=(2916739489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1203656273/10000000000 : ℝ)|^4667 ≤ (1327619632207/20000000000000 : ℝ)^3643
        have hw : |(-1203656273/10000000000 : ℝ)|=(1203656273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1585_s0_7 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4133019027/10000000000 : ℝ)*x 0 + (2678608691/5000000000 : ℝ)*x 1 + (394304881/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4133019027/10000000000 : ℝ)^4667 ≤ (6448150272587/20000000000000 : ℝ)^3643 := by
    have hnat : (4133019027 : ℕ)^4667*20000000000000^3643 ≤ 6448150272587^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4133019027 10000000000 6448150272587 20000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2678608691/5000000000 : ℝ)^4667 ≤ (22475927451921/50000000000000 : ℝ)^3643 := by
    have hnat : (2678608691 : ℕ)^4667*50000000000000^3643 ≤ 22475927451921^3643*5000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2678608691 5000000000 22475927451921 50000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (394304881/1250000000 : ℝ)^4667 ≤ (22807393711029/100000000000000 : ℝ)^3643 := by
    have hnat : (394304881 : ℕ)^4667*100000000000000^3643 ≤ 22807393711029^3643*1250000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      394304881 1250000000 22807393711029 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4133019027/10000000000 : ℝ), (2678608691/5000000000 : ℝ), (394304881/1250000000 : ℝ)] ![(6448150272587/20000000000000 : ℝ), (22475927451921/50000000000000 : ℝ), (22807393711029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4133019027/10000000000 : ℝ)|^4667 ≤ (6448150272587/20000000000000 : ℝ)^3643
        have hw : |(4133019027/10000000000 : ℝ)|=(4133019027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2678608691/5000000000 : ℝ)|^4667 ≤ (22475927451921/50000000000000 : ℝ)^3643
        have hw : |(2678608691/5000000000 : ℝ)|=(2678608691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(394304881/1250000000 : ℝ)|^4667 ≤ (22807393711029/100000000000000 : ℝ)^3643
        have hw : |(394304881/1250000000 : ℝ)|=(394304881/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1585_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (42308779/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (93/2500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6143/25000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4665/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4665 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4665*1^1024 ≤ 0^1024*1^4665 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4665 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4665 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4665/1024 : ℝ) ≤ (769288088208312143/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4665 ≤ (769288088208312143/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4665*50000000000000000000^1024 ≤ 769288088208312143^1024*5^4665 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 769288088208312143 50000000000000000000 4665 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (769288088208312143/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4665 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4665/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4665 := by
      have hnat : (1 : ℕ)^1024*1^4665 ≤ 1^4665*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4665 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4665 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50769288088208312143/50000000000000000000 : ℝ) ≤ (10033571870948353/10000000000000000 : ℝ) ^ (4665/1024 : ℝ) := by
    have hpowers : (50769288088208312143/50000000000000000000 : ℝ)^1024 ≤ (10033571870948353/10000000000000000 : ℝ)^4665 := by
      have hnat : (50769288088208312143 : ℕ)^1024*10000000000000000^4665 ≤ 10033571870948353^4665*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50769288088208312143 50000000000000000000 10033571870948353 10000000000000000 1024 4665 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10033571870948353/10000000000000000 : ℝ)) (X := (50769288088208312143/50000000000000000000 : ℝ)) (by norm_num) 4665 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25769288088208312143/25000000000000000000 : ℝ) ≤ (5033571870948353/5000000000000000 : ℝ) ^ (4665/1024 : ℝ) := by
    have hpowers : (25769288088208312143/25000000000000000000 : ℝ)^1024 ≤ (5033571870948353/5000000000000000 : ℝ)^4665 := by
      have hnat : (25769288088208312143 : ℕ)^1024*5000000000000000^4665 ≤ 5033571870948353^4665*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25769288088208312143 25000000000000000000 5033571870948353 5000000000000000 1024 4665 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5033571870948353/5000000000000000 : ℝ)) (X := (25769288088208312143/25000000000000000000 : ℝ)) (by norm_num) 4665 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(33571870948353/4000000000000000 : ℝ)*(0 : ℝ))^(4665/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(33571870948353/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(769288088208312143/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(33571870948353/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4665/1024 : ℝ) := by
    rw [show (1 : ℝ)+(33571870948353/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10033571870948353/10000000000000000 : ℝ) by norm_num, show 1+(769288088208312143/50000000000000000000 : ℝ)+(0 : ℝ)=(50769288088208312143/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(769288088208312143/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(33571870948353/4000000000000000 : ℝ)*(2/5 : ℝ))^(4665/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(33571870948353/4000000000000000 : ℝ)*(2/5 : ℝ)=(5033571870948353/5000000000000000 : ℝ) by norm_num, show 1+2*(769288088208312143/50000000000000000000 : ℝ)=(25769288088208312143/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(33571870948353/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4665/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (33571870948353/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(33571870948353/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4665/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (33571870948353/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(33571870948353/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4665/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (33571870948353/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-322214109/2000000000 : ℝ)*X 0 0+(5858790417/10000000000 : ℝ)*X 0 1+(977063553/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2731143959/5000000000 : ℝ)*X 1 0+(-215181779/1000000000 : ℝ)*X 1 1+(4885317677/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5462287991/10000000000 : ℝ)*X 2 0+(977063513/2000000000 : ℝ)*X 2 1+(-430363567/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4126000619/10000000000 : ℝ)*X 0 0+(3094079163/10000000000 : ℝ)*X 0 1+(5415521973/10000000000 : ℝ)*X 0 2+(4126000619/10000000000 : ℝ)*X 1 0+(3094079163/10000000000 : ℝ)*X 1 1+(5415521973/10000000000 : ℝ)*X 1 2+(4126000619/10000000000 : ℝ)*X 2 0+(3094079163/10000000000 : ℝ)*X 2 1+(5415521973/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1614013457/10000000000 : ℝ)*X 0 0+(2454883557/5000000000 : ℝ)*X 0 1+(1166695799/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2598074993/5000000000 : ℝ)*X 1 0+(-1203656057/10000000000 : ℝ)*X 1 1+(145836977/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5196149947/10000000000 : ℝ)*X 2 0+(2916739489/5000000000 : ℝ)*X 2 1+(-1203656273/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4133019027/10000000000 : ℝ)*X 0 0+(2678608691/5000000000 : ℝ)*X 0 1+(394304881/1250000000 : ℝ)*X 0 2+(4133019027/10000000000 : ℝ)*X 1 0+(2678608691/5000000000 : ℝ)*X 1 1+(394304881/1250000000 : ℝ)*X 1 2+(4133019027/10000000000 : ℝ)*X 2 0+(2678608691/5000000000 : ℝ)*X 2 1+(394304881/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5128557348333118604967/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18827457/25000000000000 : ℝ)*(base1) + (804070261/50000000000000 : ℝ)*(base19) + (4054673/250000000000 : ℝ)*(base23) + (211929157/100000000000000 : ℝ)*(upper3) + (50418939/25000000000000 : ℝ)*(upper5) + (9112710707563/1250000000000 : ℝ)*(major0) + (9112710707563/1250000000000 : ℝ)*(major1) + (9112710707563/1250000000000 : ℝ)*(major2) + (1027255935276229/100000000000000 : ℝ)*(sp0) + (1027260208117561/100000000000000 : ℝ)*(sp1) + (513630097194441/50000000000000 : ℝ)*(sp2) + (430768984366757/100000000000000 : ℝ)*(sp3) + (2978145841/50000000000000 : ℝ)*(sp4) + (2563752349/100000000000000 : ℝ)*(sp7) + (215385811714467/50000000000000 : ℝ)*(f.failure) + (513630908129041/50000000000000 : ℝ)*(f.sum) + (640109323761/2500000000000000000000000000 : ℝ)*base66 + (16300330256261/5000000000000000000000000000 : ℝ)*base68 + (9748055946261/5000000000000000000000000000 : ℝ)*base70 + (13469015526261/5000000000000000000000000000 : ℝ)*base72 + (1955801803761/2500000000000000000000000000 : ℝ)*base74 + (24204546056261/5000000000000000000000000000 : ℝ)*base76 + (2738044153739/5000000000000000000000000000 : ℝ)*base77 + (7265324298739/5000000000000000000000000000 : ℝ)*base79 + (155202613761/2500000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (4594207/1250000000000000000000 : ℝ)*base90 + (4594207/1250000000000000000000 : ℝ)*base92 + (4594207/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (93857124855283369497681/40000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (259762373/50000000000000 : ℝ)*(base19) + (15970999/3125000000000 : ℝ)*(base23) + (15288521/20000000000000 : ℝ)*(base32) + (1706329/2000000000000 : ℝ)*(upper3) + (895763/4000000000000 : ℝ)*(upper5) + (768280124848859/100000000000000 : ℝ)*(major0) + (768280124848859/100000000000000 : ℝ)*(major1) + (768280124848859/100000000000000 : ℝ)*(major2) + (1480197579/100000000000000 : ℝ)*(sp1) + (736902791/50000000000000 : ℝ)*(sp2) + (135323515227991/12500000000000 : ℝ)*(sp4) + (1082586122101603/100000000000000 : ℝ)*(sp5) + (541293068473189/50000000000000 : ℝ)*(sp6) + (453971973216911/100000000000000 : ℝ)*(sp7) + (113493012414879/25000000000000 : ℝ)*(f.failure) + (135323515227991/12500000000000 : ℝ)*(f.sum) + (51676180220773/200000000000000000000000000000 : ℝ)*base66 + (2158063197620773/400000000000000000000000000000 : ℝ)*base68 + (1298256115220773/400000000000000000000000000000 : ℝ)*base70 + (896660350820773/400000000000000000000000000000 : ℝ)*base72 + (542374324220773/200000000000000000000000000000 : ℝ)*base74 + (1218206860420773/400000000000000000000000000000 : ℝ)*base76 + (35207789979227/400000000000000000000000000000 : ℝ)*base77 + (4127337486420773/400000000000000000000000000000 : ℝ)*base80 + (98334192820773/200000000000000000000000000000 : ℝ)*base82 + (3172741/625000000000000000000 : ℝ)*base89 + (3172741/625000000000000000000 : ℝ)*base91 + (3172741/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1585_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (42308779/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (93/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6143/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1585_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1585_s1_0 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-349184819/2000000000 : ℝ)*x 0 + (5526485227/10000000000 : ℝ)*x 1 + (641329019/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (349184819/2000000000 : ℝ)^4667 ≤ (167027720559/1562500000000 : ℝ)^3643 := by
    have hnat : (349184819 : ℕ)^4667*1562500000000^3643 ≤ 167027720559^3643*2000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      349184819 2000000000 167027720559 1562500000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5526485227/10000000000 : ℝ)^4667 ≤ (23389706889629/50000000000000 : ℝ)^3643 := by
    have hnat : (5526485227 : ℕ)^4667*50000000000000^3643 ≤ 23389706889629^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5526485227 10000000000 23389706889629 50000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (641329019/1250000000 : ℝ)^4667 ≤ (1329087878221/3125000000000 : ℝ)^3643 := by
    have hnat : (641329019 : ℕ)^4667*3125000000000^3643 ≤ 1329087878221^3643*1250000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      641329019 1250000000 1329087878221 3125000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-349184819/2000000000 : ℝ), (5526485227/10000000000 : ℝ), (641329019/1250000000 : ℝ)] ![(167027720559/1562500000000 : ℝ), (23389706889629/50000000000000 : ℝ), (1329087878221/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-349184819/2000000000 : ℝ)|^4667 ≤ (167027720559/1562500000000 : ℝ)^3643
        have hw : |(-349184819/2000000000 : ℝ)|=(349184819/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5526485227/10000000000 : ℝ)|^4667 ≤ (23389706889629/50000000000000 : ℝ)^3643
        have hw : |(5526485227/10000000000 : ℝ)|=(5526485227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(641329019/1250000000 : ℝ)|^4667 ≤ (1329087878221/3125000000000 : ℝ)^3643
        have hw : |(641329019/1250000000 : ℝ)|=(641329019/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1585_s1_1 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5373927803/10000000000 : ℝ)*x 0 + (-390532537/2000000000 : ℝ)*x 1 + (1026126353/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5373927803/10000000000 : ℝ)^4667 ≤ (11282890432599/25000000000000 : ℝ)^3643 := by
    have hnat : (5373927803 : ℕ)^4667*25000000000000^3643 ≤ 11282890432599^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5373927803 10000000000 11282890432599 25000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (390532537/2000000000 : ℝ)^4667 ≤ (1542203782443/12500000000000 : ℝ)^3643 := by
    have hnat : (390532537 : ℕ)^4667*12500000000000^3643 ≤ 1542203782443^3643*2000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      390532537 2000000000 1542203782443 12500000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1026126353/2000000000 : ℝ)^4667 ≤ (8506161598651/20000000000000 : ℝ)^3643 := by
    have hnat : (1026126353 : ℕ)^4667*20000000000000^3643 ≤ 8506161598651^3643*2000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026126353 2000000000 8506161598651 20000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5373927803/10000000000 : ℝ), (-390532537/2000000000 : ℝ), (1026126353/2000000000 : ℝ)] ![(11282890432599/25000000000000 : ℝ), (1542203782443/12500000000000 : ℝ), (8506161598651/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5373927803/10000000000 : ℝ)|^4667 ≤ (11282890432599/25000000000000 : ℝ)^3643
        have hw : |(5373927803/10000000000 : ℝ)|=(5373927803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-390532537/2000000000 : ℝ)|^4667 ≤ (1542203782443/12500000000000 : ℝ)^3643
        have hw : |(-390532537/2000000000 : ℝ)|=(390532537/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1026126353/2000000000 : ℝ)|^4667 ≤ (8506161598651/20000000000000 : ℝ)^3643
        have hw : |(1026126353/2000000000 : ℝ)|=(1026126353/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1585_s1_2 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (671740923/1250000000 : ℝ)*x 0 + (320664509/625000000 : ℝ)*x 1 + (-390532549/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671740923/1250000000 : ℝ)^4667 ≤ (1805262288897/4000000000000 : ℝ)^3643 := by
    have hnat : (671740923 : ℕ)^4667*4000000000000^3643 ≤ 1805262288897^3643*1250000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671740923 1250000000 1805262288897 4000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (320664509/625000000 : ℝ)^4667 ≤ (21265406009057/50000000000000 : ℝ)^3643 := by
    have hnat : (320664509 : ℕ)^4667*50000000000000^3643 ≤ 21265406009057^3643*625000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      320664509 625000000 21265406009057 50000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (390532549/2000000000 : ℝ)^4667 ≤ (6168815372603/50000000000000 : ℝ)^3643 := by
    have hnat : (390532549 : ℕ)^4667*50000000000000^3643 ≤ 6168815372603^3643*2000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      390532549 2000000000 6168815372603 50000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(671740923/1250000000 : ℝ), (320664509/625000000 : ℝ), (-390532549/2000000000 : ℝ)] ![(1805262288897/4000000000000 : ℝ), (21265406009057/50000000000000 : ℝ), (6168815372603/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(671740923/1250000000 : ℝ)|^4667 ≤ (1805262288897/4000000000000 : ℝ)^3643
        have hw : |(671740923/1250000000 : ℝ)|=(671740923/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(320664509/625000000 : ℝ)|^4667 ≤ (21265406009057/50000000000000 : ℝ)^3643
        have hw : |(320664509/625000000 : ℝ)|=(320664509/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-390532549/2000000000 : ℝ)|^4667 ≤ (6168815372603/50000000000000 : ℝ)^3643
        have hw : |(-390532549/2000000000 : ℝ)|=(390532549/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1585_s1_3 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (211150361/500000000 : ℝ)*x 0 + (1886013791/5000000000 : ℝ)*x 1 + (943203997/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211150361/500000000 : ℝ)^4667 ≤ (33142783470271/100000000000000 : ℝ)^3643 := by
    have hnat : (211150361 : ℕ)^4667*100000000000000^3643 ≤ 33142783470271^3643*500000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211150361 500000000 33142783470271 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1886013791/5000000000 : ℝ)^4667 ≤ (14339220886469/50000000000000 : ℝ)^3643 := by
    have hnat : (1886013791 : ℕ)^4667*50000000000000^3643 ≤ 14339220886469^3643*5000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1886013791 5000000000 14339220886469 50000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (943203997/2000000000 : ℝ)^4667 ≤ (38178774737719/100000000000000 : ℝ)^3643 := by
    have hnat : (943203997 : ℕ)^4667*100000000000000^3643 ≤ 38178774737719^3643*2000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      943203997 2000000000 38178774737719 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(211150361/500000000 : ℝ), (1886013791/5000000000 : ℝ), (943203997/2000000000 : ℝ)] ![(33142783470271/100000000000000 : ℝ), (14339220886469/50000000000000 : ℝ), (38178774737719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(211150361/500000000 : ℝ)|^4667 ≤ (33142783470271/100000000000000 : ℝ)^3643
        have hw : |(211150361/500000000 : ℝ)|=(211150361/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1886013791/5000000000 : ℝ)|^4667 ≤ (14339220886469/50000000000000 : ℝ)^3643
        have hw : |(1886013791/5000000000 : ℝ)|=(1886013791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(943203997/2000000000 : ℝ)|^4667 ≤ (38178774737719/100000000000000 : ℝ)^3643
        have hw : |(943203997/2000000000 : ℝ)|=(943203997/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1585_s1_4 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-349223429/2000000000 : ℝ)*x 0 + (320914603/625000000 : ℝ)*x 1 + (5522425969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (349223429/2000000000 : ℝ)^4667 ≤ (10691288368467/100000000000000 : ℝ)^3643 := by
    have hnat : (349223429 : ℕ)^4667*100000000000000^3643 ≤ 10691288368467^3643*2000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      349223429 2000000000 10691288368467 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (320914603/625000000 : ℝ)^4667 ≤ (42573311366833/100000000000000 : ℝ)^3643 := by
    have hnat : (320914603 : ℕ)^4667*100000000000000^3643 ≤ 42573311366833^3643*625000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      320914603 625000000 42573311366833 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5522425969/10000000000 : ℝ)^4667 ≤ (46735400249017/100000000000000 : ℝ)^3643 := by
    have hnat : (5522425969 : ℕ)^4667*100000000000000^3643 ≤ 46735400249017^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5522425969 10000000000 46735400249017 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-349223429/2000000000 : ℝ), (320914603/625000000 : ℝ), (5522425969/10000000000 : ℝ)] ![(10691288368467/100000000000000 : ℝ), (42573311366833/100000000000000 : ℝ), (46735400249017/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-349223429/2000000000 : ℝ)|^4667 ≤ (10691288368467/100000000000000 : ℝ)^3643
        have hw : |(-349223429/2000000000 : ℝ)|=(349223429/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(320914603/625000000 : ℝ)|^4667 ≤ (42573311366833/100000000000000 : ℝ)^3643
        have hw : |(320914603/625000000 : ℝ)|=(320914603/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5522425969/10000000000 : ℝ)|^4667 ≤ (46735400249017/100000000000000 : ℝ)^3643
        have hw : |(5522425969/10000000000 : ℝ)|=(5522425969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1585_s1_5 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5268847991/10000000000 : ℝ)*x 0 + (-1560868529/10000000000 : ℝ)*x 1 + (5522426727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5268847991/10000000000 : ℝ)^4667 ≤ (44004141944211/100000000000000 : ℝ)^3643 := by
    have hnat : (5268847991 : ℕ)^4667*100000000000000^3643 ≤ 44004141944211^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5268847991 10000000000 44004141944211 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1560868529/10000000000 : ℝ)^4667 ≤ (9260449572931/100000000000000 : ℝ)^3643 := by
    have hnat : (1560868529 : ℕ)^4667*100000000000000^3643 ≤ 9260449572931^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1560868529 10000000000 9260449572931 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5522426727/10000000000 : ℝ)^4667 ≤ (1869416338679/4000000000000 : ℝ)^3643 := by
    have hnat : (5522426727 : ℕ)^4667*4000000000000^3643 ≤ 1869416338679^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5522426727 10000000000 1869416338679 4000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5268847991/10000000000 : ℝ), (-1560868529/10000000000 : ℝ), (5522426727/10000000000 : ℝ)] ![(44004141944211/100000000000000 : ℝ), (9260449572931/100000000000000 : ℝ), (1869416338679/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5268847991/10000000000 : ℝ)|^4667 ≤ (44004141944211/100000000000000 : ℝ)^3643
        have hw : |(5268847991/10000000000 : ℝ)|=(5268847991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1560868529/10000000000 : ℝ)|^4667 ≤ (9260449572931/100000000000000 : ℝ)^3643
        have hw : |(-1560868529/10000000000 : ℝ)|=(1560868529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5522426727/10000000000 : ℝ)|^4667 ≤ (1869416338679/4000000000000 : ℝ)^3643
        have hw : |(5522426727/10000000000 : ℝ)|=(5522426727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1585_s1_6 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5268847047/10000000000 : ℝ)*x 0 + (5522427103/10000000000 : ℝ)*x 1 + (-780434661/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5268847047/10000000000 : ℝ)^4667 ≤ (8800826368809/20000000000000 : ℝ)^3643 := by
    have hnat : (5268847047 : ℕ)^4667*20000000000000^3643 ≤ 8800826368809^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5268847047 10000000000 8800826368809 20000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5522427103/10000000000 : ℝ)^4667 ≤ (46735412543429/100000000000000 : ℝ)^3643 := by
    have hnat : (5522427103 : ℕ)^4667*100000000000000^3643 ≤ 46735412543429^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5522427103 10000000000 46735412543429 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (780434661/5000000000 : ℝ)^4667 ≤ (4630227800079/50000000000000 : ℝ)^3643 := by
    have hnat : (780434661 : ℕ)^4667*50000000000000^3643 ≤ 4630227800079^3643*5000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      780434661 5000000000 4630227800079 50000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5268847047/10000000000 : ℝ), (5522427103/10000000000 : ℝ), (-780434661/5000000000 : ℝ)] ![(8800826368809/20000000000000 : ℝ), (46735412543429/100000000000000 : ℝ), (4630227800079/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5268847047/10000000000 : ℝ)|^4667 ≤ (8800826368809/20000000000000 : ℝ)^3643
        have hw : |(5268847047/10000000000 : ℝ)|=(5268847047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5522427103/10000000000 : ℝ)|^4667 ≤ (46735412543429/100000000000000 : ℝ)^3643
        have hw : |(5522427103/10000000000 : ℝ)|=(5522427103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-780434661/5000000000 : ℝ)|^4667 ≤ (4630227800079/50000000000000 : ℝ)^3643
        have hw : |(-780434661/5000000000 : ℝ)|=(780434661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1585_s1_7 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4223466723/10000000000 : ℝ)*x 0 + (470647869/1000000000 : ℝ)*x 1 + (3781706389/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4223466723/10000000000 : ℝ)^4667 ≤ (33147403457527/100000000000000 : ℝ)^3643 := by
    have hnat : (4223466723 : ℕ)^4667*100000000000000^3643 ≤ 33147403457527^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4223466723 10000000000 33147403457527 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (470647869/1000000000 : ℝ)^4667 ≤ (38079849127703/100000000000000 : ℝ)^3643 := by
    have hnat : (470647869 : ℕ)^4667*100000000000000^3643 ≤ 38079849127703^3643*1000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      470647869 1000000000 38079849127703 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3781706389/10000000000 : ℝ)^4667 ≤ (28772747408011/100000000000000 : ℝ)^3643 := by
    have hnat : (3781706389 : ℕ)^4667*100000000000000^3643 ≤ 28772747408011^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3781706389 10000000000 28772747408011 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4223466723/10000000000 : ℝ), (470647869/1000000000 : ℝ), (3781706389/10000000000 : ℝ)] ![(33147403457527/100000000000000 : ℝ), (38079849127703/100000000000000 : ℝ), (28772747408011/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4223466723/10000000000 : ℝ)|^4667 ≤ (33147403457527/100000000000000 : ℝ)^3643
        have hw : |(4223466723/10000000000 : ℝ)|=(4223466723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(470647869/1000000000 : ℝ)|^4667 ≤ (38079849127703/100000000000000 : ℝ)^3643
        have hw : |(470647869/1000000000 : ℝ)|=(470647869/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3781706389/10000000000 : ℝ)|^4667 ≤ (28772747408011/100000000000000 : ℝ)^3643
        have hw : |(3781706389/10000000000 : ℝ)|=(3781706389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1585_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (42308779/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6143/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (93/2500 : ℝ)*pair X i i ≤ pair X i h) :
    (4617/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17621/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6143/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (93/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6143/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (93/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6143/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (93/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6143/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (93/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6143/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (93/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6143/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (93/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (93/2500 : ℝ) ^ (4665/1024 : ℝ) ≤ (615040674591/2000000000000000000 : ℝ) := by
    have hpowers : (93/2500 : ℝ)^4665 ≤ (615040674591/2000000000000000000 : ℝ)^1024 := by
      have hnat : (93 : ℕ)^4665*2000000000000000000^1024 ≤ 615040674591^1024*2500^4665 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        93 2500 615040674591 2000000000000000000 4665 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (93/2500 : ℝ)) (X := (615040674591/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4665 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (6143/25000 : ℝ) ^ (4665/1024 : ℝ) ≤ (33425792884520053/20000000000000000000 : ℝ) := by
    have hpowers : (6143/25000 : ℝ)^4665 ≤ (33425792884520053/20000000000000000000 : ℝ)^1024 := by
      have hnat : (6143 : ℕ)^4665*20000000000000000000^1024 ≤ 33425792884520053^1024*25000^4665 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6143 25000 33425792884520053 20000000000000000000 4665 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6143/25000 : ℝ)) (X := (33425792884520053/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4665 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1000000615040674591/1000000000000000000 : ℝ) ≤ (5000000675028403/5000000000000000 : ℝ) ^ (4665/1024 : ℝ) := by
    have hpowers : (1000000615040674591/1000000000000000000 : ℝ)^1024 ≤ (5000000675028403/5000000000000000 : ℝ)^4665 := by
      have hnat : (1000000615040674591 : ℕ)^1024*5000000000000000^4665 ≤ 5000000675028403^4665*1000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000000615040674591 1000000000000000000 5000000675028403 5000000000000000 1024 4665 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000675028403/5000000000000000 : ℝ)) (X := (1000000615040674591/1000000000000000000 : ℝ)) (by norm_num) 4665 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20033431943291265963/20000000000000000000 : ℝ) ≤ (7815364750789/7812500000000 : ℝ) ^ (4665/1024 : ℝ) := by
    have hpowers : (20033431943291265963/20000000000000000000 : ℝ)^1024 ≤ (7815364750789/7812500000000 : ℝ)^4665 := by
      have hnat : (20033431943291265963 : ℕ)^1024*7812500000000^4665 ≤ 7815364750789^4665*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20033431943291265963 20000000000000000000 7815364750789 7812500000000 1024 4665 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (7815364750789/7812500000000 : ℝ)) (X := (20033431943291265963/20000000000000000000 : ℝ)) (by norm_num) 4665 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10033425792884520053/10000000000000000000 : ℝ) ≤ (5003666205981517/5000000000000000 : ℝ) ^ (4665/1024 : ℝ) := by
    have hpowers : (10033425792884520053/10000000000000000000 : ℝ)^1024 ≤ (5003666205981517/5000000000000000 : ℝ)^4665 := by
      have hnat : (10033425792884520053 : ℕ)^1024*5000000000000000^4665 ≤ 5003666205981517^4665*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10033425792884520053 10000000000000000000 5003666205981517 5000000000000000 1024 4665 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5003666205981517/5000000000000000 : ℝ)) (X := (10033425792884520053/10000000000000000000 : ℝ)) (by norm_num) 4665 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(615040674591/2000000000000000000 : ℝ) ≤ ((26061594575136668819/26065000000000000000 : ℝ)+2*(1832765476557/1042600000000000 : ℝ)*(93/2500 : ℝ))^(4665/1024 : ℝ) := by
    rw [show (26061594575136668819/26065000000000000000 : ℝ)+2*(1832765476557/1042600000000000 : ℝ)*(93/2500 : ℝ)=(5000000675028403/5000000000000000 : ℝ) by norm_num, show 1+2*(615040674591/2000000000000000000 : ℝ)=(1000000615040674591/1000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33425792884520053/20000000000000000000 : ℝ)+(615040674591/2000000000000000000 : ℝ) ≤ ((26061594575136668819/26065000000000000000 : ℝ)+(1832765476557/1042600000000000 : ℝ)*((6143/25000 : ℝ)+(93/2500 : ℝ)))^(4665/1024 : ℝ) := by
    rw [show (26061594575136668819/26065000000000000000 : ℝ)+(1832765476557/1042600000000000 : ℝ)*((6143/25000 : ℝ)+(93/2500 : ℝ))=(7815364750789/7812500000000 : ℝ) by norm_num, show 1+(33425792884520053/20000000000000000000 : ℝ)+(615040674591/2000000000000000000 : ℝ)=(20033431943291265963/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33425792884520053/20000000000000000000 : ℝ) ≤ ((26061594575136668819/26065000000000000000 : ℝ)+2*(1832765476557/1042600000000000 : ℝ)*(6143/25000 : ℝ))^(4665/1024 : ℝ) := by
    rw [show (26061594575136668819/26065000000000000000 : ℝ)+2*(1832765476557/1042600000000000 : ℝ)*(6143/25000 : ℝ)=(5003666205981517/5000000000000000 : ℝ) by norm_num, show 1+2*(33425792884520053/20000000000000000000 : ℝ)=(10033425792884520053/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26061594575136668819/26065000000000000000 : ℝ)*(X 1 0+X 2 0)+(1832765476557/1042600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4665/1024 : ℝ)) (lo := (93/2500 : ℝ)) (hi := (6143/25000 : ℝ)) (c := (26061594575136668819/26065000000000000000 : ℝ)) (alpha := (1832765476557/1042600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26061594575136668819/26065000000000000000 : ℝ)*(X 0 1+X 2 1)+(1832765476557/1042600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4665/1024 : ℝ)) (lo := (93/2500 : ℝ)) (hi := (6143/25000 : ℝ)) (c := (26061594575136668819/26065000000000000000 : ℝ)) (alpha := (1832765476557/1042600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26061594575136668819/26065000000000000000 : ℝ)*(X 0 2+X 1 2)+(1832765476557/1042600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4665/1024 : ℝ)) (lo := (93/2500 : ℝ)) (hi := (6143/25000 : ℝ)) (c := (26061594575136668819/26065000000000000000 : ℝ)) (alpha := (1832765476557/1042600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-349184819/2000000000 : ℝ)*X 0 0+(5526485227/10000000000 : ℝ)*X 0 1+(641329019/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5373927803/10000000000 : ℝ)*X 1 0+(-390532537/2000000000 : ℝ)*X 1 1+(1026126353/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((671740923/1250000000 : ℝ)*X 2 0+(320664509/625000000 : ℝ)*X 2 1+(-390532549/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((211150361/500000000 : ℝ)*X 0 0+(1886013791/5000000000 : ℝ)*X 0 1+(943203997/2000000000 : ℝ)*X 0 2+(211150361/500000000 : ℝ)*X 1 0+(1886013791/5000000000 : ℝ)*X 1 1+(943203997/2000000000 : ℝ)*X 1 2+(211150361/500000000 : ℝ)*X 2 0+(1886013791/5000000000 : ℝ)*X 2 1+(943203997/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-349223429/2000000000 : ℝ)*X 0 0+(320914603/625000000 : ℝ)*X 0 1+(5522425969/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5268847991/10000000000 : ℝ)*X 1 0+(-1560868529/10000000000 : ℝ)*X 1 1+(5522426727/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5268847047/10000000000 : ℝ)*X 2 0+(5522427103/10000000000 : ℝ)*X 2 1+(-780434661/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4223466723/10000000000 : ℝ)*X 0 0+(470647869/1000000000 : ℝ)*X 0 1+(3781706389/10000000000 : ℝ)*X 0 2+(4223466723/10000000000 : ℝ)*X 1 0+(470647869/1000000000 : ℝ)*X 1 1+(3781706389/10000000000 : ℝ)*X 1 2+(4223466723/10000000000 : ℝ)*X 2 0+(470647869/1000000000 : ℝ)*X 2 1+(3781706389/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (19994366436626630338578621/5090820312500000000000000000000 : ℝ) := by norm_num
    linear_combination (808495347/50000000000000 : ℝ)*(base19) + (1261979821/100000000000000 : ℝ)*(base23) + (39036321/20000000000000 : ℝ)*(upper3) + (42465909/50000000000000 : ℝ)*(upper4) + (8601331/100000000000000 : ℝ)*(upper5) + (224097541470327/12500000000000 : ℝ)*(major0) + (224097541470327/12500000000000 : ℝ)*(major1) + (224097541470327/12500000000000 : ℝ)*(major2) + (39471951980063/1562500000000 : ℝ)*(sp0) + (2526215929281329/100000000000000 : ℝ)*(sp1) + (1263108142146101/50000000000000 : ℝ)*(sp2) + (529668081211881/50000000000000 : ℝ)*(sp3) + (12619547991/100000000000000 : ℝ)*(sp4) + (341195583/5000000000000 : ℝ)*(sp7) + (529671493167711/50000000000000 : ℝ)*(f.failure) + (315777193284003/12500000000000 : ℝ)*(f.sum) + (56880159106031/26065000000000000000000000000 : ℝ)*base65 + (44284858715472399/25062500000000000000000000000000 : ℝ)*base68 + (168843404788465101/25062500000000000000000000000000 : ℝ)*base69 + (158893402966340101/25062500000000000000000000000000 : ℝ)*base71 + (1915324331179/26065000000000000000000000000 : ℝ)*base74 + (42569493704590101/25062500000000000000000000000000 : ℝ)*base75 + (217450195355027601/25062500000000000000000000000000 : ℝ)*base77 + (46529995843527601/25062500000000000000000000000000 : ℝ)*base79 + (12070287995407/3258125000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (5365131/1250000000000000000000 : ℝ)*base90 + (5365131/1250000000000000000000 : ℝ)*base92 + (5365131/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1407493104959203258881/250625000000000000000000000 : ℝ) := by norm_num
    linear_combination (484084293/50000000000000 : ℝ)*(base19) + (814173373/100000000000000 : ℝ)*(base23) + (5338047/3125000000000 : ℝ)*(upper2) + (36358567/12500000000000 : ℝ)*(upper3) + (53681691/100000000000000 : ℝ)*(upper5) + (457505010369121/25000000000000 : ℝ)*(major0) + (457505010369121/25000000000000 : ℝ)*(major1) + (457505010369121/25000000000000 : ℝ)*(major2) + (2157384239/25000000000000 : ℝ)*(sp1) + (7818040843/100000000000000 : ℝ)*(sp2) + (2578692191608227/100000000000000 : ℝ)*(sp4) + (515736518780537/20000000000000 : ℝ)*(sp5) + (2578683559394011/100000000000000 : ℝ)*(sp6) + (1081347704146983/100000000000000 : ℝ)*(sp7) + (1081347704146983/100000000000000 : ℝ)*(f.failure) + (2578692191608227/100000000000000 : ℝ)*(f.sum) + (30289596573/125312500000000000000000000 : ℝ)*base65 + (51981060639514377/50125000000000000000000000000000 : ℝ)*base68 + (212543251787485623/50125000000000000000000000000000 : ℝ)*base69 + (9894899920264377/50125000000000000000000000000000 : ℝ)*base72 + (5519368491913/2005000000000000000000000000 : ℝ)*base73 + (116442480390985623/50125000000000000000000000000000 : ℝ)*base75 + (299935909188985623/50125000000000000000000000000000 : ℝ)*base77 + (213138721518139377/50125000000000000000000000000000 : ℝ)*base80 + (1013541904761/250625000000000000000000000 : ℝ)*base81 + (12736243/2500000000000000000000 : ℝ)*base90 + (12736243/2500000000000000000000 : ℝ)*base92 + (12736243/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1585_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (42308779/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6143/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (93/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4617/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17621/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1585_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1585_s2_0 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1763212811/10000000000 : ℝ)*x 0 + (169930529/312500000 : ℝ)*x 1 + (5208057209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1763212811/10000000000 : ℝ)^4667 ≤ (5412785077711/50000000000000 : ℝ)^3643 := by
    have hnat : (1763212811 : ℕ)^4667*50000000000000^3643 ≤ 5412785077711^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1763212811 10000000000 5412785077711 50000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169930529/312500000 : ℝ)^4667 ≤ (45819650800201/100000000000000 : ℝ)^3643 := by
    have hnat : (169930529 : ℕ)^4667*100000000000000^3643 ≤ 45819650800201^3643*312500000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169930529 312500000 45819650800201 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5208057209/10000000000 : ℝ)^4667 ≤ (43354779030557/100000000000000 : ℝ)^3643 := by
    have hnat : (5208057209 : ℕ)^4667*100000000000000^3643 ≤ 43354779030557^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5208057209 10000000000 43354779030557 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1763212811/10000000000 : ℝ), (169930529/312500000 : ℝ), (5208057209/10000000000 : ℝ)] ![(5412785077711/50000000000000 : ℝ), (45819650800201/100000000000000 : ℝ), (43354779030557/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1763212811/10000000000 : ℝ)|^4667 ≤ (5412785077711/50000000000000 : ℝ)^3643
        have hw : |(-1763212811/10000000000 : ℝ)|=(1763212811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(169930529/312500000 : ℝ)|^4667 ≤ (45819650800201/100000000000000 : ℝ)^3643
        have hw : |(169930529/312500000 : ℝ)|=(169930529/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5208057209/10000000000 : ℝ)|^4667 ≤ (43354779030557/100000000000000 : ℝ)^3643
        have hw : |(5208057209/10000000000 : ℝ)|=(5208057209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1585_s2_1 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668866367/1250000000 : ℝ)*x 0 + (-1881042799/10000000000 : ℝ)*x 1 + (5208057539/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668866367/1250000000 : ℝ)^4667 ≤ (44884290100577/100000000000000 : ℝ)^3643 := by
    have hnat : (668866367 : ℕ)^4667*100000000000000^3643 ≤ 44884290100577^3643*1250000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668866367 1250000000 44884290100577 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1881042799/10000000000 : ℝ)^4667 ≤ (5880463661879/50000000000000 : ℝ)^3643 := by
    have hnat : (1881042799 : ℕ)^4667*50000000000000^3643 ≤ 5880463661879^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1881042799 10000000000 5880463661879 50000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5208057539/10000000000 : ℝ)^4667 ≤ (43354782549837/100000000000000 : ℝ)^3643 := by
    have hnat : (5208057539 : ℕ)^4667*100000000000000^3643 ≤ 43354782549837^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5208057539 10000000000 43354782549837 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668866367/1250000000 : ℝ), (-1881042799/10000000000 : ℝ), (5208057539/10000000000 : ℝ)] ![(44884290100577/100000000000000 : ℝ), (5880463661879/50000000000000 : ℝ), (43354782549837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668866367/1250000000 : ℝ)|^4667 ≤ (44884290100577/100000000000000 : ℝ)^3643
        have hw : |(668866367/1250000000 : ℝ)|=(668866367/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1881042799/10000000000 : ℝ)|^4667 ≤ (5880463661879/50000000000000 : ℝ)^3643
        have hw : |(-1881042799/10000000000 : ℝ)|=(1881042799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5208057539/10000000000 : ℝ)|^4667 ≤ (43354782549837/100000000000000 : ℝ)^3643
        have hw : |(5208057539/10000000000 : ℝ)|=(5208057539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1585_s2_2 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350931097/10000000000 : ℝ)*x 0 + (2604028521/5000000000 : ℝ)*x 1 + (-376208649/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350931097/10000000000 : ℝ)^4667 ≤ (44884291830671/100000000000000 : ℝ)^3643 := by
    have hnat : (5350931097 : ℕ)^4667*100000000000000^3643 ≤ 44884291830671^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350931097 10000000000 44884291830671 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2604028521/5000000000 : ℝ)^4667 ≤ (43354777249589/100000000000000 : ℝ)^3643 := by
    have hnat : (2604028521 : ℕ)^4667*100000000000000^3643 ≤ 43354777249589^3643*5000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2604028521 5000000000 43354777249589 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (376208649/2000000000 : ℝ)^4667 ≤ (11760930896127/100000000000000 : ℝ)^3643 := by
    have hnat : (376208649 : ℕ)^4667*100000000000000^3643 ≤ 11760930896127^3643*2000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      376208649 2000000000 11760930896127 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350931097/10000000000 : ℝ), (2604028521/5000000000 : ℝ), (-376208649/2000000000 : ℝ)] ![(44884291830671/100000000000000 : ℝ), (43354777249589/100000000000000 : ℝ), (11760930896127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350931097/10000000000 : ℝ)|^4667 ≤ (44884291830671/100000000000000 : ℝ)^3643
        have hw : |(5350931097/10000000000 : ℝ)|=(5350931097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2604028521/5000000000 : ℝ)|^4667 ≤ (43354777249589/100000000000000 : ℝ)^3643
        have hw : |(2604028521/5000000000 : ℝ)|=(2604028521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-376208649/2000000000 : ℝ)|^4667 ≤ (11760930896127/100000000000000 : ℝ)^3643
        have hw : |(-376208649/2000000000 : ℝ)|=(376208649/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1585_s2_3 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (847113359/2000000000 : ℝ)*x 0 + (992186169/2500000000 : ℝ)*x 1 + (2258278549/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (847113359/2000000000 : ℝ)^4667 ≤ (16634556094547/50000000000000 : ℝ)^3643 := by
    have hnat : (847113359 : ℕ)^4667*50000000000000^3643 ≤ 16634556094547^3643*2000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847113359 2000000000 16634556094547 50000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (992186169/2500000000 : ℝ)^4667 ≤ (6121667963977/20000000000000 : ℝ)^3643 := by
    have hnat : (992186169 : ℕ)^4667*20000000000000^3643 ≤ 6121667963977^3643*2500000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      992186169 2500000000 6121667963977 20000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2258278549/5000000000 : ℝ)^4667 ≤ (7224509593867/20000000000000 : ℝ)^3643 := by
    have hnat : (2258278549 : ℕ)^4667*20000000000000^3643 ≤ 7224509593867^3643*5000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2258278549 5000000000 7224509593867 20000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(847113359/2000000000 : ℝ), (992186169/2500000000 : ℝ), (2258278549/5000000000 : ℝ)] ![(16634556094547/50000000000000 : ℝ), (6121667963977/20000000000000 : ℝ), (7224509593867/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(847113359/2000000000 : ℝ)|^4667 ≤ (16634556094547/50000000000000 : ℝ)^3643
        have hw : |(847113359/2000000000 : ℝ)|=(847113359/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(992186169/2500000000 : ℝ)|^4667 ≤ (6121667963977/20000000000000 : ℝ)^3643
        have hw : |(992186169/2500000000 : ℝ)|=(992186169/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2258278549/5000000000 : ℝ)|^4667 ≤ (7224509593867/20000000000000 : ℝ)^3643
        have hw : |(2258278549/5000000000 : ℝ)|=(2258278549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1585_s2_4 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1763250207/10000000000 : ℝ)*x 0 + (1302353193/2500000000 : ℝ)*x 1 + (5436410367/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1763250207/10000000000 : ℝ)^4667 ≤ (2706466073353/25000000000000 : ℝ)^3643 := by
    have hnat : (1763250207 : ℕ)^4667*25000000000000^3643 ≤ 2706466073353^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1763250207 10000000000 2706466073353 25000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1302353193/2500000000 : ℝ)^4667 ≤ (43369235939727/100000000000000 : ℝ)^3643 := by
    have hnat : (1302353193 : ℕ)^4667*100000000000000^3643 ≤ 43369235939727^3643*2500000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1302353193 2500000000 43369235939727 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5436410367/10000000000 : ℝ)^4667 ≤ (2862806234889/6250000000000 : ℝ)^3643 := by
    have hnat : (5436410367 : ℕ)^4667*6250000000000^3643 ≤ 2862806234889^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436410367 10000000000 2862806234889 6250000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1763250207/10000000000 : ℝ), (1302353193/2500000000 : ℝ), (5436410367/10000000000 : ℝ)] ![(2706466073353/25000000000000 : ℝ), (43369235939727/100000000000000 : ℝ), (2862806234889/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1763250207/10000000000 : ℝ)|^4667 ≤ (2706466073353/25000000000000 : ℝ)^3643
        have hw : |(-1763250207/10000000000 : ℝ)|=(1763250207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1302353193/2500000000 : ℝ)|^4667 ≤ (43369235939727/100000000000000 : ℝ)^3643
        have hw : |(1302353193/2500000000 : ℝ)|=(1302353193/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5436410367/10000000000 : ℝ)|^4667 ≤ (2862806234889/6250000000000 : ℝ)^3643
        have hw : |(5436410367/10000000000 : ℝ)|=(5436410367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1585_s2_5 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2645022133/5000000000 : ℝ)*x 0 + (-826344903/5000000000 : ℝ)*x 1 + (5436411561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2645022133/5000000000 : ℝ)^4667 ≤ (44231055952139/100000000000000 : ℝ)^3643 := by
    have hnat : (2645022133 : ℕ)^4667*100000000000000^3643 ≤ 44231055952139^3643*5000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2645022133 5000000000 44231055952139 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (826344903/5000000000 : ℝ)^4667 ≤ (9964031393273/100000000000000 : ℝ)^3643 := by
    have hnat : (826344903 : ℕ)^4667*100000000000000^3643 ≤ 9964031393273^3643*5000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      826344903 5000000000 9964031393273 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5436411561/10000000000 : ℝ)^4667 ≤ (45804912646139/100000000000000 : ℝ)^3643 := by
    have hnat : (5436411561 : ℕ)^4667*100000000000000^3643 ≤ 45804912646139^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436411561 10000000000 45804912646139 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2645022133/5000000000 : ℝ), (-826344903/5000000000 : ℝ), (5436411561/10000000000 : ℝ)] ![(44231055952139/100000000000000 : ℝ), (9964031393273/100000000000000 : ℝ), (45804912646139/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2645022133/5000000000 : ℝ)|^4667 ≤ (44231055952139/100000000000000 : ℝ)^3643
        have hw : |(2645022133/5000000000 : ℝ)|=(2645022133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-826344903/5000000000 : ℝ)|^4667 ≤ (9964031393273/100000000000000 : ℝ)^3643
        have hw : |(-826344903/5000000000 : ℝ)|=(826344903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5436411561/10000000000 : ℝ)|^4667 ≤ (45804912646139/100000000000000 : ℝ)^3643
        have hw : |(5436411561/10000000000 : ℝ)|=(5436411561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1585_s2_6 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661255541/1250000000 : ℝ)*x 0 + (1359103187/2500000000 : ℝ)*x 1 + (-82634403/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661255541/1250000000 : ℝ)^4667 ≤ (22115528308123/50000000000000 : ℝ)^3643 := by
    have hnat : (661255541 : ℕ)^4667*50000000000000^3643 ≤ 22115528308123^3643*1250000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661255541 1250000000 22115528308123 50000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1359103187/2500000000 : ℝ)^4667 ≤ (22902462729249/50000000000000 : ℝ)^3643 := by
    have hnat : (1359103187 : ℕ)^4667*50000000000000^3643 ≤ 22902462729249^3643*2500000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359103187 2500000000 22902462729249 50000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (82634403/500000000 : ℝ)^4667 ≤ (9964017907789/100000000000000 : ℝ)^3643 := by
    have hnat : (82634403 : ℕ)^4667*100000000000000^3643 ≤ 9964017907789^3643*500000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82634403 500000000 9964017907789 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661255541/1250000000 : ℝ), (1359103187/2500000000 : ℝ), (-82634403/500000000 : ℝ)] ![(22115528308123/50000000000000 : ℝ), (22902462729249/50000000000000 : ℝ), (9964017907789/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661255541/1250000000 : ℝ)|^4667 ≤ (22115528308123/50000000000000 : ℝ)^3643
        have hw : |(661255541/1250000000 : ℝ)|=(661255541/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1359103187/2500000000 : ℝ)|^4667 ≤ (22902462729249/50000000000000 : ℝ)^3643
        have hw : |(1359103187/2500000000 : ℝ)|=(1359103187/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-82634403/500000000 : ℝ)|^4667 ≤ (9964017907789/100000000000000 : ℝ)^3643
        have hw : |(-82634403/500000000 : ℝ)|=(82634403/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1585_s2_7 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4235656631/10000000000 : ℝ)*x 0 + (4513325763/10000000000 : ℝ)*x 1 + (1986001703/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4235656631/10000000000 : ℝ)^4667 ≤ (33270016171561/100000000000000 : ℝ)^3643 := by
    have hnat : (4235656631 : ℕ)^4667*100000000000000^3643 ≤ 33270016171561^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4235656631 10000000000 33270016171561 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4513325763/10000000000 : ℝ)^4667 ≤ (36089443410281/100000000000000 : ℝ)^3643 := by
    have hnat : (4513325763 : ℕ)^4667*100000000000000^3643 ≤ 36089443410281^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4513325763 10000000000 36089443410281 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1986001703/5000000000 : ℝ)^4667 ≤ (612810808047/2000000000000 : ℝ)^3643 := by
    have hnat : (1986001703 : ℕ)^4667*2000000000000^3643 ≤ 612810808047^3643*5000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1986001703 5000000000 612810808047 2000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4235656631/10000000000 : ℝ), (4513325763/10000000000 : ℝ), (1986001703/5000000000 : ℝ)] ![(33270016171561/100000000000000 : ℝ), (36089443410281/100000000000000 : ℝ), (612810808047/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4235656631/10000000000 : ℝ)|^4667 ≤ (33270016171561/100000000000000 : ℝ)^3643
        have hw : |(4235656631/10000000000 : ℝ)|=(4235656631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4513325763/10000000000 : ℝ)|^4667 ≤ (36089443410281/100000000000000 : ℝ)^3643
        have hw : |(4513325763/10000000000 : ℝ)|=(4513325763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1986001703/5000000000 : ℝ)|^4667 ≤ (612810808047/2000000000000 : ℝ)^3643
        have hw : |(1986001703/5000000000 : ℝ)|=(1986001703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1585_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (42308779/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17621/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4617/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10901/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7887/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17621/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4617/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17621/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4617/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17621/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4617/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17621/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4617/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17621/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4617/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17621/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4617/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4617/50000 : ℝ) ^ (4665/1024 : ℝ) ≤ (77396942460569/4000000000000000000 : ℝ) := by
    have hpowers : (4617/50000 : ℝ)^4665 ≤ (77396942460569/4000000000000000000 : ℝ)^1024 := by
      have hnat : (4617 : ℕ)^4665*4000000000000000000^1024 ≤ 77396942460569^1024*50000^4665 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4617 50000 77396942460569 4000000000000000000 4665 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4617/50000 : ℝ)) (X := (77396942460569/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4665 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17621/100000 : ℝ) ^ (4665/1024 : ℝ) ≤ (9185620240843301/25000000000000000000 : ℝ) := by
    have hpowers : (17621/100000 : ℝ)^4665 ≤ (9185620240843301/25000000000000000000 : ℝ)^1024 := by
      have hnat : (17621 : ℕ)^4665*25000000000000000000^1024 ≤ 9185620240843301^1024*100000^4665 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17621 100000 9185620240843301 25000000000000000000 4665 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17621/100000 : ℝ)) (X := (9185620240843301/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4665 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000077396942460569/2000000000000000000 : ℝ) ≤ (19531415907339/19531250000000 : ℝ) ^ (4665/1024 : ℝ) := by
    have hpowers : (2000077396942460569/2000000000000000000 : ℝ)^1024 ≤ (19531415907339/19531250000000 : ℝ)^4665 := by
      have hnat : (2000077396942460569 : ℕ)^1024*19531250000000^4665 ≤ 19531415907339^4665*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000077396942460569 2000000000000000000 19531415907339 19531250000000 1024 4665 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (19531415907339/19531250000000 : ℝ)) (X := (2000077396942460569/2000000000000000000 : ℝ)) (by norm_num) 4665 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100038677404524887429/100000000000000000000 : ℝ) ≤ (10000848867859307/10000000000000000 : ℝ) ^ (4665/1024 : ℝ) := by
    have hpowers : (100038677404524887429/100000000000000000000 : ℝ)^1024 ≤ (10000848867859307/10000000000000000 : ℝ)^4665 := by
      have hnat : (100038677404524887429 : ℕ)^1024*10000000000000000^4665 ≤ 10000848867859307^4665*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100038677404524887429 100000000000000000000 10000848867859307 10000000000000000 1024 4665 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000848867859307/10000000000000000 : ℝ)) (X := (100038677404524887429/100000000000000000000 : ℝ)) (by norm_num) 4665 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12509185620240843301/12500000000000000000 : ℝ) ≤ (5000806395580523/5000000000000000 : ℝ) ^ (4665/1024 : ℝ) := by
    have hpowers : (12509185620240843301/12500000000000000000 : ℝ)^1024 ≤ (5000806395580523/5000000000000000 : ℝ)^4665 := by
      have hnat : (12509185620240843301 : ℕ)^1024*5000000000000000^4665 ≤ 5000806395580523^4665*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12509185620240843301 12500000000000000000 5000806395580523 5000000000000000 1024 4665 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000806395580523/5000000000000000 : ℝ)) (X := (12509185620240843301/12500000000000000000 : ℝ)) (by norm_num) 4665 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(77396942460569/4000000000000000000 : ℝ) ≤ ((20964151073616951741/20967500000000000000 : ℝ)+2*(763923301739/838700000000000 : ℝ)*(4617/50000 : ℝ))^(4665/1024 : ℝ) := by
    rw [show (20964151073616951741/20967500000000000000 : ℝ)+2*(763923301739/838700000000000 : ℝ)*(4617/50000 : ℝ)=(19531415907339/19531250000000 : ℝ) by norm_num, show 1+2*(77396942460569/4000000000000000000 : ℝ)=(2000077396942460569/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9185620240843301/25000000000000000000 : ℝ)+(77396942460569/4000000000000000000 : ℝ) ≤ ((20964151073616951741/20967500000000000000 : ℝ)+(763923301739/838700000000000 : ℝ)*((17621/100000 : ℝ)+(4617/50000 : ℝ)))^(4665/1024 : ℝ) := by
    rw [show (20964151073616951741/20967500000000000000 : ℝ)+(763923301739/838700000000000 : ℝ)*((17621/100000 : ℝ)+(4617/50000 : ℝ))=(10000848867859307/10000000000000000 : ℝ) by norm_num, show 1+(9185620240843301/25000000000000000000 : ℝ)+(77396942460569/4000000000000000000 : ℝ)=(100038677404524887429/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9185620240843301/25000000000000000000 : ℝ) ≤ ((20964151073616951741/20967500000000000000 : ℝ)+2*(763923301739/838700000000000 : ℝ)*(17621/100000 : ℝ))^(4665/1024 : ℝ) := by
    rw [show (20964151073616951741/20967500000000000000 : ℝ)+2*(763923301739/838700000000000 : ℝ)*(17621/100000 : ℝ)=(5000806395580523/5000000000000000 : ℝ) by norm_num, show 1+2*(9185620240843301/25000000000000000000 : ℝ)=(12509185620240843301/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (20964151073616951741/20967500000000000000 : ℝ)*(X 1 0+X 2 0)+(763923301739/838700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4665/1024 : ℝ)) (lo := (4617/50000 : ℝ)) (hi := (17621/100000 : ℝ)) (c := (20964151073616951741/20967500000000000000 : ℝ)) (alpha := (763923301739/838700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (20964151073616951741/20967500000000000000 : ℝ)*(X 0 1+X 2 1)+(763923301739/838700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4665/1024 : ℝ)) (lo := (4617/50000 : ℝ)) (hi := (17621/100000 : ℝ)) (c := (20964151073616951741/20967500000000000000 : ℝ)) (alpha := (763923301739/838700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (20964151073616951741/20967500000000000000 : ℝ)*(X 0 2+X 1 2)+(763923301739/838700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4665/1024 : ℝ)) (lo := (4617/50000 : ℝ)) (hi := (17621/100000 : ℝ)) (c := (20964151073616951741/20967500000000000000 : ℝ)) (alpha := (763923301739/838700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1763212811/10000000000 : ℝ)*X 0 0+(169930529/312500000 : ℝ)*X 0 1+(5208057209/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668866367/1250000000 : ℝ)*X 1 0+(-1881042799/10000000000 : ℝ)*X 1 1+(5208057539/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350931097/10000000000 : ℝ)*X 2 0+(2604028521/5000000000 : ℝ)*X 2 1+(-376208649/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((847113359/2000000000 : ℝ)*X 0 0+(992186169/2500000000 : ℝ)*X 0 1+(2258278549/5000000000 : ℝ)*X 0 2+(847113359/2000000000 : ℝ)*X 1 0+(992186169/2500000000 : ℝ)*X 1 1+(2258278549/5000000000 : ℝ)*X 1 2+(847113359/2000000000 : ℝ)*X 2 0+(992186169/2500000000 : ℝ)*X 2 1+(2258278549/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1763250207/10000000000 : ℝ)*X 0 0+(1302353193/2500000000 : ℝ)*X 0 1+(5436410367/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2645022133/5000000000 : ℝ)*X 1 0+(-826344903/5000000000 : ℝ)*X 1 1+(5436411561/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((661255541/1250000000 : ℝ)*X 2 0+(1359103187/2500000000 : ℝ)*X 2 1+(-82634403/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4235656631/10000000000 : ℝ)*X 0 0+(4513325763/10000000000 : ℝ)*X 0 1+(1986001703/5000000000 : ℝ)*X 0 2+(4235656631/10000000000 : ℝ)*X 1 0+(4513325763/10000000000 : ℝ)*X 1 1+(1986001703/5000000000 : ℝ)*X 1 2+(4235656631/10000000000 : ℝ)*X 2 0+(4513325763/10000000000 : ℝ)*X 2 1+(1986001703/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9929593392243936073741921239/1048375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (148091551/12500000000000 : ℝ)*(base19) + (665828359/50000000000000 : ℝ)*(base23) + (126720503/50000000000000 : ℝ)*(upper3) + (11316421/50000000000000 : ℝ)*(lower4) + (3089318879270469/100000000000000 : ℝ)*(major0) + (3089318879270469/100000000000000 : ℝ)*(major1) + (3089318879270469/100000000000000 : ℝ)*(major2) + (4353157666488981/100000000000000 : ℝ)*(sp0) + (217658826768973/5000000000000 : ℝ)*(sp1) + (2176587036275033/50000000000000 : ℝ)*(sp2) + (912724852759271/50000000000000 : ℝ)*(sp3) + (20053622887/100000000000000 : ℝ)*(sp4) + (463181017/20000000000000 : ℝ)*(sp6) + (1001719673/10000000000000 : ℝ)*(sp7) + (228182465339409/12500000000000 : ℝ)*(f.failure) + (1088294430027967/25000000000000 : ℝ)*(f.sum) + (71092258983609/41935000000000000000000000000 : ℝ)*base66 + (18855209580069711529/2096750000000000000000000000000000 : ℝ)*base67 + (19333108094824711529/2096750000000000000000000000000000 : ℝ)*base69 + (23245544993059211529/2096750000000000000000000000000000 : ℝ)*base71 + (31204631443679/41935000000000000000000000000 : ℝ)*base74 + (13320959730116211529/2096750000000000000000000000000000 : ℝ)*base75 + (1593590892955711529/2096750000000000000000000000000000 : ℝ)*base77 + (7693066140034711529/2096750000000000000000000000000000 : ℝ)*base79 + (255557156528281/41935000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (253389/312500000000000000000 : ℝ)*base90 + (253389/312500000000000000000 : ℝ)*base92 + (253389/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (673470551971052330294169/41935000000000000000000000000 : ℝ) := by norm_num
    linear_combination (40235539/25000000000000 : ℝ)*(base19) + (259231273/25000000000000 : ℝ)*(base23) + (35613149/20000000000000 : ℝ)*(upper3) + (182440409/100000000000000 : ℝ)*(lower4) + (77524333/100000000000000 : ℝ)*(upper5) + (3126329824473879/100000000000000 : ℝ)*(major0) + (3126329824473879/100000000000000 : ℝ)*(major1) + (3126329824473879/100000000000000 : ℝ)*(major2) + (18452839693/100000000000000 : ℝ)*(sp1) + (60111351749/100000000000000 : ℝ)*(sp2) + (550666231081107/12500000000000 : ℝ)*(sp4) + (68832988044797/1562500000000 : ℝ)*(sp5) + (275329293773251/6250000000000 : ℝ)*(sp6) + (461832316242493/25000000000000 : ℝ)*(sp7) + (461832316242493/25000000000000 : ℝ)*(f.failure) + (550666231081107/12500000000000 : ℝ)*(f.sum) + (128047497980319/41935000000000000000000000000 : ℝ)*base66 + (5340330639418598339/2096750000000000000000000000000000 : ℝ)*base67 + (11022444897095598339/2096750000000000000000000000000000 : ℝ)*base69 + (9355843871251401661/2096750000000000000000000000000000 : ℝ)*base72 + (119320840670077/20967500000000000000000000000 : ℝ)*base74 + (19462524410600348339/2096750000000000000000000000000000 : ℝ)*base75 + (748150712095151661/2096750000000000000000000000000000 : ℝ)*base78 + (22449443660800901661/2096750000000000000000000000000000 : ℝ)*base80 + (7790627644391/10483750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (2996047/625000000000000000000 : ℝ)*base89 + (2996047/625000000000000000000 : ℝ)*base91 + (2996047/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1585_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (42308779/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17621/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4617/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10901/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7887/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1585_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1585_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (42308779/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10901/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7887/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1585_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1585_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1585_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (42308779/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10901/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7887/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1585_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
