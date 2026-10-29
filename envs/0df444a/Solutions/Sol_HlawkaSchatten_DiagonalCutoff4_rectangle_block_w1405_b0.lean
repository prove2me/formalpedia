-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1405_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:47:21.003902+00:00
-- url     : https://prove2.me/submissions/abc7fd15-3d94-445b-bf2e-a93b864d9d51

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
theorem support_rectangle_w1405_s0_0 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-886241151/5000000000 : ℝ)*x 0 + (5970148049/10000000000 : ℝ)*x 1 + (1206429043/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (886241151/5000000000 : ℝ)^4365 ≤ (2085959964391/20000000000000 : ℝ)^3341 := by
    have hnat : (886241151 : ℕ)^4365*20000000000000^3341 ≤ 2085959964391^3341*5000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      886241151 5000000000 2085959964391 20000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5970148049/10000000000 : ℝ)^4365 ≤ (50971291849843/100000000000000 : ℝ)^3341 := by
    have hnat : (5970148049 : ℕ)^4365*100000000000000^3341 ≤ 50971291849843^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5970148049 10000000000 50971291849843 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1206429043/2500000000 : ℝ)^4365 ≤ (19299454157531/50000000000000 : ℝ)^3341 := by
    have hnat : (1206429043 : ℕ)^4365*50000000000000^3341 ≤ 19299454157531^3341*2500000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1206429043 2500000000 19299454157531 50000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-886241151/5000000000 : ℝ), (5970148049/10000000000 : ℝ), (1206429043/2500000000 : ℝ)] ![(2085959964391/20000000000000 : ℝ), (50971291849843/100000000000000 : ℝ), (19299454157531/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-886241151/5000000000 : ℝ)|^4365 ≤ (2085959964391/20000000000000 : ℝ)^3341
        have hw : |(-886241151/5000000000 : ℝ)|=(886241151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5970148049/10000000000 : ℝ)|^4365 ≤ (50971291849843/100000000000000 : ℝ)^3341
        have hw : |(5970148049/10000000000 : ℝ)|=(5970148049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1206429043/2500000000 : ℝ)|^4365 ≤ (19299454157531/50000000000000 : ℝ)^3341
        have hw : |(1206429043/2500000000 : ℝ)|=(1206429043/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_s0_1 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1098954359/2000000000 : ℝ)*x 0 + (-1210025621/5000000000 : ℝ)*x 1 + (4825716443/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1098954359/2000000000 : ℝ)^4365 ≤ (45734666391953/100000000000000 : ℝ)^3341 := by
    have hnat : (1098954359 : ℕ)^4365*100000000000000^3341 ≤ 45734666391953^3341*2000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098954359 2000000000 45734666391953 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1210025621/5000000000 : ℝ)^4365 ≤ (15666422443107/100000000000000 : ℝ)^3341 := by
    have hnat : (1210025621 : ℕ)^4365*100000000000000^3341 ≤ 15666422443107^3341*5000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1210025621 5000000000 15666422443107 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4825716443/10000000000 : ℝ)^4365 ≤ (38598911147043/100000000000000 : ℝ)^3341 := by
    have hnat : (4825716443 : ℕ)^4365*100000000000000^3341 ≤ 38598911147043^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4825716443 10000000000 38598911147043 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1098954359/2000000000 : ℝ), (-1210025621/5000000000 : ℝ), (4825716443/10000000000 : ℝ)] ![(45734666391953/100000000000000 : ℝ), (15666422443107/100000000000000 : ℝ), (38598911147043/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1098954359/2000000000 : ℝ)|^4365 ≤ (45734666391953/100000000000000 : ℝ)^3341
        have hw : |(1098954359/2000000000 : ℝ)|=(1098954359/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1210025621/5000000000 : ℝ)|^4365 ≤ (15666422443107/100000000000000 : ℝ)^3341
        have hw : |(-1210025621/5000000000 : ℝ)|=(1210025621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4825716443/10000000000 : ℝ)|^4365 ≤ (38598911147043/100000000000000 : ℝ)^3341
        have hw : |(4825716443/10000000000 : ℝ)|=(4825716443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_s0_2 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5494771991/10000000000 : ℝ)*x 0 + (4825716333/10000000000 : ℝ)*x 1 + (-1210025563/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5494771991/10000000000 : ℝ)^4365 ≤ (714604195677/1562500000000 : ℝ)^3341 := by
    have hnat : (5494771991 : ℕ)^4365*1562500000000^3341 ≤ 714604195677^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5494771991 10000000000 714604195677 1562500000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4825716333/10000000000 : ℝ)^4365 ≤ (3859890999753/10000000000000 : ℝ)^3341 := by
    have hnat : (4825716333 : ℕ)^4365*10000000000000^3341 ≤ 3859890999753^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4825716333 10000000000 3859890999753 10000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1210025563/5000000000 : ℝ)^4365 ≤ (3916605365503/25000000000000 : ℝ)^3341 := by
    have hnat : (1210025563 : ℕ)^4365*25000000000000^3341 ≤ 3916605365503^3341*5000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1210025563 5000000000 3916605365503 25000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5494771991/10000000000 : ℝ), (4825716333/10000000000 : ℝ), (-1210025563/5000000000 : ℝ)] ![(714604195677/1562500000000 : ℝ), (3859890999753/10000000000000 : ℝ), (3916605365503/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5494771991/10000000000 : ℝ)|^4365 ≤ (714604195677/1562500000000 : ℝ)^3341
        have hw : |(5494771991/10000000000 : ℝ)|=(5494771991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4825716333/10000000000 : ℝ)|^4365 ≤ (3859890999753/10000000000000 : ℝ)^3341
        have hw : |(4825716333/10000000000 : ℝ)|=(4825716333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1210025563/5000000000 : ℝ)|^4365 ≤ (3916605365503/25000000000000 : ℝ)^3341
        have hw : |(-1210025563/5000000000 : ℝ)|=(1210025563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_s0_3 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4169462981/10000000000 : ℝ)*x 0 + (3104027481/10000000000 : ℝ)*x 1 + (5558063129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4169462981/10000000000 : ℝ)^4365 ≤ (31888680998159/100000000000000 : ℝ)^3341 := by
    have hnat : (4169462981 : ℕ)^4365*100000000000000^3341 ≤ 31888680998159^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4169462981 10000000000 31888680998159 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3104027481/10000000000 : ℝ)^4365 ≤ (10843594147073/50000000000000 : ℝ)^3341 := by
    have hnat : (3104027481 : ℕ)^4365*50000000000000^3341 ≤ 10843594147073^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3104027481 10000000000 10843594147073 50000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5558063129/10000000000 : ℝ)^4365 ≤ (23212065342919/50000000000000 : ℝ)^3341 := by
    have hnat : (5558063129 : ℕ)^4365*50000000000000^3341 ≤ 23212065342919^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5558063129 10000000000 23212065342919 50000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4169462981/10000000000 : ℝ), (3104027481/10000000000 : ℝ), (5558063129/10000000000 : ℝ)] ![(31888680998159/100000000000000 : ℝ), (10843594147073/50000000000000 : ℝ), (23212065342919/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4169462981/10000000000 : ℝ)|^4365 ≤ (31888680998159/100000000000000 : ℝ)^3341
        have hw : |(4169462981/10000000000 : ℝ)|=(4169462981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3104027481/10000000000 : ℝ)|^4365 ≤ (10843594147073/50000000000000 : ℝ)^3341
        have hw : |(3104027481/10000000000 : ℝ)|=(3104027481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5558063129/10000000000 : ℝ)|^4365 ≤ (23212065342919/50000000000000 : ℝ)^3341
        have hw : |(5558063129/10000000000 : ℝ)|=(5558063129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_s0_4 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1776617203/10000000000 : ℝ)*x 0 + (303440597/625000000 : ℝ)*x 1 + (2969883387/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1776617203/10000000000 : ℝ)^4365 ≤ (10461599454609/100000000000000 : ℝ)^3341 := by
    have hnat : (1776617203 : ℕ)^4365*100000000000000^3341 ≤ 10461599454609^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1776617203 10000000000 10461599454609 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (303440597/625000000 : ℝ)^4365 ≤ (38905730620093/100000000000000 : ℝ)^3341 := by
    have hnat : (303440597 : ℕ)^4365*100000000000000^3341 ≤ 38905730620093^3341*625000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      303440597 625000000 38905730620093 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2969883387/5000000000 : ℝ)^4365 ≤ (50632669913263/100000000000000 : ℝ)^3341 := by
    have hnat : (2969883387 : ℕ)^4365*100000000000000^3341 ≤ 50632669913263^3341*5000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2969883387 5000000000 50632669913263 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1776617203/10000000000 : ℝ), (303440597/625000000 : ℝ), (2969883387/5000000000 : ℝ)] ![(10461599454609/100000000000000 : ℝ), (38905730620093/100000000000000 : ℝ), (50632669913263/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1776617203/10000000000 : ℝ)|^4365 ≤ (10461599454609/100000000000000 : ℝ)^3341
        have hw : |(-1776617203/10000000000 : ℝ)|=(1776617203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(303440597/625000000 : ℝ)|^4365 ≤ (38905730620093/100000000000000 : ℝ)^3341
        have hw : |(303440597/625000000 : ℝ)|=(303440597/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2969883387/5000000000 : ℝ)|^4365 ≤ (50632669913263/100000000000000 : ℝ)^3341
        have hw : |(2969883387/5000000000 : ℝ)|=(2969883387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_s0_5 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2591262747/5000000000 : ℝ)*x 0 + (-26120021/200000000 : ℝ)*x 1 + (5939767023/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2591262747/5000000000 : ℝ)^4365 ≤ (8473831153563/20000000000000 : ℝ)^3341 := by
    have hnat : (2591262747 : ℕ)^4365*20000000000000^3341 ≤ 8473831153563^3341*5000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591262747 5000000000 8473831153563 20000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (26120021/200000000 : ℝ)^4365 ≤ (874771440763/12500000000000 : ℝ)^3341 := by
    have hnat : (26120021 : ℕ)^4365*12500000000000^3341 ≤ 874771440763^3341*200000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26120021 200000000 874771440763 12500000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5939767023/10000000000 : ℝ)^4365 ≤ (25316336343191/50000000000000 : ℝ)^3341 := by
    have hnat : (5939767023 : ℕ)^4365*50000000000000^3341 ≤ 25316336343191^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5939767023 10000000000 25316336343191 50000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2591262747/5000000000 : ℝ), (-26120021/200000000 : ℝ), (5939767023/10000000000 : ℝ)] ![(8473831153563/20000000000000 : ℝ), (874771440763/12500000000000 : ℝ), (25316336343191/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2591262747/5000000000 : ℝ)|^4365 ≤ (8473831153563/20000000000000 : ℝ)^3341
        have hw : |(2591262747/5000000000 : ℝ)|=(2591262747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-26120021/200000000 : ℝ)|^4365 ≤ (874771440763/12500000000000 : ℝ)^3341
        have hw : |(-26120021/200000000 : ℝ)|=(26120021/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5939767023/10000000000 : ℝ)|^4365 ≤ (25316336343191/50000000000000 : ℝ)^3341
        have hw : |(5939767023/10000000000 : ℝ)|=(5939767023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_s0_6 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5182525881/10000000000 : ℝ)*x 0 + (5939766853/10000000000 : ℝ)*x 1 + (-1306000731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5182525881/10000000000 : ℝ)^4365 ≤ (21184579950701/50000000000000 : ℝ)^3341 := by
    have hnat : (5182525881 : ℕ)^4365*50000000000000^3341 ≤ 21184579950701^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182525881 10000000000 21184579950701 50000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5939766853/10000000000 : ℝ)^4365 ≤ (395567740571/781250000000 : ℝ)^3341 := by
    have hnat : (5939766853 : ℕ)^4365*781250000000^3341 ≤ 395567740571^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5939766853 10000000000 395567740571 781250000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1306000731/10000000000 : ℝ)^4365 ≤ (6998169292843/100000000000000 : ℝ)^3341 := by
    have hnat : (1306000731 : ℕ)^4365*100000000000000^3341 ≤ 6998169292843^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1306000731 10000000000 6998169292843 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5182525881/10000000000 : ℝ), (5939766853/10000000000 : ℝ), (-1306000731/10000000000 : ℝ)] ![(21184579950701/50000000000000 : ℝ), (395567740571/781250000000 : ℝ), (6998169292843/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5182525881/10000000000 : ℝ)|^4365 ≤ (21184579950701/50000000000000 : ℝ)^3341
        have hw : |(5182525881/10000000000 : ℝ)|=(5182525881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5939766853/10000000000 : ℝ)|^4365 ≤ (395567740571/781250000000 : ℝ)^3341
        have hw : |(5939766853/10000000000 : ℝ)|=(5939766853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1306000731/10000000000 : ℝ)|^4365 ≤ (6998169292843/100000000000000 : ℝ)^3341
        have hw : |(-1306000731/10000000000 : ℝ)|=(1306000731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_s0_7 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1044582481/2500000000 : ℝ)*x 0 + (343447671/625000000 : ℝ)*x 1 + (3169174971/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1044582481/2500000000 : ℝ)^4365 ≤ (399716384463/1250000000000 : ℝ)^3341 := by
    have hnat : (1044582481 : ℕ)^4365*1250000000000^3341 ≤ 399716384463^3341*2500000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044582481 2500000000 399716384463 1250000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (343447671/625000000 : ℝ)^4365 ≤ (22869458835353/50000000000000 : ℝ)^3341 := by
    have hnat : (343447671 : ℕ)^4365*50000000000000^3341 ≤ 22869458835353^3341*625000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343447671 625000000 22869458835353 50000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3169174971/10000000000 : ℝ)^4365 ≤ (11141885778887/50000000000000 : ℝ)^3341 := by
    have hnat : (3169174971 : ℕ)^4365*50000000000000^3341 ≤ 11141885778887^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3169174971 10000000000 11141885778887 50000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1044582481/2500000000 : ℝ), (343447671/625000000 : ℝ), (3169174971/10000000000 : ℝ)] ![(399716384463/1250000000000 : ℝ), (22869458835353/50000000000000 : ℝ), (11141885778887/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1044582481/2500000000 : ℝ)|^4365 ≤ (399716384463/1250000000000 : ℝ)^3341
        have hw : |(1044582481/2500000000 : ℝ)|=(1044582481/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(343447671/625000000 : ℝ)|^4365 ≤ (22869458835353/50000000000000 : ℝ)^3341
        have hw : |(343447671/625000000 : ℝ)|=(343447671/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3169174971/10000000000 : ℝ)|^4365 ≤ (11141885778887/50000000000000 : ℝ)^3341
        have hw : |(3169174971/10000000000 : ℝ)|=(3169174971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1405_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157216317/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1877/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1057/4000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (1091/256 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^1091 ≤ (0 : ℝ)^256 := by
      have hnat : (0 : ℕ)^1091*1^256 ≤ 0^256*1^1091 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 1091 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 1091 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (1091/256 : ℝ) ≤ (125884314995509217/6250000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^1091 ≤ (125884314995509217/6250000000000000000 : ℝ)^256 := by
      have hnat : (2 : ℕ)^1091*6250000000000000000^256 ≤ 125884314995509217^256*5^1091 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 125884314995509217 6250000000000000000 1091 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (125884314995509217/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 1091 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (1091/256 : ℝ) := by
    have hpowers : (1 : ℝ)^256 ≤ (1 : ℝ)^1091 := by
      have hnat : (1 : ℕ)^256*1^1091 ≤ 1^1091*1^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 256 1091 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 1091 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (6375884314995509217/6250000000000000000 : ℝ) ≤ (2511725352075491/2500000000000000 : ℝ) ^ (1091/256 : ℝ) := by
    have hpowers : (6375884314995509217/6250000000000000000 : ℝ)^256 ≤ (2511725352075491/2500000000000000 : ℝ)^1091 := by
      have hnat : (6375884314995509217 : ℕ)^256*2500000000000000^1091 ≤ 2511725352075491^1091*6250000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6375884314995509217 6250000000000000000 2511725352075491 2500000000000000 256 1091 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2511725352075491/2500000000000000 : ℝ)) (X := (6375884314995509217/6250000000000000000 : ℝ)) (by norm_num) 1091 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (3250884314995509217/3125000000000000000 : ℝ) ≤ (1261725352075491/1250000000000000 : ℝ) ^ (1091/256 : ℝ) := by
    have hpowers : (3250884314995509217/3125000000000000000 : ℝ)^256 ≤ (1261725352075491/1250000000000000 : ℝ)^1091 := by
      have hnat : (3250884314995509217 : ℕ)^256*1250000000000000^1091 ≤ 1261725352075491^1091*3125000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3250884314995509217 3125000000000000000 1261725352075491 1250000000000000 256 1091 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1261725352075491/1250000000000000 : ℝ)) (X := (3250884314995509217/3125000000000000000 : ℝ)) (by norm_num) 1091 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(11725352075491/1000000000000000 : ℝ)*(0 : ℝ))^(1091/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(11725352075491/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(125884314995509217/6250000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(11725352075491/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(1091/256 : ℝ) := by
    rw [show (1 : ℝ)+(11725352075491/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2511725352075491/2500000000000000 : ℝ) by norm_num, show 1+(125884314995509217/6250000000000000000 : ℝ)+(0 : ℝ)=(6375884314995509217/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(125884314995509217/6250000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(11725352075491/1000000000000000 : ℝ)*(2/5 : ℝ))^(1091/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(11725352075491/1000000000000000 : ℝ)*(2/5 : ℝ)=(1261725352075491/1250000000000000 : ℝ) by norm_num, show 1+2*(125884314995509217/6250000000000000000 : ℝ)=(3250884314995509217/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(11725352075491/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1091/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11725352075491/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(11725352075491/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1091/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11725352075491/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(11725352075491/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1091/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11725352075491/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-886241151/5000000000 : ℝ)*X 0 0+(5970148049/10000000000 : ℝ)*X 0 1+(1206429043/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1098954359/2000000000 : ℝ)*X 1 0+(-1210025621/5000000000 : ℝ)*X 1 1+(4825716443/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5494771991/10000000000 : ℝ)*X 2 0+(4825716333/10000000000 : ℝ)*X 2 1+(-1210025563/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4169462981/10000000000 : ℝ)*X 0 0+(3104027481/10000000000 : ℝ)*X 0 1+(5558063129/10000000000 : ℝ)*X 0 2+(4169462981/10000000000 : ℝ)*X 1 0+(3104027481/10000000000 : ℝ)*X 1 1+(5558063129/10000000000 : ℝ)*X 1 2+(4169462981/10000000000 : ℝ)*X 2 0+(3104027481/10000000000 : ℝ)*X 2 1+(5558063129/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1776617203/10000000000 : ℝ)*X 0 0+(303440597/625000000 : ℝ)*X 0 1+(2969883387/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2591262747/5000000000 : ℝ)*X 1 0+(-26120021/200000000 : ℝ)*X 1 1+(5939767023/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5182525881/10000000000 : ℝ)*X 2 0+(5939766853/10000000000 : ℝ)*X 2 1+(-1306000731/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1044582481/2500000000 : ℝ)*X 0 0+(343447671/625000000 : ℝ)*X 0 1+(3169174971/10000000000 : ℝ)*X 0 2+(1044582481/2500000000 : ℝ)*X 1 0+(343447671/625000000 : ℝ)*X 1 1+(3169174971/10000000000 : ℝ)*X 1 2+(1044582481/2500000000 : ℝ)*X 2 0+(343447671/625000000 : ℝ)*X 2 1+(3169174971/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (79156600693220536533417/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6259607/800000000000 : ℝ)*(base19) + (785341679/100000000000000 : ℝ)*(base23) + (96477529/100000000000000 : ℝ)*(upper3) + (3107613/20000000000000 : ℝ)*(upper4) + (27842249/25000000000000 : ℝ)*(upper5) + (320324114444071/50000000000000 : ℝ)*(major0) + (320324114444071/50000000000000 : ℝ)*(major1) + (320324114444071/50000000000000 : ℝ)*(major2) + (218449656820159/25000000000000 : ℝ)*(sp0) + (873800825527083/100000000000000 : ℝ)*(sp1) + (873800822636279/100000000000000 : ℝ)*(sp2) + (407493365974349/100000000000000 : ℝ)*(sp3) + (2980697323/100000000000000 : ℝ)*(sp4) + (275656367/20000000000000 : ℝ)*(sp7) + (81498948851237/20000000000000 : ℝ)*(f.failure) + (436900803988979/50000000000000 : ℝ)*(f.sum) + (220460157663861/25000000000000000000000000000 : ℝ)*base65 + (540709205086139/50000000000000000000000000000 : ℝ)*base68 + (437309570636139/50000000000000000000000000000 : ℝ)*base70 + (118800044663861/50000000000000000000000000000 : ℝ)*base71 + (58388469211139/25000000000000000000000000000 : ℝ)*base74 + (35633710613861/50000000000000000000000000000 : ℝ)*base75 + (28831830536139/50000000000000000000000000000 : ℝ)*base78 + (68339972563861/50000000000000000000000000000 : ℝ)*base79 + (16505748063861/25000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (22034129/2000000000000000000000 : ℝ)*base89 + (22034129/2000000000000000000000 : ℝ)*base91 + (22034129/2000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9074963693879021337/1000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1971806359/100000000000000 : ℝ)*(base19) + (2069747003/100000000000000 : ℝ)*(base23) + (1995591/2500000000000 : ℝ)*(base32) + (299222311/100000000000000 : ℝ)*(upper3) + (230358949/100000000000000 : ℝ)*(upper5) + (168978006975779/25000000000000 : ℝ)*(major0) + (168978006975779/25000000000000 : ℝ)*(major1) + (168978006975779/25000000000000 : ℝ)*(major2) + (470653937/10000000000000 : ℝ)*(sp1) + (1297378313/25000000000000 : ℝ)*(sp2) + (921898895124229/100000000000000 : ℝ)*(sp4) + (1843784433557/200000000000 : ℝ)*(sp5) + (460945817931987/50000000000000 : ℝ)*(sp6) + (42992477835957/10000000000000 : ℝ)*(sp7) + (42992485818321/10000000000000 : ℝ)*(f.failure) + (921898895124229/100000000000000 : ℝ)*(f.sum) + (21733051619989/12500000000000000000000000000 : ℝ)*base65 + (148620656667511/25000000000000000000000000000 : ℝ)*base68 + (9498426367511/25000000000000000000000000000 : ℝ)*base70 + (19449204217511/25000000000000000000000000000 : ℝ)*base72 + (10909304282489/12500000000000000000000000000 : ℝ)*base73 + (84865905467511/25000000000000000000000000000 : ℝ)*base76 + (117681396117511/25000000000000000000000000000 : ℝ)*base78 + (55810739917511/25000000000000000000000000000 : ℝ)*base80 + (71383369982489/12500000000000000000000000000 : ℝ)*base81 + (1256243/1000000000000000000000 : ℝ)*base90 + (1256243/1000000000000000000000 : ℝ)*base92 + (1256243/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1405_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157216317/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1877/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1057/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1405_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1405_s1_0 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-974124447/5000000000 : ℝ)*x 0 + (2807499403/5000000000 : ℝ)*x 1 + (5068224263/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (974124447/5000000000 : ℝ)^4365 ≤ (11801140118873/100000000000000 : ℝ)^3341 := by
    have hnat : (974124447 : ℕ)^4365*100000000000000^3341 ≤ 11801140118873^3341*5000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      974124447 5000000000 11801140118873 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2807499403/5000000000 : ℝ)^4365 ≤ (47046419791951/100000000000000 : ℝ)^3341 := by
    have hnat : (2807499403 : ℕ)^4365*100000000000000^3341 ≤ 47046419791951^3341*5000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2807499403 5000000000 47046419791951 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5068224263/10000000000 : ℝ)^4365 ≤ (41152440078943/100000000000000 : ℝ)^3341 := by
    have hnat : (5068224263 : ℕ)^4365*100000000000000^3341 ≤ 41152440078943^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5068224263 10000000000 41152440078943 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-974124447/5000000000 : ℝ), (2807499403/5000000000 : ℝ), (5068224263/10000000000 : ℝ)] ![(11801140118873/100000000000000 : ℝ), (47046419791951/100000000000000 : ℝ), (41152440078943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-974124447/5000000000 : ℝ)|^4365 ≤ (11801140118873/100000000000000 : ℝ)^3341
        have hw : |(-974124447/5000000000 : ℝ)|=(974124447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2807499403/5000000000 : ℝ)|^4365 ≤ (47046419791951/100000000000000 : ℝ)^3341
        have hw : |(2807499403/5000000000 : ℝ)|=(2807499403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5068224263/10000000000 : ℝ)|^4365 ≤ (41152440078943/100000000000000 : ℝ)^3341
        have hw : |(5068224263/10000000000 : ℝ)|=(5068224263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_s1_1 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (337452107/625000000 : ℝ)*x 0 + (-447703343/2000000000 : ℝ)*x 1 + (2534112519/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (337452107/625000000 : ℝ)^4365 ≤ (11174632625167/25000000000000 : ℝ)^3341 := by
    have hnat : (337452107 : ℕ)^4365*25000000000000^3341 ≤ 11174632625167^3341*625000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337452107 625000000 11174632625167 25000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (447703343/2000000000 : ℝ)^4365 ≤ (884313823609/6250000000000 : ℝ)^3341 := by
    have hnat : (447703343 : ℕ)^4365*6250000000000^3341 ≤ 884313823609^3341*2000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447703343 2000000000 884313823609 6250000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2534112519/5000000000 : ℝ)^4365 ≤ (41152448300409/100000000000000 : ℝ)^3341 := by
    have hnat : (2534112519 : ℕ)^4365*100000000000000^3341 ≤ 41152448300409^3341*5000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2534112519 5000000000 41152448300409 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(337452107/625000000 : ℝ), (-447703343/2000000000 : ℝ), (2534112519/5000000000 : ℝ)] ![(11174632625167/25000000000000 : ℝ), (884313823609/6250000000000 : ℝ), (41152448300409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(337452107/625000000 : ℝ)|^4365 ≤ (11174632625167/25000000000000 : ℝ)^3341
        have hw : |(337452107/625000000 : ℝ)|=(337452107/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-447703343/2000000000 : ℝ)|^4365 ≤ (884313823609/6250000000000 : ℝ)^3341
        have hw : |(-447703343/2000000000 : ℝ)|=(447703343/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2534112519/5000000000 : ℝ)|^4365 ≤ (41152448300409/100000000000000 : ℝ)^3341
        have hw : |(2534112519/5000000000 : ℝ)|=(2534112519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_s1_2 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1349808587/2500000000 : ℝ)*x 0 + (506822457/1000000000 : ℝ)*x 1 + (-447703297/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1349808587/2500000000 : ℝ)^4365 ≤ (44698537379679/100000000000000 : ℝ)^3341 := by
    have hnat : (1349808587 : ℕ)^4365*100000000000000^3341 ≤ 44698537379679^3341*2500000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349808587 2500000000 44698537379679 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (506822457/1000000000 : ℝ)^4365 ≤ (5144055416963/12500000000000 : ℝ)^3341 := by
    have hnat : (506822457 : ℕ)^4365*12500000000000^3341 ≤ 5144055416963^3341*1000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      506822457 1000000000 5144055416963 12500000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (447703297/2000000000 : ℝ)^4365 ≤ (1768627409801/12500000000000 : ℝ)^3341 := by
    have hnat : (447703297 : ℕ)^4365*12500000000000^3341 ≤ 1768627409801^3341*2000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447703297 2000000000 1768627409801 12500000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1349808587/2500000000 : ℝ), (506822457/1000000000 : ℝ), (-447703297/2000000000 : ℝ)] ![(44698537379679/100000000000000 : ℝ), (5144055416963/12500000000000 : ℝ), (1768627409801/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1349808587/2500000000 : ℝ)|^4365 ≤ (44698537379679/100000000000000 : ℝ)^3341
        have hw : |(1349808587/2500000000 : ℝ)|=(1349808587/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(506822457/1000000000 : ℝ)|^4365 ≤ (5144055416963/12500000000000 : ℝ)^3341
        have hw : |(506822457/1000000000 : ℝ)|=(506822457/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-447703297/2000000000 : ℝ)|^4365 ≤ (1768627409801/12500000000000 : ℝ)^3341
        have hw : |(-447703297/2000000000 : ℝ)|=(447703297/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_s1_3 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2140495311/5000000000 : ℝ)*x 0 + (3730958489/10000000000 : ℝ)*x 1 + (122585507/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2140495311/5000000000 : ℝ)^4365 ≤ (16503817829233/50000000000000 : ℝ)^3341 := by
    have hnat : (2140495311 : ℕ)^4365*50000000000000^3341 ≤ 16503817829233^3341*5000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2140495311 5000000000 16503817829233 50000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3730958489/10000000000 : ℝ)^4365 ≤ (27579442916971/100000000000000 : ℝ)^3341 := by
    have hnat : (3730958489 : ℕ)^4365*100000000000000^3341 ≤ 27579442916971^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3730958489 10000000000 27579442916971 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (122585507/250000000 : ℝ)^4365 ≤ (19706460706969/50000000000000 : ℝ)^3341 := by
    have hnat : (122585507 : ℕ)^4365*50000000000000^3341 ≤ 19706460706969^3341*250000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      122585507 250000000 19706460706969 50000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2140495311/5000000000 : ℝ), (3730958489/10000000000 : ℝ), (122585507/250000000 : ℝ)] ![(16503817829233/50000000000000 : ℝ), (27579442916971/100000000000000 : ℝ), (19706460706969/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2140495311/5000000000 : ℝ)|^4365 ≤ (16503817829233/50000000000000 : ℝ)^3341
        have hw : |(2140495311/5000000000 : ℝ)|=(2140495311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3730958489/10000000000 : ℝ)|^4365 ≤ (27579442916971/100000000000000 : ℝ)^3341
        have hw : |(3730958489/10000000000 : ℝ)|=(3730958489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(122585507/250000000 : ℝ)|^4365 ≤ (19706460706969/50000000000000 : ℝ)^3341
        have hw : |(122585507/250000000 : ℝ)|=(122585507/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_s1_4 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-97434053/500000000 : ℝ)*x 0 + (79293087/156250000 : ℝ)*x 1 + (2804176283/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (97434053/500000000 : ℝ)^4365 ≤ (2360912065597/20000000000000 : ℝ)^3341 := by
    have hnat : (97434053 : ℕ)^4365*20000000000000^3341 ≤ 2360912065597^3341*500000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      97434053 500000000 2360912065597 20000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (79293087/156250000 : ℝ)^4365 ≤ (20610880652297/50000000000000 : ℝ)^3341 := by
    have hnat : (79293087 : ℕ)^4365*50000000000000^3341 ≤ 20610880652297^3341*156250000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79293087 156250000 20610880652297 50000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2804176283/5000000000 : ℝ)^4365 ≤ (11743419587873/25000000000000 : ℝ)^3341 := by
    have hnat : (2804176283 : ℕ)^4365*25000000000000^3341 ≤ 11743419587873^3341*5000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2804176283 5000000000 11743419587873 25000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-97434053/500000000 : ℝ), (79293087/156250000 : ℝ), (2804176283/5000000000 : ℝ)] ![(2360912065597/20000000000000 : ℝ), (20610880652297/50000000000000 : ℝ), (11743419587873/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-97434053/500000000 : ℝ)|^4365 ≤ (2360912065597/20000000000000 : ℝ)^3341
        have hw : |(-97434053/500000000 : ℝ)|=(97434053/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(79293087/156250000 : ℝ)|^4365 ≤ (20610880652297/50000000000000 : ℝ)^3341
        have hw : |(79293087/156250000 : ℝ)|=(79293087/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2804176283/5000000000 : ℝ)|^4365 ≤ (11743419587873/25000000000000 : ℝ)^3341
        have hw : |(2804176283/5000000000 : ℝ)|=(2804176283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_s1_5 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5256634523/10000000000 : ℝ)*x 0 + (-1698389181/10000000000 : ℝ)*x 1 + (701044057/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256634523/10000000000 : ℝ)^4365 ≤ (1079061273597/2500000000000 : ℝ)^3341 := by
    have hnat : (5256634523 : ℕ)^4365*2500000000000^3341 ≤ 1079061273597^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256634523 10000000000 1079061273597 2500000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1698389181/10000000000 : ℝ)^4365 ≤ (9863871899273/100000000000000 : ℝ)^3341 := by
    have hnat : (1698389181 : ℕ)^4365*100000000000000^3341 ≤ 9863871899273^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1698389181 10000000000 9863871899273 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (701044057/1250000000 : ℝ)^4365 ≤ (11743419286947/25000000000000 : ℝ)^3341 := by
    have hnat : (701044057 : ℕ)^4365*25000000000000^3341 ≤ 11743419286947^3341*1250000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      701044057 1250000000 11743419286947 25000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256634523/10000000000 : ℝ), (-1698389181/10000000000 : ℝ), (701044057/1250000000 : ℝ)] ![(1079061273597/2500000000000 : ℝ), (9863871899273/100000000000000 : ℝ), (11743419286947/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256634523/10000000000 : ℝ)|^4365 ≤ (1079061273597/2500000000000 : ℝ)^3341
        have hw : |(5256634523/10000000000 : ℝ)|=(5256634523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1698389181/10000000000 : ℝ)|^4365 ≤ (9863871899273/100000000000000 : ℝ)^3341
        have hw : |(-1698389181/10000000000 : ℝ)|=(1698389181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(701044057/1250000000 : ℝ)|^4365 ≤ (11743419286947/25000000000000 : ℝ)^3341
        have hw : |(701044057/1250000000 : ℝ)|=(701044057/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_s1_6 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1051327021/2000000000 : ℝ)*x 0 + (1402088231/2500000000 : ℝ)*x 1 + (-849193841/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051327021/2000000000 : ℝ)^4365 ≤ (21581228593697/50000000000000 : ℝ)^3341 := by
    have hnat : (1051327021 : ℕ)^4365*50000000000000^3341 ≤ 21581228593697^3341*2000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051327021 2000000000 21581228593697 50000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1402088231/2500000000 : ℝ)^4365 ≤ (23486841134501/50000000000000 : ℝ)^3341 := by
    have hnat : (1402088231 : ℕ)^4365*50000000000000^3341 ≤ 23486841134501^3341*2500000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1402088231 2500000000 23486841134501 50000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (849193841/5000000000 : ℝ)^4365 ≤ (2465965131277/25000000000000 : ℝ)^3341 := by
    have hnat : (849193841 : ℕ)^4365*25000000000000^3341 ≤ 2465965131277^3341*5000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849193841 5000000000 2465965131277 25000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1051327021/2000000000 : ℝ), (1402088231/2500000000 : ℝ), (-849193841/5000000000 : ℝ)] ![(21581228593697/50000000000000 : ℝ), (23486841134501/50000000000000 : ℝ), (2465965131277/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1051327021/2000000000 : ℝ)|^4365 ≤ (21581228593697/50000000000000 : ℝ)^3341
        have hw : |(1051327021/2000000000 : ℝ)|=(1051327021/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1402088231/2500000000 : ℝ)|^4365 ≤ (23486841134501/50000000000000 : ℝ)^3341
        have hw : |(1402088231/2500000000 : ℝ)|=(1402088231/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-849193841/5000000000 : ℝ)|^4365 ≤ (2465965131277/25000000000000 : ℝ)^3341
        have hw : |(-849193841/5000000000 : ℝ)|=(849193841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_s1_7 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2140959447/5000000000 : ℝ)*x 0 + (4889409767/10000000000 : ℝ)*x 1 + (1872604861/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2140959447/5000000000 : ℝ)^4365 ≤ (6603397372763/20000000000000 : ℝ)^3341 := by
    have hnat : (2140959447 : ℕ)^4365*20000000000000^3341 ≤ 6603397372763^3341*5000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2140959447 5000000000 6603397372763 20000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4889409767/10000000000 : ℝ)^4365 ≤ (39265855852617/100000000000000 : ℝ)^3341 := by
    have hnat : (4889409767 : ℕ)^4365*100000000000000^3341 ≤ 39265855852617^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4889409767 10000000000 39265855852617 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1872604861/5000000000 : ℝ)^4365 ≤ (346464465879/1250000000000 : ℝ)^3341 := by
    have hnat : (1872604861 : ℕ)^4365*1250000000000^3341 ≤ 346464465879^3341*5000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1872604861 5000000000 346464465879 1250000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2140959447/5000000000 : ℝ), (4889409767/10000000000 : ℝ), (1872604861/5000000000 : ℝ)] ![(6603397372763/20000000000000 : ℝ), (39265855852617/100000000000000 : ℝ), (346464465879/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2140959447/5000000000 : ℝ)|^4365 ≤ (6603397372763/20000000000000 : ℝ)^3341
        have hw : |(2140959447/5000000000 : ℝ)|=(2140959447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4889409767/10000000000 : ℝ)|^4365 ≤ (39265855852617/100000000000000 : ℝ)^3341
        have hw : |(4889409767/10000000000 : ℝ)|=(4889409767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1872604861/5000000000 : ℝ)|^4365 ≤ (346464465879/1250000000000 : ℝ)^3341
        have hw : |(1872604861/5000000000 : ℝ)|=(1872604861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1405_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157216317/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1057/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1877/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (7451/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (19009/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1057/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1877/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1057/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1877/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1057/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1877/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1057/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1877/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1057/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1877/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1057/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1877/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1877/100000 : ℝ) ^ (1091/256 : ℝ) ≤ (4385209215297/100000000000000000000 : ℝ) := by
    have hpowers : (1877/100000 : ℝ)^1091 ≤ (4385209215297/100000000000000000000 : ℝ)^256 := by
      have hnat : (1877 : ℕ)^1091*100000000000000000000^256 ≤ 4385209215297^256*100000^1091 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1877 100000 4385209215297 100000000000000000000 1091 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1877/100000 : ℝ)) (X := (4385209215297/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1091 256 (by norm_num) hpowers
    exact h
  have hpowhi : (1057/4000 : ℝ) ^ (1091/256 : ℝ) ≤ (10755744889052427/3125000000000000000 : ℝ) := by
    have hpowers : (1057/4000 : ℝ)^1091 ≤ (10755744889052427/3125000000000000000 : ℝ)^256 := by
      have hnat : (1057 : ℕ)^1091*3125000000000000000^256 ≤ 10755744889052427^256*4000^1091 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1057 4000 10755744889052427 3125000000000000000 1091 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1057/4000 : ℝ)) (X := (10755744889052427/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 1091 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000004385209215297/50000000000000000000 : ℝ) ≤ (1000000020579533/1000000000000000 : ℝ) ^ (1091/256 : ℝ) := by
    have hpowers : (50000004385209215297/50000000000000000000 : ℝ)^256 ≤ (1000000020579533/1000000000000000 : ℝ)^1091 := by
      have hnat : (50000004385209215297 : ℕ)^256*1000000000000000^1091 ≤ 1000000020579533^1091*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000004385209215297 50000000000000000000 1000000020579533 1000000000000000 256 1091 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000000020579533/1000000000000000 : ℝ)) (X := (50000004385209215297/50000000000000000000 : ℝ)) (by norm_num) 1091 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100344188221658892961/100000000000000000000 : ℝ) ≤ (2502016415313539/2500000000000000 : ℝ) ^ (1091/256 : ℝ) := by
    have hpowers : (100344188221658892961/100000000000000000000 : ℝ)^256 ≤ (2502016415313539/2500000000000000 : ℝ)^1091 := by
      have hnat : (100344188221658892961 : ℕ)^256*2500000000000000^1091 ≤ 2502016415313539^1091*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100344188221658892961 100000000000000000000 2502016415313539 2500000000000000 256 1091 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2502016415313539/2500000000000000 : ℝ)) (X := (100344188221658892961/100000000000000000000 : ℝ)) (by norm_num) 1091 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (1573255744889052427/1562500000000000000 : ℝ) ≤ (5008065558356491/5000000000000000 : ℝ) ^ (1091/256 : ℝ) := by
    have hpowers : (1573255744889052427/1562500000000000000 : ℝ)^256 ≤ (5008065558356491/5000000000000000 : ℝ)^1091 := by
      have hnat : (1573255744889052427 : ℕ)^256*5000000000000000^1091 ≤ 5008065558356491^1091*1562500000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1573255744889052427 1562500000000000000 5008065558356491 5000000000000000 256 1091 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5008065558356491/5000000000000000 : ℝ)) (X := (1573255744889052427/1562500000000000000 : ℝ)) (by norm_num) 1091 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4385209215297/100000000000000000000 : ℝ) ≤ ((61362431833017832009/61370000000000000000 : ℝ)+2*(4032727729413/1227400000000000 : ℝ)*(1877/100000 : ℝ))^(1091/256 : ℝ) := by
    rw [show (61362431833017832009/61370000000000000000 : ℝ)+2*(4032727729413/1227400000000000 : ℝ)*(1877/100000 : ℝ)=(1000000020579533/1000000000000000 : ℝ) by norm_num, show 1+2*(4385209215297/100000000000000000000 : ℝ)=(50000004385209215297/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10755744889052427/3125000000000000000 : ℝ)+(4385209215297/100000000000000000000 : ℝ) ≤ ((61362431833017832009/61370000000000000000 : ℝ)+(4032727729413/1227400000000000 : ℝ)*((1057/4000 : ℝ)+(1877/100000 : ℝ)))^(1091/256 : ℝ) := by
    rw [show (61362431833017832009/61370000000000000000 : ℝ)+(4032727729413/1227400000000000 : ℝ)*((1057/4000 : ℝ)+(1877/100000 : ℝ))=(2502016415313539/2500000000000000 : ℝ) by norm_num, show 1+(10755744889052427/3125000000000000000 : ℝ)+(4385209215297/100000000000000000000 : ℝ)=(100344188221658892961/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10755744889052427/3125000000000000000 : ℝ) ≤ ((61362431833017832009/61370000000000000000 : ℝ)+2*(4032727729413/1227400000000000 : ℝ)*(1057/4000 : ℝ))^(1091/256 : ℝ) := by
    rw [show (61362431833017832009/61370000000000000000 : ℝ)+2*(4032727729413/1227400000000000 : ℝ)*(1057/4000 : ℝ)=(5008065558356491/5000000000000000 : ℝ) by norm_num, show 1+2*(10755744889052427/3125000000000000000 : ℝ)=(1573255744889052427/1562500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (61362431833017832009/61370000000000000000 : ℝ)*(X 1 0+X 2 0)+(4032727729413/1227400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1091/256 : ℝ)) (lo := (1877/100000 : ℝ)) (hi := (1057/4000 : ℝ)) (c := (61362431833017832009/61370000000000000000 : ℝ)) (alpha := (4032727729413/1227400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (61362431833017832009/61370000000000000000 : ℝ)*(X 0 1+X 2 1)+(4032727729413/1227400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1091/256 : ℝ)) (lo := (1877/100000 : ℝ)) (hi := (1057/4000 : ℝ)) (c := (61362431833017832009/61370000000000000000 : ℝ)) (alpha := (4032727729413/1227400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (61362431833017832009/61370000000000000000 : ℝ)*(X 0 2+X 1 2)+(4032727729413/1227400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1091/256 : ℝ)) (lo := (1877/100000 : ℝ)) (hi := (1057/4000 : ℝ)) (c := (61362431833017832009/61370000000000000000 : ℝ)) (alpha := (4032727729413/1227400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-974124447/5000000000 : ℝ)*X 0 0+(2807499403/5000000000 : ℝ)*X 0 1+(5068224263/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((337452107/625000000 : ℝ)*X 1 0+(-447703343/2000000000 : ℝ)*X 1 1+(2534112519/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1349808587/2500000000 : ℝ)*X 2 0+(506822457/1000000000 : ℝ)*X 2 1+(-447703297/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2140495311/5000000000 : ℝ)*X 0 0+(3730958489/10000000000 : ℝ)*X 0 1+(122585507/250000000 : ℝ)*X 0 2+(2140495311/5000000000 : ℝ)*X 1 0+(3730958489/10000000000 : ℝ)*X 1 1+(122585507/250000000 : ℝ)*X 1 2+(2140495311/5000000000 : ℝ)*X 2 0+(3730958489/10000000000 : ℝ)*X 2 1+(122585507/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-97434053/500000000 : ℝ)*X 0 0+(79293087/156250000 : ℝ)*X 0 1+(2804176283/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5256634523/10000000000 : ℝ)*X 1 0+(-1698389181/10000000000 : ℝ)*X 1 1+(701044057/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1051327021/2000000000 : ℝ)*X 2 0+(1402088231/2500000000 : ℝ)*X 2 1+(-849193841/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2140959447/5000000000 : ℝ)*X 0 0+(4889409767/10000000000 : ℝ)*X 0 1+(1872604861/5000000000 : ℝ)*X 0 2+(2140959447/5000000000 : ℝ)*X 1 0+(4889409767/10000000000 : ℝ)*X 1 1+(1872604861/5000000000 : ℝ)*X 1 2+(2140959447/5000000000 : ℝ)*X 2 0+(4889409767/10000000000 : ℝ)*X 2 1+(1872604861/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2857115131927403807399853117/1534250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (63526599/20000000000000 : ℝ)*(base19) + (127802451/25000000000000 : ℝ)*(base23) + (1013091/6250000000000 : ℝ)*(upper4) + (89935813/100000000000000 : ℝ)*(upper5) + (670456780852329/50000000000000 : ℝ)*(major0) + (670456780852329/50000000000000 : ℝ)*(major1) + (670456780852329/50000000000000 : ℝ)*(major2) + (1828911309024569/100000000000000 : ℝ)*(sp0) + (914458257914457/50000000000000 : ℝ)*(sp1) + (1828916631300227/100000000000000 : ℝ)*(sp2) + (213227039560093/25000000000000 : ℝ)*(sp3) + (2916742731/50000000000000 : ℝ)*(sp4) + (309048121/100000000000000 : ℝ)*(sp5) + (1760584821/100000000000000 : ℝ)*(sp7) + (852909918825193/100000000000000 : ℝ)*(f.failure) + (1828917142510031/100000000000000 : ℝ)*(f.sum) + (40866885320757/30685000000000000000000000000 : ℝ)*base65 + (10217616247719748961/3068500000000000000000000000000000 : ℝ)*base67 + (8668330527276251039/3068500000000000000000000000000000 : ℝ)*base70 + (5351209177885748961/3068500000000000000000000000000000 : ℝ)*base71 + (110346462813137/30685000000000000000000000000 : ℝ)*base73 + (13758198268047248961/3068500000000000000000000000000000 : ℝ)*base75 + (1335871507153248961/3068500000000000000000000000000000 : ℝ)*base77 + (417302622940251039/3068500000000000000000000000000000 : ℝ)*base80 + (15137842620691/15342500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (10274181/10000000000000000000000 : ℝ)*base89 + (10274181/10000000000000000000000 : ℝ)*base91 + (10274181/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11355886751680422995540019189/1534250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12528787/5000000000000 : ℝ)*(base1) + (1798863807/100000000000000 : ℝ)*(base19) + (212152013/10000000000000 : ℝ)*(base23) + (38707433/25000000000000 : ℝ)*(upper3) + (299622713/100000000000000 : ℝ)*(upper5) + (687014051611007/50000000000000 : ℝ)*(major0) + (687014051611007/50000000000000 : ℝ)*(major1) + (687014051611007/50000000000000 : ℝ)*(major2) + (4388050047/50000000000000 : ℝ)*(sp1) + (3255339961/25000000000000 : ℝ)*(sp2) + (468520811949447/25000000000000 : ℝ)*(sp4) + (1874072422258147/100000000000000 : ℝ)*(sp5) + (937033927171037/50000000000000 : ℝ)*(sp6) + (873972711926629/100000000000000 : ℝ)*(sp7) + (27311655078199/3125000000000 : ℝ)*(f.failure) + (58565093663189/3125000000000 : ℝ)*(f.sum) + (56021026067619/30685000000000000000000000000 : ℝ)*base66 + (4922323442036373063/3068500000000000000000000000000000 : ℝ)*base67 + (28712321644115126937/3068500000000000000000000000000000 : ℝ)*base70 + (7381014817861626937/3068500000000000000000000000000000 : ℝ)*base72 + (357335130081/30685000000000000000000000000 : ℝ)*base73 + (4224122400941126937/3068500000000000000000000000000000 : ℝ)*base76 + (18765922076462126937/3068500000000000000000000000000000 : ℝ)*base78 + (7991953042804373063/3068500000000000000000000000000000 : ℝ)*base79 + (178859011987159/30685000000000000000000000000 : ℝ)*base82 + (23083/312500000000000000000 : ℝ)*base89 + (23083/312500000000000000000 : ℝ)*base91 + (23083/312500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1405_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157216317/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1057/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1877/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (7451/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (19009/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1405_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1405_s2_0 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-15493829/78125000 : ℝ)*x 0 + (5463702491/10000000000 : ℝ)*x 1 + (2598523303/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (15493829/78125000 : ℝ)^4365 ≤ (3019643840639/25000000000000 : ℝ)^3341 := by
    have hnat : (15493829 : ℕ)^4365*25000000000000^3341 ≤ 3019643840639^3341*78125000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15493829 78125000 3019643840639 25000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5463702491/10000000000 : ℝ)^4365 ≤ (5674637599921/12500000000000 : ℝ)^3341 := by
    have hnat : (5463702491 : ℕ)^4365*12500000000000^3341 ≤ 5674637599921^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5463702491 10000000000 5674637599921 12500000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2598523303/5000000000 : ℝ)^4365 ≤ (10631080957093/25000000000000 : ℝ)^3341 := by
    have hnat : (2598523303 : ℕ)^4365*25000000000000^3341 ≤ 10631080957093^3341*5000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598523303 5000000000 10631080957093 25000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-15493829/78125000 : ℝ), (5463702491/10000000000 : ℝ), (2598523303/5000000000 : ℝ)] ![(3019643840639/25000000000000 : ℝ), (5674637599921/12500000000000 : ℝ), (10631080957093/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-15493829/78125000 : ℝ)|^4365 ≤ (3019643840639/25000000000000 : ℝ)^3341
        have hw : |(-15493829/78125000 : ℝ)|=(15493829/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5463702491/10000000000 : ℝ)|^4365 ≤ (5674637599921/12500000000000 : ℝ)^3341
        have hw : |(5463702491/10000000000 : ℝ)|=(5463702491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2598523303/5000000000 : ℝ)|^4365 ≤ (10631080957093/25000000000000 : ℝ)^3341
        have hw : |(2598523303/5000000000 : ℝ)|=(2598523303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_s2_1 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5361684681/10000000000 : ℝ)*x 0 + (-424110613/2000000000 : ℝ)*x 1 + (5197046593/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5361684681/10000000000 : ℝ)^4365 ≤ (44292831650511/100000000000000 : ℝ)^3341 := by
    have hnat : (5361684681 : ℕ)^4365*100000000000000^3341 ≤ 44292831650511^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5361684681 10000000000 44292831650511 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (424110613/2000000000 : ℝ)^4365 ≤ (13182844643991/100000000000000 : ℝ)^3341 := by
    have hnat : (424110613 : ℕ)^4365*100000000000000^3341 ≤ 13182844643991^3341*2000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424110613 2000000000 13182844643991 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5197046593/10000000000 : ℝ)^4365 ≤ (42524323689399/100000000000000 : ℝ)^3341 := by
    have hnat : (5197046593 : ℕ)^4365*100000000000000^3341 ≤ 42524323689399^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5197046593 10000000000 42524323689399 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5361684681/10000000000 : ℝ), (-424110613/2000000000 : ℝ), (5197046593/10000000000 : ℝ)] ![(44292831650511/100000000000000 : ℝ), (13182844643991/100000000000000 : ℝ), (42524323689399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5361684681/10000000000 : ℝ)|^4365 ≤ (44292831650511/100000000000000 : ℝ)^3341
        have hw : |(5361684681/10000000000 : ℝ)|=(5361684681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-424110613/2000000000 : ℝ)|^4365 ≤ (13182844643991/100000000000000 : ℝ)^3341
        have hw : |(-424110613/2000000000 : ℝ)|=(424110613/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5197046593/10000000000 : ℝ)|^4365 ≤ (42524323689399/100000000000000 : ℝ)^3341
        have hw : |(5197046593/10000000000 : ℝ)|=(5197046593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_s2_2 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1072336893/2000000000 : ℝ)*x 0 + (5197046837/10000000000 : ℝ)*x 1 + (-212055303/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072336893/2000000000 : ℝ)^4365 ≤ (8858565863847/20000000000000 : ℝ)^3341 := by
    have hnat : (1072336893 : ℕ)^4365*20000000000000^3341 ≤ 8858565863847^3341*2000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072336893 2000000000 8858565863847 20000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5197046837/10000000000 : ℝ)^4365 ≤ (1328885196807/3125000000000 : ℝ)^3341 := by
    have hnat : (5197046837 : ℕ)^4365*3125000000000^3341 ≤ 1328885196807^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5197046837 10000000000 1328885196807 3125000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (212055303/1000000000 : ℝ)^4365 ≤ (6591422179859/50000000000000 : ℝ)^3341 := by
    have hnat : (212055303 : ℕ)^4365*50000000000000^3341 ≤ 6591422179859^3341*1000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212055303 1000000000 6591422179859 50000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072336893/2000000000 : ℝ), (5197046837/10000000000 : ℝ), (-212055303/1000000000 : ℝ)] ![(8858565863847/20000000000000 : ℝ), (1328885196807/3125000000000 : ℝ), (6591422179859/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072336893/2000000000 : ℝ)|^4365 ≤ (8858565863847/20000000000000 : ℝ)^3341
        have hw : |(1072336893/2000000000 : ℝ)|=(1072336893/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5197046837/10000000000 : ℝ)|^4365 ≤ (1328885196807/3125000000000 : ℝ)^3341
        have hw : |(5197046837/10000000000 : ℝ)|=(5197046837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-212055303/1000000000 : ℝ)|^4365 ≤ (6591422179859/50000000000000 : ℝ)^3341
        have hw : |(-212055303/1000000000 : ℝ)|=(212055303/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_s2_3 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (430560903/1000000000 : ℝ)*x 0 + (4028319357/10000000000 : ℝ)*x 1 + (4600116641/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (430560903/1000000000 : ℝ)^4365 ≤ (831396150869/2500000000000 : ℝ)^3341 := by
    have hnat : (430560903 : ℕ)^4365*2500000000000^3341 ≤ 831396150869^3341*1000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430560903 1000000000 831396150869 2500000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4028319357/10000000000 : ℝ)^4365 ≤ (30485710185329/100000000000000 : ℝ)^3341 := by
    have hnat : (4028319357 : ℕ)^4365*100000000000000^3341 ≤ 30485710185329^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4028319357 10000000000 30485710185329 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4600116641/10000000000 : ℝ)^4365 ≤ (36258443761899/100000000000000 : ℝ)^3341 := by
    have hnat : (4600116641 : ℕ)^4365*100000000000000^3341 ≤ 36258443761899^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4600116641 10000000000 36258443761899 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(430560903/1000000000 : ℝ), (4028319357/10000000000 : ℝ), (4600116641/10000000000 : ℝ)] ![(831396150869/2500000000000 : ℝ), (30485710185329/100000000000000 : ℝ), (36258443761899/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(430560903/1000000000 : ℝ)|^4365 ≤ (831396150869/2500000000000 : ℝ)^3341
        have hw : |(430560903/1000000000 : ℝ)|=(430560903/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4028319357/10000000000 : ℝ)|^4365 ≤ (30485710185329/100000000000000 : ℝ)^3341
        have hw : |(4028319357/10000000000 : ℝ)|=(4028319357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4600116641/10000000000 : ℝ)|^4365 ≤ (36258443761899/100000000000000 : ℝ)^3341
        have hw : |(4600116641/10000000000 : ℝ)|=(4600116641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_s2_4 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-247907507/1250000000 : ℝ)*x 0 + (1299652507/2500000000 : ℝ)*x 1 + (170691441/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (247907507/1250000000 : ℝ)^4365 ≤ (12078972773439/100000000000000 : ℝ)^3341 := by
    have hnat : (247907507 : ℕ)^4365*100000000000000^3341 ≤ 12078972773439^3341*1250000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      247907507 1250000000 12078972773439 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1299652507/2500000000 : ℝ)^4365 ≤ (42541037998417/100000000000000 : ℝ)^3341 := by
    have hnat : (1299652507 : ℕ)^4365*100000000000000^3341 ≤ 42541037998417^3341*2500000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299652507 2500000000 42541037998417 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (170691441/312500000 : ℝ)^4365 ≤ (22689994606289/50000000000000 : ℝ)^3341 := by
    have hnat : (170691441 : ℕ)^4365*50000000000000^3341 ≤ 22689994606289^3341*312500000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170691441 312500000 22689994606289 50000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-247907507/1250000000 : ℝ), (1299652507/2500000000 : ℝ), (170691441/312500000 : ℝ)] ![(12078972773439/100000000000000 : ℝ), (42541037998417/100000000000000 : ℝ), (22689994606289/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-247907507/1250000000 : ℝ)|^4365 ≤ (12078972773439/100000000000000 : ℝ)^3341
        have hw : |(-247907507/1250000000 : ℝ)|=(247907507/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1299652507/2500000000 : ℝ)|^4365 ≤ (42541037998417/100000000000000 : ℝ)^3341
        have hw : |(1299652507/2500000000 : ℝ)|=(1299652507/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(170691441/312500000 : ℝ)|^4365 ≤ (22689994606289/50000000000000 : ℝ)^3341
        have hw : |(170691441/312500000 : ℝ)|=(170691441/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_s2_5 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5292505017/10000000000 : ℝ)*x 0 + (-463868539/2500000000 : ℝ)*x 1 + (218485033/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5292505017/10000000000 : ℝ)^4365 ≤ (8709532029051/20000000000000 : ℝ)^3341 := by
    have hnat : (5292505017 : ℕ)^4365*20000000000000^3341 ≤ 8709532029051^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5292505017 10000000000 8709532029051 20000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (463868539/2500000000 : ℝ)^4365 ≤ (2214470748531/20000000000000 : ℝ)^3341 := by
    have hnat : (463868539 : ℕ)^4365*20000000000000^3341 ≤ 2214470748531^3341*2500000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      463868539 2500000000 2214470748531 20000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (218485033/400000000 : ℝ)^4365 ≤ (11344996524333/25000000000000 : ℝ)^3341 := by
    have hnat : (218485033 : ℕ)^4365*25000000000000^3341 ≤ 11344996524333^3341*400000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218485033 400000000 11344996524333 25000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5292505017/10000000000 : ℝ), (-463868539/2500000000 : ℝ), (218485033/400000000 : ℝ)] ![(8709532029051/20000000000000 : ℝ), (2214470748531/20000000000000 : ℝ), (11344996524333/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5292505017/10000000000 : ℝ)|^4365 ≤ (8709532029051/20000000000000 : ℝ)^3341
        have hw : |(5292505017/10000000000 : ℝ)|=(5292505017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-463868539/2500000000 : ℝ)|^4365 ≤ (2214470748531/20000000000000 : ℝ)^3341
        have hw : |(-463868539/2500000000 : ℝ)|=(463868539/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(218485033/400000000 : ℝ)|^4365 ≤ (11344996524333/25000000000000 : ℝ)^3341
        have hw : |(218485033/400000000 : ℝ)|=(218485033/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_s2_6 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2646253219/5000000000 : ℝ)*x 0 + (27310629/50000000 : ℝ)*x 1 + (-1855472231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646253219/5000000000 : ℝ)^4365 ≤ (21773837710553/50000000000000 : ℝ)^3341 := by
    have hnat : (2646253219 : ℕ)^4365*50000000000000^3341 ≤ 21773837710553^3341*5000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646253219 5000000000 21773837710553 50000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (27310629/50000000 : ℝ)^4365 ≤ (45379985825969/100000000000000 : ℝ)^3341 := by
    have hnat : (27310629 : ℕ)^4365*100000000000000^3341 ≤ 45379985825969^3341*50000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27310629 50000000 45379985825969 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1855472231/10000000000 : ℝ)^4365 ≤ (1384042341829/12500000000000 : ℝ)^3341 := by
    have hnat : (1855472231 : ℕ)^4365*12500000000000^3341 ≤ 1384042341829^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1855472231 10000000000 1384042341829 12500000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646253219/5000000000 : ℝ), (27310629/50000000 : ℝ), (-1855472231/10000000000 : ℝ)] ![(21773837710553/50000000000000 : ℝ), (45379985825969/100000000000000 : ℝ), (1384042341829/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646253219/5000000000 : ℝ)|^4365 ≤ (21773837710553/50000000000000 : ℝ)^3341
        have hw : |(2646253219/5000000000 : ℝ)|=(2646253219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(27310629/50000000 : ℝ)|^4365 ≤ (45379985825969/100000000000000 : ℝ)^3341
        have hw : |(27310629/50000000 : ℝ)|=(27310629/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1855472231/10000000000 : ℝ)|^4365 ≤ (1384042341829/12500000000000 : ℝ)^3341
        have hw : |(-1855472231/10000000000 : ℝ)|=(1855472231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_s2_7 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4305717363/10000000000 : ℝ)*x 0 + (1149191159/2500000000 : ℝ)*x 1 + (4031699149/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4305717363/10000000000 : ℝ)^4365 ≤ (16628469622419/50000000000000 : ℝ)^3341 := by
    have hnat : (4305717363 : ℕ)^4365*50000000000000^3341 ≤ 16628469622419^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4305717363 10000000000 16628469622419 50000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1149191159/2500000000 : ℝ)^4365 ≤ (18111964525559/50000000000000 : ℝ)^3341 := by
    have hnat : (1149191159 : ℕ)^4365*50000000000000^3341 ≤ 18111964525559^3341*2500000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1149191159 2500000000 18111964525559 50000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4031699149/10000000000 : ℝ)^4365 ≤ (30519131689729/100000000000000 : ℝ)^3341 := by
    have hnat : (4031699149 : ℕ)^4365*100000000000000^3341 ≤ 30519131689729^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4031699149 10000000000 30519131689729 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4305717363/10000000000 : ℝ), (1149191159/2500000000 : ℝ), (4031699149/10000000000 : ℝ)] ![(16628469622419/50000000000000 : ℝ), (18111964525559/50000000000000 : ℝ), (30519131689729/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4305717363/10000000000 : ℝ)|^4365 ≤ (16628469622419/50000000000000 : ℝ)^3341
        have hw : |(4305717363/10000000000 : ℝ)|=(4305717363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1149191159/2500000000 : ℝ)|^4365 ≤ (18111964525559/50000000000000 : ℝ)^3341
        have hw : |(1149191159/2500000000 : ℝ)|=(1149191159/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4031699149/10000000000 : ℝ)|^4365 ≤ (30519131689729/100000000000000 : ℝ)^3341
        have hw : |(4031699149/10000000000 : ℝ)|=(4031699149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1405_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157216317/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19009/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7451/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2559/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3969/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (19009/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (7451/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (19009/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (7451/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (19009/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (7451/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (19009/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (7451/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (19009/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (7451/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (19009/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (7451/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (7451/100000 : ℝ) ^ (1091/256 : ℝ) ≤ (1562052617228997/100000000000000000000 : ℝ) := by
    have hpowers : (7451/100000 : ℝ)^1091 ≤ (1562052617228997/100000000000000000000 : ℝ)^256 := by
      have hnat : (7451 : ℕ)^1091*100000000000000000000^256 ≤ 1562052617228997^256*100000^1091 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7451 100000 1562052617228997 100000000000000000000 1091 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7451/100000 : ℝ)) (X := (1562052617228997/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1091 256 (by norm_num) hpowers
    exact h
  have hpowhi : (19009/100000 : ℝ) ^ (1091/256 : ℝ) ≤ (528454039148221/625000000000000000 : ℝ) := by
    have hpowers : (19009/100000 : ℝ)^1091 ≤ (528454039148221/625000000000000000 : ℝ)^256 := by
      have hnat : (19009 : ℕ)^1091*625000000000000000^256 ≤ 528454039148221^256*100000^1091 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19009 100000 528454039148221 625000000000000000 1091 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19009/100000 : ℝ)) (X := (528454039148221/625000000000000000 : ℝ)) (by norm_num) (by norm_num) 1091 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001562052617228997/50000000000000000000 : ℝ) ≤ (10000073305350941/10000000000000000 : ℝ) ^ (1091/256 : ℝ) := by
    have hpowers : (50001562052617228997/50000000000000000000 : ℝ)^256 ≤ (10000073305350941/10000000000000000 : ℝ)^1091 := by
      have hnat : (50001562052617228997 : ℕ)^256*10000000000000000^1091 ≤ 10000073305350941^1091*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001562052617228997 50000000000000000000 10000073305350941 10000000000000000 256 1091 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000073305350941/10000000000000000 : ℝ)) (X := (50001562052617228997/50000000000000000000 : ℝ)) (by norm_num) 1091 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100086114698880944357/100000000000000000000 : ℝ) ≤ (5001009995497211/5000000000000000 : ℝ) ^ (1091/256 : ℝ) := by
    have hpowers : (100086114698880944357/100000000000000000000 : ℝ)^256 ≤ (5001009995497211/5000000000000000 : ℝ)^1091 := by
      have hnat : (100086114698880944357 : ℕ)^256*5000000000000000^1091 ≤ 5001009995497211^1091*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100086114698880944357 100000000000000000000 5001009995497211 5000000000000000 256 1091 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001009995497211/5000000000000000 : ℝ)) (X := (100086114698880944357/100000000000000000000 : ℝ)) (by norm_num) 1091 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (313028454039148221/312500000000000000 : ℝ) ≤ (10003966676637903/10000000000000000 : ℝ) ^ (1091/256 : ℝ) := by
    have hpowers : (313028454039148221/312500000000000000 : ℝ)^256 ≤ (10003966676637903/10000000000000000 : ℝ)^1091 := by
      have hnat : (313028454039148221 : ℕ)^256*10000000000000000^1091 ≤ 10003966676637903^1091*312500000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        313028454039148221 312500000000000000 10003966676637903 10000000000000000 256 1091 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003966676637903/10000000000000000 : ℝ)) (X := (313028454039148221/312500000000000000 : ℝ)) (by norm_num) 1091 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1562052617228997/100000000000000000000 : ℝ) ≤ ((14443979719223377777/14447500000000000000 : ℝ)+2*(1946685643481/1155800000000000 : ℝ)*(7451/100000 : ℝ))^(1091/256 : ℝ) := by
    rw [show (14443979719223377777/14447500000000000000 : ℝ)+2*(1946685643481/1155800000000000 : ℝ)*(7451/100000 : ℝ)=(10000073305350941/10000000000000000 : ℝ) by norm_num, show 1+2*(1562052617228997/100000000000000000000 : ℝ)=(50001562052617228997/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(528454039148221/625000000000000000 : ℝ)+(1562052617228997/100000000000000000000 : ℝ) ≤ ((14443979719223377777/14447500000000000000 : ℝ)+(1946685643481/1155800000000000 : ℝ)*((19009/100000 : ℝ)+(7451/100000 : ℝ)))^(1091/256 : ℝ) := by
    rw [show (14443979719223377777/14447500000000000000 : ℝ)+(1946685643481/1155800000000000 : ℝ)*((19009/100000 : ℝ)+(7451/100000 : ℝ))=(5001009995497211/5000000000000000 : ℝ) by norm_num, show 1+(528454039148221/625000000000000000 : ℝ)+(1562052617228997/100000000000000000000 : ℝ)=(100086114698880944357/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(528454039148221/625000000000000000 : ℝ) ≤ ((14443979719223377777/14447500000000000000 : ℝ)+2*(1946685643481/1155800000000000 : ℝ)*(19009/100000 : ℝ))^(1091/256 : ℝ) := by
    rw [show (14443979719223377777/14447500000000000000 : ℝ)+2*(1946685643481/1155800000000000 : ℝ)*(19009/100000 : ℝ)=(10003966676637903/10000000000000000 : ℝ) by norm_num, show 1+2*(528454039148221/625000000000000000 : ℝ)=(313028454039148221/312500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14443979719223377777/14447500000000000000 : ℝ)*(X 1 0+X 2 0)+(1946685643481/1155800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1091/256 : ℝ)) (lo := (7451/100000 : ℝ)) (hi := (19009/100000 : ℝ)) (c := (14443979719223377777/14447500000000000000 : ℝ)) (alpha := (1946685643481/1155800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14443979719223377777/14447500000000000000 : ℝ)*(X 0 1+X 2 1)+(1946685643481/1155800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1091/256 : ℝ)) (lo := (7451/100000 : ℝ)) (hi := (19009/100000 : ℝ)) (c := (14443979719223377777/14447500000000000000 : ℝ)) (alpha := (1946685643481/1155800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14443979719223377777/14447500000000000000 : ℝ)*(X 0 2+X 1 2)+(1946685643481/1155800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1091/256 : ℝ)) (lo := (7451/100000 : ℝ)) (hi := (19009/100000 : ℝ)) (c := (14443979719223377777/14447500000000000000 : ℝ)) (alpha := (1946685643481/1155800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-15493829/78125000 : ℝ)*X 0 0+(5463702491/10000000000 : ℝ)*X 0 1+(2598523303/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5361684681/10000000000 : ℝ)*X 1 0+(-424110613/2000000000 : ℝ)*X 1 1+(5197046593/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1072336893/2000000000 : ℝ)*X 2 0+(5197046837/10000000000 : ℝ)*X 2 1+(-212055303/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((430560903/1000000000 : ℝ)*X 0 0+(4028319357/10000000000 : ℝ)*X 0 1+(4600116641/10000000000 : ℝ)*X 0 2+(430560903/1000000000 : ℝ)*X 1 0+(4028319357/10000000000 : ℝ)*X 1 1+(4600116641/10000000000 : ℝ)*X 1 2+(430560903/1000000000 : ℝ)*X 2 0+(4028319357/10000000000 : ℝ)*X 2 1+(4600116641/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-247907507/1250000000 : ℝ)*X 0 0+(1299652507/2500000000 : ℝ)*X 0 1+(170691441/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5292505017/10000000000 : ℝ)*X 1 0+(-463868539/2500000000 : ℝ)*X 1 1+(218485033/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2646253219/5000000000 : ℝ)*X 2 0+(27310629/50000000 : ℝ)*X 2 1+(-1855472231/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4305717363/10000000000 : ℝ)*X 0 0+(1149191159/2500000000 : ℝ)*X 0 1+(4031699149/10000000000 : ℝ)*X 0 2+(4305717363/10000000000 : ℝ)*X 1 0+(1149191159/2500000000 : ℝ)*X 1 1+(4031699149/10000000000 : ℝ)*X 1 2+(4305717363/10000000000 : ℝ)*X 2 0+(1149191159/2500000000 : ℝ)*X 2 1+(4031699149/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (245247053974875000758971677/90296875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3331747/1250000000000 : ℝ)*(base19) + (170567/2500000000000 : ℝ)*(base23) + (29124373/50000000000000 : ℝ)*(lower2) + (47943993/50000000000000 : ℝ)*(upper3) + (210357/2500000000000 : ℝ)*(upper5) + (687378677864817/25000000000000 : ℝ)*(major0) + (687378677864817/25000000000000 : ℝ)*(major1) + (687378677864817/25000000000000 : ℝ)*(major2) + (3750154673333809/100000000000000 : ℝ)*(sp0) + (3750155434961627/100000000000000 : ℝ)*(sp1) + (3750155694678707/100000000000000 : ℝ)*(sp2) + (874436090883303/50000000000000 : ℝ)*(sp3) + (514083789/50000000000000 : ℝ)*(sp4) + (5660613/390625000000 : ℝ)*(sp7) + (349774726176707/20000000000000 : ℝ)*(f.failure) + (1875077850750693/50000000000000 : ℝ)*(f.sum) + (25370234255547/14447500000000000000000000000 : ℝ)*base65 + (439792314565996809/361187500000000000000000000000000 : ℝ)*base67 + (1436303240505565691/361187500000000000000000000000000 : ℝ)*base70 + (598971405606628191/361187500000000000000000000000000 : ℝ)*base72 + (44898427509429/28895000000000000000000000000 : ℝ)*base73 + (5269220591603003191/361187500000000000000000000000000 : ℝ)*base76 + (302599279873628191/361187500000000000000000000000000 : ℝ)*base78 + (2082202783454253191/361187500000000000000000000000000 : ℝ)*base80 + (76203467698647/14447500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (5728119/2000000000000000000000 : ℝ)*base89 + (5728119/2000000000000000000000 : ℝ)*base91 + (5728119/2000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (557158250292761118547365411/90296875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (708507549/100000000000000 : ℝ)*(base19) + (1414253447/50000000000000 : ℝ)*(base23) + (184162609/100000000000000 : ℝ)*(upper3) + (150212959/50000000000000 : ℝ)*(lower4) + (12165809/25000000000000 : ℝ)*(upper5) + (347784017167319/12500000000000 : ℝ)*(major0) + (347784017167319/12500000000000 : ℝ)*(major1) + (347784017167319/12500000000000 : ℝ)*(major2) + (53639531/5000000000000 : ℝ)*(sp1) + (41886239609/100000000000000 : ℝ)*(sp2) + (1897417271830057/50000000000000 : ℝ)*(sp4) + (1897416381180973/50000000000000 : ℝ)*(sp5) + (948697457228403/25000000000000 : ℝ)*(sp6) + (1769709525340523/100000000000000 : ℝ)*(sp7) + (1769709525340523/100000000000000 : ℝ)*(f.failure) + (1897417271830057/50000000000000 : ℝ)*(f.sum) + (132420045676419/28895000000000000000000000000 : ℝ)*base66 + (1293295311155132363/180593750000000000000000000000000 : ℝ)*base67 + (1575754071979351113/180593750000000000000000000000000 : ℝ)*base69 + (244985696496398887/180593750000000000000000000000000 : ℝ)*base72 + (19286210902321/7223750000000000000000000000 : ℝ)*base74 + (2084140586341288613/180593750000000000000000000000000 : ℝ)*base75 + (161452648676069863/180593750000000000000000000000000 : ℝ)*base77 + (41280427027336387/180593750000000000000000000000000 : ℝ)*base80 + (78890521540319/28895000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (3086209/10000000000000000000000 : ℝ)*base90 + (3086209/10000000000000000000000 : ℝ)*base92 + (3086209/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1405_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157216317/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19009/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7451/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2559/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3969/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1405_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1405_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157216317/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2559/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3969/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1405_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1405_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1405_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157216317/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2559/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3969/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1405_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
