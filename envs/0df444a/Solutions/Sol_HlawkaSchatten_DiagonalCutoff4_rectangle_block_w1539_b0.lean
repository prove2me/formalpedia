-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1539_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:06:52.968001+00:00
-- url     : https://prove2.me/submissions/38d13510-5a25-4ec3-b6f4-8861b3af961e

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
theorem support_rectangle_w1539_s0_0 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-828784219/5000000000 : ℝ)*x 0 + (235693627/400000000 : ℝ)*x 1 + (608337223/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (828784219/5000000000 : ℝ)^4575 ≤ (77122464181/781250000000 : ℝ)^3551 := by
    have hnat : (828784219 : ℕ)^4575*781250000000^3551 ≤ 77122464181^3551*5000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      828784219 5000000000 77122464181 781250000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (235693627/400000000 : ℝ)^4575 ≤ (1580869052897/3125000000000 : ℝ)^3551 := by
    have hnat : (235693627 : ℕ)^4575*3125000000000^3551 ≤ 1580869052897^3551*400000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      235693627 400000000 1580869052897 3125000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (608337223/1250000000 : ℝ)^4575 ≤ (39540514877787/100000000000000 : ℝ)^3551 := by
    have hnat : (608337223 : ℕ)^4575*100000000000000^3551 ≤ 39540514877787^3551*1250000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      608337223 1250000000 39540514877787 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-828784219/5000000000 : ℝ), (235693627/400000000 : ℝ), (608337223/1250000000 : ℝ)] ![(77122464181/781250000000 : ℝ), (1580869052897/3125000000000 : ℝ), (39540514877787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-828784219/5000000000 : ℝ)|^4575 ≤ (77122464181/781250000000 : ℝ)^3551
        have hw : |(-828784219/5000000000 : ℝ)|=(828784219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(235693627/400000000 : ℝ)|^4575 ≤ (1580869052897/3125000000000 : ℝ)^3551
        have hw : |(235693627/400000000 : ℝ)|=(235693627/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(608337223/1250000000 : ℝ)|^4575 ≤ (39540514877787/100000000000000 : ℝ)^3551
        have hw : |(608337223/1250000000 : ℝ)|=(608337223/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1539_s0_1 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5472129389/10000000000 : ℝ)*x 0 + (-89219787/400000000 : ℝ)*x 1 + (4866697841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5472129389/10000000000 : ℝ)^4575 ≤ (22994218235373/50000000000000 : ℝ)^3551 := by
    have hnat : (5472129389 : ℕ)^4575*50000000000000^3551 ≤ 22994218235373^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5472129389 10000000000 22994218235373 50000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (89219787/400000000 : ℝ)^4575 ≤ (7235524020231/50000000000000 : ℝ)^3551 := by
    have hnat : (89219787 : ℕ)^4575*50000000000000^3551 ≤ 7235524020231^3551*400000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89219787 400000000 7235524020231 50000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4866697841/10000000000 : ℝ)^4575 ≤ (19770257737221/50000000000000 : ℝ)^3551 := by
    have hnat : (4866697841 : ℕ)^4575*50000000000000^3551 ≤ 19770257737221^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4866697841 10000000000 19770257737221 50000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5472129389/10000000000 : ℝ), (-89219787/400000000 : ℝ), (4866697841/10000000000 : ℝ)] ![(22994218235373/50000000000000 : ℝ), (7235524020231/50000000000000 : ℝ), (19770257737221/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5472129389/10000000000 : ℝ)|^4575 ≤ (22994218235373/50000000000000 : ℝ)^3551
        have hw : |(5472129389/10000000000 : ℝ)|=(5472129389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-89219787/400000000 : ℝ)|^4575 ≤ (7235524020231/50000000000000 : ℝ)^3551
        have hw : |(-89219787/400000000 : ℝ)|=(89219787/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4866697841/10000000000 : ℝ)|^4575 ≤ (19770257737221/50000000000000 : ℝ)^3551
        have hw : |(4866697841/10000000000 : ℝ)|=(4866697841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1539_s0_2 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1368032333/2500000000 : ℝ)*x 0 + (973339563/2000000000 : ℝ)*x 1 + (-1115247391/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1368032333/2500000000 : ℝ)^4575 ≤ (11497108963393/25000000000000 : ℝ)^3551 := by
    have hnat : (1368032333 : ℕ)^4575*25000000000000^3551 ≤ 11497108963393^3551*2500000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1368032333 2500000000 11497108963393 25000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (973339563/2000000000 : ℝ)^4575 ≤ (9885128800571/25000000000000 : ℝ)^3551 := by
    have hnat : (973339563 : ℕ)^4575*25000000000000^3551 ≤ 9885128800571^3551*2000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      973339563 2000000000 9885128800571 25000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1115247391/5000000000 : ℝ)^4575 ≤ (3617762233711/25000000000000 : ℝ)^3551 := by
    have hnat : (1115247391 : ℕ)^4575*25000000000000^3551 ≤ 3617762233711^3551*5000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1115247391 5000000000 3617762233711 25000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1368032333/2500000000 : ℝ), (973339563/2000000000 : ℝ), (-1115247391/5000000000 : ℝ)] ![(11497108963393/25000000000000 : ℝ), (9885128800571/25000000000000 : ℝ), (3617762233711/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1368032333/2500000000 : ℝ)|^4575 ≤ (11497108963393/25000000000000 : ℝ)^3551
        have hw : |(1368032333/2500000000 : ℝ)|=(1368032333/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(973339563/2000000000 : ℝ)|^4575 ≤ (9885128800571/25000000000000 : ℝ)^3551
        have hw : |(973339563/2000000000 : ℝ)|=(973339563/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1115247391/5000000000 : ℝ)|^4575 ≤ (3617762233711/25000000000000 : ℝ)^3551
        have hw : |(-1115247391/5000000000 : ℝ)|=(1115247391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1539_s0_3 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (206897033/500000000 : ℝ)*x 0 + (3091806067/10000000000 : ℝ)*x 1 + (2730927423/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (206897033/500000000 : ℝ)^4575 ≤ (8020778912417/25000000000000 : ℝ)^3551 := by
    have hnat : (206897033 : ℕ)^4575*25000000000000^3551 ≤ 8020778912417^3551*500000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206897033 500000000 8020778912417 25000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3091806067/10000000000 : ℝ)^4575 ≤ (22039666502663/100000000000000 : ℝ)^3551 := by
    have hnat : (3091806067 : ℕ)^4575*100000000000000^3551 ≤ 22039666502663^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3091806067 10000000000 22039666502663 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2730927423/5000000000 : ℝ)^4575 ≤ (45877217829501/100000000000000 : ℝ)^3551 := by
    have hnat : (2730927423 : ℕ)^4575*100000000000000^3551 ≤ 45877217829501^3551*5000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2730927423 5000000000 45877217829501 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(206897033/500000000 : ℝ), (3091806067/10000000000 : ℝ), (2730927423/5000000000 : ℝ)] ![(8020778912417/25000000000000 : ℝ), (22039666502663/100000000000000 : ℝ), (45877217829501/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(206897033/500000000 : ℝ)|^4575 ≤ (8020778912417/25000000000000 : ℝ)^3551
        have hw : |(206897033/500000000 : ℝ)|=(206897033/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3091806067/10000000000 : ℝ)|^4575 ≤ (22039666502663/100000000000000 : ℝ)^3551
        have hw : |(3091806067/10000000000 : ℝ)|=(3091806067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2730927423/5000000000 : ℝ)|^4575 ≤ (45877217829501/100000000000000 : ℝ)^3551
        have hw : |(2730927423/5000000000 : ℝ)|=(2730927423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1539_s0_4 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-51902061/312500000 : ℝ)*x 0 + (4892719049/10000000000 : ℝ)*x 1 + (2932695359/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (51902061/312500000 : ℝ)^4575 ≤ (4948492090501/50000000000000 : ℝ)^3551 := by
    have hnat : (51902061 : ℕ)^4575*50000000000000^3551 ≤ 4948492090501^3551*312500000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51902061 312500000 4948492090501 50000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4892719049/10000000000 : ℝ)^4575 ≤ (4976638196917/12500000000000 : ℝ)^3551 := by
    have hnat : (4892719049 : ℕ)^4575*12500000000000^3551 ≤ 4976638196917^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4892719049 10000000000 4976638196917 12500000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2932695359/5000000000 : ℝ)^4575 ≤ (50289910227253/100000000000000 : ℝ)^3551 := by
    have hnat : (2932695359 : ℕ)^4575*100000000000000^3551 ≤ 50289910227253^3551*5000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2932695359 5000000000 50289910227253 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-51902061/312500000 : ℝ), (4892719049/10000000000 : ℝ), (2932695359/5000000000 : ℝ)] ![(4948492090501/50000000000000 : ℝ), (4976638196917/12500000000000 : ℝ), (50289910227253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-51902061/312500000 : ℝ)|^4575 ≤ (4948492090501/50000000000000 : ℝ)^3551
        have hw : |(-51902061/312500000 : ℝ)|=(51902061/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4892719049/10000000000 : ℝ)|^4575 ≤ (4976638196917/12500000000000 : ℝ)^3551
        have hw : |(4892719049/10000000000 : ℝ)|=(4892719049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2932695359/5000000000 : ℝ)|^4575 ≤ (50289910227253/100000000000000 : ℝ)^3551
        have hw : |(2932695359/5000000000 : ℝ)|=(2932695359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1539_s0_5 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5191812719/10000000000 : ℝ)*x 0 + (-307950439/2500000000 : ℝ)*x 1 + (5865390887/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5191812719/10000000000 : ℝ)^4575 ≤ (8595194502083/20000000000000 : ℝ)^3551 := by
    have hnat : (5191812719 : ℕ)^4575*20000000000000^3551 ≤ 8595194502083^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5191812719 10000000000 8595194502083 20000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (307950439/2500000000 : ℝ)^4575 ≤ (3367057694391/50000000000000 : ℝ)^3551 := by
    have hnat : (307950439 : ℕ)^4575*50000000000000^3551 ≤ 3367057694391^3551*2500000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      307950439 2500000000 3367057694391 50000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5865390887/10000000000 : ℝ)^4575 ≤ (5028991209411/10000000000000 : ℝ)^3551 := by
    have hnat : (5865390887 : ℕ)^4575*10000000000000^3551 ≤ 5028991209411^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5865390887 10000000000 5028991209411 10000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5191812719/10000000000 : ℝ), (-307950439/2500000000 : ℝ), (5865390887/10000000000 : ℝ)] ![(8595194502083/20000000000000 : ℝ), (3367057694391/50000000000000 : ℝ), (5028991209411/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5191812719/10000000000 : ℝ)|^4575 ≤ (8595194502083/20000000000000 : ℝ)^3551
        have hw : |(5191812719/10000000000 : ℝ)|=(5191812719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-307950439/2500000000 : ℝ)|^4575 ≤ (3367057694391/50000000000000 : ℝ)^3551
        have hw : |(-307950439/2500000000 : ℝ)|=(307950439/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5865390887/10000000000 : ℝ)|^4575 ≤ (5028991209411/10000000000000 : ℝ)^3551
        have hw : |(5865390887/10000000000 : ℝ)|=(5865390887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1539_s0_6 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5191811779/10000000000 : ℝ)*x 0 + (5865392163/10000000000 : ℝ)*x 1 + (-153975147/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5191811779/10000000000 : ℝ)^4575 ≤ (42975962485633/100000000000000 : ℝ)^3551 := by
    have hnat : (5191811779 : ℕ)^4575*100000000000000^3551 ≤ 42975962485633^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5191811779 10000000000 42975962485633 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5865392163/10000000000 : ℝ)^4575 ≤ (50289926189433/100000000000000 : ℝ)^3551 := by
    have hnat : (5865392163 : ℕ)^4575*100000000000000^3551 ≤ 50289926189433^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5865392163 10000000000 50289926189433 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (153975147/1250000000 : ℝ)^4575 ≤ (6734111303631/100000000000000 : ℝ)^3551 := by
    have hnat : (153975147 : ℕ)^4575*100000000000000^3551 ≤ 6734111303631^3551*1250000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      153975147 1250000000 6734111303631 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5191811779/10000000000 : ℝ), (5865392163/10000000000 : ℝ), (-153975147/1250000000 : ℝ)] ![(42975962485633/100000000000000 : ℝ), (50289926189433/100000000000000 : ℝ), (6734111303631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5191811779/10000000000 : ℝ)|^4575 ≤ (42975962485633/100000000000000 : ℝ)^3551
        have hw : |(5191811779/10000000000 : ℝ)|=(5191811779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5865392163/10000000000 : ℝ)|^4575 ≤ (50289926189433/100000000000000 : ℝ)^3551
        have hw : |(5865392163/10000000000 : ℝ)|=(5865392163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-153975147/1250000000 : ℝ)|^4575 ≤ (6734111303631/100000000000000 : ℝ)^3551
        have hw : |(-153975147/1250000000 : ℝ)|=(153975147/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1539_s0_7 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4145557751/10000000000 : ℝ)*x 0 + (540172421/1000000000 : ℝ)*x 1 + (630815893/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4145557751/10000000000 : ℝ)^4575 ≤ (8039806207769/25000000000000 : ℝ)^3551 := by
    have hnat : (4145557751 : ℕ)^4575*25000000000000^3551 ≤ 8039806207769^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4145557751 10000000000 8039806207769 25000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (540172421/1000000000 : ℝ)^4575 ≤ (45227534980861/100000000000000 : ℝ)^3551 := by
    have hnat : (540172421 : ℕ)^4575*100000000000000^3551 ≤ 45227534980861^3551*1000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540172421 1000000000 45227534980861 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (630815893/2000000000 : ℝ)^4575 ≤ (2826655021717/12500000000000 : ℝ)^3551 := by
    have hnat : (630815893 : ℕ)^4575*12500000000000^3551 ≤ 2826655021717^3551*2000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      630815893 2000000000 2826655021717 12500000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4145557751/10000000000 : ℝ), (540172421/1000000000 : ℝ), (630815893/2000000000 : ℝ)] ![(8039806207769/25000000000000 : ℝ), (45227534980861/100000000000000 : ℝ), (2826655021717/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4145557751/10000000000 : ℝ)|^4575 ≤ (8039806207769/25000000000000 : ℝ)^3551
        have hw : |(4145557751/10000000000 : ℝ)|=(4145557751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(540172421/1000000000 : ℝ)|^4575 ≤ (45227534980861/100000000000000 : ℝ)^3551
        have hw : |(540172421/1000000000 : ℝ)|=(540172421/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(630815893/2000000000 : ℝ)|^4575 ≤ (2826655021717/12500000000000 : ℝ)^3551
        have hw : |(630815893/2000000000 : ℝ)|=(630815893/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1539_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165539681/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (3169/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (25139/100000 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (4573/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4573 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4573*1^1024 ≤ 0^1024*1^4573 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4573 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4573 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4573/1024 : ℝ) ≤ (167059595730212557/10000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4573 ≤ (167059595730212557/10000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4573*10000000000000000000^1024 ≤ 167059595730212557^1024*5^4573 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 167059595730212557 10000000000000000000 4573 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (167059595730212557/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4573 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4573/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4573 := by
      have hnat : (1 : ℕ)^1024*1^4573 ≤ 1^4573*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4573 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4573 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10167059595730212557/10000000000000000000 : ℝ) ≤ (5018584179322287/5000000000000000 : ℝ) ^ (4573/1024 : ℝ) := by
    have hpowers : (10167059595730212557/10000000000000000000 : ℝ)^1024 ≤ (5018584179322287/5000000000000000 : ℝ)^4573 := by
      have hnat : (10167059595730212557 : ℕ)^1024*5000000000000000^4573 ≤ 5018584179322287^4573*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10167059595730212557 10000000000000000000 5018584179322287 5000000000000000 1024 4573 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5018584179322287/5000000000000000 : ℝ)) (X := (10167059595730212557/10000000000000000000 : ℝ)) (by norm_num) 4573 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5167059595730212557/5000000000000000000 : ℝ) ≤ (2518584179322287/2500000000000000 : ℝ) ^ (4573/1024 : ℝ) := by
    have hpowers : (5167059595730212557/5000000000000000000 : ℝ)^1024 ≤ (2518584179322287/2500000000000000 : ℝ)^4573 := by
      have hnat : (5167059595730212557 : ℕ)^1024*2500000000000000^4573 ≤ 2518584179322287^4573*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5167059595730212557 5000000000000000000 2518584179322287 2500000000000000 1024 4573 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2518584179322287/2500000000000000 : ℝ)) (X := (5167059595730212557/5000000000000000000 : ℝ)) (by norm_num) 4573 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(18584179322287/2000000000000000 : ℝ)*(0 : ℝ))^(4573/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(18584179322287/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(167059595730212557/10000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(18584179322287/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4573/1024 : ℝ) := by
    rw [show (1 : ℝ)+(18584179322287/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5018584179322287/5000000000000000 : ℝ) by norm_num, show 1+(167059595730212557/10000000000000000000 : ℝ)+(0 : ℝ)=(10167059595730212557/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(167059595730212557/10000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(18584179322287/2000000000000000 : ℝ)*(2/5 : ℝ))^(4573/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(18584179322287/2000000000000000 : ℝ)*(2/5 : ℝ)=(2518584179322287/2500000000000000 : ℝ) by norm_num, show 1+2*(167059595730212557/10000000000000000000 : ℝ)=(5167059595730212557/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(18584179322287/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4573/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (18584179322287/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(18584179322287/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4573/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (18584179322287/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(18584179322287/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4573/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (18584179322287/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-828784219/5000000000 : ℝ)*X 0 0+(235693627/400000000 : ℝ)*X 0 1+(608337223/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5472129389/10000000000 : ℝ)*X 1 0+(-89219787/400000000 : ℝ)*X 1 1+(4866697841/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1368032333/2500000000 : ℝ)*X 2 0+(973339563/2000000000 : ℝ)*X 2 1+(-1115247391/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((206897033/500000000 : ℝ)*X 0 0+(3091806067/10000000000 : ℝ)*X 0 1+(2730927423/5000000000 : ℝ)*X 0 2+(206897033/500000000 : ℝ)*X 1 0+(3091806067/10000000000 : ℝ)*X 1 1+(2730927423/5000000000 : ℝ)*X 1 2+(206897033/500000000 : ℝ)*X 2 0+(3091806067/10000000000 : ℝ)*X 2 1+(2730927423/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-51902061/312500000 : ℝ)*X 0 0+(4892719049/10000000000 : ℝ)*X 0 1+(2932695359/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5191812719/10000000000 : ℝ)*X 1 0+(-307950439/2500000000 : ℝ)*X 1 1+(5865390887/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5191811779/10000000000 : ℝ)*X 2 0+(5865392163/10000000000 : ℝ)*X 2 1+(-153975147/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4145557751/10000000000 : ℝ)*X 0 0+(540172421/1000000000 : ℝ)*X 0 1+(630815893/2000000000 : ℝ)*X 0 2+(4145557751/10000000000 : ℝ)*X 1 0+(540172421/1000000000 : ℝ)*X 1 1+(630815893/2000000000 : ℝ)*X 1 2+(4145557751/10000000000 : ℝ)*X 2 0+(540172421/1000000000 : ℝ)*X 2 1+(630815893/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (44166184900868010979929/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (17018857/50000000000000 : ℝ)*(base1) + (414500839/100000000000000 : ℝ)*(base19) + (404344823/100000000000000 : ℝ)*(base23) + (54953/80000000000 : ℝ)*(upper3) + (17307131/50000000000000 : ℝ)*(upper5) + (698467283508611/100000000000000 : ℝ)*(major0) + (698467283508611/100000000000000 : ℝ)*(major1) + (698467283508611/100000000000000 : ℝ)*(major2) + (121874968392591/12500000000000 : ℝ)*(sp0) + (2437501577783/250000000000 : ℝ)*(sp1) + (975000641269217/100000000000000 : ℝ)*(sp2) + (421932767137623/100000000000000 : ℝ)*(sp3) + (666255513/50000000000000 : ℝ)*(sp4) + (80827191/12500000000000 : ℝ)*(sp7) + (84386689558573/20000000000000 : ℝ)*(f.failure) + (24375026140351/2500000000000 : ℝ)*(f.sum) + (506747399513357/100000000000000000000000000000 : ℝ)*base65 + (84354049713357/200000000000000000000000000000 : ℝ)*base67 + (833838109113357/200000000000000000000000000000 : ℝ)*base69 + (1367036407113357/200000000000000000000000000000 : ℝ)*base71 + (230155346613357/100000000000000000000000000000 : ℝ)*base73 + (2225878553113357/200000000000000000000000000000 : ℝ)*base75 + (857328758313357/200000000000000000000000000000 : ℝ)*base77 + (64528986486643/200000000000000000000000000000 : ℝ)*base80 + (687304720313357/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (14764787/2000000000000000000000 : ℝ)*base90 + (14764787/2000000000000000000000 : ℝ)*base92 + (14764787/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (725281551345748083981/312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (585410939/100000000000000 : ℝ)*(base19) + (469654151/50000000000000 : ℝ)*(base23) + (587894719/100000000000000 : ℝ)*(base39) + (1228557/2500000000000 : ℝ)*(upper3) + (378969543/100000000000000 : ℝ)*(upper5) + (46031321132239/6250000000000 : ℝ)*(major0) + (46031321132239/6250000000000 : ℝ)*(major1) + (46031284388819/6250000000000 : ℝ)*(major2) + (2105522061/100000000000000 : ℝ)*(sp1) + (282805549/20000000000000 : ℝ)*(sp2) + (25702312272407/2500000000000 : ℝ)*(sp4) + (12851122499541/1250000000000 : ℝ)*(sp5) + (128511340681869/12500000000000 : ℝ)*(sp6) + (55613640009659/12500000000000 : ℝ)*(sp7) + (55613640009659/12500000000000 : ℝ)*(f.failure) + (1028093078791/100000000000 : ℝ)*(f.sum) + (10274244159823/6250000000000000000000000000 : ℝ)*base65 + (59041509809053/12500000000000000000000000000 : ℝ)*base67 + (79373829589407/12500000000000000000000000000 : ℝ)*base70 + (43928366296553/12500000000000000000000000000 : ℝ)*base71 + (944715546427/6250000000000000000000000000 : ℝ)*base74 + (379712351907/12500000000000000000000000000 : ℝ)*base76 + (67861386660593/12500000000000000000000000000 : ℝ)*base77 + (130585858523093/12500000000000000000000000000 : ℝ)*base79 + (22572406451907/6250000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (12221221/1250000000000000000000 : ℝ)*base90 + (12221221/1250000000000000000000 : ℝ)*base92 + (278779/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1539_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165539681/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3169/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (25139/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1539_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1539_s1_0 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-225517023/1250000000 : ℝ)*x 0 + (5553194441/10000000000 : ℝ)*x 1 + (5111523411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (225517023/1250000000 : ℝ)^4575 ≤ (2752580951323/25000000000000 : ℝ)^3551 := by
    have hnat : (225517023 : ℕ)^4575*25000000000000^3551 ≤ 2752580951323^3551*1250000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225517023 1250000000 2752580951323 25000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5553194441/10000000000 : ℝ)^4575 ≤ (1171701143631/2500000000000 : ℝ)^3551 := by
    have hnat : (5553194441 : ℕ)^4575*2500000000000^3551 ≤ 1171701143631^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5553194441 10000000000 1171701143631 2500000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5111523411/10000000000 : ℝ)^4575 ≤ (21060815214341/50000000000000 : ℝ)^3551 := by
    have hnat : (5111523411 : ℕ)^4575*50000000000000^3551 ≤ 21060815214341^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5111523411 10000000000 21060815214341 50000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-225517023/1250000000 : ℝ), (5553194441/10000000000 : ℝ), (5111523411/10000000000 : ℝ)] ![(2752580951323/25000000000000 : ℝ), (1171701143631/2500000000000 : ℝ), (21060815214341/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-225517023/1250000000 : ℝ)|^4575 ≤ (2752580951323/25000000000000 : ℝ)^3551
        have hw : |(-225517023/1250000000 : ℝ)|=(225517023/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5553194441/10000000000 : ℝ)|^4575 ≤ (1171701143631/2500000000000 : ℝ)^3551
        have hw : |(5553194441/10000000000 : ℝ)|=(5553194441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5111523411/10000000000 : ℝ)|^4575 ≤ (21060815214341/50000000000000 : ℝ)^3551
        have hw : |(5111523411/10000000000 : ℝ)|=(5111523411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1539_s1_1 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5381787043/10000000000 : ℝ)*x 0 + (-8143811/40000000 : ℝ)*x 1 + (1022304107/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5381787043/10000000000 : ℝ)^4575 ≤ (22506291116553/50000000000000 : ℝ)^3551 := by
    have hnat : (5381787043 : ℕ)^4575*50000000000000^3551 ≤ 22506291116553^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5381787043 10000000000 22506291116553 50000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8143811/40000000 : ℝ)^4575 ≤ (2573163572357/20000000000000 : ℝ)^3551 := by
    have hnat : (8143811 : ℕ)^4575*20000000000000^3551 ≤ 2573163572357^3551*40000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8143811 40000000 2573163572357 20000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1022304107/2000000000 : ℝ)^4575 ≤ (21060799947327/50000000000000 : ℝ)^3551 := by
    have hnat : (1022304107 : ℕ)^4575*50000000000000^3551 ≤ 21060799947327^3551*2000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1022304107 2000000000 21060799947327 50000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5381787043/10000000000 : ℝ), (-8143811/40000000 : ℝ), (1022304107/2000000000 : ℝ)] ![(22506291116553/50000000000000 : ℝ), (2573163572357/20000000000000 : ℝ), (21060799947327/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5381787043/10000000000 : ℝ)|^4575 ≤ (22506291116553/50000000000000 : ℝ)^3551
        have hw : |(5381787043/10000000000 : ℝ)|=(5381787043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-8143811/40000000 : ℝ)|^4575 ≤ (2573163572357/20000000000000 : ℝ)^3551
        have hw : |(-8143811/40000000 : ℝ)|=(8143811/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1022304107/2000000000 : ℝ)|^4575 ≤ (21060799947327/50000000000000 : ℝ)^3551
        have hw : |(1022304107/2000000000 : ℝ)|=(1022304107/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1539_s1_2 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5381784259/10000000000 : ℝ)*x 0 + (1277880873/2500000000 : ℝ)*x 1 + (-1017976289/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5381784259/10000000000 : ℝ)^4575 ≤ (45012552233397/100000000000000 : ℝ)^3551 := by
    have hnat : (5381784259 : ℕ)^4575*100000000000000^3551 ≤ 45012552233397^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5381784259 10000000000 45012552233397 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1277880873/2500000000 : ℝ)^4575 ≤ (21060815644323/50000000000000 : ℝ)^3551 := by
    have hnat : (1277880873 : ℕ)^4575*50000000000000^3551 ≤ 21060815644323^3551*2500000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1277880873 2500000000 21060815644323 50000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1017976289/5000000000 : ℝ)^4575 ≤ (3216454115357/25000000000000 : ℝ)^3551 := by
    have hnat : (1017976289 : ℕ)^4575*25000000000000^3551 ≤ 3216454115357^3551*5000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1017976289 5000000000 3216454115357 25000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5381784259/10000000000 : ℝ), (1277880873/2500000000 : ℝ), (-1017976289/5000000000 : ℝ)] ![(45012552233397/100000000000000 : ℝ), (21060815644323/50000000000000 : ℝ), (3216454115357/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5381784259/10000000000 : ℝ)|^4575 ≤ (45012552233397/100000000000000 : ℝ)^3551
        have hw : |(5381784259/10000000000 : ℝ)|=(5381784259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1277880873/2500000000 : ℝ)|^4575 ≤ (21060815644323/50000000000000 : ℝ)^3551
        have hw : |(1277880873/2500000000 : ℝ)|=(1277880873/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1017976289/5000000000 : ℝ)|^4575 ≤ (3216454115357/25000000000000 : ℝ)^3551
        have hw : |(-1017976289/5000000000 : ℝ)|=(1017976289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1539_s1_3 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2119880691/5000000000 : ℝ)*x 0 + (1877412819/5000000000 : ℝ)*x 1 + (2387719267/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2119880691/5000000000 : ℝ)^4575 ≤ (33103815647181/100000000000000 : ℝ)^3551 := by
    have hnat : (2119880691 : ℕ)^4575*100000000000000^3551 ≤ 33103815647181^3551*5000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119880691 5000000000 33103815647181 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1877412819/5000000000 : ℝ)^4575 ≤ (1415417159021/5000000000000 : ℝ)^3551 := by
    have hnat : (1877412819 : ℕ)^4575*5000000000000^3551 ≤ 1415417159021^3551*5000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1877412819 5000000000 1415417159021 5000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2387719267/5000000000 : ℝ)^4575 ≤ (19293920581459/50000000000000 : ℝ)^3551 := by
    have hnat : (2387719267 : ℕ)^4575*50000000000000^3551 ≤ 19293920581459^3551*5000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2387719267 5000000000 19293920581459 50000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2119880691/5000000000 : ℝ), (1877412819/5000000000 : ℝ), (2387719267/5000000000 : ℝ)] ![(33103815647181/100000000000000 : ℝ), (1415417159021/5000000000000 : ℝ), (19293920581459/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2119880691/5000000000 : ℝ)|^4575 ≤ (33103815647181/100000000000000 : ℝ)^3551
        have hw : |(2119880691/5000000000 : ℝ)|=(2119880691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1877412819/5000000000 : ℝ)|^4575 ≤ (1415417159021/5000000000000 : ℝ)^3551
        have hw : |(1877412819/5000000000 : ℝ)|=(1877412819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2387719267/5000000000 : ℝ)|^4575 ≤ (19293920581459/50000000000000 : ℝ)^3551
        have hw : |(2387719267/5000000000 : ℝ)|=(2387719267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1539_s1_4 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1804391789/10000000000 : ℝ)*x 0 + (5116278221/10000000000 : ℝ)*x 1 + (277418293/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1804391789/10000000000 : ℝ)^4575 ≤ (5506166794721/50000000000000 : ℝ)^3551 := by
    have hnat : (1804391789 : ℕ)^4575*50000000000000^3551 ≤ 5506166794721^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1804391789 10000000000 5506166794721 50000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5116278221/10000000000 : ℝ)^4575 ≤ (42172118251681/100000000000000 : ℝ)^3551 := by
    have hnat : (5116278221 : ℕ)^4575*100000000000000^3551 ≤ 42172118251681^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5116278221 10000000000 42172118251681 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (277418293/500000000 : ℝ)^4575 ≤ (46815548145213/100000000000000 : ℝ)^3551 := by
    have hnat : (277418293 : ℕ)^4575*100000000000000^3551 ≤ 46815548145213^3551*500000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277418293 500000000 46815548145213 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1804391789/10000000000 : ℝ), (5116278221/10000000000 : ℝ), (277418293/500000000 : ℝ)] ![(5506166794721/50000000000000 : ℝ), (42172118251681/100000000000000 : ℝ), (46815548145213/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1804391789/10000000000 : ℝ)|^4575 ≤ (5506166794721/50000000000000 : ℝ)^3551
        have hw : |(-1804391789/10000000000 : ℝ)|=(1804391789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5116278221/10000000000 : ℝ)|^4575 ≤ (42172118251681/100000000000000 : ℝ)^3551
        have hw : |(5116278221/10000000000 : ℝ)|=(5116278221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(277418293/500000000 : ℝ)|^4575 ≤ (46815548145213/100000000000000 : ℝ)^3551
        have hw : |(277418293/500000000 : ℝ)|=(277418293/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1539_s1_5 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1053017769/2000000000 : ℝ)*x 0 + (-1599110071/10000000000 : ℝ)*x 1 + (5548365769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1053017769/2000000000 : ℝ)^4575 ≤ (43759022656197/100000000000000 : ℝ)^3551 := by
    have hnat : (1053017769 : ℕ)^4575*100000000000000^3551 ≤ 43759022656197^3551*2000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053017769 2000000000 43759022656197 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1599110071/10000000000 : ℝ)^4575 ≤ (1178178770327/12500000000000 : ℝ)^3551 := by
    have hnat : (1599110071 : ℕ)^4575*12500000000000^3551 ≤ 1178178770327^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1599110071 10000000000 1178178770327 12500000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5548365769/10000000000 : ℝ)^4575 ≤ (23407773577981/50000000000000 : ℝ)^3551 := by
    have hnat : (5548365769 : ℕ)^4575*50000000000000^3551 ≤ 23407773577981^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5548365769 10000000000 23407773577981 50000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1053017769/2000000000 : ℝ), (-1599110071/10000000000 : ℝ), (5548365769/10000000000 : ℝ)] ![(43759022656197/100000000000000 : ℝ), (1178178770327/12500000000000 : ℝ), (23407773577981/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1053017769/2000000000 : ℝ)|^4575 ≤ (43759022656197/100000000000000 : ℝ)^3551
        have hw : |(1053017769/2000000000 : ℝ)|=(1053017769/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1599110071/10000000000 : ℝ)|^4575 ≤ (1178178770327/12500000000000 : ℝ)^3551
        have hw : |(-1599110071/10000000000 : ℝ)|=(1599110071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5548365769/10000000000 : ℝ)|^4575 ≤ (23407773577981/50000000000000 : ℝ)^3551
        have hw : |(5548365769/10000000000 : ℝ)|=(5548365769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1539_s1_6 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (52650893/100000000 : ℝ)*x 0 + (2774182849/5000000000 : ℝ)*x 1 + (-1599109531/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (52650893/100000000 : ℝ)^4575 ≤ (4375902752827/10000000000000 : ℝ)^3551 := by
    have hnat : (52650893 : ℕ)^4575*10000000000000^3551 ≤ 4375902752827^3551*100000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52650893 100000000 4375902752827 10000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2774182849/5000000000 : ℝ)^4575 ≤ (182873228063/390625000000 : ℝ)^3551 := by
    have hnat : (2774182849 : ℕ)^4575*390625000000^3551 ≤ 182873228063^3551*5000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2774182849 5000000000 182873228063 390625000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1599109531/10000000000 : ℝ)^4575 ≤ (377017042477/4000000000000 : ℝ)^3551 := by
    have hnat : (1599109531 : ℕ)^4575*4000000000000^3551 ≤ 377017042477^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1599109531 10000000000 377017042477 4000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(52650893/100000000 : ℝ), (2774182849/5000000000 : ℝ), (-1599109531/10000000000 : ℝ)] ![(4375902752827/10000000000000 : ℝ), (182873228063/390625000000 : ℝ), (377017042477/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(52650893/100000000 : ℝ)|^4575 ≤ (4375902752827/10000000000000 : ℝ)^3551
        have hw : |(52650893/100000000 : ℝ)|=(52650893/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2774182849/5000000000 : ℝ)|^4575 ≤ (182873228063/390625000000 : ℝ)^3551
        have hw : |(2774182849/5000000000 : ℝ)|=(2774182849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1599109531/10000000000 : ℝ)|^4575 ≤ (377017042477/4000000000000 : ℝ)^3551
        have hw : |(-1599109531/10000000000 : ℝ)|=(1599109531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1539_s1_7 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4240349977/10000000000 : ℝ)*x 0 + (2382224983/5000000000 : ℝ)*x 1 + (1882992437/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4240349977/10000000000 : ℝ)^4575 ≤ (33109736746249/100000000000000 : ℝ)^3551 := by
    have hnat : (4240349977 : ℕ)^4575*100000000000000^3551 ≤ 33109736746249^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4240349977 10000000000 33109736746249 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2382224983/5000000000 : ℝ)^4575 ≤ (19236740527441/50000000000000 : ℝ)^3551 := by
    have hnat : (2382224983 : ℕ)^4575*50000000000000^3551 ≤ 19236740527441^3551*5000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2382224983 5000000000 19236740527441 50000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1882992437/5000000000 : ℝ)^4575 ≤ (28416782178361/100000000000000 : ℝ)^3551 := by
    have hnat : (1882992437 : ℕ)^4575*100000000000000^3551 ≤ 28416782178361^3551*5000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1882992437 5000000000 28416782178361 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4240349977/10000000000 : ℝ), (2382224983/5000000000 : ℝ), (1882992437/5000000000 : ℝ)] ![(33109736746249/100000000000000 : ℝ), (19236740527441/50000000000000 : ℝ), (28416782178361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4240349977/10000000000 : ℝ)|^4575 ≤ (33109736746249/100000000000000 : ℝ)^3551
        have hw : |(4240349977/10000000000 : ℝ)|=(4240349977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2382224983/5000000000 : ℝ)|^4575 ≤ (19236740527441/50000000000000 : ℝ)^3551
        have hw : |(2382224983/5000000000 : ℝ)|=(2382224983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1882992437/5000000000 : ℝ)|^4575 ≤ (28416782178361/100000000000000 : ℝ)^3551
        have hw : |(1882992437/5000000000 : ℝ)|=(1882992437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1539_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165539681/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (25139/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3169/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (272/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18051/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (25139/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3169/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (25139/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3169/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (25139/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3169/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (25139/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3169/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (25139/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3169/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (25139/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3169/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3169/100000 : ℝ) ^ (4573/1024 : ℝ) ≤ (404034156587/2000000000000000000 : ℝ) := by
    have hpowers : (3169/100000 : ℝ)^4573 ≤ (404034156587/2000000000000000000 : ℝ)^1024 := by
      have hnat : (3169 : ℕ)^4573*2000000000000000000^1024 ≤ 404034156587^1024*100000^4573 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3169 100000 404034156587 2000000000000000000 4573 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3169/100000 : ℝ)) (X := (404034156587/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4573 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (25139/100000 : ℝ) ^ (4573/1024 : ℝ) ≤ (52480977746466149/25000000000000000000 : ℝ) := by
    have hpowers : (25139/100000 : ℝ)^4573 ≤ (52480977746466149/25000000000000000000 : ℝ)^1024 := by
      have hnat : (25139 : ℕ)^4573*25000000000000000000^1024 ≤ 52480977746466149^1024*100000^4573 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25139 100000 52480977746466149 25000000000000000000 4573 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (25139/100000 : ℝ)) (X := (52480977746466149/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4573 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1000000404034156587/1000000000000000000 : ℝ) ≤ (1000000090472537/1000000000000000 : ℝ) ^ (4573/1024 : ℝ) := by
    have hpowers : (1000000404034156587/1000000000000000000 : ℝ)^1024 ≤ (1000000090472537/1000000000000000 : ℝ)^4573 := by
      have hnat : (1000000404034156587 : ℕ)^1024*1000000000000000^4573 ≤ 1000000090472537^4573*1000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000000404034156587 1000000000000000000 1000000090472537 1000000000000000 1024 4573 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000000090472537/1000000000000000 : ℝ)) (X := (1000000404034156587/1000000000000000000 : ℝ)) (by norm_num) 4573 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50104972056346846973/50000000000000000000 : ℝ) ≤ (125058716337757/125000000000000 : ℝ) ^ (4573/1024 : ℝ) := by
    have hpowers : (50104972056346846973/50000000000000000000 : ℝ)^1024 ≤ (125058716337757/125000000000000 : ℝ)^4573 := by
      have hnat : (50104972056346846973 : ℕ)^1024*125000000000000^4573 ≤ 125058716337757^4573*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50104972056346846973 50000000000000000000 125058716337757 125000000000000 1024 4573 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125058716337757/125000000000000 : ℝ)) (X := (50104972056346846973/50000000000000000000 : ℝ)) (by norm_num) 4573 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12552480977746466149/12500000000000000000 : ℝ) ≤ (40037574837263/40000000000000 : ℝ) ^ (4573/1024 : ℝ) := by
    have hpowers : (12552480977746466149/12500000000000000000 : ℝ)^1024 ≤ (40037574837263/40000000000000 : ℝ)^4573 := by
      have hnat : (12552480977746466149 : ℕ)^1024*40000000000000^4573 ≤ 40037574837263^4573*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12552480977746466149 12500000000000000000 40037574837263 40000000000000 1024 4573 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (40037574837263/40000000000000 : ℝ)) (X := (12552480977746466149/12500000000000000000 : ℝ)) (by norm_num) 4573 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(404034156587/2000000000000000000 : ℝ) ≤ ((5491756351976736617/5492500000000000000 : ℝ)+2*(469640229519/219700000000000 : ℝ)*(3169/100000 : ℝ))^(4573/1024 : ℝ) := by
    rw [show (5491756351976736617/5492500000000000000 : ℝ)+2*(469640229519/219700000000000 : ℝ)*(3169/100000 : ℝ)=(1000000090472537/1000000000000000 : ℝ) by norm_num, show 1+2*(404034156587/2000000000000000000 : ℝ)=(1000000404034156587/1000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(52480977746466149/25000000000000000000 : ℝ)+(404034156587/2000000000000000000 : ℝ) ≤ ((5491756351976736617/5492500000000000000 : ℝ)+(469640229519/219700000000000 : ℝ)*((25139/100000 : ℝ)+(3169/100000 : ℝ)))^(4573/1024 : ℝ) := by
    rw [show (5491756351976736617/5492500000000000000 : ℝ)+(469640229519/219700000000000 : ℝ)*((25139/100000 : ℝ)+(3169/100000 : ℝ))=(125058716337757/125000000000000 : ℝ) by norm_num, show 1+(52480977746466149/25000000000000000000 : ℝ)+(404034156587/2000000000000000000 : ℝ)=(50104972056346846973/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(52480977746466149/25000000000000000000 : ℝ) ≤ ((5491756351976736617/5492500000000000000 : ℝ)+2*(469640229519/219700000000000 : ℝ)*(25139/100000 : ℝ))^(4573/1024 : ℝ) := by
    rw [show (5491756351976736617/5492500000000000000 : ℝ)+2*(469640229519/219700000000000 : ℝ)*(25139/100000 : ℝ)=(40037574837263/40000000000000 : ℝ) by norm_num, show 1+2*(52480977746466149/25000000000000000000 : ℝ)=(12552480977746466149/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5491756351976736617/5492500000000000000 : ℝ)*(X 1 0+X 2 0)+(469640229519/219700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4573/1024 : ℝ)) (lo := (3169/100000 : ℝ)) (hi := (25139/100000 : ℝ)) (c := (5491756351976736617/5492500000000000000 : ℝ)) (alpha := (469640229519/219700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5491756351976736617/5492500000000000000 : ℝ)*(X 0 1+X 2 1)+(469640229519/219700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4573/1024 : ℝ)) (lo := (3169/100000 : ℝ)) (hi := (25139/100000 : ℝ)) (c := (5491756351976736617/5492500000000000000 : ℝ)) (alpha := (469640229519/219700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5491756351976736617/5492500000000000000 : ℝ)*(X 0 2+X 1 2)+(469640229519/219700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4573/1024 : ℝ)) (lo := (3169/100000 : ℝ)) (hi := (25139/100000 : ℝ)) (c := (5491756351976736617/5492500000000000000 : ℝ)) (alpha := (469640229519/219700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-225517023/1250000000 : ℝ)*X 0 0+(5553194441/10000000000 : ℝ)*X 0 1+(5111523411/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5381787043/10000000000 : ℝ)*X 1 0+(-8143811/40000000 : ℝ)*X 1 1+(1022304107/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5381784259/10000000000 : ℝ)*X 2 0+(1277880873/2500000000 : ℝ)*X 2 1+(-1017976289/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2119880691/5000000000 : ℝ)*X 0 0+(1877412819/5000000000 : ℝ)*X 0 1+(2387719267/5000000000 : ℝ)*X 0 2+(2119880691/5000000000 : ℝ)*X 1 0+(1877412819/5000000000 : ℝ)*X 1 1+(2387719267/5000000000 : ℝ)*X 1 2+(2119880691/5000000000 : ℝ)*X 2 0+(1877412819/5000000000 : ℝ)*X 2 1+(2387719267/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1804391789/10000000000 : ℝ)*X 0 0+(5116278221/10000000000 : ℝ)*X 0 1+(277418293/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1053017769/2000000000 : ℝ)*X 1 0+(-1599110071/10000000000 : ℝ)*X 1 1+(5548365769/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((52650893/100000000 : ℝ)*X 2 0+(2774182849/5000000000 : ℝ)*X 2 1+(-1599109531/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4240349977/10000000000 : ℝ)*X 0 0+(2382224983/5000000000 : ℝ)*X 0 1+(1882992437/5000000000 : ℝ)*X 0 2+(4240349977/10000000000 : ℝ)*X 1 0+(2382224983/5000000000 : ℝ)*X 1 1+(1882992437/5000000000 : ℝ)*X 1 2+(4240349977/10000000000 : ℝ)*X 2 0+(2382224983/5000000000 : ℝ)*X 2 1+(1882992437/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1460642530751282569118939709/274625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (47986687/12500000000000 : ℝ)*(base1) + (1970307819/100000000000000 : ℝ)*(base19) + (48492223/6250000000000 : ℝ)*(base23) + (28947131/25000000000000 : ℝ)*(upper3) + (41087053/50000000000000 : ℝ)*(upper5) + (1621969641483559/100000000000000 : ℝ)*(major0) + (1621969641483559/100000000000000 : ℝ)*(major1) + (1621969641483559/100000000000000 : ℝ)*(major2) + (1132066166475743/50000000000000 : ℝ)*(sp0) + (226412997875017/10000000000000 : ℝ)*(sp1) + (566032525848653/25000000000000 : ℝ)*(sp2) + (979805688603197/100000000000000 : ℝ)*(sp3) + (1069787811/100000000000000 : ℝ)*(sp6) + (1084123089/100000000000000 : ℝ)*(sp7) + (979807156619783/100000000000000 : ℝ)*(f.failure) + (226413194905799/10000000000000 : ℝ)*(f.sum) + (7140975840933/5492500000000000000000000000 : ℝ)*base65 + (851451134671304903/549250000000000000000000000000000 : ℝ)*base67 + (761074772970695097/549250000000000000000000000000000 : ℝ)*base70 + (5840712768230445097/549250000000000000000000000000000 : ℝ)*base72 + (51671877650521/10985000000000000000000000000 : ℝ)*base73 + (4636129141482304903/549250000000000000000000000000000 : ℝ)*base75 + (1476090776506945097/549250000000000000000000000000000 : ℝ)*base78 + (4474759503986695097/549250000000000000000000000000000 : ℝ)*base80 + (15447696495113/5492500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (16109223/10000000000000000000000 : ℝ)*base89 + (16109223/10000000000000000000000 : ℝ)*base91 + (16109223/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (286035704983540492284139911/68656250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (24734073/5000000000000 : ℝ)*(base19) + (162472607/20000000000000 : ℝ)*(base23) + (20917321/20000000000000 : ℝ)*(upper3) + (1475559/6250000000000 : ℝ)*(lower4) + (30449257/25000000000000 : ℝ)*(upper5) + (828970923245311/50000000000000 : ℝ)*(major0) + (828970923245311/50000000000000 : ℝ)*(major1) + (828970923245311/50000000000000 : ℝ)*(major2) + (10823849/500000000000 : ℝ)*(sp1) + (272561/5000000000 : ℝ)*(sp2) + (1157173068163347/50000000000000 : ℝ)*(sp4) + (462868695375087/20000000000000 : ℝ)*(sp5) + (115716993637183/5000000000000 : ℝ)*(sp6) + (125192177222649/12500000000000 : ℝ)*(sp7) + (125192177222649/12500000000000 : ℝ)*(f.failure) + (1157173068163347/50000000000000 : ℝ)*(f.sum) + (2171333828511/1373125000000000000000000000 : ℝ)*base65 + (856126514970272113/274625000000000000000000000000000 : ℝ)*base68 + (514008971655477887/274625000000000000000000000000000 : ℝ)*base69 + (1601866778902897113/274625000000000000000000000000000 : ℝ)*base72 + (3543119867623/10985000000000000000000000000 : ℝ)*base73 + (1705664253716397113/274625000000000000000000000000000 : ℝ)*base76 + (3047518600518522113/274625000000000000000000000000000 : ℝ)*base78 + (2750512642880522113/274625000000000000000000000000000 : ℝ)*base80 + (30492815919019/5492500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (6434969/1250000000000000000000 : ℝ)*base89 + (6434969/1250000000000000000000 : ℝ)*base91 + (6434969/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1539_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165539681/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (25139/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3169/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (272/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18051/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1539_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1539_s2_0 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-912858909/5000000000 : ℝ)*x 0 + (2724878407/5000000000 : ℝ)*x 1 + (650117737/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (912858909/5000000000 : ℝ)^4575 ≤ (1397538171653/12500000000000 : ℝ)^3551 := by
    have hnat : (912858909 : ℕ)^4575*12500000000000^3551 ≤ 1397538171653^3551*5000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      912858909 5000000000 1397538171653 12500000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2724878407/5000000000 : ℝ)^4575 ≤ (11436584458009/25000000000000 : ℝ)^3551 := by
    have hnat : (2724878407 : ℕ)^4575*25000000000000^3551 ≤ 11436584458009^3551*5000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2724878407 5000000000 11436584458009 25000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (650117737/1250000000 : ℝ)^4575 ≤ (21536678388309/50000000000000 : ℝ)^3551 := by
    have hnat : (650117737 : ℕ)^4575*50000000000000^3551 ≤ 21536678388309^3551*1250000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      650117737 1250000000 21536678388309 50000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-912858909/5000000000 : ℝ), (2724878407/5000000000 : ℝ), (650117737/1250000000 : ℝ)] ![(1397538171653/12500000000000 : ℝ), (11436584458009/25000000000000 : ℝ), (21536678388309/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-912858909/5000000000 : ℝ)|^4575 ≤ (1397538171653/12500000000000 : ℝ)^3551
        have hw : |(-912858909/5000000000 : ℝ)|=(912858909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2724878407/5000000000 : ℝ)|^4575 ≤ (11436584458009/25000000000000 : ℝ)^3551
        have hw : |(2724878407/5000000000 : ℝ)|=(2724878407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(650117737/1250000000 : ℝ)|^4575 ≤ (21536678388309/50000000000000 : ℝ)^3551
        have hw : |(650117737/1250000000 : ℝ)|=(650117737/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1539_s2_1 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5355290547/10000000000 : ℝ)*x 0 + (-1953611569/10000000000 : ℝ)*x 1 + (1040188419/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5355290547/10000000000 : ℝ)^4575 ≤ (11181816328599/25000000000000 : ℝ)^3551 := by
    have hnat : (5355290547 : ℕ)^4575*25000000000000^3551 ≤ 11181816328599^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355290547 10000000000 11181816328599 25000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1953611569/10000000000 : ℝ)^4575 ≤ (6099687886633/50000000000000 : ℝ)^3551 := by
    have hnat : (1953611569 : ℕ)^4575*50000000000000^3551 ≤ 6099687886633^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1953611569 10000000000 6099687886633 50000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1040188419/2000000000 : ℝ)^4575 ≤ (43073358899961/100000000000000 : ℝ)^3551 := by
    have hnat : (1040188419 : ℕ)^4575*100000000000000^3551 ≤ 43073358899961^3551*2000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040188419 2000000000 43073358899961 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5355290547/10000000000 : ℝ), (-1953611569/10000000000 : ℝ), (1040188419/2000000000 : ℝ)] ![(11181816328599/25000000000000 : ℝ), (6099687886633/50000000000000 : ℝ), (43073358899961/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5355290547/10000000000 : ℝ)|^4575 ≤ (11181816328599/25000000000000 : ℝ)^3551
        have hw : |(5355290547/10000000000 : ℝ)|=(5355290547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1953611569/10000000000 : ℝ)|^4575 ≤ (6099687886633/50000000000000 : ℝ)^3551
        have hw : |(-1953611569/10000000000 : ℝ)|=(1953611569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1040188419/2000000000 : ℝ)|^4575 ≤ (43073358899961/100000000000000 : ℝ)^3551
        have hw : |(1040188419/2000000000 : ℝ)|=(1040188419/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1539_s2_2 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1071058087/2000000000 : ℝ)*x 0 + (5200942109/10000000000 : ℝ)*x 1 + (-19536117/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071058087/2000000000 : ℝ)^4575 ≤ (11181816027307/25000000000000 : ℝ)^3551 := by
    have hnat : (1071058087 : ℕ)^4575*25000000000000^3551 ≤ 11181816027307^3551*2000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071058087 2000000000 11181816027307 25000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5200942109/10000000000 : ℝ)^4575 ≤ (21536679524671/50000000000000 : ℝ)^3551 := by
    have hnat : (5200942109 : ℕ)^4575*50000000000000^3551 ≤ 21536679524671^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5200942109 10000000000 21536679524671 50000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (19536117/100000000 : ℝ)^4575 ≤ (6099688413597/50000000000000 : ℝ)^3551 := by
    have hnat : (19536117 : ℕ)^4575*50000000000000^3551 ≤ 6099688413597^3551*100000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19536117 100000000 6099688413597 50000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071058087/2000000000 : ℝ), (5200942109/10000000000 : ℝ), (-19536117/100000000 : ℝ)] ![(11181816027307/25000000000000 : ℝ), (21536679524671/50000000000000 : ℝ), (6099688413597/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071058087/2000000000 : ℝ)|^4575 ≤ (11181816027307/25000000000000 : ℝ)^3551
        have hw : |(1071058087/2000000000 : ℝ)|=(1071058087/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5200942109/10000000000 : ℝ)|^4575 ≤ (21536679524671/50000000000000 : ℝ)^3551
        have hw : |(5200942109/10000000000 : ℝ)|=(5200942109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-19536117/100000000 : ℝ)|^4575 ≤ (6099688413597/50000000000000 : ℝ)^3551
        have hw : |(-19536117/100000000 : ℝ)|=(19536117/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1539_s2_3 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2127661747/5000000000 : ℝ)*x 0 + (397590133/1000000000 : ℝ)*x 1 + (4550859633/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2127661747/5000000000 : ℝ)^4575 ≤ (33260445732651/100000000000000 : ℝ)^3551 := by
    have hnat : (2127661747 : ℕ)^4575*100000000000000^3551 ≤ 33260445732651^3551*5000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2127661747 5000000000 33260445732651 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (397590133/1000000000 : ℝ)^4575 ≤ (3809211311497/12500000000000 : ℝ)^3551 := by
    have hnat : (397590133 : ℕ)^4575*12500000000000^3551 ≤ 3809211311497^3551*1000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397590133 1000000000 3809211311497 12500000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4550859633/10000000000 : ℝ)^4575 ≤ (18132931881539/50000000000000 : ℝ)^3551 := by
    have hnat : (4550859633 : ℕ)^4575*50000000000000^3551 ≤ 18132931881539^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4550859633 10000000000 18132931881539 50000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2127661747/5000000000 : ℝ), (397590133/1000000000 : ℝ), (4550859633/10000000000 : ℝ)] ![(33260445732651/100000000000000 : ℝ), (3809211311497/12500000000000 : ℝ), (18132931881539/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2127661747/5000000000 : ℝ)|^4575 ≤ (33260445732651/100000000000000 : ℝ)^3551
        have hw : |(2127661747/5000000000 : ℝ)|=(2127661747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(397590133/1000000000 : ℝ)|^4575 ≤ (3809211311497/12500000000000 : ℝ)^3551
        have hw : |(397590133/1000000000 : ℝ)|=(397590133/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4550859633/10000000000 : ℝ)|^4575 ≤ (18132931881539/50000000000000 : ℝ)^3551
        have hw : |(4550859633/10000000000 : ℝ)|=(4550859633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1539_s2_4 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1825763947/10000000000 : ℝ)*x 0 + (5202459133/10000000000 : ℝ)*x 1 + (5448226109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1825763947/10000000000 : ℝ)^4575 ≤ (5590334659239/50000000000000 : ℝ)^3551 := by
    have hnat : (1825763947 : ℕ)^4575*50000000000000^3551 ≤ 5590334659239^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1825763947 10000000000 5590334659239 50000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5202459133/10000000000 : ℝ)^4575 ≤ (10772386619453/25000000000000 : ℝ)^3551 := by
    have hnat : (5202459133 : ℕ)^4575*25000000000000^3551 ≤ 10772386619453^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5202459133 10000000000 10772386619453 25000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5448226109/10000000000 : ℝ)^4575 ≤ (22864892095237/50000000000000 : ℝ)^3551 := by
    have hnat : (5448226109 : ℕ)^4575*50000000000000^3551 ≤ 22864892095237^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5448226109 10000000000 22864892095237 50000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1825763947/10000000000 : ℝ), (5202459133/10000000000 : ℝ), (5448226109/10000000000 : ℝ)] ![(5590334659239/50000000000000 : ℝ), (10772386619453/25000000000000 : ℝ), (22864892095237/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1825763947/10000000000 : ℝ)|^4575 ≤ (5590334659239/50000000000000 : ℝ)^3551
        have hw : |(-1825763947/10000000000 : ℝ)|=(1825763947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5202459133/10000000000 : ℝ)|^4575 ≤ (10772386619453/25000000000000 : ℝ)^3551
        have hw : |(5202459133/10000000000 : ℝ)|=(5202459133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5448226109/10000000000 : ℝ)|^4575 ≤ (22864892095237/50000000000000 : ℝ)^3551
        have hw : |(5448226109/10000000000 : ℝ)|=(5448226109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1539_s2_5 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1322427667/2500000000 : ℝ)*x 0 + (-1706327537/10000000000 : ℝ)*x 1 + (5448225511/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322427667/2500000000 : ℝ)^4575 ≤ (44022847050469/100000000000000 : ℝ)^3551 := by
    have hnat : (1322427667 : ℕ)^4575*100000000000000^3551 ≤ 44022847050469^3551*2500000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322427667 2500000000 44022847050469 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1706327537/10000000000 : ℝ)^4575 ≤ (1280921900731/12500000000000 : ℝ)^3551 := by
    have hnat : (1706327537 : ℕ)^4575*12500000000000^3551 ≤ 1280921900731^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1706327537 10000000000 1280921900731 12500000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5448225511/10000000000 : ℝ)^4575 ≤ (45729777723731/100000000000000 : ℝ)^3551 := by
    have hnat : (5448225511 : ℕ)^4575*100000000000000^3551 ≤ 45729777723731^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5448225511 10000000000 45729777723731 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322427667/2500000000 : ℝ), (-1706327537/10000000000 : ℝ), (5448225511/10000000000 : ℝ)] ![(44022847050469/100000000000000 : ℝ), (1280921900731/12500000000000 : ℝ), (45729777723731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322427667/2500000000 : ℝ)|^4575 ≤ (44022847050469/100000000000000 : ℝ)^3551
        have hw : |(1322427667/2500000000 : ℝ)|=(1322427667/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1706327537/10000000000 : ℝ)|^4575 ≤ (1280921900731/12500000000000 : ℝ)^3551
        have hw : |(-1706327537/10000000000 : ℝ)|=(1706327537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5448225511/10000000000 : ℝ)|^4575 ≤ (45729777723731/100000000000000 : ℝ)^3551
        have hw : |(5448225511/10000000000 : ℝ)|=(5448225511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1539_s2_6 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (528971017/1000000000 : ℝ)*x 0 + (5448225559/10000000000 : ℝ)*x 1 + (-1706328161/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528971017/1000000000 : ℝ)^4575 ≤ (2201142085539/5000000000000 : ℝ)^3551 := by
    have hnat : (528971017 : ℕ)^4575*5000000000000^3551 ≤ 2201142085539^3551*1000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528971017 1000000000 2201142085539 5000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5448225559/10000000000 : ℝ)^4575 ≤ (45729778242801/100000000000000 : ℝ)^3551 := by
    have hnat : (5448225559 : ℕ)^4575*100000000000000^3551 ≤ 45729778242801^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5448225559 10000000000 45729778242801 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1706328161/10000000000 : ℝ)^4575 ≤ (10247380033937/100000000000000 : ℝ)^3551 := by
    have hnat : (1706328161 : ℕ)^4575*100000000000000^3551 ≤ 10247380033937^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1706328161 10000000000 10247380033937 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528971017/1000000000 : ℝ), (5448225559/10000000000 : ℝ), (-1706328161/10000000000 : ℝ)] ![(2201142085539/5000000000000 : ℝ), (45729778242801/100000000000000 : ℝ), (10247380033937/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528971017/1000000000 : ℝ)|^4575 ≤ (2201142085539/5000000000000 : ℝ)^3551
        have hw : |(528971017/1000000000 : ℝ)|=(528971017/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5448225559/10000000000 : ℝ)|^4575 ≤ (45729778242801/100000000000000 : ℝ)^3551
        have hw : |(5448225559/10000000000 : ℝ)|=(5448225559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1706328161/10000000000 : ℝ)|^4575 ≤ (10247380033937/100000000000000 : ℝ)^3551
        have hw : |(-1706328161/10000000000 : ℝ)|=(1706328161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1539_s2_7 (p : ℝ) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2127714523/5000000000 : ℝ)*x 0 + (4547353289/10000000000 : ℝ)*x 1 + (994859609/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2127714523/5000000000 : ℝ)^4575 ≤ (33261508660853/100000000000000 : ℝ)^3551 := by
    have hnat : (2127714523 : ℕ)^4575*100000000000000^3551 ≤ 33261508660853^3551*5000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2127714523 5000000000 33261508660853 100000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4547353289/10000000000 : ℝ)^4575 ≤ (3622986800907/10000000000000 : ℝ)^3551 := by
    have hnat : (4547353289 : ℕ)^4575*10000000000000^3551 ≤ 3622986800907^3551*10000000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4547353289 10000000000 3622986800907 10000000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (994859609/2500000000 : ℝ)^4575 ≤ (762715582803/2500000000000 : ℝ)^3551 := by
    have hnat : (994859609 : ℕ)^4575*2500000000000^3551 ≤ 762715582803^3551*2500000000^4575 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      994859609 2500000000 762715582803 2500000000000 4575 3551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4575/1024 : ℝ)) 4575 3551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2127714523/5000000000 : ℝ), (4547353289/10000000000 : ℝ), (994859609/2500000000 : ℝ)] ![(33261508660853/100000000000000 : ℝ), (3622986800907/10000000000000 : ℝ), (762715582803/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2127714523/5000000000 : ℝ)|^4575 ≤ (33261508660853/100000000000000 : ℝ)^3551
        have hw : |(2127714523/5000000000 : ℝ)|=(2127714523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4547353289/10000000000 : ℝ)|^4575 ≤ (3622986800907/10000000000000 : ℝ)^3551
        have hw : |(4547353289/10000000000 : ℝ)|=(4547353289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(994859609/2500000000 : ℝ)|^4575 ≤ (762715582803/2500000000000 : ℝ)^3551
        have hw : |(994859609/2500000000 : ℝ)|=(994859609/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1539_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165539681/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18051/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (272/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (1329/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7951/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18051/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (272/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18051/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (272/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18051/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (272/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18051/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (272/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18051/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (272/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18051/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (272/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (272/3125 : ℝ) ^ (4573/1024 : ℝ) ≤ (368133248799071/20000000000000000000 : ℝ) := by
    have hpowers : (272/3125 : ℝ)^4573 ≤ (368133248799071/20000000000000000000 : ℝ)^1024 := by
      have hnat : (272 : ℕ)^4573*20000000000000000000^1024 ≤ 368133248799071^1024*3125^4573 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        272 3125 368133248799071 20000000000000000000 4573 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (272/3125 : ℝ)) (X := (368133248799071/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4573 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (18051/100000 : ℝ) ^ (4573/1024 : ℝ) ≤ (47826461729405559/100000000000000000000 : ℝ) := by
    have hpowers : (18051/100000 : ℝ)^4573 ≤ (47826461729405559/100000000000000000000 : ℝ)^1024 := by
      have hnat : (18051 : ℕ)^4573*100000000000000000000^1024 ≤ 47826461729405559^1024*100000^4573 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18051 100000 47826461729405559 100000000000000000000 4573 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18051/100000 : ℝ)) (X := (47826461729405559/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4573 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000368133248799071/10000000000000000000 : ℝ) ≤ (2500020608083419/2500000000000000 : ℝ) ^ (4573/1024 : ℝ) := by
    have hpowers : (10000368133248799071/10000000000000000000 : ℝ)^1024 ≤ (2500020608083419/2500000000000000 : ℝ)^4573 := by
      have hnat : (10000368133248799071 : ℕ)^1024*2500000000000000^4573 ≤ 2500020608083419^4573*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000368133248799071 10000000000000000000 2500020608083419 2500000000000000 1024 4573 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500020608083419/2500000000000000 : ℝ)) (X := (10000368133248799071/10000000000000000000 : ℝ)) (by norm_num) 4573 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024833563986700457/50000000000000000000 : ℝ) ≤ (10001111947079983/10000000000000000 : ℝ) ^ (4573/1024 : ℝ) := by
    have hpowers : (50024833563986700457/50000000000000000000 : ℝ)^1024 ≤ (10001111947079983/10000000000000000 : ℝ)^4573 := by
      have hnat : (50024833563986700457 : ℕ)^1024*10000000000000000^4573 ≤ 10001111947079983^4573*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024833563986700457 50000000000000000000 10001111947079983 10000000000000000 1024 4573 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001111947079983/10000000000000000 : ℝ)) (X := (50024833563986700457/50000000000000000000 : ℝ)) (by norm_num) 4573 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50047826461729405559/50000000000000000000 : ℝ) ≤ (1000214146182629/1000000000000000 : ℝ) ^ (4573/1024 : ℝ) := by
    have hpowers : (50047826461729405559/50000000000000000000 : ℝ)^1024 ≤ (1000214146182629/1000000000000000 : ℝ)^4573 := by
      have hnat : (50047826461729405559 : ℕ)^1024*1000000000000000^4573 ≤ 1000214146182629^4573*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50047826461729405559 50000000000000000000 1000214146182629 1000000000000000 1024 4573 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000214146182629/1000000000000000 : ℝ)) (X := (50047826461729405559/50000000000000000000 : ℝ)) (by norm_num) 4573 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(368133248799071/20000000000000000000 : ℝ) ≤ ((23363212175579789329/23367500000000000000 : ℝ)+2*(1029514746307/934700000000000 : ℝ)*(272/3125 : ℝ))^(4573/1024 : ℝ) := by
    rw [show (23363212175579789329/23367500000000000000 : ℝ)+2*(1029514746307/934700000000000 : ℝ)*(272/3125 : ℝ)=(2500020608083419/2500000000000000 : ℝ) by norm_num, show 1+2*(368133248799071/20000000000000000000 : ℝ)=(10000368133248799071/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(47826461729405559/100000000000000000000 : ℝ)+(368133248799071/20000000000000000000 : ℝ) ≤ ((23363212175579789329/23367500000000000000 : ℝ)+(1029514746307/934700000000000 : ℝ)*((18051/100000 : ℝ)+(272/3125 : ℝ)))^(4573/1024 : ℝ) := by
    rw [show (23363212175579789329/23367500000000000000 : ℝ)+(1029514746307/934700000000000 : ℝ)*((18051/100000 : ℝ)+(272/3125 : ℝ))=(10001111947079983/10000000000000000 : ℝ) by norm_num, show 1+(47826461729405559/100000000000000000000 : ℝ)+(368133248799071/20000000000000000000 : ℝ)=(50024833563986700457/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(47826461729405559/100000000000000000000 : ℝ) ≤ ((23363212175579789329/23367500000000000000 : ℝ)+2*(1029514746307/934700000000000 : ℝ)*(18051/100000 : ℝ))^(4573/1024 : ℝ) := by
    rw [show (23363212175579789329/23367500000000000000 : ℝ)+2*(1029514746307/934700000000000 : ℝ)*(18051/100000 : ℝ)=(1000214146182629/1000000000000000 : ℝ) by norm_num, show 1+2*(47826461729405559/100000000000000000000 : ℝ)=(50047826461729405559/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (23363212175579789329/23367500000000000000 : ℝ)*(X 1 0+X 2 0)+(1029514746307/934700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4573/1024 : ℝ)) (lo := (272/3125 : ℝ)) (hi := (18051/100000 : ℝ)) (c := (23363212175579789329/23367500000000000000 : ℝ)) (alpha := (1029514746307/934700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (23363212175579789329/23367500000000000000 : ℝ)*(X 0 1+X 2 1)+(1029514746307/934700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4573/1024 : ℝ)) (lo := (272/3125 : ℝ)) (hi := (18051/100000 : ℝ)) (c := (23363212175579789329/23367500000000000000 : ℝ)) (alpha := (1029514746307/934700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (23363212175579789329/23367500000000000000 : ℝ)*(X 0 2+X 1 2)+(1029514746307/934700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4573/1024 : ℝ)) (lo := (272/3125 : ℝ)) (hi := (18051/100000 : ℝ)) (c := (23363212175579789329/23367500000000000000 : ℝ)) (alpha := (1029514746307/934700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-912858909/5000000000 : ℝ)*X 0 0+(2724878407/5000000000 : ℝ)*X 0 1+(650117737/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5355290547/10000000000 : ℝ)*X 1 0+(-1953611569/10000000000 : ℝ)*X 1 1+(1040188419/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1071058087/2000000000 : ℝ)*X 2 0+(5200942109/10000000000 : ℝ)*X 2 1+(-19536117/100000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2127661747/5000000000 : ℝ)*X 0 0+(397590133/1000000000 : ℝ)*X 0 1+(4550859633/10000000000 : ℝ)*X 0 2+(2127661747/5000000000 : ℝ)*X 1 0+(397590133/1000000000 : ℝ)*X 1 1+(4550859633/10000000000 : ℝ)*X 1 2+(2127661747/5000000000 : ℝ)*X 2 0+(397590133/1000000000 : ℝ)*X 2 1+(4550859633/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1825763947/10000000000 : ℝ)*X 0 0+(5202459133/10000000000 : ℝ)*X 0 1+(5448226109/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1322427667/2500000000 : ℝ)*X 1 0+(-1706327537/10000000000 : ℝ)*X 1 1+(5448225511/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((528971017/1000000000 : ℝ)*X 2 0+(5448225559/10000000000 : ℝ)*X 2 1+(-1706328161/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2127714523/5000000000 : ℝ)*X 0 0+(4547353289/10000000000 : ℝ)*X 0 1+(994859609/2500000000 : ℝ)*X 0 2+(2127714523/5000000000 : ℝ)*X 1 0+(4547353289/10000000000 : ℝ)*X 1 1+(994859609/2500000000 : ℝ)*X 1 2+(2127714523/5000000000 : ℝ)*X 2 0+(4547353289/10000000000 : ℝ)*X 2 1+(994859609/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1539_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (284495039724050332201380483/146046875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (103930697/25000000000000 : ℝ)*(base19) + (355798107/100000000000000 : ℝ)*(base23) + (5603813/12500000000000 : ℝ)*(upper3) + (19881201/100000000000000 : ℝ)*(lower4) + (179947911079217/6250000000000 : ℝ)*(major0) + (179947911079217/6250000000000 : ℝ)*(major1) + (179947911079217/6250000000000 : ℝ)*(major2) + (502382865345083/12500000000000 : ℝ)*(sp0) + (2009535998197287/50000000000000 : ℝ)*(sp1) + (251191937198541/6250000000000 : ℝ)*(sp2) + (869629273558051/50000000000000 : ℝ)*(sp3) + (9489356699/100000000000000 : ℝ)*(sp4) + (1061142599/100000000000000 : ℝ)*(sp6) + (1065184559/50000000000000 : ℝ)*(sp7) + (86963033874261/5000000000000 : ℝ)*(f.failure) + (2009536206058681/50000000000000 : ℝ)*(f.sum) + (250576367681/46735000000000000000000000000 : ℝ)*base66 + (469097921253960741/73023437500000000000000000000000 : ℝ)*base68 + (493763188235429491/73023437500000000000000000000000 : ℝ)*base70 + (703429076047656643/146046875000000000000000000000000 : ℝ)*base71 + (24818856448689/11683750000000000000000000000 : ℝ)*base74 + (61875352487499607/146046875000000000000000000000000 : ℝ)*base76 + (40620861101344143/146046875000000000000000000000000 : ℝ)*base77 + (25477743379454077/9127929687500000000000000000000 : ℝ)*base80 + (233942618939721/46735000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (50741/500000000000000000000 : ℝ)*base89 + (50741/500000000000000000000 : ℝ)*base91 + (50741/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2849542055564382879903282549/584187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (90845677/5000000000000 : ℝ)*(base19) + (385740411/25000000000000 : ℝ)*(base23) + (4554621/3125000000000 : ℝ)*(upper2) + (282802801/100000000000000 : ℝ)*(upper5) + (1457430315276227/50000000000000 : ℝ)*(major0) + (1457430315276227/50000000000000 : ℝ)*(major1) + (1457430315276227/50000000000000 : ℝ)*(major2) + (490845247/100000000000000 : ℝ)*(sp0) + (24095258653/100000000000000 : ℝ)*(sp1) + (5335977899/50000000000000 : ℝ)*(sp2) + (508612212029873/12500000000000 : ℝ)*(sp4) + (2034436137456019/50000000000000 : ℝ)*(sp5) + (4068885972166789/100000000000000 : ℝ)*(sp6) + (27512857991059/1562500000000 : ℝ)*(sp7) + (27512857991059/1562500000000 : ℝ)*(f.failure) + (406889818708423/10000000000000 : ℝ)*(f.sum) + (5493762051477/11683750000000000000000000000 : ℝ)*base65 + (409330157595543317/1168375000000000000000000000000000 : ℝ)*base68 + (2772883509641793317/1168375000000000000000000000000000 : ℝ)*base70 + (1310260704935418317/1168375000000000000000000000000000 : ℝ)*base72 + (15934666340143/46735000000000000000000000000 : ℝ)*base73 + (2244004373971331683/1168375000000000000000000000000000 : ℝ)*base75 + (1755016301147293317/1168375000000000000000000000000000 : ℝ)*base78 + (4116424029811831683/1168375000000000000000000000000000 : ℝ)*base79 + (170257916985733/46735000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1662821/156250000000000000000 : ℝ)*base90 + (1662821/156250000000000000000 : ℝ)*base92 + (1662821/156250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1539_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165539681/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18051/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (272/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1329/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7951/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1539_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1539_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165539681/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1329/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7951/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1539_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1539_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1539_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4573/1024 : ℝ) ≤ p) (hpb : p ≤ (4575/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165539681/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1329/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7951/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1539_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
