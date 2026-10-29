-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1564_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:25:18.159719+00:00
-- url     : https://prove2.me/submissions/30f0db71-aea1-48ff-8c19-6d43ecbd2340

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
theorem support_rectangle_w1564_s0_0 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-163204411/1000000000 : ℝ)*x 0 + (183559323/312500000 : ℝ)*x 1 + (1219234209/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (163204411/1000000000 : ℝ)^4625 ≤ (60917217357/625000000000 : ℝ)^3601 := by
    have hnat : (163204411 : ℕ)^4625*625000000000^3601 ≤ 60917217357^3601*1000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163204411 1000000000 60917217357 625000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (183559323/312500000 : ℝ)^4625 ≤ (1009827234829/2000000000000 : ℝ)^3601 := by
    have hnat : (183559323 : ℕ)^4625*2000000000000^3601 ≤ 1009827234829^3601*312500000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      183559323 312500000 1009827234829 2000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1219234209/2500000000 : ℝ)^4625 ≤ (2485117716333/6250000000000 : ℝ)^3601 := by
    have hnat : (1219234209 : ℕ)^4625*6250000000000^3601 ≤ 2485117716333^3601*2500000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1219234209 2500000000 2485117716333 6250000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-163204411/1000000000 : ℝ), (183559323/312500000 : ℝ), (1219234209/2500000000 : ℝ)] ![(60917217357/625000000000 : ℝ), (1009827234829/2000000000000 : ℝ), (2485117716333/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-163204411/1000000000 : ℝ)|^4625 ≤ (60917217357/625000000000 : ℝ)^3601
        have hw : |(-163204411/1000000000 : ℝ)|=(163204411/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(183559323/312500000 : ℝ)|^4625 ≤ (1009827234829/2000000000000 : ℝ)^3601
        have hw : |(183559323/312500000 : ℝ)|=(183559323/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1219234209/2500000000 : ℝ)|^4625 ≤ (2485117716333/6250000000000 : ℝ)^3601
        have hw : |(1219234209/2500000000 : ℝ)|=(1219234209/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_s0_1 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5466759827/10000000000 : ℝ)*x 0 + (-21872363/100000000 : ℝ)*x 1 + (4876936839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5466759827/10000000000 : ℝ)^4625 ≤ (46041500090573/100000000000000 : ℝ)^3601 := by
    have hnat : (5466759827 : ℕ)^4625*100000000000000^3601 ≤ 46041500090573^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5466759827 10000000000 46041500090573 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21872363/100000000 : ℝ)^4625 ≤ (7098308196029/50000000000000 : ℝ)^3601 := by
    have hnat : (21872363 : ℕ)^4625*50000000000000^3601 ≤ 7098308196029^3601*100000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21872363 100000000 7098308196029 50000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4876936839/10000000000 : ℝ)^4625 ≤ (19880941746371/50000000000000 : ℝ)^3601 := by
    have hnat : (4876936839 : ℕ)^4625*50000000000000^3601 ≤ 19880941746371^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4876936839 10000000000 19880941746371 50000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5466759827/10000000000 : ℝ), (-21872363/100000000 : ℝ), (4876936839/10000000000 : ℝ)] ![(46041500090573/100000000000000 : ℝ), (7098308196029/50000000000000 : ℝ), (19880941746371/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5466759827/10000000000 : ℝ)|^4625 ≤ (46041500090573/100000000000000 : ℝ)^3601
        have hw : |(5466759827/10000000000 : ℝ)|=(5466759827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-21872363/100000000 : ℝ)|^4625 ≤ (7098308196029/50000000000000 : ℝ)^3601
        have hw : |(-21872363/100000000 : ℝ)|=(21872363/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4876936839/10000000000 : ℝ)|^4625 ≤ (19880941746371/50000000000000 : ℝ)^3601
        have hw : |(4876936839/10000000000 : ℝ)|=(4876936839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_s0_2 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5466759877/10000000000 : ℝ)*x 0 + (2438468391/5000000000 : ℝ)*x 1 + (-546809077/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5466759877/10000000000 : ℝ)^4625 ≤ (1841660025257/4000000000000 : ℝ)^3601 := by
    have hnat : (5466759877 : ℕ)^4625*4000000000000^3601 ≤ 1841660025257^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5466759877 10000000000 1841660025257 4000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2438468391/5000000000 : ℝ)^4625 ≤ (39761882895867/100000000000000 : ℝ)^3601 := by
    have hnat : (2438468391 : ℕ)^4625*100000000000000^3601 ≤ 39761882895867^3601*5000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2438468391 5000000000 39761882895867 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (546809077/2500000000 : ℝ)^4625 ≤ (14196616458749/100000000000000 : ℝ)^3601 := by
    have hnat : (546809077 : ℕ)^4625*100000000000000^3601 ≤ 14196616458749^3601*2500000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546809077 2500000000 14196616458749 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5466759877/10000000000 : ℝ), (2438468391/5000000000 : ℝ), (-546809077/2500000000 : ℝ)] ![(1841660025257/4000000000000 : ℝ), (39761882895867/100000000000000 : ℝ), (14196616458749/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5466759877/10000000000 : ℝ)|^4625 ≤ (1841660025257/4000000000000 : ℝ)^3601
        have hw : |(5466759877/10000000000 : ℝ)|=(5466759877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2438468391/5000000000 : ℝ)|^4625 ≤ (39761882895867/100000000000000 : ℝ)^3601
        have hw : |(2438468391/5000000000 : ℝ)|=(2438468391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-546809077/2500000000 : ℝ)|^4625 ≤ (14196616458749/100000000000000 : ℝ)^3601
        have hw : |(-546809077/2500000000 : ℝ)|=(546809077/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_s0_3 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (206570111/500000000 : ℝ)*x 0 + (193302469/625000000 : ℝ)*x 1 + (2718306357/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (206570111/500000000 : ℝ)^4625 ≤ (31378263601/97656250000 : ℝ)^3601 := by
    have hnat : (206570111 : ℕ)^4625*97656250000^3601 ≤ 31378263601^3601*500000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206570111 500000000 31378263601 97656250000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (193302469/625000000 : ℝ)^4625 ≤ (22153004203421/100000000000000 : ℝ)^3601 := by
    have hnat : (193302469 : ℕ)^4625*100000000000000^3601 ≤ 22153004203421^3601*625000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      193302469 625000000 22153004203421 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2718306357/5000000000 : ℝ)^4625 ≤ (9143130770861/20000000000000 : ℝ)^3601 := by
    have hnat : (2718306357 : ℕ)^4625*20000000000000^3601 ≤ 9143130770861^3601*5000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718306357 5000000000 9143130770861 20000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(206570111/500000000 : ℝ), (193302469/625000000 : ℝ), (2718306357/5000000000 : ℝ)] ![(31378263601/97656250000 : ℝ), (22153004203421/100000000000000 : ℝ), (9143130770861/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(206570111/500000000 : ℝ)|^4625 ≤ (31378263601/97656250000 : ℝ)^3601
        have hw : |(206570111/500000000 : ℝ)|=(206570111/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(193302469/625000000 : ℝ)|^4625 ≤ (22153004203421/100000000000000 : ℝ)^3601
        have hw : |(193302469/625000000 : ℝ)|=(193302469/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2718306357/5000000000 : ℝ)|^4625 ≤ (9143130770861/20000000000000 : ℝ)^3601
        have hw : |(2718306357/5000000000 : ℝ)|=(2718306357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_s0_4 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1635144051/10000000000 : ℝ)*x 0 + (980419211/2000000000 : ℝ)*x 1 + (584784703/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1635144051/10000000000 : ℝ)^4625 ≤ (9770538914779/100000000000000 : ℝ)^3601 := by
    have hnat : (1635144051 : ℕ)^4625*100000000000000^3601 ≤ 9770538914779^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1635144051 10000000000 9770538914779 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (980419211/2000000000 : ℝ)^4625 ≤ (40025530946687/100000000000000 : ℝ)^3601 := by
    have hnat : (980419211 : ℕ)^4625*100000000000000^3601 ≤ 40025530946687^3601*2000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      980419211 2000000000 40025530946687 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (584784703/1000000000 : ℝ)^4625 ≤ (25101965063727/50000000000000 : ℝ)^3601 := by
    have hnat : (584784703 : ℕ)^4625*50000000000000^3601 ≤ 25101965063727^3601*1000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      584784703 1000000000 25101965063727 50000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1635144051/10000000000 : ℝ), (980419211/2000000000 : ℝ), (584784703/1000000000 : ℝ)] ![(9770538914779/100000000000000 : ℝ), (40025530946687/100000000000000 : ℝ), (25101965063727/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1635144051/10000000000 : ℝ)|^4625 ≤ (9770538914779/100000000000000 : ℝ)^3601
        have hw : |(-1635144051/10000000000 : ℝ)|=(1635144051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(980419211/2000000000 : ℝ)|^4625 ≤ (40025530946687/100000000000000 : ℝ)^3601
        have hw : |(980419211/2000000000 : ℝ)|=(980419211/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(584784703/1000000000 : ℝ)|^4625 ≤ (25101965063727/50000000000000 : ℝ)^3601
        have hw : |(584784703/1000000000 : ℝ)|=(584784703/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_s0_5 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5194226121/10000000000 : ℝ)*x 0 + (-608162471/5000000000 : ℝ)*x 1 + (1169569347/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5194226121/10000000000 : ℝ)^4625 ≤ (10778661132529/25000000000000 : ℝ)^3601 := by
    have hnat : (5194226121 : ℕ)^4625*25000000000000^3601 ≤ 10778661132529^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5194226121 10000000000 10778661132529 25000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (608162471/5000000000 : ℝ)^4625 ≤ (3340714287467/50000000000000 : ℝ)^3601 := by
    have hnat : (608162471 : ℕ)^4625*50000000000000^3601 ≤ 3340714287467^3601*5000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      608162471 5000000000 3340714287467 50000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1169569347/2000000000 : ℝ)^4625 ≤ (50203926874691/100000000000000 : ℝ)^3601 := by
    have hnat : (1169569347 : ℕ)^4625*100000000000000^3601 ≤ 50203926874691^3601*2000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1169569347 2000000000 50203926874691 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5194226121/10000000000 : ℝ), (-608162471/5000000000 : ℝ), (1169569347/2000000000 : ℝ)] ![(10778661132529/25000000000000 : ℝ), (3340714287467/50000000000000 : ℝ), (50203926874691/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5194226121/10000000000 : ℝ)|^4625 ≤ (10778661132529/25000000000000 : ℝ)^3601
        have hw : |(5194226121/10000000000 : ℝ)|=(5194226121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-608162471/5000000000 : ℝ)|^4625 ≤ (3340714287467/50000000000000 : ℝ)^3601
        have hw : |(-608162471/5000000000 : ℝ)|=(608162471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1169569347/2000000000 : ℝ)|^4625 ≤ (50203926874691/100000000000000 : ℝ)^3601
        have hw : |(1169569347/2000000000 : ℝ)|=(1169569347/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_s0_6 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (519422449/1000000000 : ℝ)*x 0 + (1461961999/2500000000 : ℝ)*x 1 + (-1216325437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (519422449/1000000000 : ℝ)^4625 ≤ (43114627142241/100000000000000 : ℝ)^3601 := by
    have hnat : (519422449 : ℕ)^4625*100000000000000^3601 ≤ 43114627142241^3601*1000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519422449 1000000000 43114627142241 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1461961999/2500000000 : ℝ)^4625 ≤ (6275492597359/12500000000000 : ℝ)^3601 := by
    have hnat : (1461961999 : ℕ)^4625*12500000000000^3601 ≤ 6275492597359^3601*2500000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1461961999 2500000000 6275492597359 12500000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1216325437/10000000000 : ℝ)^4625 ≤ (26725728269/400000000000 : ℝ)^3601 := by
    have hnat : (1216325437 : ℕ)^4625*400000000000^3601 ≤ 26725728269^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1216325437 10000000000 26725728269 400000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(519422449/1000000000 : ℝ), (1461961999/2500000000 : ℝ), (-1216325437/10000000000 : ℝ)] ![(43114627142241/100000000000000 : ℝ), (6275492597359/12500000000000 : ℝ), (26725728269/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(519422449/1000000000 : ℝ)|^4625 ≤ (43114627142241/100000000000000 : ℝ)^3601
        have hw : |(519422449/1000000000 : ℝ)|=(519422449/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1461961999/2500000000 : ℝ)|^4625 ≤ (6275492597359/12500000000000 : ℝ)^3601
        have hw : |(1461961999/2500000000 : ℝ)|=(1461961999/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1216325437/10000000000 : ℝ)|^4625 ≤ (26725728269/400000000000 : ℝ)^3601
        have hw : |(-1216325437/10000000000 : ℝ)|=(1216325437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_s0_7 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4138687709/10000000000 : ℝ)*x 0 + (5377466591/10000000000 : ℝ)*x 1 + (315408397/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4138687709/10000000000 : ℝ)^4625 ≤ (16102067289493/50000000000000 : ℝ)^3601 := by
    have hnat : (4138687709 : ℕ)^4625*50000000000000^3601 ≤ 16102067289493^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4138687709 10000000000 16102067289493 50000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5377466591/10000000000 : ℝ)^4625 ≤ (45077864332999/100000000000000 : ℝ)^3601 := by
    have hnat : (5377466591 : ℕ)^4625*100000000000000^3601 ≤ 45077864332999^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377466591 10000000000 45077864332999 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (315408397/1000000000 : ℝ)^4625 ≤ (5679500268691/25000000000000 : ℝ)^3601 := by
    have hnat : (315408397 : ℕ)^4625*25000000000000^3601 ≤ 5679500268691^3601*1000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      315408397 1000000000 5679500268691 25000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4138687709/10000000000 : ℝ), (5377466591/10000000000 : ℝ), (315408397/1000000000 : ℝ)] ![(16102067289493/50000000000000 : ℝ), (45077864332999/100000000000000 : ℝ), (5679500268691/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4138687709/10000000000 : ℝ)|^4625 ≤ (16102067289493/50000000000000 : ℝ)^3601
        have hw : |(4138687709/10000000000 : ℝ)|=(4138687709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5377466591/10000000000 : ℝ)|^4625 ≤ (45077864332999/100000000000000 : ℝ)^3601
        have hw : |(5377466591/10000000000 : ℝ)|=(5377466591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(315408397/1000000000 : ℝ)|^4625 ≤ (5679500268691/25000000000000 : ℝ)^3601
        have hw : |(315408397/1000000000 : ℝ)|=(315408397/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1564_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5235807/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (3473/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6207/25000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4623/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4623 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4623*1^1024 ≤ 0^1024*1^4623 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4623 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4623 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4623/1024 : ℝ) ≤ (1597499613033073689/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4623 ≤ (1597499613033073689/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4623*100000000000000000000^1024 ≤ 1597499613033073689^1024*5^4623 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1597499613033073689 100000000000000000000 4623 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1597499613033073689/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4623 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4623/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4623 := by
      have hnat : (1 : ℕ)^1024*1^4623 ≤ 1^4623*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4623 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4623 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101597499613033073689/100000000000000000000 : ℝ) ≤ (10035166835601779/10000000000000000 : ℝ) ^ (4623/1024 : ℝ) := by
    have hpowers : (101597499613033073689/100000000000000000000 : ℝ)^1024 ≤ (10035166835601779/10000000000000000 : ℝ)^4623 := by
      have hnat : (101597499613033073689 : ℕ)^1024*10000000000000000^4623 ≤ 10035166835601779^4623*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101597499613033073689 100000000000000000000 10035166835601779 10000000000000000 1024 4623 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10035166835601779/10000000000000000 : ℝ)) (X := (101597499613033073689/100000000000000000000 : ℝ)) (by norm_num) 4623 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51597499613033073689/50000000000000000000 : ℝ) ≤ (5035166835601779/5000000000000000 : ℝ) ^ (4623/1024 : ℝ) := by
    have hpowers : (51597499613033073689/50000000000000000000 : ℝ)^1024 ≤ (5035166835601779/5000000000000000 : ℝ)^4623 := by
      have hnat : (51597499613033073689 : ℕ)^1024*5000000000000000^4623 ≤ 5035166835601779^4623*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51597499613033073689 50000000000000000000 5035166835601779 5000000000000000 1024 4623 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5035166835601779/5000000000000000 : ℝ)) (X := (51597499613033073689/50000000000000000000 : ℝ)) (by norm_num) 4623 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(35166835601779/4000000000000000 : ℝ)*(0 : ℝ))^(4623/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(35166835601779/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1597499613033073689/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(35166835601779/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4623/1024 : ℝ) := by
    rw [show (1 : ℝ)+(35166835601779/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10035166835601779/10000000000000000 : ℝ) by norm_num, show 1+(1597499613033073689/100000000000000000000 : ℝ)+(0 : ℝ)=(101597499613033073689/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1597499613033073689/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(35166835601779/4000000000000000 : ℝ)*(2/5 : ℝ))^(4623/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(35166835601779/4000000000000000 : ℝ)*(2/5 : ℝ)=(5035166835601779/5000000000000000 : ℝ) by norm_num, show 1+2*(1597499613033073689/100000000000000000000 : ℝ)=(51597499613033073689/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(35166835601779/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4623/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (35166835601779/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(35166835601779/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4623/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (35166835601779/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(35166835601779/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4623/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (35166835601779/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-163204411/1000000000 : ℝ)*X 0 0+(183559323/312500000 : ℝ)*X 0 1+(1219234209/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5466759827/10000000000 : ℝ)*X 1 0+(-21872363/100000000 : ℝ)*X 1 1+(4876936839/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5466759877/10000000000 : ℝ)*X 2 0+(2438468391/5000000000 : ℝ)*X 2 1+(-546809077/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((206570111/500000000 : ℝ)*X 0 0+(193302469/625000000 : ℝ)*X 0 1+(2718306357/5000000000 : ℝ)*X 0 2+(206570111/500000000 : ℝ)*X 1 0+(193302469/625000000 : ℝ)*X 1 1+(2718306357/5000000000 : ℝ)*X 1 2+(206570111/500000000 : ℝ)*X 2 0+(193302469/625000000 : ℝ)*X 2 1+(2718306357/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1635144051/10000000000 : ℝ)*X 0 0+(980419211/2000000000 : ℝ)*X 0 1+(584784703/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5194226121/10000000000 : ℝ)*X 1 0+(-608162471/5000000000 : ℝ)*X 1 1+(1169569347/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((519422449/1000000000 : ℝ)*X 2 0+(1461961999/2500000000 : ℝ)*X 2 1+(-1216325437/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4138687709/10000000000 : ℝ)*X 0 0+(5377466591/10000000000 : ℝ)*X 0 1+(315408397/1000000000 : ℝ)*X 0 2+(4138687709/10000000000 : ℝ)*X 1 0+(5377466591/10000000000 : ℝ)*X 1 1+(315408397/1000000000 : ℝ)*X 1 2+(4138687709/10000000000 : ℝ)*X 2 0+(5377466591/10000000000 : ℝ)*X 2 1+(315408397/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (196248331741822421231193/40000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (23276481/50000000000000 : ℝ)*(base1) + (254069501/25000000000000 : ℝ)*(base19) + (512726061/50000000000000 : ℝ)*(base23) + (131513553/100000000000000 : ℝ)*(upper3) + (131824727/100000000000000 : ℝ)*(upper5) + (714860419557311/100000000000000 : ℝ)*(major0) + (714860419557311/100000000000000 : ℝ)*(major1) + (714860419557311/100000000000000 : ℝ)*(major2) + (1003051330444827/100000000000000 : ℝ)*(sp0) + (501527022392611/50000000000000 : ℝ)*(sp1) + (1003054035611103/100000000000000 : ℝ)*(sp2) + (426663961544923/100000000000000 : ℝ)*(sp3) + (3777171361/100000000000000 : ℝ)*(sp4) + (1606413229/100000000000000 : ℝ)*(sp7) + (85333122902223/20000000000000 : ℝ)*(f.failure) + (501527530531613/50000000000000 : ℝ)*(f.sum) + (353963656056269/200000000000000000000000000000 : ℝ)*base65 + (203337760856269/400000000000000000000000000000 : ℝ)*base67 + (1703143322456269/400000000000000000000000000000 : ℝ)*base69 + (148558258056269/400000000000000000000000000000 : ℝ)*base71 + (367199077856269/200000000000000000000000000000 : ℝ)*base73 + (187951899943731/400000000000000000000000000000 : ℝ)*base76 + (1515263163256269/400000000000000000000000000000 : ℝ)*base77 + (3084897033256269/400000000000000000000000000000 : ℝ)*base79 + (557548978456269/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (123961/62500000000000000000 : ℝ)*base89 + (123961/62500000000000000000 : ℝ)*base91 + (123961/62500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (74233961464139598543249/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1215265589/100000000000000 : ℝ)*(base19) + (597282383/50000000000000 : ℝ)*(base23) + (389034611/100000000000000 : ℝ)*(base39) + (49478369/100000000000000 : ℝ)*(upper3) + (250956473/100000000000000 : ℝ)*(upper5) + (376780695513071/50000000000000 : ℝ)*(major0) + (376780695513071/50000000000000 : ℝ)*(major1) + (188390250497883/25000000000000 : ℝ)*(major2) + (4366280277/100000000000000 : ℝ)*(sp1) + (3010442731/100000000000000 : ℝ)*(sp2) + (211471568443837/20000000000000 : ℝ)*(sp4) + (1057352260673319/100000000000000 : ℝ)*(sp5) + (528677013123149/50000000000000 : ℝ)*(sp6) + (112441088210313/25000000000000 : ℝ)*(sp7) + (112441088210313/25000000000000 : ℝ)*(f.failure) + (264339557813449/25000000000000 : ℝ)*(f.sum) + (227855860178977/200000000000000000000000000000 : ℝ)*base66 + (1163178040166143/100000000000000000000000000000 : ℝ)*base68 + (781474752646691/200000000000000000000000000000 : ℝ)*base70 + (504552264066143/100000000000000000000000000000 : ℝ)*base72 + (1272812080378977/200000000000000000000000000000 : ℝ)*base74 + (802458216246691/200000000000000000000000000000 : ℝ)*base76 + (1193857309646691/200000000000000000000000000000 : ℝ)*base78 + (408987031046691/200000000000000000000000000000 : ℝ)*base80 + (342191661246691/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (840091/78125000000000000000 : ℝ)*base89 + (840091/78125000000000000000 : ℝ)*base91 + (58841/78125000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1564_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5235807/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3473/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6207/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1564_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1564_s1_0 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-443042213/2500000000 : ℝ)*x 0 + (346141763/625000000 : ℝ)*x 1 + (1280569513/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (443042213/2500000000 : ℝ)^4625 ≤ (10834426066343/100000000000000 : ℝ)^3601 := by
    have hnat : (443042213 : ℕ)^4625*100000000000000^3601 ≤ 10834426066343^3601*2500000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      443042213 2500000000 10834426066343 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (346141763/625000000 : ℝ)^4625 ≤ (46816442618261/100000000000000 : ℝ)^3601 := by
    have hnat : (346141763 : ℕ)^4625*100000000000000^3601 ≤ 46816442618261^3601*625000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      346141763 625000000 46816442618261 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1280569513/2500000000 : ℝ)^4625 ≤ (42349131297293/100000000000000 : ℝ)^3601 := by
    have hnat : (1280569513 : ℕ)^4625*100000000000000^3601 ≤ 42349131297293^3601*2500000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1280569513 2500000000 42349131297293 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-443042213/2500000000 : ℝ), (346141763/625000000 : ℝ), (1280569513/2500000000 : ℝ)] ![(10834426066343/100000000000000 : ℝ), (46816442618261/100000000000000 : ℝ), (42349131297293/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-443042213/2500000000 : ℝ)|^4625 ≤ (10834426066343/100000000000000 : ℝ)^3601
        have hw : |(-443042213/2500000000 : ℝ)|=(443042213/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(346141763/625000000 : ℝ)|^4625 ≤ (46816442618261/100000000000000 : ℝ)^3601
        have hw : |(346141763/625000000 : ℝ)|=(346141763/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1280569513/2500000000 : ℝ)|^4625 ≤ (42349131297293/100000000000000 : ℝ)^3601
        have hw : |(1280569513/2500000000 : ℝ)|=(1280569513/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_s1_1 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1075491277/2000000000 : ℝ)*x 0 + (-1989899321/10000000000 : ℝ)*x 1 + (5122277969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075491277/2000000000 : ℝ)^4625 ≤ (4507775445021/10000000000000 : ℝ)^3601 := by
    have hnat : (1075491277 : ℕ)^4625*10000000000000^3601 ≤ 4507775445021^3601*2000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075491277 2000000000 4507775445021 10000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1989899321/10000000000 : ℝ)^4625 ≤ (3143278782287/25000000000000 : ℝ)^3601 := by
    have hnat : (1989899321 : ℕ)^4625*25000000000000^3601 ≤ 3143278782287^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1989899321 10000000000 3143278782287 25000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5122277969/10000000000 : ℝ)^4625 ≤ (42349130415943/100000000000000 : ℝ)^3601 := by
    have hnat : (5122277969 : ℕ)^4625*100000000000000^3601 ≤ 42349130415943^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5122277969 10000000000 42349130415943 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075491277/2000000000 : ℝ), (-1989899321/10000000000 : ℝ), (5122277969/10000000000 : ℝ)] ![(4507775445021/10000000000000 : ℝ), (3143278782287/25000000000000 : ℝ), (42349130415943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075491277/2000000000 : ℝ)|^4625 ≤ (4507775445021/10000000000000 : ℝ)^3601
        have hw : |(1075491277/2000000000 : ℝ)|=(1075491277/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1989899321/10000000000 : ℝ)|^4625 ≤ (3143278782287/25000000000000 : ℝ)^3601
        have hw : |(-1989899321/10000000000 : ℝ)|=(1989899321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5122277969/10000000000 : ℝ)|^4625 ≤ (42349130415943/100000000000000 : ℝ)^3601
        have hw : |(5122277969/10000000000 : ℝ)|=(5122277969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_s1_2 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (537745629/1000000000 : ℝ)*x 0 + (5122278437/10000000000 : ℝ)*x 1 + (-994949417/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537745629/1000000000 : ℝ)^4625 ≤ (45077753427393/100000000000000 : ℝ)^3601 := by
    have hnat : (537745629 : ℕ)^4625*100000000000000^3601 ≤ 45077753427393^3601*1000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537745629 1000000000 45077753427393 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5122278437/10000000000 : ℝ)^4625 ≤ (42349135385479/100000000000000 : ℝ)^3601 := by
    have hnat : (5122278437 : ℕ)^4625*100000000000000^3601 ≤ 42349135385479^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5122278437 10000000000 42349135385479 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (994949417/5000000000 : ℝ)^4625 ≤ (2514622235407/20000000000000 : ℝ)^3601 := by
    have hnat : (994949417 : ℕ)^4625*20000000000000^3601 ≤ 2514622235407^3601*5000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      994949417 5000000000 2514622235407 20000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537745629/1000000000 : ℝ), (5122278437/10000000000 : ℝ), (-994949417/5000000000 : ℝ)] ![(45077753427393/100000000000000 : ℝ), (42349135385479/100000000000000 : ℝ), (2514622235407/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537745629/1000000000 : ℝ)|^4625 ≤ (45077753427393/100000000000000 : ℝ)^3601
        have hw : |(537745629/1000000000 : ℝ)|=(537745629/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5122278437/10000000000 : ℝ)|^4625 ≤ (42349135385479/100000000000000 : ℝ)^3601
        have hw : |(5122278437/10000000000 : ℝ)|=(5122278437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-994949417/5000000000 : ℝ)|^4625 ≤ (2514622235407/20000000000000 : ℝ)^3601
        have hw : |(-994949417/5000000000 : ℝ)|=(994949417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_s1_3 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1057661073/2500000000 : ℝ)*x 0 + (1882275783/5000000000 : ℝ)*x 1 + (148203461/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057661073/2500000000 : ℝ)^4625 ≤ (16563016492627/50000000000000 : ℝ)^3601 := by
    have hnat : (1057661073 : ℕ)^4625*50000000000000^3601 ≤ 16563016492627^3601*2500000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057661073 2500000000 16563016492627 50000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1882275783/5000000000 : ℝ)^4625 ≤ (14257085711547/50000000000000 : ℝ)^3601 := by
    have hnat : (1882275783 : ℕ)^4625*50000000000000^3601 ≤ 14257085711547^3601*5000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1882275783 5000000000 14257085711547 50000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (148203461/312500000 : ℝ)^4625 ≤ (38359795582681/100000000000000 : ℝ)^3601 := by
    have hnat : (148203461 : ℕ)^4625*100000000000000^3601 ≤ 38359795582681^3601*312500000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      148203461 312500000 38359795582681 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057661073/2500000000 : ℝ), (1882275783/5000000000 : ℝ), (148203461/312500000 : ℝ)] ![(16563016492627/50000000000000 : ℝ), (14257085711547/50000000000000 : ℝ), (38359795582681/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057661073/2500000000 : ℝ)|^4625 ≤ (16563016492627/50000000000000 : ℝ)^3601
        have hw : |(1057661073/2500000000 : ℝ)|=(1057661073/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1882275783/5000000000 : ℝ)|^4625 ≤ (14257085711547/50000000000000 : ℝ)^3601
        have hw : |(1882275783/5000000000 : ℝ)|=(1882275783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(148203461/312500000 : ℝ)|^4625 ≤ (38359795582681/100000000000000 : ℝ)^3601
        have hw : |(148203461/312500000 : ℝ)|=(148203461/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_s1_4 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1772387901/10000000000 : ℝ)*x 0 + (640825647/1250000000 : ℝ)*x 1 + (221355067/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1772387901/10000000000 : ℝ)^4625 ≤ (10836146105501/100000000000000 : ℝ)^3601 := by
    have hnat : (1772387901 : ℕ)^4625*100000000000000^3601 ≤ 10836146105501^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1772387901 10000000000 10836146105501 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (640825647/1250000000 : ℝ)^4625 ≤ (42395085100803/100000000000000 : ℝ)^3601 := by
    have hnat : (640825647 : ℕ)^4625*100000000000000^3601 ≤ 42395085100803^3601*1250000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      640825647 1250000000 42395085100803 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (221355067/400000000 : ℝ)^4625 ≤ (46768768769203/100000000000000 : ℝ)^3601 := by
    have hnat : (221355067 : ℕ)^4625*100000000000000^3601 ≤ 46768768769203^3601*400000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221355067 400000000 46768768769203 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1772387901/10000000000 : ℝ), (640825647/1250000000 : ℝ), (221355067/400000000 : ℝ)] ![(10836146105501/100000000000000 : ℝ), (42395085100803/100000000000000 : ℝ), (46768768769203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1772387901/10000000000 : ℝ)|^4625 ≤ (10836146105501/100000000000000 : ℝ)^3601
        have hw : |(-1772387901/10000000000 : ℝ)|=(1772387901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(640825647/1250000000 : ℝ)|^4625 ≤ (42395085100803/100000000000000 : ℝ)^3601
        have hw : |(640825647/1250000000 : ℝ)|=(640825647/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(221355067/400000000 : ℝ)|^4625 ≤ (46768768769203/100000000000000 : ℝ)^3601
        have hw : |(221355067/400000000 : ℝ)|=(221355067/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_s1_5 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1053451263/2000000000 : ℝ)*x 0 + (-1578300459/10000000000 : ℝ)*x 1 + (2766938523/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1053451263/2000000000 : ℝ)^4625 ≤ (43894761021097/100000000000000 : ℝ)^3601 := by
    have hnat : (1053451263 : ℕ)^4625*100000000000000^3601 ≤ 43894761021097^3601*2000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053451263 2000000000 43894761021097 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1578300459/10000000000 : ℝ)^4625 ≤ (93364661701/1000000000000 : ℝ)^3601 := by
    have hnat : (1578300459 : ℕ)^4625*1000000000000^3601 ≤ 93364661701^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1578300459 10000000000 93364661701 1000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2766938523/5000000000 : ℝ)^4625 ≤ (46768772796271/100000000000000 : ℝ)^3601 := by
    have hnat : (2766938523 : ℕ)^4625*100000000000000^3601 ≤ 46768772796271^3601*5000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2766938523 5000000000 46768772796271 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1053451263/2000000000 : ℝ), (-1578300459/10000000000 : ℝ), (2766938523/5000000000 : ℝ)] ![(43894761021097/100000000000000 : ℝ), (93364661701/1000000000000 : ℝ), (46768772796271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1053451263/2000000000 : ℝ)|^4625 ≤ (43894761021097/100000000000000 : ℝ)^3601
        have hw : |(1053451263/2000000000 : ℝ)|=(1053451263/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1578300459/10000000000 : ℝ)|^4625 ≤ (93364661701/1000000000000 : ℝ)^3601
        have hw : |(-1578300459/10000000000 : ℝ)|=(1578300459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2766938523/5000000000 : ℝ)|^4625 ≤ (46768772796271/100000000000000 : ℝ)^3601
        have hw : |(2766938523/5000000000 : ℝ)|=(2766938523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_s1_6 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1053451183/2000000000 : ℝ)*x 0 + (1383469297/2500000000 : ℝ)*x 1 + (-78915041/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1053451183/2000000000 : ℝ)^4625 ≤ (8778951347957/20000000000000 : ℝ)^3601 := by
    have hnat : (1053451183 : ℕ)^4625*20000000000000^3601 ≤ 8778951347957^3601*2000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053451183 2000000000 8778951347957 20000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1383469297/2500000000 : ℝ)^4625 ≤ (46768774337629/100000000000000 : ℝ)^3601 := by
    have hnat : (1383469297 : ℕ)^4625*100000000000000^3601 ≤ 46768774337629^3601*2500000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1383469297 2500000000 46768774337629 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (78915041/500000000 : ℝ)^4625 ≤ (1867293782573/20000000000000 : ℝ)^3601 := by
    have hnat : (78915041 : ℕ)^4625*20000000000000^3601 ≤ 1867293782573^3601*500000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      78915041 500000000 1867293782573 20000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1053451183/2000000000 : ℝ), (1383469297/2500000000 : ℝ), (-78915041/500000000 : ℝ)] ![(8778951347957/20000000000000 : ℝ), (46768774337629/100000000000000 : ℝ), (1867293782573/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1053451183/2000000000 : ℝ)|^4625 ≤ (8778951347957/20000000000000 : ℝ)^3601
        have hw : |(1053451183/2000000000 : ℝ)|=(1053451183/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1383469297/2500000000 : ℝ)|^4625 ≤ (46768774337629/100000000000000 : ℝ)^3601
        have hw : |(1383469297/2500000000 : ℝ)|=(1383469297/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-78915041/500000000 : ℝ)|^4625 ≤ (1867293782573/20000000000000 : ℝ)^3601
        have hw : |(-78915041/500000000 : ℝ)|=(78915041/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_s1_7 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (528894763/1250000000 : ℝ)*x 0 + (2366169203/5000000000 : ℝ)*x 1 + (3774875861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528894763/1250000000 : ℝ)^4625 ≤ (3313120028049/10000000000000 : ℝ)^3601 := by
    have hnat : (528894763 : ℕ)^4625*10000000000000^3601 ≤ 3313120028049^3601*1250000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528894763 1250000000 3313120028049 10000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2366169203/5000000000 : ℝ)^4625 ≤ (19127075751531/50000000000000 : ℝ)^3601 := by
    have hnat : (2366169203 : ℕ)^4625*50000000000000^3601 ≤ 19127075751531^3601*5000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2366169203 5000000000 19127075751531 50000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3774875861/10000000000 : ℝ)^4625 ≤ (28614648208141/100000000000000 : ℝ)^3601 := by
    have hnat : (3774875861 : ℕ)^4625*100000000000000^3601 ≤ 28614648208141^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3774875861 10000000000 28614648208141 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528894763/1250000000 : ℝ), (2366169203/5000000000 : ℝ), (3774875861/10000000000 : ℝ)] ![(3313120028049/10000000000000 : ℝ), (19127075751531/50000000000000 : ℝ), (28614648208141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528894763/1250000000 : ℝ)|^4625 ≤ (3313120028049/10000000000000 : ℝ)^3601
        have hw : |(528894763/1250000000 : ℝ)|=(528894763/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2366169203/5000000000 : ℝ)|^4625 ≤ (19127075751531/50000000000000 : ℝ)^3601
        have hw : |(2366169203/5000000000 : ℝ)|=(2366169203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3774875861/10000000000 : ℝ)|^4625 ≤ (28614648208141/100000000000000 : ℝ)^3601
        have hw : |(3774875861/10000000000 : ℝ)|=(3774875861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1564_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5235807/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6207/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3473/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9001/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1781/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6207/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3473/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6207/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3473/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6207/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3473/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6207/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3473/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6207/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3473/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6207/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3473/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3473/100000 : ℝ) ^ (4623/1024 : ℝ) ≤ (25810423474639/100000000000000000000 : ℝ) := by
    have hpowers : (3473/100000 : ℝ)^4623 ≤ (25810423474639/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3473 : ℕ)^4623*100000000000000000000^1024 ≤ 25810423474639^1024*100000^4623 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3473 100000 25810423474639 100000000000000000000 4623 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3473/100000 : ℝ)) (X := (25810423474639/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4623 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (6207/25000 : ℝ) ^ (4623/1024 : ℝ) ≤ (2318914146913839/1250000000000000000 : ℝ) := by
    have hpowers : (6207/25000 : ℝ)^4623 ≤ (2318914146913839/1250000000000000000 : ℝ)^1024 := by
      have hnat : (6207 : ℕ)^4623*1250000000000000000^1024 ≤ 2318914146913839^1024*25000^4623 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6207 25000 2318914146913839 1250000000000000000 4623 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6207/25000 : ℝ)) (X := (2318914146913839/1250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4623 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000025810423474639/50000000000000000000 : ℝ) ≤ (1250000142925959/1250000000000000 : ℝ) ^ (4623/1024 : ℝ) := by
    have hpowers : (50000025810423474639/50000000000000000000 : ℝ)^1024 ≤ (1250000142925959/1250000000000000 : ℝ)^4623 := by
      have hnat : (50000025810423474639 : ℕ)^1024*1250000000000000^4623 ≤ 1250000142925959^4623*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000025810423474639 50000000000000000000 1250000142925959 1250000000000000 1024 4623 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250000142925959/1250000000000000 : ℝ)) (X := (50000025810423474639/50000000000000000000 : ℝ)) (by norm_num) 4623 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100185538942176581759/100000000000000000000 : ℝ) ≤ (5002053372416551/5000000000000000 : ℝ) ^ (4623/1024 : ℝ) := by
    have hpowers : (100185538942176581759/100000000000000000000 : ℝ)^1024 ≤ (5002053372416551/5000000000000000 : ℝ)^4623 := by
      have hnat : (100185538942176581759 : ℕ)^1024*5000000000000000^4623 ≤ 5002053372416551^4623*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100185538942176581759 100000000000000000000 5002053372416551 5000000000000000 1024 4623 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002053372416551/5000000000000000 : ℝ)) (X := (100185538942176581759/100000000000000000000 : ℝ)) (by norm_num) 4623 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (627318914146913839/625000000000000000 : ℝ) ≤ (2502053086564633/2500000000000000 : ℝ) ^ (4623/1024 : ℝ) := by
    have hpowers : (627318914146913839/625000000000000000 : ℝ)^1024 ≤ (2502053086564633/2500000000000000 : ℝ)^4623 := by
      have hnat : (627318914146913839 : ℕ)^1024*2500000000000000^4623 ≤ 2502053086564633^4623*625000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        627318914146913839 625000000000000000 2502053086564633 2500000000000000 1024 4623 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2502053086564633/2500000000000000 : ℝ)) (X := (627318914146913839/625000000000000000 : ℝ)) (by norm_num) 4623 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(25810423474639/100000000000000000000 : ℝ) ≤ ((10676075345498489939/10677500000000000000 : ℝ)+2*(410560142543/213550000000000 : ℝ)*(3473/100000 : ℝ))^(4623/1024 : ℝ) := by
    rw [show (10676075345498489939/10677500000000000000 : ℝ)+2*(410560142543/213550000000000 : ℝ)*(3473/100000 : ℝ)=(1250000142925959/1250000000000000 : ℝ) by norm_num, show 1+2*(25810423474639/100000000000000000000 : ℝ)=(50000025810423474639/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2318914146913839/1250000000000000000 : ℝ)+(25810423474639/100000000000000000000 : ℝ) ≤ ((10676075345498489939/10677500000000000000 : ℝ)+(410560142543/213550000000000 : ℝ)*((6207/25000 : ℝ)+(3473/100000 : ℝ)))^(4623/1024 : ℝ) := by
    rw [show (10676075345498489939/10677500000000000000 : ℝ)+(410560142543/213550000000000 : ℝ)*((6207/25000 : ℝ)+(3473/100000 : ℝ))=(5002053372416551/5000000000000000 : ℝ) by norm_num, show 1+(2318914146913839/1250000000000000000 : ℝ)+(25810423474639/100000000000000000000 : ℝ)=(100185538942176581759/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2318914146913839/1250000000000000000 : ℝ) ≤ ((10676075345498489939/10677500000000000000 : ℝ)+2*(410560142543/213550000000000 : ℝ)*(6207/25000 : ℝ))^(4623/1024 : ℝ) := by
    rw [show (10676075345498489939/10677500000000000000 : ℝ)+2*(410560142543/213550000000000 : ℝ)*(6207/25000 : ℝ)=(2502053086564633/2500000000000000 : ℝ) by norm_num, show 1+2*(2318914146913839/1250000000000000000 : ℝ)=(627318914146913839/625000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (10676075345498489939/10677500000000000000 : ℝ)*(X 1 0+X 2 0)+(410560142543/213550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4623/1024 : ℝ)) (lo := (3473/100000 : ℝ)) (hi := (6207/25000 : ℝ)) (c := (10676075345498489939/10677500000000000000 : ℝ)) (alpha := (410560142543/213550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (10676075345498489939/10677500000000000000 : ℝ)*(X 0 1+X 2 1)+(410560142543/213550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4623/1024 : ℝ)) (lo := (3473/100000 : ℝ)) (hi := (6207/25000 : ℝ)) (c := (10676075345498489939/10677500000000000000 : ℝ)) (alpha := (410560142543/213550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (10676075345498489939/10677500000000000000 : ℝ)*(X 0 2+X 1 2)+(410560142543/213550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4623/1024 : ℝ)) (lo := (3473/100000 : ℝ)) (hi := (6207/25000 : ℝ)) (c := (10676075345498489939/10677500000000000000 : ℝ)) (alpha := (410560142543/213550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-443042213/2500000000 : ℝ)*X 0 0+(346141763/625000000 : ℝ)*X 0 1+(1280569513/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1075491277/2000000000 : ℝ)*X 1 0+(-1989899321/10000000000 : ℝ)*X 1 1+(5122277969/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((537745629/1000000000 : ℝ)*X 2 0+(5122278437/10000000000 : ℝ)*X 2 1+(-994949417/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1057661073/2500000000 : ℝ)*X 0 0+(1882275783/5000000000 : ℝ)*X 0 1+(148203461/312500000 : ℝ)*X 0 2+(1057661073/2500000000 : ℝ)*X 1 0+(1882275783/5000000000 : ℝ)*X 1 1+(148203461/312500000 : ℝ)*X 1 2+(1057661073/2500000000 : ℝ)*X 2 0+(1882275783/5000000000 : ℝ)*X 2 1+(148203461/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1772387901/10000000000 : ℝ)*X 0 0+(640825647/1250000000 : ℝ)*X 0 1+(221355067/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1053451263/2000000000 : ℝ)*X 1 0+(-1578300459/10000000000 : ℝ)*X 1 1+(2766938523/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1053451183/2000000000 : ℝ)*X 2 0+(1383469297/2500000000 : ℝ)*X 2 1+(-78915041/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((528894763/1250000000 : ℝ)*X 0 0+(2366169203/5000000000 : ℝ)*X 0 1+(3774875861/10000000000 : ℝ)*X 0 2+(528894763/1250000000 : ℝ)*X 1 0+(2366169203/5000000000 : ℝ)*X 1 1+(3774875861/10000000000 : ℝ)*X 1 2+(528894763/1250000000 : ℝ)*X 2 0+(2366169203/5000000000 : ℝ)*X 2 1+(3774875861/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2225704158539551943619288081/266937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (141914961/100000000000000 : ℝ)*(base1) + (1867745723/100000000000000 : ℝ)*(base19) + (1825277027/100000000000000 : ℝ)*(base23) + (83264027/100000000000000 : ℝ)*(upper3) + (174932733/50000000000000 : ℝ)*(upper5) + (856621576387893/50000000000000 : ℝ)*(major0) + (856621576387893/50000000000000 : ℝ)*(major1) + (856621576387893/50000000000000 : ℝ)*(major2) + (2403916322100879/100000000000000 : ℝ)*(sp0) + (600983043169793/25000000000000 : ℝ)*(sp1) + (600983053786967/25000000000000 : ℝ)*(sp2) + (40901817733801/4000000000000 : ℝ)*(sp3) + (17860238977/100000000000000 : ℝ)*(sp4) + (6401935937/100000000000000 : ℝ)*(sp7) + (255637996798981/25000000000000 : ℝ)*(f.failure) + (480786808084979/20000000000000 : ℝ)*(f.sum) + (6786354455269/21355000000000000000000000000 : ℝ)*base66 + (3313897838032358527/533875000000000000000000000000000 : ℝ)*base67 + (2455405811899358527/533875000000000000000000000000000 : ℝ)*base69 + (537630494699141473/533875000000000000000000000000000 : ℝ)*base72 + (26679290481199/5338750000000000000000000000 : ℝ)*base73 + (1101799301030016473/533875000000000000000000000000000 : ℝ)*base76 + (552993548636641473/533875000000000000000000000000000 : ℝ)*base78 + (1492697591239141473/533875000000000000000000000000000 : ℝ)*base80 + (20399690608621/21355000000000000000000000000 : ℝ)*base81 + (499833/78125000000000000000 : ℝ)*base90 + (499833/78125000000000000000 : ℝ)*base92 + (499833/78125000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1038101453116617220924525401/266937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (670315077/100000000000000 : ℝ)*(base19) + (587794439/100000000000000 : ℝ)*(base23) + (30387003/50000000000000 : ℝ)*(upper2) + (154915563/100000000000000 : ℝ)*(upper3) + (14208661/25000000000000 : ℝ)*(upper5) + (874947310372147/50000000000000 : ℝ)*(major0) + (874947310372147/50000000000000 : ℝ)*(major1) + (874947310372147/50000000000000 : ℝ)*(major2) + (5722785149/100000000000000 : ℝ)*(sp1) + (161750339/3125000000000 : ℝ)*(sp2) + (2455361635858933/100000000000000 : ℝ)*(sp4) + (1227677621379353/50000000000000 : ℝ)*(sp5) + (1227677936026823/50000000000000 : ℝ)*(sp6) + (522213737999311/50000000000000 : ℝ)*(sp7) + (522213737999311/50000000000000 : ℝ)*(f.failure) + (2455361635858933/100000000000000 : ℝ)*(f.sum) + (6835825759759/21355000000000000000000000000 : ℝ)*base65 + (1768207534826120967/533875000000000000000000000000000 : ℝ)*base68 + (3277531803753004033/533875000000000000000000000000000 : ℝ)*base69 + (1789015629484754033/533875000000000000000000000000000 : ℝ)*base71 + (65503886390111/21355000000000000000000000000 : ℝ)*base74 + (4359132079100254033/533875000000000000000000000000000 : ℝ)*base75 + (3605094674778370967/533875000000000000000000000000000 : ℝ)*base78 + (2728901972781879033/533875000000000000000000000000000 : ℝ)*base79 + (57781768444917/10677500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (846023/156250000000000000000 : ℝ)*base90 + (846023/156250000000000000000 : ℝ)*base92 + (846023/156250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1564_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5235807/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6207/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3473/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9001/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1781/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1564_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1564_s2_0 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-223914263/1250000000 : ℝ)*x 0 + (2721488963/5000000000 : ℝ)*x 1 + (2602549911/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (223914263/1250000000 : ℝ)^4625 ≤ (2196997614153/20000000000000 : ℝ)^3601 := by
    have hnat : (223914263 : ℕ)^4625*20000000000000^3601 ≤ 2196997614153^3601*1250000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223914263 1250000000 2196997614153 20000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2721488963/5000000000 : ℝ)^4625 ≤ (11446102451503/25000000000000 : ℝ)^3601 := by
    have hnat : (2721488963 : ℕ)^4625*25000000000000^3601 ≤ 11446102451503^3601*5000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2721488963 5000000000 11446102451503 25000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2602549911/5000000000 : ℝ)^4625 ≤ (43230602110251/100000000000000 : ℝ)^3601 := by
    have hnat : (2602549911 : ℕ)^4625*100000000000000^3601 ≤ 43230602110251^3601*5000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2602549911 5000000000 43230602110251 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-223914263/1250000000 : ℝ), (2721488963/5000000000 : ℝ), (2602549911/5000000000 : ℝ)] ![(2196997614153/20000000000000 : ℝ), (11446102451503/25000000000000 : ℝ), (43230602110251/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-223914263/1250000000 : ℝ)|^4625 ≤ (2196997614153/20000000000000 : ℝ)^3601
        have hw : |(-223914263/1250000000 : ℝ)|=(223914263/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2721488963/5000000000 : ℝ)|^4625 ≤ (11446102451503/25000000000000 : ℝ)^3601
        have hw : |(2721488963/5000000000 : ℝ)|=(2721488963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2602549911/5000000000 : ℝ)|^4625 ≤ (43230602110251/100000000000000 : ℝ)^3601
        have hw : |(2602549911/5000000000 : ℝ)|=(2602549911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_s2_1 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352882819/10000000000 : ℝ)*x 0 + (-7474371/39062500 : ℝ)*x 1 + (2602549833/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352882819/10000000000 : ℝ)^4625 ≤ (22406677788873/50000000000000 : ℝ)^3601 := by
    have hnat : (5352882819 : ℕ)^4625*50000000000000^3601 ≤ 22406677788873^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352882819 10000000000 22406677788873 50000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7474371/39062500 : ℝ)^4625 ≤ (11956043964649/100000000000000 : ℝ)^3601 := by
    have hnat : (7474371 : ℕ)^4625*100000000000000^3601 ≤ 11956043964649^3601*39062500^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7474371 39062500 11956043964649 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2602549833/5000000000 : ℝ)^4625 ≤ (21615300223083/50000000000000 : ℝ)^3601 := by
    have hnat : (2602549833 : ℕ)^4625*50000000000000^3601 ≤ 21615300223083^3601*5000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2602549833 5000000000 21615300223083 50000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352882819/10000000000 : ℝ), (-7474371/39062500 : ℝ), (2602549833/5000000000 : ℝ)] ![(22406677788873/50000000000000 : ℝ), (11956043964649/100000000000000 : ℝ), (21615300223083/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352882819/10000000000 : ℝ)|^4625 ≤ (22406677788873/50000000000000 : ℝ)^3601
        have hw : |(5352882819/10000000000 : ℝ)|=(5352882819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7474371/39062500 : ℝ)|^4625 ≤ (11956043964649/100000000000000 : ℝ)^3601
        have hw : |(-7474371/39062500 : ℝ)|=(7474371/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2602549833/5000000000 : ℝ)|^4625 ≤ (21615300223083/50000000000000 : ℝ)^3601
        have hw : |(2602549833/5000000000 : ℝ)|=(2602549833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_s2_2 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535288269/1000000000 : ℝ)*x 0 + (5205099681/10000000000 : ℝ)*x 1 + (-1913439129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535288269/1000000000 : ℝ)^4625 ≤ (44813354190677/100000000000000 : ℝ)^3601 := by
    have hnat : (535288269 : ℕ)^4625*100000000000000^3601 ≤ 44813354190677^3601*1000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535288269 1000000000 44813354190677 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5205099681/10000000000 : ℝ)^4625 ≤ (21615300303087/50000000000000 : ℝ)^3601 := by
    have hnat : (5205099681 : ℕ)^4625*50000000000000^3601 ≤ 21615300303087^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5205099681 10000000000 21615300303087 50000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1913439129/10000000000 : ℝ)^4625 ≤ (11956045192521/100000000000000 : ℝ)^3601 := by
    have hnat : (1913439129 : ℕ)^4625*100000000000000^3601 ≤ 11956045192521^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1913439129 10000000000 11956045192521 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535288269/1000000000 : ℝ), (5205099681/10000000000 : ℝ), (-1913439129/10000000000 : ℝ)] ![(44813354190677/100000000000000 : ℝ), (21615300303087/50000000000000 : ℝ), (11956045192521/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535288269/1000000000 : ℝ)|^4625 ≤ (44813354190677/100000000000000 : ℝ)^3601
        have hw : |(535288269/1000000000 : ℝ)|=(535288269/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5205099681/10000000000 : ℝ)|^4625 ≤ (21615300303087/50000000000000 : ℝ)^3601
        have hw : |(5205099681/10000000000 : ℝ)|=(5205099681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1913439129/10000000000 : ℝ)|^4625 ≤ (11956045192521/100000000000000 : ℝ)^3601
        have hw : |(-1913439129/10000000000 : ℝ)|=(1913439129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_s2_3 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061126459/2500000000 : ℝ)*x 0 + (3972380017/10000000000 : ℝ)*x 1 + (1132902833/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061126459/2500000000 : ℝ)^4625 ≤ (16632748996541/50000000000000 : ℝ)^3601 := by
    have hnat : (1061126459 : ℕ)^4625*50000000000000^3601 ≤ 16632748996541^3601*2500000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061126459 2500000000 16632748996541 50000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3972380017/10000000000 : ℝ)^4625 ≤ (15275825486391/50000000000000 : ℝ)^3601 := by
    have hnat : (3972380017 : ℕ)^4625*50000000000000^3601 ≤ 15275825486391^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3972380017 10000000000 15275825486391 50000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1132902833/2500000000 : ℝ)^4625 ≤ (18091425512299/50000000000000 : ℝ)^3601 := by
    have hnat : (1132902833 : ℕ)^4625*50000000000000^3601 ≤ 18091425512299^3601*2500000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1132902833 2500000000 18091425512299 50000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061126459/2500000000 : ℝ), (3972380017/10000000000 : ℝ), (1132902833/2500000000 : ℝ)] ![(16632748996541/50000000000000 : ℝ), (15275825486391/50000000000000 : ℝ), (18091425512299/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061126459/2500000000 : ℝ)|^4625 ≤ (16632748996541/50000000000000 : ℝ)^3601
        have hw : |(1061126459/2500000000 : ℝ)|=(1061126459/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3972380017/10000000000 : ℝ)|^4625 ≤ (15275825486391/50000000000000 : ℝ)^3601
        have hw : |(3972380017/10000000000 : ℝ)|=(3972380017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1132902833/2500000000 : ℝ)|^4625 ≤ (18091425512299/50000000000000 : ℝ)^3601
        have hw : |(1132902833/2500000000 : ℝ)|=(1132902833/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_s2_4 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-358270937/2000000000 : ℝ)*x 0 + (5206523009/10000000000 : ℝ)*x 1 + (680192877/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (358270937/2000000000 : ℝ)^4625 ≤ (10985307695663/100000000000000 : ℝ)^3601 := by
    have hnat : (358270937 : ℕ)^4625*100000000000000^3601 ≤ 10985307695663^3601*2000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      358270937 2000000000 10985307695663 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5206523009/10000000000 : ℝ)^4625 ≤ (21622892067369/50000000000000 : ℝ)^3601 := by
    have hnat : (5206523009 : ℕ)^4625*50000000000000^3601 ≤ 21622892067369^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5206523009 10000000000 21622892067369 50000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (680192877/1250000000 : ℝ)^4625 ≤ (228844540759/500000000000 : ℝ)^3601 := by
    have hnat : (680192877 : ℕ)^4625*500000000000^3601 ≤ 228844540759^3601*1250000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      680192877 1250000000 228844540759 500000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-358270937/2000000000 : ℝ), (5206523009/10000000000 : ℝ), (680192877/1250000000 : ℝ)] ![(10985307695663/100000000000000 : ℝ), (21622892067369/50000000000000 : ℝ), (228844540759/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-358270937/2000000000 : ℝ)|^4625 ≤ (10985307695663/100000000000000 : ℝ)^3601
        have hw : |(-358270937/2000000000 : ℝ)|=(358270937/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5206523009/10000000000 : ℝ)|^4625 ≤ (21622892067369/50000000000000 : ℝ)^3601
        have hw : |(5206523009/10000000000 : ℝ)|=(5206523009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(680192877/1250000000 : ℝ)|^4625 ≤ (228844540759/500000000000 : ℝ)^3601
        have hw : |(680192877/1250000000 : ℝ)|=(680192877/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_s2_5 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661248189/1250000000 : ℝ)*x 0 + (-1676996343/10000000000 : ℝ)*x 1 + (5441543741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661248189/1250000000 : ℝ)^4625 ≤ (1379318345917/3125000000000 : ℝ)^3601 := by
    have hnat : (661248189 : ℕ)^4625*3125000000000^3601 ≤ 1379318345917^3601*1250000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661248189 1250000000 1379318345917 3125000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1676996343/10000000000 : ℝ)^4625 ≤ (2523224234177/25000000000000 : ℝ)^3601 := by
    have hnat : (1676996343 : ℕ)^4625*25000000000000^3601 ≤ 2523224234177^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1676996343 10000000000 2523224234177 25000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5441543741/10000000000 : ℝ)^4625 ≤ (11442228995961/25000000000000 : ℝ)^3601 := by
    have hnat : (5441543741 : ℕ)^4625*25000000000000^3601 ≤ 11442228995961^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5441543741 10000000000 11442228995961 25000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661248189/1250000000 : ℝ), (-1676996343/10000000000 : ℝ), (5441543741/10000000000 : ℝ)] ![(1379318345917/3125000000000 : ℝ), (2523224234177/25000000000000 : ℝ), (11442228995961/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661248189/1250000000 : ℝ)|^4625 ≤ (1379318345917/3125000000000 : ℝ)^3601
        have hw : |(661248189/1250000000 : ℝ)|=(661248189/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1676996343/10000000000 : ℝ)|^4625 ≤ (2523224234177/25000000000000 : ℝ)^3601
        have hw : |(-1676996343/10000000000 : ℝ)|=(1676996343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5441543741/10000000000 : ℝ)|^4625 ≤ (11442228995961/25000000000000 : ℝ)^3601
        have hw : |(5441543741/10000000000 : ℝ)|=(5441543741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_s2_6 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5289985729/10000000000 : ℝ)*x 0 + (544154481/1000000000 : ℝ)*x 1 + (-419248637/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289985729/10000000000 : ℝ)^4625 ≤ (44138189394801/100000000000000 : ℝ)^3601 := by
    have hnat : (5289985729 : ℕ)^4625*100000000000000^3601 ≤ 44138189394801^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289985729 10000000000 44138189394801 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (544154481/1000000000 : ℝ)^4625 ≤ (22884463766029/50000000000000 : ℝ)^3601 := by
    have hnat : (544154481 : ℕ)^4625*50000000000000^3601 ≤ 22884463766029^3601*1000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544154481 1000000000 22884463766029 50000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (419248637/2500000000 : ℝ)^4625 ≤ (10092883061589/100000000000000 : ℝ)^3601 := by
    have hnat : (419248637 : ℕ)^4625*100000000000000^3601 ≤ 10092883061589^3601*2500000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419248637 2500000000 10092883061589 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289985729/10000000000 : ℝ), (544154481/1000000000 : ℝ), (-419248637/2500000000 : ℝ)] ![(44138189394801/100000000000000 : ℝ), (22884463766029/50000000000000 : ℝ), (10092883061589/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289985729/10000000000 : ℝ)|^4625 ≤ (44138189394801/100000000000000 : ℝ)^3601
        have hw : |(5289985729/10000000000 : ℝ)|=(5289985729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(544154481/1000000000 : ℝ)|^4625 ≤ (22884463766029/50000000000000 : ℝ)^3601
        have hw : |(544154481/1000000000 : ℝ)|=(544154481/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-419248637/2500000000 : ℝ)|^4625 ≤ (10092883061589/100000000000000 : ℝ)^3601
        have hw : |(-419248637/2500000000 : ℝ)|=(419248637/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1564_s2_7 (p : ℝ) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061150551/2500000000 : ℝ)*x 0 + (283016661/625000000 : ℝ)*x 1 + (3975753451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061150551/2500000000 : ℝ)^4625 ≤ (16633234016669/50000000000000 : ℝ)^3601 := by
    have hnat : (1061150551 : ℕ)^4625*50000000000000^3601 ≤ 16633234016669^3601*2500000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061150551 2500000000 16633234016669 50000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (283016661/625000000 : ℝ)^4625 ≤ (2259284619299/6250000000000 : ℝ)^3601 := by
    have hnat : (283016661 : ℕ)^4625*6250000000000^3601 ≤ 2259284619299^3601*625000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283016661 625000000 2259284619299 6250000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3975753451/10000000000 : ℝ)^4625 ≤ (30584978044333/100000000000000 : ℝ)^3601 := by
    have hnat : (3975753451 : ℕ)^4625*100000000000000^3601 ≤ 30584978044333^3601*10000000000^4625 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3975753451 10000000000 30584978044333 100000000000000 4625 3601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4625/1024 : ℝ)) 4625 3601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061150551/2500000000 : ℝ), (283016661/625000000 : ℝ), (3975753451/10000000000 : ℝ)] ![(16633234016669/50000000000000 : ℝ), (2259284619299/6250000000000 : ℝ), (30584978044333/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061150551/2500000000 : ℝ)|^4625 ≤ (16633234016669/50000000000000 : ℝ)^3601
        have hw : |(1061150551/2500000000 : ℝ)|=(1061150551/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(283016661/625000000 : ℝ)|^4625 ≤ (2259284619299/6250000000000 : ℝ)^3601
        have hw : |(283016661/625000000 : ℝ)|=(283016661/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3975753451/10000000000 : ℝ)|^4625 ≤ (30584978044333/100000000000000 : ℝ)^3601
        have hw : |(3975753451/10000000000 : ℝ)|=(3975753451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1564_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5235807/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1781/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9001/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2157/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3957/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1781/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9001/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1781/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9001/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1781/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9001/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1781/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9001/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1781/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9001/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1781/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9001/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9001/100000 : ℝ) ^ (4623/1024 : ℝ) ≤ (950518175175493/50000000000000000000 : ℝ) := by
    have hpowers : (9001/100000 : ℝ)^4623 ≤ (950518175175493/50000000000000000000 : ℝ)^1024 := by
      have hnat : (9001 : ℕ)^4623*50000000000000000000^1024 ≤ 950518175175493^1024*100000^4623 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9001 100000 950518175175493 50000000000000000000 4623 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9001/100000 : ℝ)) (X := (950518175175493/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4623 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1781/10000 : ℝ) ^ (4623/1024 : ℝ) ≤ (41401019413180463/100000000000000000000 : ℝ) := by
    have hpowers : (1781/10000 : ℝ)^4623 ≤ (41401019413180463/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1781 : ℕ)^4623*100000000000000000000^1024 ≤ 41401019413180463^1024*10000^4623 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1781 10000 41401019413180463 100000000000000000000 4623 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1781/10000 : ℝ)) (X := (41401019413180463/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4623 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000950518175175493/25000000000000000000 : ℝ) ≤ (10000084215116319/10000000000000000 : ℝ) ^ (4623/1024 : ℝ) := by
    have hpowers : (25000950518175175493/25000000000000000000 : ℝ)^1024 ≤ (10000084215116319/10000000000000000 : ℝ)^4623 := by
      have hnat : (25000950518175175493 : ℕ)^1024*10000000000000000^4623 ≤ 10000084215116319^4623*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000950518175175493 25000000000000000000 10000084215116319 10000000000000000 1024 4623 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000084215116319/10000000000000000 : ℝ)) (X := (25000950518175175493/25000000000000000000 : ℝ)) (by norm_num) 4623 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100043302055763531449/100000000000000000000 : ℝ) ≤ (2000191796812287/2000000000000000 : ℝ) ^ (4623/1024 : ℝ) := by
    have hpowers : (100043302055763531449/100000000000000000000 : ℝ)^1024 ≤ (2000191796812287/2000000000000000 : ℝ)^4623 := by
      have hnat : (100043302055763531449 : ℕ)^1024*2000000000000000^4623 ≤ 2000191796812287^4623*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100043302055763531449 100000000000000000000 2000191796812287 2000000000000000 1024 4623 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000191796812287/2000000000000000 : ℝ)) (X := (100043302055763531449/100000000000000000000 : ℝ)) (by norm_num) 4623 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50041401019413180463/50000000000000000000 : ℝ) ≤ (10001833753006551/10000000000000000 : ℝ) ^ (4623/1024 : ℝ) := by
    have hpowers : (50041401019413180463/50000000000000000000 : ℝ)^1024 ≤ (10001833753006551/10000000000000000 : ℝ)^4623 := by
      have hnat : (50041401019413180463 : ℕ)^1024*10000000000000000^4623 ≤ 10001833753006551^4623*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50041401019413180463 50000000000000000000 10001833753006551 10000000000000000 1024 4623 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001833753006551/10000000000000000 : ℝ)) (X := (50041401019413180463/50000000000000000000 : ℝ)) (by norm_num) 4623 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(950518175175493/50000000000000000000 : ℝ) ≤ ((88074994260409675839/88090000000000000000 : ℝ)+2*(218692236279/220225000000000 : ℝ)*(9001/100000 : ℝ))^(4623/1024 : ℝ) := by
    rw [show (88074994260409675839/88090000000000000000 : ℝ)+2*(218692236279/220225000000000 : ℝ)*(9001/100000 : ℝ)=(10000084215116319/10000000000000000 : ℝ) by norm_num, show 1+2*(950518175175493/50000000000000000000 : ℝ)=(25000950518175175493/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(41401019413180463/100000000000000000000 : ℝ)+(950518175175493/50000000000000000000 : ℝ) ≤ ((88074994260409675839/88090000000000000000 : ℝ)+(218692236279/220225000000000 : ℝ)*((1781/10000 : ℝ)+(9001/100000 : ℝ)))^(4623/1024 : ℝ) := by
    rw [show (88074994260409675839/88090000000000000000 : ℝ)+(218692236279/220225000000000 : ℝ)*((1781/10000 : ℝ)+(9001/100000 : ℝ))=(2000191796812287/2000000000000000 : ℝ) by norm_num, show 1+(41401019413180463/100000000000000000000 : ℝ)+(950518175175493/50000000000000000000 : ℝ)=(100043302055763531449/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(41401019413180463/100000000000000000000 : ℝ) ≤ ((88074994260409675839/88090000000000000000 : ℝ)+2*(218692236279/220225000000000 : ℝ)*(1781/10000 : ℝ))^(4623/1024 : ℝ) := by
    rw [show (88074994260409675839/88090000000000000000 : ℝ)+2*(218692236279/220225000000000 : ℝ)*(1781/10000 : ℝ)=(10001833753006551/10000000000000000 : ℝ) by norm_num, show 1+2*(41401019413180463/100000000000000000000 : ℝ)=(50041401019413180463/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (88074994260409675839/88090000000000000000 : ℝ)*(X 1 0+X 2 0)+(218692236279/220225000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4623/1024 : ℝ)) (lo := (9001/100000 : ℝ)) (hi := (1781/10000 : ℝ)) (c := (88074994260409675839/88090000000000000000 : ℝ)) (alpha := (218692236279/220225000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (88074994260409675839/88090000000000000000 : ℝ)*(X 0 1+X 2 1)+(218692236279/220225000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4623/1024 : ℝ)) (lo := (9001/100000 : ℝ)) (hi := (1781/10000 : ℝ)) (c := (88074994260409675839/88090000000000000000 : ℝ)) (alpha := (218692236279/220225000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (88074994260409675839/88090000000000000000 : ℝ)*(X 0 2+X 1 2)+(218692236279/220225000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4623/1024 : ℝ)) (lo := (9001/100000 : ℝ)) (hi := (1781/10000 : ℝ)) (c := (88074994260409675839/88090000000000000000 : ℝ)) (alpha := (218692236279/220225000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-223914263/1250000000 : ℝ)*X 0 0+(2721488963/5000000000 : ℝ)*X 0 1+(2602549911/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352882819/10000000000 : ℝ)*X 1 0+(-7474371/39062500 : ℝ)*X 1 1+(2602549833/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((535288269/1000000000 : ℝ)*X 2 0+(5205099681/10000000000 : ℝ)*X 2 1+(-1913439129/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1061126459/2500000000 : ℝ)*X 0 0+(3972380017/10000000000 : ℝ)*X 0 1+(1132902833/2500000000 : ℝ)*X 0 2+(1061126459/2500000000 : ℝ)*X 1 0+(3972380017/10000000000 : ℝ)*X 1 1+(1132902833/2500000000 : ℝ)*X 1 2+(1061126459/2500000000 : ℝ)*X 2 0+(3972380017/10000000000 : ℝ)*X 2 1+(1132902833/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-358270937/2000000000 : ℝ)*X 0 0+(5206523009/10000000000 : ℝ)*X 0 1+(680192877/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((661248189/1250000000 : ℝ)*X 1 0+(-1676996343/10000000000 : ℝ)*X 1 1+(5441543741/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5289985729/10000000000 : ℝ)*X 2 0+(544154481/1000000000 : ℝ)*X 2 1+(-419248637/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1061150551/2500000000 : ℝ)*X 0 0+(283016661/625000000 : ℝ)*X 0 1+(3975753451/10000000000 : ℝ)*X 0 2+(1061150551/2500000000 : ℝ)*X 1 0+(283016661/625000000 : ℝ)*X 1 1+(3975753451/10000000000 : ℝ)*X 1 2+(1061150551/2500000000 : ℝ)*X 2 0+(283016661/625000000 : ℝ)*X 2 1+(3975753451/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1564_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (507298761724935055612761/44045000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2189517271/100000000000000 : ℝ)*(base19) + (972042861/50000000000000 : ℝ)*(base23) + (19286609/25000000000000 : ℝ)*(lower2) + (88406277/25000000000000 : ℝ)*(upper3) + (3646717/4000000000000 : ℝ)*(upper5) + (1498021742961529/50000000000000 : ℝ)*(major0) + (1498021742961529/50000000000000 : ℝ)*(major1) + (1498021742961529/50000000000000 : ℝ)*(major2) + (525483305574409/12500000000000 : ℝ)*(sp0) + (2101945463635899/50000000000000 : ℝ)*(sp1) + (2101945586351673/50000000000000 : ℝ)*(sp2) + (894089855345621/50000000000000 : ℝ)*(sp3) + (5334438759/20000000000000 : ℝ)*(sp4) + (13760441203/100000000000000 : ℝ)*(sp7) + (357638694226489/20000000000000 : ℝ)*(f.failure) + (1050973279197267/25000000000000 : ℝ)*(f.sum) + (215809304826983/44045000000000000000000000000 : ℝ)*base65 + (35433121770563697831/4404500000000000000000000000000000 : ℝ)*base67 + (7643871002169697831/4404500000000000000000000000000000 : ℝ)*base69 + (7205967189712802169/4404500000000000000000000000000000 : ℝ)*base72 + (7168466702499/22022500000000000000000000000 : ℝ)*base73 + (20240983984168302169/4404500000000000000000000000000000 : ℝ)*base76 + (13710817537286197831/4404500000000000000000000000000000 : ℝ)*base77 + (10804163484231802169/4404500000000000000000000000000000 : ℝ)*base80 + (120772296349107/44045000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base85 + (558377/62500000000000000000 : ℝ)*base90 + (558377/62500000000000000000 : ℝ)*base92 + (558377/62500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (566218552748522545540076343/44045000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (254524183/50000000000000 : ℝ)*(base23) + (150559817/100000000000000 : ℝ)*(lower2) + (178842057/100000000000000 : ℝ)*(upper3) + (109392683/100000000000000 : ℝ)*(lower4) + (56932019/100000000000000 : ℝ)*(upper5) + (60648722912421/2000000000000 : ℝ)*(major0) + (60648722912421/2000000000000 : ℝ)*(major1) + (60648722912421/2000000000000 : ℝ)*(major2) + (5483002807/100000000000000 : ℝ)*(sp1) + (40162040557/100000000000000 : ℝ)*(sp2) + (2127478686466361/50000000000000 : ℝ)*(sp4) + (850990377985983/20000000000000 : ℝ)*(sp5) + (4254916701843799/100000000000000 : ℝ)*(sp6) + (1809914489794177/100000000000000 : ℝ)*(sp7) + (1809914489794177/100000000000000 : ℝ)*(f.failure) + (2127478686466361/50000000000000 : ℝ)*(f.sum) + (5109113423941/4404500000000000000000000000 : ℝ)*base66 + (1955099904859296219/176180000000000000000000000000000 : ℝ)*base67 + (376792092088076219/176180000000000000000000000000000 : ℝ)*base69 + (744778175990516219/176180000000000000000000000000000 : ℝ)*base71 + (3312300737017/1761800000000000000000000000 : ℝ)*base73 + (649394538401576219/176180000000000000000000000000000 : ℝ)*base75 + (343298649207323781/176180000000000000000000000000000 : ℝ)*base78 + (3271711542173676219/176180000000000000000000000000000 : ℝ)*base79 + (19696943322169/4404500000000000000000000000 : ℝ)*base82 + (754161/312500000000000000000 : ℝ)*base90 + (754161/312500000000000000000 : ℝ)*base92 + (754161/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1564_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5235807/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1781/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9001/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2157/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3957/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1564_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1564_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5235807/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2157/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3957/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1564_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1564_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1564_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4623/1024 : ℝ) ≤ p) (hpb : p ≤ (4625/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5235807/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2157/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3957/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1564_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
