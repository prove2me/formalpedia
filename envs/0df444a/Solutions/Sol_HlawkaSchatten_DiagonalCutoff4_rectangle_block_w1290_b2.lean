-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1290_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:25:46.442464+00:00
-- url     : https://prove2.me/submissions/b6470bf9-d622-4cdf-b886-484a500096b5

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
theorem support_rectangle_w1290_s6_0 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-417950859/2000000000 : ℝ)*x 0 + (5415425293/10000000000 : ℝ)*x 1 + (2621416619/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (417950859/2000000000 : ℝ)^2125 ≤ (1271391208903/10000000000000 : ℝ)^1613 := by
    have hnat : (417950859 : ℕ)^2125*10000000000000^1613 ≤ 1271391208903^1613*2000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417950859 2000000000 1271391208903 10000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5415425293/10000000000 : ℝ)^2125 ≤ (44574036541993/100000000000000 : ℝ)^1613 := by
    have hnat : (5415425293 : ℕ)^2125*100000000000000^1613 ≤ 44574036541993^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415425293 10000000000 44574036541993 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621416619/5000000000 : ℝ)^2125 ≤ (26695032097/62500000000 : ℝ)^1613 := by
    have hnat : (2621416619 : ℕ)^2125*62500000000^1613 ≤ 26695032097^1613*5000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621416619 5000000000 26695032097 62500000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-417950859/2000000000 : ℝ), (5415425293/10000000000 : ℝ), (2621416619/5000000000 : ℝ)] ![(1271391208903/10000000000000 : ℝ), (44574036541993/100000000000000 : ℝ), (26695032097/62500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-417950859/2000000000 : ℝ)|^2125 ≤ (1271391208903/10000000000000 : ℝ)^1613
        have hw : |(-417950859/2000000000 : ℝ)|=(417950859/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5415425293/10000000000 : ℝ)|^2125 ≤ (44574036541993/100000000000000 : ℝ)^1613
        have hw : |(5415425293/10000000000 : ℝ)|=(5415425293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621416619/5000000000 : ℝ)|^2125 ≤ (26695032097/62500000000 : ℝ)^1613
        have hw : |(2621416619/5000000000 : ℝ)|=(2621416619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1290_s6_1 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5349836369/10000000000 : ℝ)*x 0 + (-1088868023/5000000000 : ℝ)*x 1 + (1310708319/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349836369/10000000000 : ℝ)^2125 ≤ (21932093310351/50000000000000 : ℝ)^1613 := by
    have hnat : (5349836369 : ℕ)^2125*50000000000000^1613 ≤ 21932093310351^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349836369 10000000000 21932093310351 50000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1088868023/5000000000 : ℝ)^2125 ≤ (6711880801607/50000000000000 : ℝ)^1613 := by
    have hnat : (1088868023 : ℕ)^2125*50000000000000^1613 ≤ 6711880801607^1613*5000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088868023 5000000000 6711880801607 50000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310708319/2500000000 : ℝ)^2125 ≤ (21356025881521/50000000000000 : ℝ)^1613 := by
    have hnat : (1310708319 : ℕ)^2125*50000000000000^1613 ≤ 21356025881521^1613*2500000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310708319 2500000000 21356025881521 50000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349836369/10000000000 : ℝ), (-1088868023/5000000000 : ℝ), (1310708319/2500000000 : ℝ)] ![(21932093310351/50000000000000 : ℝ), (6711880801607/50000000000000 : ℝ), (21356025881521/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349836369/10000000000 : ℝ)|^2125 ≤ (21932093310351/50000000000000 : ℝ)^1613
        have hw : |(5349836369/10000000000 : ℝ)|=(5349836369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1088868023/5000000000 : ℝ)|^2125 ≤ (6711880801607/50000000000000 : ℝ)^1613
        have hw : |(-1088868023/5000000000 : ℝ)|=(1088868023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310708319/2500000000 : ℝ)|^2125 ≤ (21356025881521/50000000000000 : ℝ)^1613
        have hw : |(1310708319/2500000000 : ℝ)|=(1310708319/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1290_s6_2 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1337459121/2500000000 : ℝ)*x 0 + (5242833201/10000000000 : ℝ)*x 1 + (-272216999/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337459121/2500000000 : ℝ)^2125 ≤ (43864187862903/100000000000000 : ℝ)^1613 := by
    have hnat : (1337459121 : ℕ)^2125*100000000000000^1613 ≤ 43864187862903^1613*2500000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337459121 2500000000 43864187862903 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242833201/10000000000 : ℝ)^2125 ≤ (4271205095809/10000000000000 : ℝ)^1613 := by
    have hnat : (5242833201 : ℕ)^2125*10000000000000^1613 ≤ 4271205095809^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242833201 10000000000 4271205095809 10000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (272216999/1250000000 : ℝ)^2125 ≤ (1677970145587/12500000000000 : ℝ)^1613 := by
    have hnat : (272216999 : ℕ)^2125*12500000000000^1613 ≤ 1677970145587^1613*1250000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272216999 1250000000 1677970145587 12500000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337459121/2500000000 : ℝ), (5242833201/10000000000 : ℝ), (-272216999/1250000000 : ℝ)] ![(43864187862903/100000000000000 : ℝ), (4271205095809/10000000000000 : ℝ), (1677970145587/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337459121/2500000000 : ℝ)|^2125 ≤ (43864187862903/100000000000000 : ℝ)^1613
        have hw : |(1337459121/2500000000 : ℝ)|=(1337459121/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242833201/10000000000 : ℝ)|^2125 ≤ (4271205095809/10000000000000 : ℝ)^1613
        have hw : |(5242833201/10000000000 : ℝ)|=(5242833201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-272216999/1250000000 : ℝ)|^2125 ≤ (1677970145587/12500000000000 : ℝ)^1613
        have hw : |(-272216999/1250000000 : ℝ)|=(272216999/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1290_s6_3 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (542549701/1250000000 : ℝ)*x 0 + (260414753/625000000 : ℝ)*x 1 + (28256767/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (542549701/1250000000 : ℝ)^2125 ≤ (16651133107753/50000000000000 : ℝ)^1613 := by
    have hnat : (542549701 : ℕ)^2125*50000000000000^1613 ≤ 16651133107753^1613*1250000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542549701 1250000000 16651133107753 50000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (260414753/625000000 : ℝ)^2125 ≤ (15778566438253/50000000000000 : ℝ)^1613 := by
    have hnat : (260414753 : ℕ)^2125*50000000000000^1613 ≤ 15778566438253^1613*625000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260414753 625000000 15778566438253 50000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (28256767/62500000 : ℝ)^2125 ≤ (7028120178447/20000000000000 : ℝ)^1613 := by
    have hnat : (28256767 : ℕ)^2125*20000000000000^1613 ≤ 7028120178447^1613*62500000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28256767 62500000 7028120178447 20000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(542549701/1250000000 : ℝ), (260414753/625000000 : ℝ), (28256767/62500000 : ℝ)] ![(16651133107753/50000000000000 : ℝ), (15778566438253/50000000000000 : ℝ), (7028120178447/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(542549701/1250000000 : ℝ)|^2125 ≤ (16651133107753/50000000000000 : ℝ)^1613
        have hw : |(542549701/1250000000 : ℝ)|=(542549701/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(260414753/625000000 : ℝ)|^2125 ≤ (15778566438253/50000000000000 : ℝ)^1613
        have hw : |(260414753/625000000 : ℝ)|=(260414753/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(28256767/62500000 : ℝ)|^2125 ≤ (7028120178447/20000000000000 : ℝ)^1613
        have hw : |(28256767/62500000 : ℝ)|=(28256767/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1290_s6_4 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2089767263/10000000000 : ℝ)*x 0 + (2621724457/5000000000 : ℝ)*x 1 + (2707403153/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2089767263/10000000000 : ℝ)^2125 ≤ (12714016028853/100000000000000 : ℝ)^1613 := by
    have hnat : (2089767263 : ℕ)^2125*100000000000000^1613 ≤ 12714016028853^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2089767263 10000000000 12714016028853 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621724457/5000000000 : ℝ)^2125 ≤ (42718659343591/100000000000000 : ℝ)^1613 := by
    have hnat : (2621724457 : ℕ)^2125*100000000000000^1613 ≤ 42718659343591^1613*5000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621724457 5000000000 42718659343591 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707403153/5000000000 : ℝ)^2125 ≤ (44567324609001/100000000000000 : ℝ)^1613 := by
    have hnat : (2707403153 : ℕ)^2125*100000000000000^1613 ≤ 44567324609001^1613*5000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707403153 5000000000 44567324609001 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2089767263/10000000000 : ℝ), (2621724457/5000000000 : ℝ), (2707403153/5000000000 : ℝ)] ![(12714016028853/100000000000000 : ℝ), (42718659343591/100000000000000 : ℝ), (44567324609001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2089767263/10000000000 : ℝ)|^2125 ≤ (12714016028853/100000000000000 : ℝ)^1613
        have hw : |(-2089767263/10000000000 : ℝ)|=(2089767263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621724457/5000000000 : ℝ)|^2125 ≤ (42718659343591/100000000000000 : ℝ)^1613
        have hw : |(2621724457/5000000000 : ℝ)|=(2621724457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707403153/5000000000 : ℝ)|^2125 ≤ (44567324609001/100000000000000 : ℝ)^1613
        have hw : |(2707403153/5000000000 : ℝ)|=(2707403153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1290_s6_5 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1061131907/2000000000 : ℝ)*x 0 + (-2005762753/10000000000 : ℝ)*x 1 + (676850823/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061131907/2000000000 : ℝ)^2125 ≤ (10846906509911/25000000000000 : ℝ)^1613 := by
    have hnat : (1061131907 : ℕ)^2125*25000000000000^1613 ≤ 10846906509911^1613*2000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061131907 2000000000 10846906509911 25000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2005762753/10000000000 : ℝ)^2125 ≤ (2409009265401/20000000000000 : ℝ)^1613 := by
    have hnat : (2005762753 : ℕ)^2125*20000000000000^1613 ≤ 2409009265401^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2005762753 10000000000 2409009265401 20000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676850823/1250000000 : ℝ)^2125 ≤ (5570915952927/12500000000000 : ℝ)^1613 := by
    have hnat : (676850823 : ℕ)^2125*12500000000000^1613 ≤ 5570915952927^1613*1250000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676850823 1250000000 5570915952927 12500000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061131907/2000000000 : ℝ), (-2005762753/10000000000 : ℝ), (676850823/1250000000 : ℝ)] ![(10846906509911/25000000000000 : ℝ), (2409009265401/20000000000000 : ℝ), (5570915952927/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061131907/2000000000 : ℝ)|^2125 ≤ (10846906509911/25000000000000 : ℝ)^1613
        have hw : |(1061131907/2000000000 : ℝ)|=(1061131907/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2005762753/10000000000 : ℝ)|^2125 ≤ (2409009265401/20000000000000 : ℝ)^1613
        have hw : |(-2005762753/10000000000 : ℝ)|=(2005762753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(676850823/1250000000 : ℝ)|^2125 ≤ (5570915952927/12500000000000 : ℝ)^1613
        have hw : |(676850823/1250000000 : ℝ)|=(676850823/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1290_s6_6 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652829861/5000000000 : ℝ)*x 0 + (135370163/250000000 : ℝ)*x 1 + (-401152517/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652829861/5000000000 : ℝ)^2125 ≤ (21693814027131/50000000000000 : ℝ)^1613 := by
    have hnat : (2652829861 : ℕ)^2125*50000000000000^1613 ≤ 21693814027131^1613*5000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652829861 5000000000 21693814027131 50000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (135370163/250000000 : ℝ)^2125 ≤ (891346538589/2000000000000 : ℝ)^1613 := by
    have hnat : (135370163 : ℕ)^2125*2000000000000^1613 ≤ 891346538589^1613*250000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135370163 250000000 891346538589 2000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (401152517/2000000000 : ℝ)^2125 ≤ (1204504499789/10000000000000 : ℝ)^1613 := by
    have hnat : (401152517 : ℕ)^2125*10000000000000^1613 ≤ 1204504499789^1613*2000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      401152517 2000000000 1204504499789 10000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652829861/5000000000 : ℝ), (135370163/250000000 : ℝ), (-401152517/2000000000 : ℝ)] ![(21693814027131/50000000000000 : ℝ), (891346538589/2000000000000 : ℝ), (1204504499789/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652829861/5000000000 : ℝ)|^2125 ≤ (21693814027131/50000000000000 : ℝ)^1613
        have hw : |(2652829861/5000000000 : ℝ)|=(2652829861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(135370163/250000000 : ℝ)|^2125 ≤ (891346538589/2000000000000 : ℝ)^1613
        have hw : |(135370163/250000000 : ℝ)|=(135370163/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-401152517/2000000000 : ℝ)|^2125 ≤ (1204504499789/10000000000000 : ℝ)^1613
        have hw : |(-401152517/2000000000 : ℝ)|=(401152517/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1290_s6_7 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2170212013/5000000000 : ℝ)*x 0 + (4519818273/10000000000 : ℝ)*x 1 + (4167906809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2170212013/5000000000 : ℝ)^2125 ≤ (266420266009/800000000000 : ℝ)^1613 := by
    have hnat : (2170212013 : ℕ)^2125*800000000000^1613 ≤ 266420266009^1613*5000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2170212013 5000000000 266420266009 800000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4519818273/10000000000 : ℝ)^2125 ≤ (281021230303/800000000000 : ℝ)^1613 := by
    have hnat : (4519818273 : ℕ)^2125*800000000000^1613 ≤ 281021230303^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4519818273 10000000000 281021230303 800000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4167906809/10000000000 : ℝ)^2125 ≤ (3156981294023/10000000000000 : ℝ)^1613 := by
    have hnat : (4167906809 : ℕ)^2125*10000000000000^1613 ≤ 3156981294023^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4167906809 10000000000 3156981294023 10000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2170212013/5000000000 : ℝ), (4519818273/10000000000 : ℝ), (4167906809/10000000000 : ℝ)] ![(266420266009/800000000000 : ℝ), (281021230303/800000000000 : ℝ), (3156981294023/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2170212013/5000000000 : ℝ)|^2125 ≤ (266420266009/800000000000 : ℝ)^1613
        have hw : |(2170212013/5000000000 : ℝ)|=(2170212013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4519818273/10000000000 : ℝ)|^2125 ≤ (281021230303/800000000000 : ℝ)^1613
        have hw : |(4519818273/10000000000 : ℝ)|=(4519818273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4167906809/10000000000 : ℝ)|^2125 ≤ (3156981294023/10000000000000 : ℝ)^1613
        have hw : |(4167906809/10000000000 : ℝ)|=(4167906809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1290_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152683333/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2937/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11009/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (551/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14673/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2937/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11009/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2937/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11009/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2937/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11009/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2937/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11009/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2937/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11009/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2937/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11009/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11009/100000 : ℝ) ^ (4249/1024 : ℝ) ≤ (5281838864421137/50000000000000000000 : ℝ) := by
    have hpowers : (11009/100000 : ℝ)^4249 ≤ (5281838864421137/50000000000000000000 : ℝ)^1024 := by
      have hnat : (11009 : ℕ)^4249*50000000000000000000^1024 ≤ 5281838864421137^1024*100000^4249 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11009 100000 5281838864421137 50000000000000000000 4249 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11009/100000 : ℝ)) (X := (5281838864421137/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4249 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2937/20000 : ℝ) ^ (4249/1024 : ℝ) ≤ (8728810486843839/25000000000000000000 : ℝ) := by
    have hpowers : (2937/20000 : ℝ)^4249 ≤ (8728810486843839/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2937 : ℕ)^4249*25000000000000000000^1024 ≤ 8728810486843839^1024*20000^4249 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2937 20000 8728810486843839 25000000000000000000 4249 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2937/20000 : ℝ)) (X := (8728810486843839/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4249 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005281838864421137/25000000000000000000 : ℝ) ≤ (5000254561986209/5000000000000000 : ℝ) ^ (4249/1024 : ℝ) := by
    have hpowers : (25005281838864421137/25000000000000000000 : ℝ)^1024 ≤ (5000254561986209/5000000000000000 : ℝ)^4249 := by
      have hnat : (25005281838864421137 : ℕ)^1024*5000000000000000^4249 ≤ 5000254561986209^4249*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005281838864421137 25000000000000000000 5000254561986209 5000000000000000 1024 4249 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000254561986209/5000000000000000 : ℝ)) (X := (25005281838864421137/25000000000000000000 : ℝ)) (by norm_num) 4249 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10004547891967621763/10000000000000000000 : ℝ) ≤ (250027396080351/250000000000000 : ℝ) ^ (4249/1024 : ℝ) := by
    have hpowers : (10004547891967621763/10000000000000000000 : ℝ)^1024 ≤ (250027396080351/250000000000000 : ℝ)^4249 := by
      have hnat : (10004547891967621763 : ℕ)^1024*250000000000000^4249 ≤ 250027396080351^4249*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004547891967621763 10000000000000000000 250027396080351 250000000000000 1024 4249 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250027396080351/250000000000000 : ℝ)) (X := (10004547891967621763/10000000000000000000 : ℝ)) (by norm_num) 4249 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508728810486843839/12500000000000000000 : ℝ) ≤ (5000841281227831/5000000000000000 : ℝ) ^ (4249/1024 : ℝ) := by
    have hpowers : (12508728810486843839/12500000000000000000 : ℝ)^1024 ≤ (5000841281227831/5000000000000000 : ℝ)^4249 := by
      have hnat : (12508728810486843839 : ℕ)^1024*5000000000000000^4249 ≤ 5000841281227831^4249*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508728810486843839 12500000000000000000 5000841281227831 5000000000000000 1024 4249 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000841281227831/5000000000000000 : ℝ)) (X := (12508728810486843839/12500000000000000000 : ℝ)) (by norm_num) 4249 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5281838864421137/50000000000000000000 : ℝ) ≤ ((9187238288865143843/9190000000000000000 : ℝ)+2*(293359620811/183800000000000 : ℝ)*(11009/100000 : ℝ))^(4249/1024 : ℝ) := by
    rw [show (9187238288865143843/9190000000000000000 : ℝ)+2*(293359620811/183800000000000 : ℝ)*(11009/100000 : ℝ)=(5000254561986209/5000000000000000 : ℝ) by norm_num, show 1+2*(5281838864421137/50000000000000000000 : ℝ)=(25005281838864421137/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8728810486843839/25000000000000000000 : ℝ)+(5281838864421137/50000000000000000000 : ℝ) ≤ ((9187238288865143843/9190000000000000000 : ℝ)+(293359620811/183800000000000 : ℝ)*((2937/20000 : ℝ)+(11009/100000 : ℝ)))^(4249/1024 : ℝ) := by
    rw [show (9187238288865143843/9190000000000000000 : ℝ)+(293359620811/183800000000000 : ℝ)*((2937/20000 : ℝ)+(11009/100000 : ℝ))=(250027396080351/250000000000000 : ℝ) by norm_num, show 1+(8728810486843839/25000000000000000000 : ℝ)+(5281838864421137/50000000000000000000 : ℝ)=(10004547891967621763/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8728810486843839/25000000000000000000 : ℝ) ≤ ((9187238288865143843/9190000000000000000 : ℝ)+2*(293359620811/183800000000000 : ℝ)*(2937/20000 : ℝ))^(4249/1024 : ℝ) := by
    rw [show (9187238288865143843/9190000000000000000 : ℝ)+2*(293359620811/183800000000000 : ℝ)*(2937/20000 : ℝ)=(5000841281227831/5000000000000000 : ℝ) by norm_num, show 1+2*(8728810486843839/25000000000000000000 : ℝ)=(12508728810486843839/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9187238288865143843/9190000000000000000 : ℝ)*(X 1 0+X 2 0)+(293359620811/183800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4249/1024 : ℝ)) (lo := (11009/100000 : ℝ)) (hi := (2937/20000 : ℝ)) (c := (9187238288865143843/9190000000000000000 : ℝ)) (alpha := (293359620811/183800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9187238288865143843/9190000000000000000 : ℝ)*(X 0 1+X 2 1)+(293359620811/183800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4249/1024 : ℝ)) (lo := (11009/100000 : ℝ)) (hi := (2937/20000 : ℝ)) (c := (9187238288865143843/9190000000000000000 : ℝ)) (alpha := (293359620811/183800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9187238288865143843/9190000000000000000 : ℝ)*(X 0 2+X 1 2)+(293359620811/183800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4249/1024 : ℝ)) (lo := (11009/100000 : ℝ)) (hi := (2937/20000 : ℝ)) (c := (9187238288865143843/9190000000000000000 : ℝ)) (alpha := (293359620811/183800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-417950859/2000000000 : ℝ)*X 0 0+(5415425293/10000000000 : ℝ)*X 0 1+(2621416619/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349836369/10000000000 : ℝ)*X 1 0+(-1088868023/5000000000 : ℝ)*X 1 1+(1310708319/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337459121/2500000000 : ℝ)*X 2 0+(5242833201/10000000000 : ℝ)*X 2 1+(-272216999/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((542549701/1250000000 : ℝ)*X 0 0+(260414753/625000000 : ℝ)*X 0 1+(28256767/62500000 : ℝ)*X 0 2+(542549701/1250000000 : ℝ)*X 1 0+(260414753/625000000 : ℝ)*X 1 1+(28256767/62500000 : ℝ)*X 1 2+(542549701/1250000000 : ℝ)*X 2 0+(260414753/625000000 : ℝ)*X 2 1+(28256767/62500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2089767263/10000000000 : ℝ)*X 0 0+(2621724457/5000000000 : ℝ)*X 0 1+(2707403153/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1061131907/2000000000 : ℝ)*X 1 0+(-2005762753/10000000000 : ℝ)*X 1 1+(676850823/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652829861/5000000000 : ℝ)*X 2 0+(135370163/250000000 : ℝ)*X 2 1+(-401152517/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2170212013/5000000000 : ℝ)*X 0 0+(4519818273/10000000000 : ℝ)*X 0 1+(4167906809/10000000000 : ℝ)*X 0 2+(2170212013/5000000000 : ℝ)*X 1 0+(4519818273/10000000000 : ℝ)*X 1 1+(4167906809/10000000000 : ℝ)*X 1 2+(2170212013/5000000000 : ℝ)*X 2 0+(4519818273/10000000000 : ℝ)*X 2 1+(4167906809/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (52312785763698927477663/4595000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1858027303/100000000000000 : ℝ)*(base19) + (1885740841/100000000000000 : ℝ)*(base23) + (647571/1250000000000 : ℝ)*(lower2) + (3434709/1562500000000 : ℝ)*(upper3) + (46954319/20000000000000 : ℝ)*(upper5) + (1076928026518859/25000000000000 : ℝ)*(major0) + (1076928026518859/25000000000000 : ℝ)*(major1) + (1076928026518859/25000000000000 : ℝ)*(major2) + (1448511613301149/25000000000000 : ℝ)*(sp0) + (1448521122604867/25000000000000 : ℝ)*(sp1) + (579408446270593/10000000000000 : ℝ)*(sp2) + (705329449470831/25000000000000 : ℝ)*(sp3) + (1595809687/4000000000000 : ℝ)*(sp4) + (492158253/2500000000000 : ℝ)*(sp7) + (564267496842689/20000000000000 : ℝ)*(f.failure) + (5794086348446771/100000000000000 : ℝ)*(f.sum) + (9295239997433/4595000000000000000000000000 : ℝ)*base65 + (341141872842185137/229750000000000000000000000000000 : ℝ)*base67 + (1856054990580814863/229750000000000000000000000000000 : ℝ)*base70 + (1076057886649314863/229750000000000000000000000000000 : ℝ)*base72 + (10052471478409/2297500000000000000000000000 : ℝ)*base73 + (1838715637261685137/229750000000000000000000000000000 : ℝ)*base75 + (5603308845482314863/229750000000000000000000000000000 : ℝ)*base78 + (2695944428720185137/229750000000000000000000000000000 : ℝ)*base79 + (7363217824149/2297500000000000000000000000 : ℝ)*base81 + (13202437/2000000000000000000000 : ℝ)*base89 + (13202437/2000000000000000000000 : ℝ)*base91 + (13202437/2000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (101800129631839142482171431/22975000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (428487257/50000000000000 : ℝ)*(base19) + (255045307/20000000000000 : ℝ)*(base23) + (28813857/50000000000000 : ℝ)*(upper2) + (57786153/25000000000000 : ℝ)*(upper3) + (1752417/1562500000000 : ℝ)*(upper5) + (216934485311413/5000000000000 : ℝ)*(major0) + (216934485311413/5000000000000 : ℝ)*(major1) + (216934485311413/5000000000000 : ℝ)*(major2) + (1177612659/6250000000000 : ℝ)*(sp1) + (244739689/781250000000 : ℝ)*(sp2) + (23343011963873/400000000000 : ℝ)*(sp4) + (5835733292191193/100000000000000 : ℝ)*(sp5) + (1458930097265381/25000000000000 : ℝ)*(sp6) + (1420813136895649/50000000000000 : ℝ)*(sp7) + (1420813136895649/50000000000000 : ℝ)*(f.failure) + (23343011963873/400000000000 : ℝ)*(f.sum) + (375470959931/229750000000000000000000000 : ℝ)*base65 + (214332911149569841/45950000000000000000000000000000 : ℝ)*base68 + (203680034451169841/45950000000000000000000000000000 : ℝ)*base70 + (412448858115319841/45950000000000000000000000000000 : ℝ)*base72 + (4346255923967/919000000000000000000000000 : ℝ)*base73 + (387575810609369841/45950000000000000000000000000000 : ℝ)*base76 + (386581915142069841/45950000000000000000000000000000 : ℝ)*base78 + (779150796932969841/45950000000000000000000000000000 : ℝ)*base80 + (1143186999551/229750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (37481883/5000000000000000000000 : ℝ)*base90 + (37481883/5000000000000000000000 : ℝ)*base92 + (37481883/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1290_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152683333/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2937/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11009/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (551/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14673/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1290_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1290_s7_0 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2089767313/10000000000 : ℝ)*x 0 + (216612823/400000000 : ℝ)*x 1 + (1048585863/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2089767313/10000000000 : ℝ)^2125 ≤ (1589252053701/12500000000000 : ℝ)^1613 := by
    have hnat : (2089767313 : ℕ)^2125*12500000000000^1613 ≤ 1589252053701^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2089767313 10000000000 1589252053701 12500000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216612823/400000000 : ℝ)^2125 ≤ (22286450512067/50000000000000 : ℝ)^1613 := by
    have hnat : (216612823 : ℕ)^2125*50000000000000^1613 ≤ 22286450512067^1613*400000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216612823 400000000 22286450512067 50000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048585863/2000000000 : ℝ)^2125 ≤ (2669567657733/6250000000000 : ℝ)^1613 := by
    have hnat : (1048585863 : ℕ)^2125*6250000000000^1613 ≤ 2669567657733^1613*2000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048585863 2000000000 2669567657733 6250000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2089767313/10000000000 : ℝ), (216612823/400000000 : ℝ), (1048585863/2000000000 : ℝ)] ![(1589252053701/12500000000000 : ℝ), (22286450512067/50000000000000 : ℝ), (2669567657733/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2089767313/10000000000 : ℝ)|^2125 ≤ (1589252053701/12500000000000 : ℝ)^1613
        have hw : |(-2089767313/10000000000 : ℝ)|=(2089767313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(216612823/400000000 : ℝ)|^2125 ≤ (22286450512067/50000000000000 : ℝ)^1613
        have hw : |(216612823/400000000 : ℝ)|=(216612823/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048585863/2000000000 : ℝ)|^2125 ≤ (2669567657733/6250000000000 : ℝ)^1613
        have hw : |(1048585863/2000000000 : ℝ)|=(1048585863/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1290_s7_1 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (20897693/39062500 : ℝ)*x 0 + (-2177644809/10000000000 : ℝ)*x 1 + (2621464721/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20897693/39062500 : ℝ)^2125 ≤ (8772779078987/20000000000000 : ℝ)^1613 := by
    have hnat : (20897693 : ℕ)^2125*20000000000000^1613 ≤ 8772779078987^1613*39062500^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20897693 39062500 8772779078987 20000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2177644809/10000000000 : ℝ)^2125 ≤ (13423020699679/100000000000000 : ℝ)^1613 := by
    have hnat : (2177644809 : ℕ)^2125*100000000000000^1613 ≤ 13423020699679^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177644809 10000000000 13423020699679 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621464721/5000000000 : ℝ)^2125 ≤ (42713083886789/100000000000000 : ℝ)^1613 := by
    have hnat : (2621464721 : ℕ)^2125*100000000000000^1613 ≤ 42713083886789^1613*5000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621464721 5000000000 42713083886789 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(20897693/39062500 : ℝ), (-2177644809/10000000000 : ℝ), (2621464721/5000000000 : ℝ)] ![(8772779078987/20000000000000 : ℝ), (13423020699679/100000000000000 : ℝ), (42713083886789/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(20897693/39062500 : ℝ)|^2125 ≤ (8772779078987/20000000000000 : ℝ)^1613
        have hw : |(20897693/39062500 : ℝ)|=(20897693/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2177644809/10000000000 : ℝ)|^2125 ≤ (13423020699679/100000000000000 : ℝ)^1613
        have hw : |(-2177644809/10000000000 : ℝ)|=(2177644809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621464721/5000000000 : ℝ)|^2125 ≤ (42713083886789/100000000000000 : ℝ)^1613
        have hw : |(2621464721/5000000000 : ℝ)|=(2621464721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1290_s7_2 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5349809717/10000000000 : ℝ)*x 0 + (5242929059/10000000000 : ℝ)*x 1 + (-435528981/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349809717/10000000000 : ℝ)^2125 ≤ (43863898732671/100000000000000 : ℝ)^1613 := by
    have hnat : (5349809717 : ℕ)^2125*100000000000000^1613 ≤ 43863898732671^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349809717 10000000000 43863898732671 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242929059/10000000000 : ℝ)^2125 ≤ (21356539888071/50000000000000 : ℝ)^1613 := by
    have hnat : (5242929059 : ℕ)^2125*50000000000000^1613 ≤ 21356539888071^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242929059 10000000000 21356539888071 50000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (435528981/2000000000 : ℝ)^2125 ≤ (1677877684907/12500000000000 : ℝ)^1613 := by
    have hnat : (435528981 : ℕ)^2125*12500000000000^1613 ≤ 1677877684907^1613*2000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435528981 2000000000 1677877684907 12500000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349809717/10000000000 : ℝ), (5242929059/10000000000 : ℝ), (-435528981/2000000000 : ℝ)] ![(43863898732671/100000000000000 : ℝ), (21356539888071/50000000000000 : ℝ), (1677877684907/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349809717/10000000000 : ℝ)|^2125 ≤ (43863898732671/100000000000000 : ℝ)^1613
        have hw : |(5349809717/10000000000 : ℝ)|=(5349809717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242929059/10000000000 : ℝ)|^2125 ≤ (21356539888071/50000000000000 : ℝ)^1613
        have hw : |(5242929059/10000000000 : ℝ)|=(5242929059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-435528981/2000000000 : ℝ)|^2125 ≤ (1677877684907/12500000000000 : ℝ)^1613
        have hw : |(-435528981/2000000000 : ℝ)|=(435528981/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1290_s7_3 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (542550551/1250000000 : ℝ)*x 0 + (208342071/500000000 : ℝ)*x 1 + (4520875887/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (542550551/1250000000 : ℝ)^2125 ≤ (33302334950493/100000000000000 : ℝ)^1613 := by
    have hnat : (542550551 : ℕ)^2125*100000000000000^1613 ≤ 33302334950493^1613*1250000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542550551 1250000000 33302334950493 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (208342071/500000000 : ℝ)^2125 ≤ (31559182061507/100000000000000 : ℝ)^1613 := by
    have hnat : (208342071 : ℕ)^2125*100000000000000^1613 ≤ 31559182061507^1613*500000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208342071 500000000 31559182061507 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4520875887/10000000000 : ℝ)^2125 ≤ (35138482979923/100000000000000 : ℝ)^1613 := by
    have hnat : (4520875887 : ℕ)^2125*100000000000000^1613 ≤ 35138482979923^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4520875887 10000000000 35138482979923 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(542550551/1250000000 : ℝ), (208342071/500000000 : ℝ), (4520875887/10000000000 : ℝ)] ![(33302334950493/100000000000000 : ℝ), (31559182061507/100000000000000 : ℝ), (35138482979923/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(542550551/1250000000 : ℝ)|^2125 ≤ (33302334950493/100000000000000 : ℝ)^1613
        have hw : |(542550551/1250000000 : ℝ)|=(542550551/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(208342071/500000000 : ℝ)|^2125 ≤ (31559182061507/100000000000000 : ℝ)^1613
        have hw : |(208342071/500000000 : ℝ)|=(208342071/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4520875887/10000000000 : ℝ)|^2125 ≤ (35138482979923/100000000000000 : ℝ)^1613
        have hw : |(4520875887/10000000000 : ℝ)|=(4520875887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1290_s7_4 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1044889993/5000000000 : ℝ)*x 0 + (262177177/500000000 : ℝ)*x 1 + (1353675809/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1044889993/5000000000 : ℝ)^2125 ≤ (1589264750647/12500000000000 : ℝ)^1613 := by
    have hnat : (1044889993 : ℕ)^2125*12500000000000^1613 ≤ 1589264750647^1613*5000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044889993 5000000000 1589264750647 12500000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (262177177/500000000 : ℝ)^2125 ≤ (21359837488369/50000000000000 : ℝ)^1613 := by
    have hnat : (262177177 : ℕ)^2125*50000000000000^1613 ≤ 21359837488369^1613*500000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262177177 500000000 21359837488369 50000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1353675809/2500000000 : ℝ)^2125 ≤ (22283103500929/50000000000000 : ℝ)^1613 := by
    have hnat : (1353675809 : ℕ)^2125*50000000000000^1613 ≤ 22283103500929^1613*2500000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353675809 2500000000 22283103500929 50000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1044889993/5000000000 : ℝ), (262177177/500000000 : ℝ), (1353675809/2500000000 : ℝ)] ![(1589264750647/12500000000000 : ℝ), (21359837488369/50000000000000 : ℝ), (22283103500929/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1044889993/5000000000 : ℝ)|^2125 ≤ (1589264750647/12500000000000 : ℝ)^1613
        have hw : |(-1044889993/5000000000 : ℝ)|=(1044889993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(262177177/500000000 : ℝ)|^2125 ≤ (21359837488369/50000000000000 : ℝ)^1613
        have hw : |(262177177/500000000 : ℝ)|=(262177177/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1353675809/2500000000 : ℝ)|^2125 ≤ (22283103500929/50000000000000 : ℝ)^1613
        have hw : |(1353675809/2500000000 : ℝ)|=(1353675809/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1290_s7_5 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305684387/10000000000 : ℝ)*x 0 + (-2005870607/10000000000 : ℝ)*x 1 + (5414703199/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305684387/10000000000 : ℝ)^2125 ≤ (338967920151/781250000000 : ℝ)^1613 := by
    have hnat : (5305684387 : ℕ)^2125*781250000000^1613 ≤ 338967920151^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305684387 10000000000 338967920151 781250000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2005870607/10000000000 : ℝ)^2125 ≤ (12045899610691/100000000000000 : ℝ)^1613 := by
    have hnat : (2005870607 : ℕ)^2125*100000000000000^1613 ≤ 12045899610691^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2005870607 10000000000 12045899610691 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5414703199/10000000000 : ℝ)^2125 ≤ (44566206600661/100000000000000 : ℝ)^1613 := by
    have hnat : (5414703199 : ℕ)^2125*100000000000000^1613 ≤ 44566206600661^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414703199 10000000000 44566206600661 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305684387/10000000000 : ℝ), (-2005870607/10000000000 : ℝ), (5414703199/10000000000 : ℝ)] ![(338967920151/781250000000 : ℝ), (12045899610691/100000000000000 : ℝ), (44566206600661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305684387/10000000000 : ℝ)|^2125 ≤ (338967920151/781250000000 : ℝ)^1613
        have hw : |(5305684387/10000000000 : ℝ)|=(5305684387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2005870607/10000000000 : ℝ)|^2125 ≤ (12045899610691/100000000000000 : ℝ)^1613
        have hw : |(-2005870607/10000000000 : ℝ)|=(2005870607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5414703199/10000000000 : ℝ)|^2125 ≤ (44566206600661/100000000000000 : ℝ)^1613
        have hw : |(5414703199/10000000000 : ℝ)|=(5414703199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1290_s7_6 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1061136857/2000000000 : ℝ)*x 0 + (5414703287/10000000000 : ℝ)*x 1 + (-62683457/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061136857/2000000000 : ℝ)^2125 ≤ (10846973170111/25000000000000 : ℝ)^1613 := by
    have hnat : (1061136857 : ℕ)^2125*25000000000000^1613 ≤ 10846973170111^1613*2000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061136857 2000000000 10846973170111 25000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414703287/10000000000 : ℝ)^2125 ≤ (22283103777429/50000000000000 : ℝ)^1613 := by
    have hnat : (5414703287 : ℕ)^2125*50000000000000^1613 ≤ 22283103777429^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414703287 10000000000 22283103777429 50000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (62683457/312500000 : ℝ)^2125 ≤ (12045899745187/100000000000000 : ℝ)^1613 := by
    have hnat : (62683457 : ℕ)^2125*100000000000000^1613 ≤ 12045899745187^1613*312500000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62683457 312500000 12045899745187 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061136857/2000000000 : ℝ), (5414703287/10000000000 : ℝ), (-62683457/312500000 : ℝ)] ![(10846973170111/25000000000000 : ℝ), (22283103777429/50000000000000 : ℝ), (12045899745187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061136857/2000000000 : ℝ)|^2125 ≤ (10846973170111/25000000000000 : ℝ)^1613
        have hw : |(1061136857/2000000000 : ℝ)|=(1061136857/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414703287/10000000000 : ℝ)|^2125 ≤ (22283103777429/50000000000000 : ℝ)^1613
        have hw : |(5414703287/10000000000 : ℝ)|=(5414703287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-62683457/312500000 : ℝ)|^2125 ≤ (12045899745187/100000000000000 : ℝ)^1613
        have hw : |(-62683457/312500000 : ℝ)|=(62683457/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1290_s7_7 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1085107727/2500000000 : ℝ)*x 0 + (4519614253/10000000000 : ℝ)*x 1 + (1042027293/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1085107727/2500000000 : ℝ)^2125 ≤ (33302602815111/100000000000000 : ℝ)^1613 := by
    have hnat : (1085107727 : ℕ)^2125*100000000000000^1613 ≤ 33302602815111^1613*2500000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085107727 2500000000 33302602815111 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4519614253/10000000000 : ℝ)^2125 ≤ (4390695608147/12500000000000 : ℝ)^1613 := by
    have hnat : (4519614253 : ℕ)^2125*12500000000000^1613 ≤ 4390695608147^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4519614253 10000000000 4390695608147 12500000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1042027293/2500000000 : ℝ)^2125 ≤ (31571832296891/100000000000000 : ℝ)^1613 := by
    have hnat : (1042027293 : ℕ)^2125*100000000000000^1613 ≤ 31571832296891^1613*2500000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042027293 2500000000 31571832296891 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1085107727/2500000000 : ℝ), (4519614253/10000000000 : ℝ), (1042027293/2500000000 : ℝ)] ![(33302602815111/100000000000000 : ℝ), (4390695608147/12500000000000 : ℝ), (31571832296891/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1085107727/2500000000 : ℝ)|^2125 ≤ (33302602815111/100000000000000 : ℝ)^1613
        have hw : |(1085107727/2500000000 : ℝ)|=(1085107727/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4519614253/10000000000 : ℝ)|^2125 ≤ (4390695608147/12500000000000 : ℝ)^1613
        have hw : |(4519614253/10000000000 : ℝ)|=(4519614253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1042027293/2500000000 : ℝ)|^2125 ≤ (31571832296891/100000000000000 : ℝ)^1613
        have hw : |(1042027293/2500000000 : ℝ)|=(1042027293/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1290_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152683333/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14673/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (551/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (5511/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14671/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14673/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (551/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14673/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (551/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14673/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (551/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14673/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (551/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14673/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (551/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14673/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (551/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (551/5000 : ℝ) ^ (4249/1024 : ℝ) ≤ (1325942991055283/12500000000000000000 : ℝ) := by
    have hpowers : (551/5000 : ℝ)^4249 ≤ (1325942991055283/12500000000000000000 : ℝ)^1024 := by
      have hnat : (551 : ℕ)^4249*12500000000000000000^1024 ≤ 1325942991055283^1024*5000^4249 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        551 5000 1325942991055283 12500000000000000000 4249 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (551/5000 : ℝ)) (X := (1325942991055283/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4249 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14673/100000 : ℝ) ^ (4249/1024 : ℝ) ≤ (34797005805990813/100000000000000000000 : ℝ) := by
    have hpowers : (14673/100000 : ℝ)^4249 ≤ (34797005805990813/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14673 : ℕ)^4249*100000000000000000000^1024 ≤ 34797005805990813^1024*100000^4249 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14673 100000 34797005805990813 100000000000000000000 4249 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14673/100000 : ℝ)) (X := (34797005805990813/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4249 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251325942991055283/6250000000000000000 : ℝ) ≤ (5000255618982483/5000000000000000 : ℝ) ^ (4249/1024 : ℝ) := by
    have hpowers : (6251325942991055283/6250000000000000000 : ℝ)^1024 ≤ (5000255618982483/5000000000000000 : ℝ)^4249 := by
      have hnat : (6251325942991055283 : ℕ)^1024*5000000000000000^4249 ≤ 5000255618982483^4249*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251325942991055283 6250000000000000000 5000255618982483 5000000000000000 1024 4249 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000255618982483/5000000000000000 : ℝ)) (X := (6251325942991055283/6250000000000000000 : ℝ)) (by norm_num) 4249 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045404549734433077/100000000000000000000 : ℝ) ≤ (10001094051532119/10000000000000000 : ℝ) ^ (4249/1024 : ℝ) := by
    have hpowers : (100045404549734433077/100000000000000000000 : ℝ)^1024 ≤ (10001094051532119/10000000000000000 : ℝ)^4249 := by
      have hnat : (100045404549734433077 : ℕ)^1024*10000000000000000^4249 ≤ 10001094051532119^4249*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045404549734433077 100000000000000000000 10001094051532119 10000000000000000 1024 4249 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001094051532119/10000000000000000 : ℝ)) (X := (100045404549734433077/100000000000000000000 : ℝ)) (by norm_num) 4249 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034797005805990813/50000000000000000000 : ℝ) ≤ (1250209608137409/1250000000000000 : ℝ) ^ (4249/1024 : ℝ) := by
    have hpowers : (50034797005805990813/50000000000000000000 : ℝ)^1024 ≤ (1250209608137409/1250000000000000 : ℝ)^4249 := by
      have hnat : (50034797005805990813 : ℕ)^1024*1250000000000000^4249 ≤ 1250209608137409^4249*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034797005805990813 50000000000000000000 1250209608137409 1250000000000000 1024 4249 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250209608137409/1250000000000000 : ℝ)) (X := (50034797005805990813/50000000000000000000 : ℝ)) (by norm_num) 4249 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1325942991055283/12500000000000000000 : ℝ) ≤ ((18259511170632984339/18265000000000000000 : ℝ)+2*(582813567153/365300000000000 : ℝ)*(551/5000 : ℝ))^(4249/1024 : ℝ) := by
    rw [show (18259511170632984339/18265000000000000000 : ℝ)+2*(582813567153/365300000000000 : ℝ)*(551/5000 : ℝ)=(5000255618982483/5000000000000000 : ℝ) by norm_num, show 1+2*(1325942991055283/12500000000000000000 : ℝ)=(6251325942991055283/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34797005805990813/100000000000000000000 : ℝ)+(1325942991055283/12500000000000000000 : ℝ) ≤ ((18259511170632984339/18265000000000000000 : ℝ)+(582813567153/365300000000000 : ℝ)*((14673/100000 : ℝ)+(551/5000 : ℝ)))^(4249/1024 : ℝ) := by
    rw [show (18259511170632984339/18265000000000000000 : ℝ)+(582813567153/365300000000000 : ℝ)*((14673/100000 : ℝ)+(551/5000 : ℝ))=(10001094051532119/10000000000000000 : ℝ) by norm_num, show 1+(34797005805990813/100000000000000000000 : ℝ)+(1325942991055283/12500000000000000000 : ℝ)=(100045404549734433077/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34797005805990813/100000000000000000000 : ℝ) ≤ ((18259511170632984339/18265000000000000000 : ℝ)+2*(582813567153/365300000000000 : ℝ)*(14673/100000 : ℝ))^(4249/1024 : ℝ) := by
    rw [show (18259511170632984339/18265000000000000000 : ℝ)+2*(582813567153/365300000000000 : ℝ)*(14673/100000 : ℝ)=(1250209608137409/1250000000000000 : ℝ) by norm_num, show 1+2*(34797005805990813/100000000000000000000 : ℝ)=(50034797005805990813/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18259511170632984339/18265000000000000000 : ℝ)*(X 1 0+X 2 0)+(582813567153/365300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4249/1024 : ℝ)) (lo := (551/5000 : ℝ)) (hi := (14673/100000 : ℝ)) (c := (18259511170632984339/18265000000000000000 : ℝ)) (alpha := (582813567153/365300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18259511170632984339/18265000000000000000 : ℝ)*(X 0 1+X 2 1)+(582813567153/365300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4249/1024 : ℝ)) (lo := (551/5000 : ℝ)) (hi := (14673/100000 : ℝ)) (c := (18259511170632984339/18265000000000000000 : ℝ)) (alpha := (582813567153/365300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18259511170632984339/18265000000000000000 : ℝ)*(X 0 2+X 1 2)+(582813567153/365300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4249/1024 : ℝ)) (lo := (551/5000 : ℝ)) (hi := (14673/100000 : ℝ)) (c := (18259511170632984339/18265000000000000000 : ℝ)) (alpha := (582813567153/365300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2089767313/10000000000 : ℝ)*X 0 0+(216612823/400000000 : ℝ)*X 0 1+(1048585863/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((20897693/39062500 : ℝ)*X 1 0+(-2177644809/10000000000 : ℝ)*X 1 1+(2621464721/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349809717/10000000000 : ℝ)*X 2 0+(5242929059/10000000000 : ℝ)*X 2 1+(-435528981/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((542550551/1250000000 : ℝ)*X 0 0+(208342071/500000000 : ℝ)*X 0 1+(4520875887/10000000000 : ℝ)*X 0 2+(542550551/1250000000 : ℝ)*X 1 0+(208342071/500000000 : ℝ)*X 1 1+(4520875887/10000000000 : ℝ)*X 1 2+(542550551/1250000000 : ℝ)*X 2 0+(208342071/500000000 : ℝ)*X 2 1+(4520875887/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1044889993/5000000000 : ℝ)*X 0 0+(262177177/500000000 : ℝ)*X 0 1+(1353675809/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305684387/10000000000 : ℝ)*X 1 0+(-2005870607/10000000000 : ℝ)*X 1 1+(5414703199/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1061136857/2000000000 : ℝ)*X 2 0+(5414703287/10000000000 : ℝ)*X 2 1+(-62683457/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1085107727/2500000000 : ℝ)*X 0 0+(4519614253/10000000000 : ℝ)*X 0 1+(1042027293/2500000000 : ℝ)*X 0 2+(1085107727/2500000000 : ℝ)*X 1 0+(4519614253/10000000000 : ℝ)*X 1 1+(1042027293/2500000000 : ℝ)*X 1 2+(1085107727/2500000000 : ℝ)*X 2 0+(4519614253/10000000000 : ℝ)*X 2 1+(1042027293/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2890293551467816829456347089/228312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (81014063/5000000000000 : ℝ)*(base19) + (475445253/25000000000000 : ℝ)*(base23) + (987249/400000000000 : ℝ)*(upper3) + (28648513/100000000000000 : ℝ)*(upper4) + (15487899/10000000000000 : ℝ)*(upper5) + (1078181020292417/25000000000000 : ℝ)*(major0) + (1078181020292417/25000000000000 : ℝ)*(major1) + (1078181020292417/25000000000000 : ℝ)*(major2) + (2900396434643011/50000000000000 : ℝ)*(sp0) + (2900413020550833/50000000000000 : ℝ)*(sp1) + (5800825759601913/100000000000000 : ℝ)*(sp2) + (8826876447981/312500000000 : ℝ)*(sp3) + (4349012113/12500000000000 : ℝ)*(sp4) + (19615623311/100000000000000 : ℝ)*(sp7) + (282462007897723/10000000000000 : ℝ)*(f.failure) + (2900413830691463/50000000000000 : ℝ)*(f.sum) + (1630045595533/9132500000000000000000000000 : ℝ)*base66 + (7852711837664617637/456625000000000000000000000000000 : ℝ)*base68 + (9328674940813242637/456625000000000000000000000000000 : ℝ)*base70 + (1696080123123007363/456625000000000000000000000000000 : ℝ)*base71 + (113530513053381/18265000000000000000000000000 : ℝ)*base74 + (2757263148312492637/456625000000000000000000000000000 : ℝ)*base76 + (432180985106882363/456625000000000000000000000000000 : ℝ)*base77 + (4848113427567242637/456625000000000000000000000000000 : ℝ)*base80 + (117813034141551/18265000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (9249241/1000000000000000000000 : ℝ)*base90 + (9249241/1000000000000000000000 : ℝ)*base92 + (9249241/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (120231406158181077955593/18265000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1317906447/100000000000000 : ℝ)*(base19) + (26841873/2000000000000 : ℝ)*(base23) + (113919013/25000000000000 : ℝ)*(lower1) + (127006039/100000000000000 : ℝ)*(upper3) + (6298971/10000000000000 : ℝ)*(lower4) + (50033037/50000000000000 : ℝ)*(upper5) + (2171840789786509/50000000000000 : ℝ)*(major0) + (2171840789786509/50000000000000 : ℝ)*(major1) + (2171840789786509/50000000000000 : ℝ)*(major2) + (1069271113/50000000000000 : ℝ)*(sp2) + (2921233618409043/50000000000000 : ℝ)*(sp4) + (146061647972791/2500000000000 : ℝ)*(sp5) + (584246375618221/10000000000000 : ℝ)*(sp6) + (568979140581509/20000000000000 : ℝ)*(sp7) + (568979140581509/20000000000000 : ℝ)*(f.failure) + (2921233618409043/50000000000000 : ℝ)*(f.sum) + (28611749200603/9132500000000000000000000000 : ℝ)*base66 + (607257241738082551/913250000000000000000000000000000 : ℝ)*base67 + (4140780661167332551/913250000000000000000000000000000 : ℝ)*base69 + (826510751110667449/913250000000000000000000000000000 : ℝ)*base72 + (43630364135429/18265000000000000000000000000 : ℝ)*base73 + (16954207629780667449/913250000000000000000000000000000 : ℝ)*base76 + (7842659093469667449/913250000000000000000000000000000 : ℝ)*base78 + (5491861475715082551/913250000000000000000000000000000 : ℝ)*base79 + (29292424730963/2283125000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (7710503/2000000000000000000000 : ℝ)*base90 + (7710503/2000000000000000000000 : ℝ)*base92 + (7710503/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1290_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152683333/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14673/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (551/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5511/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14671/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1290_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1290_s8_0 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2089769067/10000000000 : ℝ)*x 0 + (1083060559/2000000000 : ℝ)*x 1 + (524294597/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2089769067/10000000000 : ℝ)^2125 ≤ (12714030488111/100000000000000 : ℝ)^1613 := by
    have hnat : (2089769067 : ℕ)^2125*100000000000000^1613 ≤ 12714030488111^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2089769067 10000000000 12714030488111 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1083060559/2000000000 : ℝ)^2125 ≤ (22286354113/50000000000 : ℝ)^1613 := by
    have hnat : (1083060559 : ℕ)^2125*50000000000^1613 ≤ 22286354113^1613*2000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083060559 2000000000 22286354113 50000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524294597/1000000000 : ℝ)^2125 ≤ (21356630638981/50000000000000 : ℝ)^1613 := by
    have hnat : (524294597 : ℕ)^2125*50000000000000^1613 ≤ 21356630638981^1613*1000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524294597 1000000000 21356630638981 50000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2089769067/10000000000 : ℝ), (1083060559/2000000000 : ℝ), (524294597/1000000000 : ℝ)] ![(12714030488111/100000000000000 : ℝ), (22286354113/50000000000 : ℝ), (21356630638981/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2089769067/10000000000 : ℝ)|^2125 ≤ (12714030488111/100000000000000 : ℝ)^1613
        have hw : |(-2089769067/10000000000 : ℝ)|=(2089769067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1083060559/2000000000 : ℝ)|^2125 ≤ (22286354113/50000000000 : ℝ)^1613
        have hw : |(1083060559/2000000000 : ℝ)|=(1083060559/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(524294597/1000000000 : ℝ)|^2125 ≤ (21356630638981/50000000000000 : ℝ)^1613
        have hw : |(524294597/1000000000 : ℝ)|=(524294597/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1290_s8_1 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5349805247/10000000000 : ℝ)*x 0 + (-2177628477/10000000000 : ℝ)*x 1 + (5242945987/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349805247/10000000000 : ℝ)^2125 ≤ (1370745326529/3125000000000 : ℝ)^1613 := by
    have hnat : (5349805247 : ℕ)^2125*3125000000000^1613 ≤ 1370745326529^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349805247 10000000000 1370745326529 3125000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2177628477/10000000000 : ℝ)^2125 ≤ (134228880743/1000000000000 : ℝ)^1613 := by
    have hnat : (2177628477 : ℕ)^2125*1000000000000^1613 ≤ 134228880743^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177628477 10000000000 134228880743 1000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242945987/10000000000 : ℝ)^2125 ≤ (42713261460419/100000000000000 : ℝ)^1613 := by
    have hnat : (5242945987 : ℕ)^2125*100000000000000^1613 ≤ 42713261460419^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242945987 10000000000 42713261460419 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349805247/10000000000 : ℝ), (-2177628477/10000000000 : ℝ), (5242945987/10000000000 : ℝ)] ![(1370745326529/3125000000000 : ℝ), (134228880743/1000000000000 : ℝ), (42713261460419/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349805247/10000000000 : ℝ)|^2125 ≤ (1370745326529/3125000000000 : ℝ)^1613
        have hw : |(5349805247/10000000000 : ℝ)|=(5349805247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2177628477/10000000000 : ℝ)|^2125 ≤ (134228880743/1000000000000 : ℝ)^1613
        have hw : |(-2177628477/10000000000 : ℝ)|=(2177628477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242945987/10000000000 : ℝ)|^2125 ≤ (42713261460419/100000000000000 : ℝ)^1613
        have hw : |(5242945987/10000000000 : ℝ)|=(5242945987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1290_s8_2 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1337451311/2500000000 : ℝ)*x 0 + (209717839/400000000 : ℝ)*x 1 + (-2177628497/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337451311/2500000000 : ℝ)^2125 ≤ (43863850416523/100000000000000 : ℝ)^1613 := by
    have hnat : (1337451311 : ℕ)^2125*100000000000000^1613 ≤ 43863850416523^1613*2500000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337451311 2500000000 43863850416523 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209717839/400000000 : ℝ)^2125 ≤ (341706090653/800000000000 : ℝ)^1613 := by
    have hnat : (209717839 : ℕ)^2125*800000000000^1613 ≤ 341706090653^1613*400000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209717839 400000000 341706090653 800000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2177628497/10000000000 : ℝ)^2125 ≤ (1677861029589/12500000000000 : ℝ)^1613 := by
    have hnat : (2177628497 : ℕ)^2125*12500000000000^1613 ≤ 1677861029589^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177628497 10000000000 1677861029589 12500000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337451311/2500000000 : ℝ), (209717839/400000000 : ℝ), (-2177628497/10000000000 : ℝ)] ![(43863850416523/100000000000000 : ℝ), (341706090653/800000000000 : ℝ), (1677861029589/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337451311/2500000000 : ℝ)|^2125 ≤ (43863850416523/100000000000000 : ℝ)^1613
        have hw : |(1337451311/2500000000 : ℝ)|=(1337451311/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(209717839/400000000 : ℝ)|^2125 ≤ (341706090653/800000000000 : ℝ)^1613
        have hw : |(209717839/400000000 : ℝ)|=(209717839/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2177628497/10000000000 : ℝ)|^2125 ≤ (1677861029589/12500000000000 : ℝ)^1613
        have hw : |(-2177628497/10000000000 : ℝ)|=(2177628497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1290_s8_3 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1085101511/2500000000 : ℝ)*x 0 + (130214893/312500000 : ℝ)*x 1 + (4520840013/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1085101511/2500000000 : ℝ)^2125 ≤ (1040698483979/3125000000000 : ℝ)^1613 := by
    have hnat : (1085101511 : ℕ)^2125*3125000000000^1613 ≤ 1040698483979^1613*2500000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085101511 2500000000 1040698483979 3125000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (130214893/312500000 : ℝ)^2125 ≤ (3155953284841/10000000000000 : ℝ)^1613 := by
    have hnat : (130214893 : ℕ)^2125*10000000000000^1613 ≤ 3155953284841^1613*312500000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130214893 312500000 3155953284841 10000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4520840013/10000000000 : ℝ)^2125 ≤ (8784528910821/25000000000000 : ℝ)^1613 := by
    have hnat : (4520840013 : ℕ)^2125*25000000000000^1613 ≤ 8784528910821^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4520840013 10000000000 8784528910821 25000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1085101511/2500000000 : ℝ), (130214893/312500000 : ℝ), (4520840013/10000000000 : ℝ)] ![(1040698483979/3125000000000 : ℝ), (3155953284841/10000000000000 : ℝ), (8784528910821/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1085101511/2500000000 : ℝ)|^2125 ≤ (1040698483979/3125000000000 : ℝ)^1613
        have hw : |(1085101511/2500000000 : ℝ)|=(1085101511/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(130214893/312500000 : ℝ)|^2125 ≤ (3155953284841/10000000000000 : ℝ)^1613
        have hw : |(130214893/312500000 : ℝ)|=(130214893/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4520840013/10000000000 : ℝ)|^2125 ≤ (8784528910821/25000000000000 : ℝ)^1613
        have hw : |(4520840013/10000000000 : ℝ)|=(4520840013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1290_s8_4 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-522445483/2500000000 : ℝ)*x 0 + (1310890163/2500000000 : ℝ)*x 1 + (5414684859/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (522445483/2500000000 : ℝ)^2125 ≤ (12714133602609/100000000000000 : ℝ)^1613 := by
    have hnat : (522445483 : ℕ)^2125*100000000000000^1613 ≤ 12714133602609^1613*2500000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522445483 2500000000 12714133602609 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310890163/2500000000 : ℝ)^2125 ≤ (21359929321339/50000000000000 : ℝ)^1613 := by
    have hnat : (1310890163 : ℕ)^2125*50000000000000^1613 ≤ 21359929321339^1613*2500000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310890163 2500000000 21359929321339 50000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5414684859/10000000000 : ℝ)^2125 ≤ (8913201547469/20000000000000 : ℝ)^1613 := by
    have hnat : (5414684859 : ℕ)^2125*20000000000000^1613 ≤ 8913201547469^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414684859 10000000000 8913201547469 20000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-522445483/2500000000 : ℝ), (1310890163/2500000000 : ℝ), (5414684859/10000000000 : ℝ)] ![(12714133602609/100000000000000 : ℝ), (21359929321339/50000000000000 : ℝ), (8913201547469/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-522445483/2500000000 : ℝ)|^2125 ≤ (12714133602609/100000000000000 : ℝ)^1613
        have hw : |(-522445483/2500000000 : ℝ)|=(522445483/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310890163/2500000000 : ℝ)|^2125 ≤ (21359929321339/50000000000000 : ℝ)^1613
        have hw : |(1310890163/2500000000 : ℝ)|=(1310890163/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5414684859/10000000000 : ℝ)|^2125 ≤ (8913201547469/20000000000000 : ℝ)^1613
        have hw : |(5414684859/10000000000 : ℝ)|=(5414684859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1290_s8_5 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4340432271/10000000000 : ℝ)*x 0 + (903915917/2000000000 : ℝ)*x 1 + (4168143363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4340432271/10000000000 : ℝ)^2125 ≤ (33302616592463/100000000000000 : ℝ)^1613 := by
    have hnat : (4340432271 : ℕ)^2125*100000000000000^1613 ≤ 33302616592463^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4340432271 10000000000 33302616592463 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (903915917/2000000000 : ℝ)^2125 ≤ (3512520990897/10000000000000 : ℝ)^1613 := by
    have hnat : (903915917 : ℕ)^2125*10000000000000^1613 ≤ 3512520990897^1613*2000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903915917 2000000000 3512520990897 10000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4168143363/10000000000 : ℝ)^2125 ≤ (31572173487947/100000000000000 : ℝ)^1613 := by
    have hnat : (4168143363 : ℕ)^2125*100000000000000^1613 ≤ 31572173487947^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4168143363 10000000000 31572173487947 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4340432271/10000000000 : ℝ), (903915917/2000000000 : ℝ), (4168143363/10000000000 : ℝ)] ![(33302616592463/100000000000000 : ℝ), (3512520990897/10000000000000 : ℝ), (31572173487947/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4340432271/10000000000 : ℝ)|^2125 ≤ (33302616592463/100000000000000 : ℝ)^1613
        have hw : |(4340432271/10000000000 : ℝ)|=(4340432271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(903915917/2000000000 : ℝ)|^2125 ≤ (3512520990897/10000000000000 : ℝ)^1613
        have hw : |(903915917/2000000000 : ℝ)|=(903915917/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4168143363/10000000000 : ℝ)|^2125 ≤ (31572173487947/100000000000000 : ℝ)^1613
        have hw : |(4168143363/10000000000 : ℝ)|=(4168143363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1290_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152683333/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14671/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5511/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11023/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14671/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14671/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5511/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14671/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5511/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14671/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5511/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14671/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5511/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14671/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5511/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14671/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5511/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5511/50000 : ℝ) ^ (4249/1024 : ℝ) ≤ (5307767215826137/50000000000000000000 : ℝ) := by
    have hpowers : (5511/50000 : ℝ)^4249 ≤ (5307767215826137/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5511 : ℕ)^4249*50000000000000000000^1024 ≤ 5307767215826137^1024*50000^4249 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5511 50000 5307767215826137 50000000000000000000 4249 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5511/50000 : ℝ)) (X := (5307767215826137/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4249 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14671/100000 : ℝ) ^ (4249/1024 : ℝ) ≤ (17388664683342161/50000000000000000000 : ℝ) := by
    have hpowers : (14671/100000 : ℝ)^4249 ≤ (17388664683342161/50000000000000000000 : ℝ)^1024 := by
      have hnat : (14671 : ℕ)^4249*50000000000000000000^1024 ≤ 17388664683342161^1024*100000^4249 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14671 100000 17388664683342161 50000000000000000000 4249 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14671/100000 : ℝ)) (X := (17388664683342161/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4249 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005307767215826137/25000000000000000000 : ℝ) ≤ (625031976440113/625000000000000 : ℝ) ^ (4249/1024 : ℝ) := by
    have hpowers : (25005307767215826137/25000000000000000000 : ℝ)^1024 ≤ (625031976440113/625000000000000 : ℝ)^4249 := by
      have hnat : (25005307767215826137 : ℕ)^1024*625000000000000^4249 ≤ 625031976440113^4249*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005307767215826137 25000000000000000000 625031976440113 625000000000000 1024 4249 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625031976440113/625000000000000 : ℝ)) (X := (25005307767215826137/25000000000000000000 : ℝ)) (by norm_num) 4249 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011348215949584149/25000000000000000000 : ℝ) ≤ (10001093770000539/10000000000000000 : ℝ) ^ (4249/1024 : ℝ) := by
    have hpowers : (25011348215949584149/25000000000000000000 : ℝ)^1024 ≤ (10001093770000539/10000000000000000 : ℝ)^4249 := by
      have hnat : (25011348215949584149 : ℕ)^1024*10000000000000000^4249 ≤ 10001093770000539^4249*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011348215949584149 25000000000000000000 10001093770000539 10000000000000000 1024 4249 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001093770000539/10000000000000000 : ℝ)) (X := (25011348215949584149/25000000000000000000 : ℝ)) (by norm_num) 4249 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017388664683342161/25000000000000000000 : ℝ) ≤ (1000167591695927/1000000000000000 : ℝ) ^ (4249/1024 : ℝ) := by
    have hpowers : (25017388664683342161/25000000000000000000 : ℝ)^1024 ≤ (1000167591695927/1000000000000000 : ℝ)^4249 := by
      have hnat : (25017388664683342161 : ℕ)^1024*1000000000000000^4249 ≤ 1000167591695927^4249*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017388664683342161 25000000000000000000 1000167591695927 1000000000000000 1024 4249 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000167591695927/1000000000000000 : ℝ)) (X := (25017388664683342161/25000000000000000000 : ℝ)) (by norm_num) 4249 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5307767215826137/50000000000000000000 : ℝ) ≤ ((9119758516230322807/9122500000000000000 : ℝ)+2*(582146958731/364900000000000 : ℝ)*(5511/50000 : ℝ))^(4249/1024 : ℝ) := by
    rw [show (9119758516230322807/9122500000000000000 : ℝ)+2*(582146958731/364900000000000 : ℝ)*(5511/50000 : ℝ)=(625031976440113/625000000000000 : ℝ) by norm_num, show 1+2*(5307767215826137/50000000000000000000 : ℝ)=(25005307767215826137/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17388664683342161/50000000000000000000 : ℝ)+(5307767215826137/50000000000000000000 : ℝ) ≤ ((9119758516230322807/9122500000000000000 : ℝ)+(582146958731/364900000000000 : ℝ)*((14671/100000 : ℝ)+(5511/50000 : ℝ)))^(4249/1024 : ℝ) := by
    rw [show (9119758516230322807/9122500000000000000 : ℝ)+(582146958731/364900000000000 : ℝ)*((14671/100000 : ℝ)+(5511/50000 : ℝ))=(10001093770000539/10000000000000000 : ℝ) by norm_num, show 1+(17388664683342161/50000000000000000000 : ℝ)+(5307767215826137/50000000000000000000 : ℝ)=(25011348215949584149/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17388664683342161/50000000000000000000 : ℝ) ≤ ((9119758516230322807/9122500000000000000 : ℝ)+2*(582146958731/364900000000000 : ℝ)*(14671/100000 : ℝ))^(4249/1024 : ℝ) := by
    rw [show (9119758516230322807/9122500000000000000 : ℝ)+2*(582146958731/364900000000000 : ℝ)*(14671/100000 : ℝ)=(1000167591695927/1000000000000000 : ℝ) by norm_num, show 1+2*(17388664683342161/50000000000000000000 : ℝ)=(25017388664683342161/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9119758516230322807/9122500000000000000 : ℝ)*(X 1 0+X 2 0)+(582146958731/364900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4249/1024 : ℝ)) (lo := (5511/50000 : ℝ)) (hi := (14671/100000 : ℝ)) (c := (9119758516230322807/9122500000000000000 : ℝ)) (alpha := (582146958731/364900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9119758516230322807/9122500000000000000 : ℝ)*(X 0 1+X 2 1)+(582146958731/364900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4249/1024 : ℝ)) (lo := (5511/50000 : ℝ)) (hi := (14671/100000 : ℝ)) (c := (9119758516230322807/9122500000000000000 : ℝ)) (alpha := (582146958731/364900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9119758516230322807/9122500000000000000 : ℝ)*(X 0 2+X 1 2)+(582146958731/364900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4249/1024 : ℝ)) (lo := (5511/50000 : ℝ)) (hi := (14671/100000 : ℝ)) (c := (9119758516230322807/9122500000000000000 : ℝ)) (alpha := (582146958731/364900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2089769067/10000000000 : ℝ)*X 0 0+(1083060559/2000000000 : ℝ)*X 0 1+(524294597/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349805247/10000000000 : ℝ)*X 1 0+(-2177628477/10000000000 : ℝ)*X 1 1+(5242945987/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337451311/2500000000 : ℝ)*X 2 0+(209717839/400000000 : ℝ)*X 2 1+(-2177628497/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1085101511/2500000000 : ℝ)*X 0 0+(130214893/312500000 : ℝ)*X 0 1+(4520840013/10000000000 : ℝ)*X 0 2+(1085101511/2500000000 : ℝ)*X 1 0+(130214893/312500000 : ℝ)*X 1 1+(4520840013/10000000000 : ℝ)*X 1 2+(1085101511/2500000000 : ℝ)*X 2 0+(130214893/312500000 : ℝ)*X 2 1+(4520840013/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-522445483/2500000000 : ℝ)*X 0 0+(1310890163/2500000000 : ℝ)*X 0 1+(5414684859/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4340432271/10000000000 : ℝ)*X 0 0+(903915917/2000000000 : ℝ)*X 0 1+(4168143363/10000000000 : ℝ)*X 0 2+(4340432271/10000000000 : ℝ)*X 1 0+(903915917/2000000000 : ℝ)*X 1 1+(4168143363/10000000000 : ℝ)*X 1 2+(4340432271/10000000000 : ℝ)*X 2 0+(903915917/2000000000 : ℝ)*X 2 1+(4168143363/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s8_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (23809901207105701690887/4561250000000000000000000000 : ℝ) := by norm_num
    linear_combination (504114161/50000000000000 : ℝ)*(base19) + (187437247/20000000000000 : ℝ)*(base23) + (7253109/20000000000000 : ℝ)*(lower2) + (3621807/2500000000000 : ℝ)*(upper3) + (4378901/6250000000000 : ℝ)*(upper5) + (2156782506539817/50000000000000 : ℝ)*(major0) + (2156782506539817/50000000000000 : ℝ)*(major1) + (2156782506539817/50000000000000 : ℝ)*(major2) + (5801938938576943/100000000000000 : ℝ)*(sp0) + (2900978998158407/50000000000000 : ℝ)*(sp1) + (5801958067358901/100000000000000 : ℝ)*(sp2) + (2825159987543151/100000000000000 : ℝ)*(sp3) + (20065968193/100000000000000 : ℝ)*(sp4) + (1357508711/12500000000000 : ℝ)*(sp5) + (70629271190321/2500000000000 : ℝ)*(f.failure) + (362622437784071/6250000000000 : ℝ)*(f.sum) + (68345787170879/18245000000000000000000000000 : ℝ)*base65 + (185592492305256319/456125000000000000000000000000000 : ℝ)*base67 + (330460881639881319/456125000000000000000000000000000 : ℝ)*base69 + (1182781554770631319/456125000000000000000000000000000 : ℝ)*base71 + (9626710618289/4561250000000000000000000000 : ℝ)*base74 + (1536215136576243681/456125000000000000000000000000000 : ℝ)*base76 + (1366206315868618681/456125000000000000000000000000000 : ℝ)*base78 + (2108522839712993681/456125000000000000000000000000000 : ℝ)*base80 + (4212351015813/2280625000000000000000000000 : ℝ)*base81 + (2619893/250000000000000000000 : ℝ)*base89 + (2619893/250000000000000000000 : ℝ)*base91 + (2619893/250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1290_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152683333/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14671/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5511/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11023/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14671/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1290_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1290_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152683333/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2937/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11009/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11023/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14671/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1290_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1290_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1290_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152683333/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2937/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11009/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11023/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14671/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1290_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
