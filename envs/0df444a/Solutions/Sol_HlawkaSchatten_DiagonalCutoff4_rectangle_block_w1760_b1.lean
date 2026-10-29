-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1760_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:25:27.799461+00:00
-- url     : https://prove2.me/submissions/159a588b-d33a-4f80-a7b3-d00e07b3132e

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
theorem support_rectangle_w1760_s3_0 (p : ℝ) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1168622087/10000000000 : ℝ)*x 0 + (1096773797/2000000000 : ℝ)*x 1 + (203349579/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1168622087/10000000000 : ℝ)^5935 ≤ (7469188361821/100000000000000 : ℝ)^4911 := by
    have hnat : (1168622087 : ℕ)^5935*100000000000000^4911 ≤ 7469188361821^4911*10000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1168622087 10000000000 7469188361821 100000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1096773797/2000000000 : ℝ)^5935 ≤ (48381989511441/100000000000000 : ℝ)^4911 := by
    have hnat : (1096773797 : ℕ)^5935*100000000000000^4911 ≤ 48381989511441^4911*2000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1096773797 2000000000 48381989511441 100000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (203349579/400000000 : ℝ)^5935 ≤ (22074411058909/50000000000000 : ℝ)^4911 := by
    have hnat : (203349579 : ℕ)^5935*50000000000000^4911 ≤ 22074411058909^4911*400000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      203349579 400000000 22074411058909 50000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5935/1024 : ℝ)) 5935 4911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1168622087/10000000000 : ℝ), (1096773797/2000000000 : ℝ), (203349579/400000000 : ℝ)] ![(7469188361821/100000000000000 : ℝ), (48381989511441/100000000000000 : ℝ), (22074411058909/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1168622087/10000000000 : ℝ)|^5935 ≤ (7469188361821/100000000000000 : ℝ)^4911
        have hw : |(-1168622087/10000000000 : ℝ)|=(1168622087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1096773797/2000000000 : ℝ)|^5935 ≤ (48381989511441/100000000000000 : ℝ)^4911
        have hw : |(1096773797/2000000000 : ℝ)|=(1096773797/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(203349579/400000000 : ℝ)|^5935 ≤ (22074411058909/50000000000000 : ℝ)^4911
        have hw : |(203349579/400000000 : ℝ)|=(203349579/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1760_s3_1 (p : ℝ) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5329335387/10000000000 : ℝ)*x 0 + (-688790183/5000000000 : ℝ)*x 1 + (2541869653/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5329335387/10000000000 : ℝ)^5935 ≤ (46739196170851/100000000000000 : ℝ)^4911 := by
    have hnat : (5329335387 : ℕ)^5935*100000000000000^4911 ≤ 46739196170851^4911*10000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5329335387 10000000000 46739196170851 100000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (688790183/5000000000 : ℝ)^5935 ≤ (1822396693011/20000000000000 : ℝ)^4911 := by
    have hnat : (688790183 : ℕ)^5935*20000000000000^4911 ≤ 1822396693011^4911*5000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      688790183 5000000000 1822396693011 20000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2541869653/5000000000 : ℝ)^5935 ≤ (22074410172073/50000000000000 : ℝ)^4911 := by
    have hnat : (2541869653 : ℕ)^5935*50000000000000^4911 ≤ 22074410172073^4911*5000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2541869653 5000000000 22074410172073 50000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5935/1024 : ℝ)) 5935 4911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5329335387/10000000000 : ℝ), (-688790183/5000000000 : ℝ), (2541869653/5000000000 : ℝ)] ![(46739196170851/100000000000000 : ℝ), (1822396693011/20000000000000 : ℝ), (22074410172073/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5329335387/10000000000 : ℝ)|^5935 ≤ (46739196170851/100000000000000 : ℝ)^4911
        have hw : |(5329335387/10000000000 : ℝ)|=(5329335387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-688790183/5000000000 : ℝ)|^5935 ≤ (1822396693011/20000000000000 : ℝ)^4911
        have hw : |(-688790183/5000000000 : ℝ)|=(688790183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2541869653/5000000000 : ℝ)|^5935 ≤ (22074410172073/50000000000000 : ℝ)^4911
        have hw : |(2541869653/5000000000 : ℝ)|=(2541869653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1760_s3_2 (p : ℝ) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1065867093/2000000000 : ℝ)*x 0 + (1016747863/2000000000 : ℝ)*x 1 + (-1377580251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1065867093/2000000000 : ℝ)^5935 ≤ (46739196997561/100000000000000 : ℝ)^4911 := by
    have hnat : (1065867093 : ℕ)^5935*100000000000000^4911 ≤ 46739196997561^4911*2000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065867093 2000000000 46739196997561 100000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1016747863/2000000000 : ℝ)^5935 ≤ (22074410219301/50000000000000 : ℝ)^4911 := by
    have hnat : (1016747863 : ℕ)^5935*50000000000000^4911 ≤ 22074410219301^4911*2000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1016747863 2000000000 22074410219301 50000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1377580251/10000000000 : ℝ)^5935 ≤ (4555991272891/50000000000000 : ℝ)^4911 := by
    have hnat : (1377580251 : ℕ)^5935*50000000000000^4911 ≤ 4555991272891^4911*10000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1377580251 10000000000 4555991272891 50000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5935/1024 : ℝ)) 5935 4911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1065867093/2000000000 : ℝ), (1016747863/2000000000 : ℝ), (-1377580251/10000000000 : ℝ)] ![(46739196997561/100000000000000 : ℝ), (22074410219301/50000000000000 : ℝ), (4555991272891/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1065867093/2000000000 : ℝ)|^5935 ≤ (46739196997561/100000000000000 : ℝ)^4911
        have hw : |(1065867093/2000000000 : ℝ)|=(1065867093/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1016747863/2000000000 : ℝ)|^5935 ≤ (22074410219301/50000000000000 : ℝ)^4911
        have hw : |(1016747863/2000000000 : ℝ)|=(1016747863/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1377580251/10000000000 : ℝ)|^5935 ≤ (4555991272891/50000000000000 : ℝ)^4911
        have hw : |(-1377580251/10000000000 : ℝ)|=(1377580251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1760_s3_3 (p : ℝ) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (250039653/625000000 : ℝ)*x 0 + (3346837321/10000000000 : ℝ)*x 1 + (94305217/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (250039653/625000000 : ℝ)^5935 ≤ (33049748745573/100000000000000 : ℝ)^4911 := by
    have hnat : (250039653 : ℕ)^5935*100000000000000^4911 ≤ 33049748745573^4911*625000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      250039653 625000000 33049748745573 100000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3346837321/10000000000 : ℝ)^5935 ≤ (26638848565253/100000000000000 : ℝ)^4911 := by
    have hnat : (3346837321 : ℕ)^5935*100000000000000^4911 ≤ 26638848565253^4911*10000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3346837321 10000000000 26638848565253 100000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (94305217/200000000 : ℝ)^5935 ≤ (20155701335873/50000000000000 : ℝ)^4911 := by
    have hnat : (94305217 : ℕ)^5935*50000000000000^4911 ≤ 20155701335873^4911*200000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94305217 200000000 20155701335873 50000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5935/1024 : ℝ)) 5935 4911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(250039653/625000000 : ℝ), (3346837321/10000000000 : ℝ), (94305217/200000000 : ℝ)] ![(33049748745573/100000000000000 : ℝ), (26638848565253/100000000000000 : ℝ), (20155701335873/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(250039653/625000000 : ℝ)|^5935 ≤ (33049748745573/100000000000000 : ℝ)^4911
        have hw : |(250039653/625000000 : ℝ)|=(250039653/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3346837321/10000000000 : ℝ)|^5935 ≤ (26638848565253/100000000000000 : ℝ)^4911
        have hw : |(3346837321/10000000000 : ℝ)|=(3346837321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(94305217/200000000 : ℝ)|^5935 ≤ (20155701335873/50000000000000 : ℝ)^4911
        have hw : |(94305217/200000000 : ℝ)|=(94305217/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1760_s3_4 (p : ℝ) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-146119151/1250000000 : ℝ)*x 0 + (79536757/156250000 : ℝ)*x 1 + (2738559013/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (146119151/1250000000 : ℝ)^5935 ≤ (233492064443/3125000000000 : ℝ)^4911 := by
    have hnat : (146119151 : ℕ)^5935*3125000000000^4911 ≤ 233492064443^4911*1250000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      146119151 1250000000 233492064443 3125000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (79536757/156250000 : ℝ)^5935 ≤ (11054558836681/25000000000000 : ℝ)^4911 := by
    have hnat : (79536757 : ℕ)^5935*25000000000000^4911 ≤ 11054558836681^4911*156250000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79536757 156250000 11054558836681 25000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2738559013/5000000000 : ℝ)^5935 ≤ (4831001857543/10000000000000 : ℝ)^4911 := by
    have hnat : (2738559013 : ℕ)^5935*10000000000000^4911 ≤ 4831001857543^4911*5000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2738559013 5000000000 4831001857543 10000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5935/1024 : ℝ)) 5935 4911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-146119151/1250000000 : ℝ), (79536757/156250000 : ℝ), (2738559013/5000000000 : ℝ)] ![(233492064443/3125000000000 : ℝ), (11054558836681/25000000000000 : ℝ), (4831001857543/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-146119151/1250000000 : ℝ)|^5935 ≤ (233492064443/3125000000000 : ℝ)^4911
        have hw : |(-146119151/1250000000 : ℝ)|=(146119151/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(79536757/156250000 : ℝ)|^5935 ≤ (11054558836681/25000000000000 : ℝ)^4911
        have hw : |(79536757/156250000 : ℝ)|=(79536757/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2738559013/5000000000 : ℝ)|^5935 ≤ (4831001857543/10000000000000 : ℝ)^4911
        have hw : |(2738559013/5000000000 : ℝ)|=(2738559013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1760_s3_5 (p : ℝ) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5223594503/10000000000 : ℝ)*x 0 + (-492100811/5000000000 : ℝ)*x 1 + (2738559013/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5223594503/10000000000 : ℝ)^5935 ≤ (22810397182527/50000000000000 : ℝ)^4911 := by
    have hnat : (5223594503 : ℕ)^5935*50000000000000^4911 ≤ 22810397182527^4911*10000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5223594503 10000000000 22810397182527 50000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (492100811/5000000000 : ℝ)^5935 ≤ (6069187043453/100000000000000 : ℝ)^4911 := by
    have hnat : (492100811 : ℕ)^5935*100000000000000^4911 ≤ 6069187043453^4911*5000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      492100811 5000000000 6069187043453 100000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2738559013/5000000000 : ℝ)^5935 ≤ (4831001857543/10000000000000 : ℝ)^4911 := by
    have hnat : (2738559013 : ℕ)^5935*10000000000000^4911 ≤ 4831001857543^4911*5000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2738559013 5000000000 4831001857543 10000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5935/1024 : ℝ)) 5935 4911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5223594503/10000000000 : ℝ), (-492100811/5000000000 : ℝ), (2738559013/5000000000 : ℝ)] ![(22810397182527/50000000000000 : ℝ), (6069187043453/100000000000000 : ℝ), (4831001857543/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5223594503/10000000000 : ℝ)|^5935 ≤ (22810397182527/50000000000000 : ℝ)^4911
        have hw : |(5223594503/10000000000 : ℝ)|=(5223594503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-492100811/5000000000 : ℝ)|^5935 ≤ (6069187043453/100000000000000 : ℝ)^4911
        have hw : |(-492100811/5000000000 : ℝ)|=(492100811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2738559013/5000000000 : ℝ)|^5935 ≤ (4831001857543/10000000000000 : ℝ)^4911
        have hw : |(2738559013/5000000000 : ℝ)|=(2738559013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1760_s3_6 (p : ℝ) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5223594503/10000000000 : ℝ)*x 0 + (2738559013/5000000000 : ℝ)*x 1 + (-492100811/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5223594503/10000000000 : ℝ)^5935 ≤ (22810397182527/50000000000000 : ℝ)^4911 := by
    have hnat : (5223594503 : ℕ)^5935*50000000000000^4911 ≤ 22810397182527^4911*10000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5223594503 10000000000 22810397182527 50000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2738559013/5000000000 : ℝ)^5935 ≤ (4831001857543/10000000000000 : ℝ)^4911 := by
    have hnat : (2738559013 : ℕ)^5935*10000000000000^4911 ≤ 4831001857543^4911*5000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2738559013 5000000000 4831001857543 10000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (492100811/5000000000 : ℝ)^5935 ≤ (6069187043453/100000000000000 : ℝ)^4911 := by
    have hnat : (492100811 : ℕ)^5935*100000000000000^4911 ≤ 6069187043453^4911*5000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      492100811 5000000000 6069187043453 100000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5935/1024 : ℝ)) 5935 4911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5223594503/10000000000 : ℝ), (2738559013/5000000000 : ℝ), (-492100811/5000000000 : ℝ)] ![(22810397182527/50000000000000 : ℝ), (4831001857543/10000000000000 : ℝ), (6069187043453/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5223594503/10000000000 : ℝ)|^5935 ≤ (22810397182527/50000000000000 : ℝ)^4911
        have hw : |(5223594503/10000000000 : ℝ)|=(5223594503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2738559013/5000000000 : ℝ)|^5935 ≤ (4831001857543/10000000000000 : ℝ)^4911
        have hw : |(2738559013/5000000000 : ℝ)|=(2738559013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-492100811/5000000000 : ℝ)|^5935 ≤ (6069187043453/100000000000000 : ℝ)^4911
        have hw : |(-492100811/5000000000 : ℝ)|=(492100811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1760_s3_7 (p : ℝ) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2000883353/5000000000 : ℝ)*x 0 + (469264399/1000000000 : ℝ)*x 1 + (67398519/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2000883353/5000000000 : ℝ)^5935 ≤ (8265263291443/25000000000000 : ℝ)^4911 := by
    have hnat : (2000883353 : ℕ)^5935*25000000000000^4911 ≤ 8265263291443^4911*5000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2000883353 5000000000 8265263291443 25000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (469264399/1000000000 : ℝ)^5935 ≤ (20038924209287/50000000000000 : ℝ)^4911 := by
    have hnat : (469264399 : ℕ)^5935*50000000000000^4911 ≤ 20038924209287^4911*1000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      469264399 1000000000 20038924209287 50000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (67398519/200000000 : ℝ)^5935 ≤ (2686109840487/10000000000000 : ℝ)^4911 := by
    have hnat : (67398519 : ℕ)^5935*10000000000000^4911 ≤ 2686109840487^4911*200000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67398519 200000000 2686109840487 10000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5935/1024 : ℝ)) 5935 4911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2000883353/5000000000 : ℝ), (469264399/1000000000 : ℝ), (67398519/200000000 : ℝ)] ![(8265263291443/25000000000000 : ℝ), (20038924209287/50000000000000 : ℝ), (2686109840487/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2000883353/5000000000 : ℝ)|^5935 ≤ (8265263291443/25000000000000 : ℝ)^4911
        have hw : |(2000883353/5000000000 : ℝ)|=(2000883353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(469264399/1000000000 : ℝ)|^5935 ≤ (20038924209287/50000000000000 : ℝ)^4911
        have hw : |(469264399/1000000000 : ℝ)|=(469264399/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(67398519/200000000 : ℝ)|^5935 ≤ (2686109840487/10000000000000 : ℝ)^4911
        have hw : |(67398519/200000000 : ℝ)|=(67398519/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1760_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (27624673/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17783/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1831/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2289/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8891/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17783/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1831/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17783/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1831/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17783/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1831/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17783/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1831/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17783/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1831/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17783/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1831/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1831/20000 : ℝ) ^ (5919/1024 : ℝ) ≤ (99563770159191/100000000000000000000 : ℝ) := by
    have hpowers : (1831/20000 : ℝ)^5919 ≤ (99563770159191/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1831 : ℕ)^5919*100000000000000000000^1024 ≤ 99563770159191^1024*20000^5919 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1831 20000 99563770159191 100000000000000000000 5919 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1831/20000 : ℝ)) (X := (99563770159191/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5919 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17783/100000 : ℝ) ^ (5919/1024 : ℝ) ≤ (4621936642802179/100000000000000000000 : ℝ) := by
    have hpowers : (17783/100000 : ℝ)^5919 ≤ (4621936642802179/100000000000000000000 : ℝ)^1024 := by
      have hnat : (17783 : ℕ)^5919*100000000000000000000^1024 ≤ 4621936642802179^1024*100000^5919 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17783 100000 4621936642802179 100000000000000000000 5919 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17783/100000 : ℝ)) (X := (4621936642802179/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5919 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000099563770159191/50000000000000000000 : ℝ) ≤ (5000001722473673/5000000000000000 : ℝ) ^ (5919/1024 : ℝ) := by
    have hpowers : (50000099563770159191/50000000000000000000 : ℝ)^1024 ≤ (5000001722473673/5000000000000000 : ℝ)^5919 := by
      have hnat : (50000099563770159191 : ℕ)^1024*5000000000000000^5919 ≤ 5000001722473673^5919*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000099563770159191 50000000000000000000 5000001722473673 5000000000000000 1024 5919 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000001722473673/5000000000000000 : ℝ)) (X := (50000099563770159191/50000000000000000000 : ℝ)) (by norm_num) 5919 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10000472150041296137/10000000000000000000 : ℝ) ≤ (312502552543733/312500000000000 : ℝ) ^ (5919/1024 : ℝ) := by
    have hpowers : (10000472150041296137/10000000000000000000 : ℝ)^1024 ≤ (312502552543733/312500000000000 : ℝ)^5919 := by
      have hnat : (10000472150041296137 : ℕ)^1024*312500000000000^5919 ≤ 312502552543733^5919*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000472150041296137 10000000000000000000 312502552543733 312500000000000 1024 5919 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312502552543733/312500000000000 : ℝ)) (X := (10000472150041296137/10000000000000000000 : ℝ)) (by norm_num) 5919 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50004621936642802179/50000000000000000000 : ℝ) ≤ (5000079958925783/5000000000000000 : ℝ) ^ (5919/1024 : ℝ) := by
    have hpowers : (50004621936642802179/50000000000000000000 : ℝ)^1024 ≤ (5000079958925783/5000000000000000 : ℝ)^5919 := by
      have hnat : (50004621936642802179 : ℕ)^1024*5000000000000000^5919 ≤ 5000079958925783^5919*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004621936642802179 50000000000000000000 5000079958925783 5000000000000000 1024 5919 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000079958925783/5000000000000000 : ℝ)) (X := (50004621936642802179/50000000000000000000 : ℝ)) (by norm_num) 5919 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(99563770159191/100000000000000000000 : ℝ) ≤ ((7189883101130630599/7190000000000000000 : ℝ)+2*(2607881737/28760000000000 : ℝ)*(1831/20000 : ℝ))^(5919/1024 : ℝ) := by
    rw [show (7189883101130630599/7190000000000000000 : ℝ)+2*(2607881737/28760000000000 : ℝ)*(1831/20000 : ℝ)=(5000001722473673/5000000000000000 : ℝ) by norm_num, show 1+2*(99563770159191/100000000000000000000 : ℝ)=(50000099563770159191/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4621936642802179/100000000000000000000 : ℝ)+(99563770159191/100000000000000000000 : ℝ) ≤ ((7189883101130630599/7190000000000000000 : ℝ)+(2607881737/28760000000000 : ℝ)*((17783/100000 : ℝ)+(1831/20000 : ℝ)))^(5919/1024 : ℝ) := by
    rw [show (7189883101130630599/7190000000000000000 : ℝ)+(2607881737/28760000000000 : ℝ)*((17783/100000 : ℝ)+(1831/20000 : ℝ))=(312502552543733/312500000000000 : ℝ) by norm_num, show 1+(4621936642802179/100000000000000000000 : ℝ)+(99563770159191/100000000000000000000 : ℝ)=(10000472150041296137/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4621936642802179/100000000000000000000 : ℝ) ≤ ((7189883101130630599/7190000000000000000 : ℝ)+2*(2607881737/28760000000000 : ℝ)*(17783/100000 : ℝ))^(5919/1024 : ℝ) := by
    rw [show (7189883101130630599/7190000000000000000 : ℝ)+2*(2607881737/28760000000000 : ℝ)*(17783/100000 : ℝ)=(5000079958925783/5000000000000000 : ℝ) by norm_num, show 1+2*(4621936642802179/100000000000000000000 : ℝ)=(50004621936642802179/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7189883101130630599/7190000000000000000 : ℝ)*(X 1 0+X 2 0)+(2607881737/28760000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5919/1024 : ℝ)) (lo := (1831/20000 : ℝ)) (hi := (17783/100000 : ℝ)) (c := (7189883101130630599/7190000000000000000 : ℝ)) (alpha := (2607881737/28760000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7189883101130630599/7190000000000000000 : ℝ)*(X 0 1+X 2 1)+(2607881737/28760000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5919/1024 : ℝ)) (lo := (1831/20000 : ℝ)) (hi := (17783/100000 : ℝ)) (c := (7189883101130630599/7190000000000000000 : ℝ)) (alpha := (2607881737/28760000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7189883101130630599/7190000000000000000 : ℝ)*(X 0 2+X 1 2)+(2607881737/28760000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5919/1024 : ℝ)) (lo := (1831/20000 : ℝ)) (hi := (17783/100000 : ℝ)) (c := (7189883101130630599/7190000000000000000 : ℝ)) (alpha := (2607881737/28760000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1168622087/10000000000 : ℝ)*X 0 0+(1096773797/2000000000 : ℝ)*X 0 1+(203349579/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1760_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5329335387/10000000000 : ℝ)*X 1 0+(-688790183/5000000000 : ℝ)*X 1 1+(2541869653/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1760_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1065867093/2000000000 : ℝ)*X 2 0+(1016747863/2000000000 : ℝ)*X 2 1+(-1377580251/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1760_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((250039653/625000000 : ℝ)*X 0 0+(3346837321/10000000000 : ℝ)*X 0 1+(94305217/200000000 : ℝ)*X 0 2+(250039653/625000000 : ℝ)*X 1 0+(3346837321/10000000000 : ℝ)*X 1 1+(94305217/200000000 : ℝ)*X 1 2+(250039653/625000000 : ℝ)*X 2 0+(3346837321/10000000000 : ℝ)*X 2 1+(94305217/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1760_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-146119151/1250000000 : ℝ)*X 0 0+(79536757/156250000 : ℝ)*X 0 1+(2738559013/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1760_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5223594503/10000000000 : ℝ)*X 1 0+(-492100811/5000000000 : ℝ)*X 1 1+(2738559013/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1760_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5223594503/10000000000 : ℝ)*X 2 0+(2738559013/5000000000 : ℝ)*X 2 1+(-492100811/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1760_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2000883353/5000000000 : ℝ)*X 0 0+(469264399/1000000000 : ℝ)*X 0 1+(67398519/200000000 : ℝ)*X 0 2+(2000883353/5000000000 : ℝ)*X 1 0+(469264399/1000000000 : ℝ)*X 1 1+(67398519/200000000 : ℝ)*X 1 2+(2000883353/5000000000 : ℝ)*X 2 0+(469264399/1000000000 : ℝ)*X 2 1+(67398519/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1760_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2214875747373478476670587507/359500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (819944723/100000000000000 : ℝ)*(base19) + (394766829/50000000000000 : ℝ)*(base23) + (35700849/100000000000000 : ℝ)*(lower2) + (114901979/100000000000000 : ℝ)*(upper3) + (133290233/100000000000000 : ℝ)*(upper5) + (1614987354159431/100000000000000 : ℝ)*(major0) + (1614987354159431/100000000000000 : ℝ)*(major1) + (1614987354159431/100000000000000 : ℝ)*(major2) + (124959804567983/5000000000000 : ℝ)*(sp0) + (624800381028073/25000000000000 : ℝ)*(sp1) + (1249600777261679/50000000000000 : ℝ)*(sp2) + (365384987308503/50000000000000 : ℝ)*(sp3) + (1250539471/20000000000000 : ℝ)*(sp4) + (1092139259/50000000000000 : ℝ)*(sp7) + (182693039723881/25000000000000 : ℝ)*(f.failure) + (499840468811403/20000000000000 : ℝ)*(f.sum) + (2807311405921/1438000000000000000000000000 : ℝ)*base66 + (692043864509220831/719000000000000000000000000000000 : ℝ)*base68 + (3004156072854779169/719000000000000000000000000000000 : ℝ)*base69 + (1673272881075220831/719000000000000000000000000000000 : ℝ)*base72 + (517160301833/287600000000000000000000000 : ℝ)*base74 + (1968400894636779169/719000000000000000000000000000000 : ℝ)*base75 + (2710800282129220831/719000000000000000000000000000000 : ℝ)*base78 + (6134082698479220831/719000000000000000000000000000000 : ℝ)*base80 + (4646870467851/1438000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (1040913/312500000000000000000 : ℝ)*base89 + (1040913/312500000000000000000 : ℝ)*base91 + (1040913/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (406196245685558137852413993/44937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1145195249/100000000000000 : ℝ)*(base19) + (1224709453/100000000000000 : ℝ)*(base23) + (161297121/50000000000000 : ℝ)*(lower1) + (24420507/12500000000000 : ℝ)*(upper3) + (17651197/50000000000000 : ℝ)*(lower4) + (18829011/10000000000000 : ℝ)*(upper5) + (208847091819977/12500000000000 : ℝ)*(major0) + (208847091819977/12500000000000 : ℝ)*(major1) + (208847091819977/12500000000000 : ℝ)*(major2) + (589421717/100000000000000 : ℝ)*(sp2) + (1292768323284891/50000000000000 : ℝ)*(sp4) + (1292767750687267/50000000000000 : ℝ)*(sp5) + (2585534832438613/100000000000000 : ℝ)*(sp6) + (378008260622627/50000000000000 : ℝ)*(sp7) + (378008260622627/50000000000000 : ℝ)*(f.failure) + (1292768323284891/50000000000000 : ℝ)*(f.sum) + (22232272753/22468750000000000000000000 : ℝ)*base66 + (614403668192426223/89875000000000000000000000000000 : ℝ)*base67 + (380622450681926223/89875000000000000000000000000000 : ℝ)*base69 + (246414962758676223/89875000000000000000000000000000 : ℝ)*base71 + (64107491217/179750000000000000000000000 : ℝ)*base73 + (2727289298445926223/89875000000000000000000000000000 : ℝ)*base75 + (205571166371426223/89875000000000000000000000000000 : ℝ)*base77 + (432684016494551223/89875000000000000000000000000000 : ℝ)*base79 + (377994593597/719000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (2724029/625000000000000000000 : ℝ)*base90 + (2724029/625000000000000000000 : ℝ)*base92 + (2724029/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1760_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (27624673/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17783/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1831/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2289/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8891/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1760_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1760_box_0 (p : ℝ) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-398896781/5000000000 : ℝ)*x 0 + (5414706567/10000000000 : ℝ)*x 1 + (5414706209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (398896781/5000000000 : ℝ)^5935 ≤ (2354464101313/50000000000000 : ℝ)^4911 := by
    have hnat : (398896781 : ℕ)^5935*50000000000000^4911 ≤ 2354464101313^4911*5000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      398896781 5000000000 2354464101313 50000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414706567/10000000000 : ℝ)^5935 ≤ (9529107558709/20000000000000 : ℝ)^4911 := by
    have hnat : (5414706567 : ℕ)^5935*20000000000000^4911 ≤ 9529107558709^4911*10000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414706567 10000000000 9529107558709 20000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5414706209/10000000000 : ℝ)^5935 ≤ (37223073427/78125000000 : ℝ)^4911 := by
    have hnat : (5414706209 : ℕ)^5935*78125000000^4911 ≤ 37223073427^4911*10000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414706209 10000000000 37223073427 78125000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5935/1024 : ℝ)) 5935 4911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-398896781/5000000000 : ℝ), (5414706567/10000000000 : ℝ), (5414706209/10000000000 : ℝ)] ![(2354464101313/50000000000000 : ℝ), (9529107558709/20000000000000 : ℝ), (37223073427/78125000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-398896781/5000000000 : ℝ)|^5935 ≤ (2354464101313/50000000000000 : ℝ)^4911
        have hw : |(-398896781/5000000000 : ℝ)|=(398896781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414706567/10000000000 : ℝ)|^5935 ≤ (9529107558709/20000000000000 : ℝ)^4911
        have hw : |(5414706567/10000000000 : ℝ)|=(5414706567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5414706209/10000000000 : ℝ)|^5935 ≤ (37223073427/78125000000 : ℝ)^4911
        have hw : |(5414706209/10000000000 : ℝ)|=(5414706209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1760_box_1 (p : ℝ) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (207730893/400000000 : ℝ)*x 0 + (-1114542901/10000000000 : ℝ)*x 1 + (1353676653/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (207730893/400000000 : ℝ)^5935 ≤ (566261851511/1250000000000 : ℝ)^4911 := by
    have hnat : (207730893 : ℕ)^5935*1250000000000^4911 ≤ 566261851511^4911*400000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207730893 400000000 566261851511 1250000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1114542901/10000000000 : ℝ)^5935 ≤ (7053513595551/100000000000000 : ℝ)^4911 := by
    have hnat : (1114542901 : ℕ)^5935*100000000000000^4911 ≤ 7053513595551^4911*10000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1114542901 10000000000 7053513595551 100000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1353676653/2500000000 : ℝ)^5935 ≤ (11911384568019/25000000000000 : ℝ)^4911 := by
    have hnat : (1353676653 : ℕ)^5935*25000000000000^4911 ≤ 11911384568019^4911*2500000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353676653 2500000000 11911384568019 25000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5935/1024 : ℝ)) 5935 4911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(207730893/400000000 : ℝ), (-1114542901/10000000000 : ℝ), (1353676653/2500000000 : ℝ)] ![(566261851511/1250000000000 : ℝ), (7053513595551/100000000000000 : ℝ), (11911384568019/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(207730893/400000000 : ℝ)|^5935 ≤ (566261851511/1250000000000 : ℝ)^4911
        have hw : |(207730893/400000000 : ℝ)|=(207730893/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1114542901/10000000000 : ℝ)|^5935 ≤ (7053513595551/100000000000000 : ℝ)^4911
        have hw : |(-1114542901/10000000000 : ℝ)|=(1114542901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1353676653/2500000000 : ℝ)|^5935 ≤ (11911384568019/25000000000000 : ℝ)^4911
        have hw : |(1353676653/2500000000 : ℝ)|=(1353676653/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1760_box_2 (p : ℝ) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5193272069/10000000000 : ℝ)*x 0 + (338419157/625000000 : ℝ)*x 1 + (-1114543393/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5193272069/10000000000 : ℝ)^5935 ≤ (9060189084433/20000000000000 : ℝ)^4911 := by
    have hnat : (5193272069 : ℕ)^5935*20000000000000^4911 ≤ 9060189084433^4911*10000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5193272069 10000000000 9060189084433 20000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (338419157/625000000 : ℝ)^5935 ≤ (47645537208673/100000000000000 : ℝ)^4911 := by
    have hnat : (338419157 : ℕ)^5935*100000000000000^4911 ≤ 47645537208673^4911*625000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338419157 625000000 47645537208673 100000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1114543393/10000000000 : ℝ)^5935 ≤ (1763379339617/25000000000000 : ℝ)^4911 := by
    have hnat : (1114543393 : ℕ)^5935*25000000000000^4911 ≤ 1763379339617^4911*10000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1114543393 10000000000 1763379339617 25000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5935/1024 : ℝ)) 5935 4911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5193272069/10000000000 : ℝ), (338419157/625000000 : ℝ), (-1114543393/10000000000 : ℝ)] ![(9060189084433/20000000000000 : ℝ), (47645537208673/100000000000000 : ℝ), (1763379339617/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5193272069/10000000000 : ℝ)|^5935 ≤ (9060189084433/20000000000000 : ℝ)^4911
        have hw : |(5193272069/10000000000 : ℝ)|=(5193272069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(338419157/625000000 : ℝ)|^5935 ≤ (47645537208673/100000000000000 : ℝ)^4911
        have hw : |(338419157/625000000 : ℝ)|=(338419157/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1114543393/10000000000 : ℝ)|^5935 ≤ (1763379339617/25000000000000 : ℝ)^4911
        have hw : |(-1114543393/10000000000 : ℝ)|=(1114543393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1760_box_3 (p : ℝ) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4525444493/10000000000 : ℝ)*x 0 + (3776029721/10000000000 : ℝ)*x 1 + (377603173/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4525444493/10000000000 : ℝ)^5935 ≤ (7671718266413/20000000000000 : ℝ)^4911 := by
    have hnat : (4525444493 : ℕ)^5935*20000000000000^4911 ≤ 7671718266413^4911*10000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4525444493 10000000000 7671718266413 20000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3776029721/10000000000 : ℝ)^5935 ≤ (30820694419853/100000000000000 : ℝ)^4911 := by
    have hnat : (3776029721 : ℕ)^5935*100000000000000^4911 ≤ 30820694419853^4911*10000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3776029721 10000000000 30820694419853 100000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (377603173/1000000000 : ℝ)^5935 ≤ (15410357118423/50000000000000 : ℝ)^4911 := by
    have hnat : (377603173 : ℕ)^5935*50000000000000^4911 ≤ 15410357118423^4911*1000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      377603173 1000000000 15410357118423 50000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5935/1024 : ℝ)) 5935 4911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4525444493/10000000000 : ℝ), (3776029721/10000000000 : ℝ), (377603173/1000000000 : ℝ)] ![(7671718266413/20000000000000 : ℝ), (30820694419853/100000000000000 : ℝ), (15410357118423/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4525444493/10000000000 : ℝ)|^5935 ≤ (7671718266413/20000000000000 : ℝ)^4911
        have hw : |(4525444493/10000000000 : ℝ)|=(4525444493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3776029721/10000000000 : ℝ)|^5935 ≤ (30820694419853/100000000000000 : ℝ)^4911
        have hw : |(3776029721/10000000000 : ℝ)|=(3776029721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(377603173/1000000000 : ℝ)|^5935 ≤ (15410357118423/50000000000000 : ℝ)^4911
        have hw : |(377603173/1000000000 : ℝ)|=(377603173/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1760_box_4 (p : ℝ) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1578499501/10000000000 : ℝ)*x 0 + (5129467989/10000000000 : ℝ)*x 1 + (320591759/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1578499501/10000000000 : ℝ)^5935 ≤ (5370802678721/50000000000000 : ℝ)^4911 := by
    have hnat : (1578499501 : ℕ)^5935*50000000000000^4911 ≤ 5370802678721^4911*10000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1578499501 10000000000 5370802678721 50000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5129467989/10000000000 : ℝ)^5935 ≤ (35703357197/80000000000 : ℝ)^4911 := by
    have hnat : (5129467989 : ℕ)^5935*80000000000^4911 ≤ 35703357197^4911*10000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5129467989 10000000000 35703357197 80000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (320591759/625000000 : ℝ)^5935 ≤ (4462919812603/10000000000000 : ℝ)^4911 := by
    have hnat : (320591759 : ℕ)^5935*10000000000000^4911 ≤ 4462919812603^4911*625000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      320591759 625000000 4462919812603 10000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5935/1024 : ℝ)) 5935 4911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1578499501/10000000000 : ℝ), (5129467989/10000000000 : ℝ), (320591759/625000000 : ℝ)] ![(5370802678721/50000000000000 : ℝ), (35703357197/80000000000 : ℝ), (4462919812603/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1578499501/10000000000 : ℝ)|^5935 ≤ (5370802678721/50000000000000 : ℝ)^4911
        have hw : |(-1578499501/10000000000 : ℝ)|=(1578499501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5129467989/10000000000 : ℝ)|^5935 ≤ (35703357197/80000000000 : ℝ)^4911
        have hw : |(5129467989/10000000000 : ℝ)|=(5129467989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(320591759/625000000 : ℝ)|^5935 ≤ (4462919812603/10000000000000 : ℝ)^4911
        have hw : |(320591759/625000000 : ℝ)|=(320591759/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1760_box_5 (p : ℝ) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1076684693/2000000000 : ℝ)*x 0 + (-1244314421/10000000000 : ℝ)*x 1 + (5129468147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1076684693/2000000000 : ℝ)^5935 ≤ (1478533527019/3125000000000 : ℝ)^4911 := by
    have hnat : (1076684693 : ℕ)^5935*3125000000000^4911 ≤ 1478533527019^4911*2000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076684693 2000000000 1478533527019 3125000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1244314421/10000000000 : ℝ)^5935 ≤ (8057728959801/100000000000000 : ℝ)^4911 := by
    have hnat : (1244314421 : ℕ)^5935*100000000000000^4911 ≤ 8057728959801^4911*10000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1244314421 10000000000 8057728959801 100000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5129468147/10000000000 : ℝ)^5935 ≤ (1785167926303/4000000000000 : ℝ)^4911 := by
    have hnat : (5129468147 : ℕ)^5935*4000000000000^4911 ≤ 1785167926303^4911*10000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5129468147 10000000000 1785167926303 4000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5935/1024 : ℝ)) 5935 4911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1076684693/2000000000 : ℝ), (-1244314421/10000000000 : ℝ), (5129468147/10000000000 : ℝ)] ![(1478533527019/3125000000000 : ℝ), (8057728959801/100000000000000 : ℝ), (1785167926303/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1076684693/2000000000 : ℝ)|^5935 ≤ (1478533527019/3125000000000 : ℝ)^4911
        have hw : |(1076684693/2000000000 : ℝ)|=(1076684693/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1244314421/10000000000 : ℝ)|^5935 ≤ (8057728959801/100000000000000 : ℝ)^4911
        have hw : |(-1244314421/10000000000 : ℝ)|=(1244314421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5129468147/10000000000 : ℝ)|^5935 ≤ (1785167926303/4000000000000 : ℝ)^4911
        have hw : |(5129468147/10000000000 : ℝ)|=(5129468147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1760_box_6 (p : ℝ) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (269171181/500000000 : ℝ)*x 0 + (641183509/1250000000 : ℝ)*x 1 + (-1244314311/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (269171181/500000000 : ℝ)^5935 ≤ (47313074510893/100000000000000 : ℝ)^4911 := by
    have hnat : (269171181 : ℕ)^5935*100000000000000^4911 ≤ 47313074510893^4911*500000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269171181 500000000 47313074510893 100000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (641183509/1250000000 : ℝ)^5935 ≤ (44629197368971/100000000000000 : ℝ)^4911 := by
    have hnat : (641183509 : ℕ)^5935*100000000000000^4911 ≤ 44629197368971^4911*1250000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      641183509 1250000000 44629197368971 100000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1244314311/10000000000 : ℝ)^5935 ≤ (4028864049477/50000000000000 : ℝ)^4911 := by
    have hnat : (1244314311 : ℕ)^5935*50000000000000^4911 ≤ 4028864049477^4911*10000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1244314311 10000000000 4028864049477 50000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5935/1024 : ℝ)) 5935 4911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(269171181/500000000 : ℝ), (641183509/1250000000 : ℝ), (-1244314311/10000000000 : ℝ)] ![(47313074510893/100000000000000 : ℝ), (44629197368971/100000000000000 : ℝ), (4028864049477/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(269171181/500000000 : ℝ)|^5935 ≤ (47313074510893/100000000000000 : ℝ)^4911
        have hw : |(269171181/500000000 : ℝ)|=(269171181/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(641183509/1250000000 : ℝ)|^5935 ≤ (44629197368971/100000000000000 : ℝ)^4911
        have hw : |(641183509/1250000000 : ℝ)|=(641183509/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1244314311/10000000000 : ℝ)|^5935 ≤ (4028864049477/50000000000000 : ℝ)^4911
        have hw : |(-1244314311/10000000000 : ℝ)|=(1244314311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1760_box_7 (p : ℝ) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (42968743/125000000 : ℝ)*x 0 + (1079485577/2500000000 : ℝ)*x 1 + (4317942561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42968743/125000000 : ℝ)^5935 ≤ (859793013807/3125000000000 : ℝ)^4911 := by
    have hnat : (42968743 : ℕ)^5935*3125000000000^4911 ≤ 859793013807^4911*125000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42968743 125000000 859793013807 3125000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1079485577/2500000000 : ℝ)^5935 ≤ (36243310487541/100000000000000 : ℝ)^4911 := by
    have hnat : (1079485577 : ℕ)^5935*100000000000000^4911 ≤ 36243310487541^4911*2500000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079485577 2500000000 36243310487541 100000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4317942561/10000000000 : ℝ)^5935 ≤ (36243313053929/100000000000000 : ℝ)^4911 := by
    have hnat : (4317942561 : ℕ)^5935*100000000000000^4911 ≤ 36243313053929^4911*10000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4317942561 10000000000 36243313053929 100000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5935/1024 : ℝ)) 5935 4911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42968743/125000000 : ℝ), (1079485577/2500000000 : ℝ), (4317942561/10000000000 : ℝ)] ![(859793013807/3125000000000 : ℝ), (36243310487541/100000000000000 : ℝ), (36243313053929/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42968743/125000000 : ℝ)|^5935 ≤ (859793013807/3125000000000 : ℝ)^4911
        have hw : |(42968743/125000000 : ℝ)|=(42968743/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1079485577/2500000000 : ℝ)|^5935 ≤ (36243310487541/100000000000000 : ℝ)^4911
        have hw : |(1079485577/2500000000 : ℝ)|=(1079485577/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4317942561/10000000000 : ℝ)|^5935 ≤ (36243313053929/100000000000000 : ℝ)^4911
        have hw : |(4317942561/10000000000 : ℝ)|=(4317942561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1760_box_8 (p : ℝ) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1408478103/10000000000 : ℝ)*x 0 + (2455647403/5000000000 : ℝ)*x 1 + (1095141797/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1408478103/10000000000 : ℝ)^5935 ≤ (9359544250333/100000000000000 : ℝ)^4911 := by
    have hnat : (1408478103 : ℕ)^5935*100000000000000^4911 ≤ 9359544250333^4911*10000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1408478103 10000000000 9359544250333 100000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2455647403/5000000000 : ℝ)^5935 ≤ (21172728198257/50000000000000 : ℝ)^4911 := by
    have hnat : (2455647403 : ℕ)^5935*50000000000000^4911 ≤ 21172728198257^4911*5000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2455647403 5000000000 21172728198257 50000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1095141797/2000000000 : ℝ)^5935 ≤ (24147499669131/50000000000000 : ℝ)^4911 := by
    have hnat : (1095141797 : ℕ)^5935*50000000000000^4911 ≤ 24147499669131^4911*2000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095141797 2000000000 24147499669131 50000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5935/1024 : ℝ)) 5935 4911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1408478103/10000000000 : ℝ), (2455647403/5000000000 : ℝ), (1095141797/2000000000 : ℝ)] ![(9359544250333/100000000000000 : ℝ), (21172728198257/50000000000000 : ℝ), (24147499669131/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1408478103/10000000000 : ℝ)|^5935 ≤ (9359544250333/100000000000000 : ℝ)^4911
        have hw : |(-1408478103/10000000000 : ℝ)|=(1408478103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2455647403/5000000000 : ℝ)|^5935 ≤ (21172728198257/50000000000000 : ℝ)^4911
        have hw : |(2455647403/5000000000 : ℝ)|=(2455647403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1095141797/2000000000 : ℝ)|^5935 ≤ (24147499669131/50000000000000 : ℝ)^4911
        have hw : |(1095141797/2000000000 : ℝ)|=(1095141797/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1760_box_9 (p : ℝ) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2576340227/5000000000 : ℝ)*x 0 + (-542725217/5000000000 : ℝ)*x 1 + (5475708843/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2576340227/5000000000 : ℝ)^5935 ≤ (44873383979409/100000000000000 : ℝ)^4911 := by
    have hnat : (2576340227 : ℕ)^5935*100000000000000^4911 ≤ 44873383979409^4911*5000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2576340227 5000000000 44873383979409 100000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (542725217/5000000000 : ℝ)^5935 ≤ (1707904545919/25000000000000 : ℝ)^4911 := by
    have hnat : (542725217 : ℕ)^5935*25000000000000^4911 ≤ 1707904545919^4911*5000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542725217 5000000000 1707904545919 25000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5475708843/10000000000 : ℝ)^5935 ≤ (48294997824697/100000000000000 : ℝ)^4911 := by
    have hnat : (5475708843 : ℕ)^5935*100000000000000^4911 ≤ 48294997824697^4911*10000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5475708843 10000000000 48294997824697 100000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5935/1024 : ℝ)) 5935 4911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2576340227/5000000000 : ℝ), (-542725217/5000000000 : ℝ), (5475708843/10000000000 : ℝ)] ![(44873383979409/100000000000000 : ℝ), (1707904545919/25000000000000 : ℝ), (48294997824697/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2576340227/5000000000 : ℝ)|^5935 ≤ (44873383979409/100000000000000 : ℝ)^4911
        have hw : |(2576340227/5000000000 : ℝ)|=(2576340227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-542725217/5000000000 : ℝ)|^5935 ≤ (1707904545919/25000000000000 : ℝ)^4911
        have hw : |(-542725217/5000000000 : ℝ)|=(542725217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5475708843/10000000000 : ℝ)|^5935 ≤ (48294997824697/100000000000000 : ℝ)^4911
        have hw : |(5475708843/10000000000 : ℝ)|=(5475708843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1760_box_10 (p : ℝ) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1288170077/2500000000 : ℝ)*x 0 + (5475709273/10000000000 : ℝ)*x 1 + (-1085450033/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1288170077/2500000000 : ℝ)^5935 ≤ (8974676488563/20000000000000 : ℝ)^4911 := by
    have hnat : (1288170077 : ℕ)^5935*20000000000000^4911 ≤ 8974676488563^4911*2500000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1288170077 2500000000 8974676488563 20000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5475709273/10000000000 : ℝ)^5935 ≤ (24147501204013/50000000000000 : ℝ)^4911 := by
    have hnat : (5475709273 : ℕ)^5935*50000000000000^4911 ≤ 24147501204013^4911*10000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5475709273 10000000000 24147501204013 50000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1085450033/10000000000 : ℝ)^5935 ≤ (6831615133613/100000000000000 : ℝ)^4911 := by
    have hnat : (1085450033 : ℕ)^5935*100000000000000^4911 ≤ 6831615133613^4911*10000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085450033 10000000000 6831615133613 100000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5935/1024 : ℝ)) 5935 4911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1288170077/2500000000 : ℝ), (5475709273/10000000000 : ℝ), (-1085450033/10000000000 : ℝ)] ![(8974676488563/20000000000000 : ℝ), (24147501204013/50000000000000 : ℝ), (6831615133613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1288170077/2500000000 : ℝ)|^5935 ≤ (8974676488563/20000000000000 : ℝ)^4911
        have hw : |(1288170077/2500000000 : ℝ)|=(1288170077/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5475709273/10000000000 : ℝ)|^5935 ≤ (24147501204013/50000000000000 : ℝ)^4911
        have hw : |(5475709273/10000000000 : ℝ)|=(5475709273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1085450033/10000000000 : ℝ)|^5935 ≤ (6831615133613/100000000000000 : ℝ)^4911
        have hw : |(-1085450033/10000000000 : ℝ)|=(1085450033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1760_box_11 (p : ℝ) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (474763299/1000000000 : ℝ)*x 0 + (3659703619/10000000000 : ℝ)*x 1 + (3659702021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (474763299/1000000000 : ℝ)^5935 ≤ (20323050893129/50000000000000 : ℝ)^4911 := by
    have hnat : (474763299 : ℕ)^5935*50000000000000^4911 ≤ 20323050893129^4911*1000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      474763299 1000000000 20323050893129 50000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3659703619/10000000000 : ℝ)^5935 ≤ (1187078277203/4000000000000 : ℝ)^4911 := by
    have hnat : (3659703619 : ℕ)^5935*4000000000000^4911 ≤ 1187078277203^4911*10000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3659703619 10000000000 1187078277203 4000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3659702021/10000000000 : ℝ)^5935 ≤ (29676941269741/100000000000000 : ℝ)^4911 := by
    have hnat : (3659702021 : ℕ)^5935*100000000000000^4911 ≤ 29676941269741^4911*10000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3659702021 10000000000 29676941269741 100000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5935/1024 : ℝ)) 5935 4911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(474763299/1000000000 : ℝ), (3659703619/10000000000 : ℝ), (3659702021/10000000000 : ℝ)] ![(20323050893129/50000000000000 : ℝ), (1187078277203/4000000000000 : ℝ), (29676941269741/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(474763299/1000000000 : ℝ)|^5935 ≤ (20323050893129/50000000000000 : ℝ)^4911
        have hw : |(474763299/1000000000 : ℝ)|=(474763299/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3659703619/10000000000 : ℝ)|^5935 ≤ (1187078277203/4000000000000 : ℝ)^4911
        have hw : |(3659703619/10000000000 : ℝ)|=(3659703619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3659702021/10000000000 : ℝ)|^5935 ≤ (29676941269741/100000000000000 : ℝ)^4911
        have hw : |(3659702021/10000000000 : ℝ)|=(3659702021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1760_box_12 (p : ℝ) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-95356591/1000000000 : ℝ)*x 0 + (1124092659/2000000000 : ℝ)*x 1 + (5099685421/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (95356591/1000000000 : ℝ)^5935 ≤ (5841623984137/100000000000000 : ℝ)^4911 := by
    have hnat : (95356591 : ℕ)^5935*100000000000000^4911 ≤ 5841623984137^4911*1000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      95356591 1000000000 5841623984137 100000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1124092659/2000000000 : ℝ)^5935 ≤ (3115134055471/6250000000000 : ℝ)^4911 := by
    have hnat : (1124092659 : ℕ)^5935*6250000000000^4911 ≤ 3115134055471^4911*2000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124092659 2000000000 3115134055471 6250000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5099685421/10000000000 : ℝ)^5935 ≤ (22158115557167/50000000000000 : ℝ)^4911 := by
    have hnat : (5099685421 : ℕ)^5935*50000000000000^4911 ≤ 22158115557167^4911*10000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5099685421 10000000000 22158115557167 50000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5935/1024 : ℝ)) 5935 4911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-95356591/1000000000 : ℝ), (1124092659/2000000000 : ℝ), (5099685421/10000000000 : ℝ)] ![(5841623984137/100000000000000 : ℝ), (3115134055471/6250000000000 : ℝ), (22158115557167/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-95356591/1000000000 : ℝ)|^5935 ≤ (5841623984137/100000000000000 : ℝ)^4911
        have hw : |(-95356591/1000000000 : ℝ)|=(95356591/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1124092659/2000000000 : ℝ)|^5935 ≤ (3115134055471/6250000000000 : ℝ)^4911
        have hw : |(1124092659/2000000000 : ℝ)|=(1124092659/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5099685421/10000000000 : ℝ)|^5935 ≤ (22158115557167/50000000000000 : ℝ)^4911
        have hw : |(5099685421/10000000000 : ℝ)|=(5099685421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1760_box_13 (p : ℝ) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (675419071/1250000000 : ℝ)*x 0 + (-1257233601/10000000000 : ℝ)*x 1 + (1274921389/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (675419071/1250000000 : ℝ)^5935 ≤ (23762412688683/50000000000000 : ℝ)^4911 := by
    have hnat : (675419071 : ℕ)^5935*50000000000000^4911 ≤ 23762412688683^4911*1250000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675419071 1250000000 23762412688683 50000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1257233601/10000000000 : ℝ)^5935 ≤ (4079471041101/50000000000000 : ℝ)^4911 := by
    have hnat : (1257233601 : ℕ)^5935*50000000000000^4911 ≤ 4079471041101^4911*10000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1257233601 10000000000 4079471041101 50000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1274921389/2500000000 : ℝ)^5935 ≤ (22158116266049/50000000000000 : ℝ)^4911 := by
    have hnat : (1274921389 : ℕ)^5935*50000000000000^4911 ≤ 22158116266049^4911*2500000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1274921389 2500000000 22158116266049 50000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5935/1024 : ℝ)) 5935 4911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(675419071/1250000000 : ℝ), (-1257233601/10000000000 : ℝ), (1274921389/2500000000 : ℝ)] ![(23762412688683/50000000000000 : ℝ), (4079471041101/50000000000000 : ℝ), (22158116266049/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(675419071/1250000000 : ℝ)|^5935 ≤ (23762412688683/50000000000000 : ℝ)^4911
        have hw : |(675419071/1250000000 : ℝ)|=(675419071/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1257233601/10000000000 : ℝ)|^5935 ≤ (4079471041101/50000000000000 : ℝ)^4911
        have hw : |(-1257233601/10000000000 : ℝ)|=(1257233601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1274921389/2500000000 : ℝ)|^5935 ≤ (22158116266049/50000000000000 : ℝ)^4911
        have hw : |(1274921389/2500000000 : ℝ)|=(1274921389/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1760_box_14 (p : ℝ) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1080670491/2000000000 : ℝ)*x 0 + (5099684633/10000000000 : ℝ)*x 1 + (-314308747/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1080670491/2000000000 : ℝ)^5935 ≤ (23762412088123/50000000000000 : ℝ)^4911 := by
    have hnat : (1080670491 : ℕ)^5935*50000000000000^4911 ≤ 23762412088123^4911*2000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080670491 2000000000 23762412088123 50000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5099684633/10000000000 : ℝ)^5935 ≤ (5539527854849/12500000000000 : ℝ)^4911 := by
    have hnat : (5099684633 : ℕ)^5935*12500000000000^4911 ≤ 5539527854849^4911*10000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5099684633 10000000000 5539527854849 12500000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (314308747/2500000000 : ℝ)^5935 ≤ (1631790592021/20000000000000 : ℝ)^4911 := by
    have hnat : (314308747 : ℕ)^5935*20000000000000^4911 ≤ 1631790592021^4911*2500000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      314308747 2500000000 1631790592021 20000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5935/1024 : ℝ)) 5935 4911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1080670491/2000000000 : ℝ), (5099684633/10000000000 : ℝ), (-314308747/2500000000 : ℝ)] ![(23762412088123/50000000000000 : ℝ), (5539527854849/12500000000000 : ℝ), (1631790592021/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1080670491/2000000000 : ℝ)|^5935 ≤ (23762412088123/50000000000000 : ℝ)^4911
        have hw : |(1080670491/2000000000 : ℝ)|=(1080670491/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5099684633/10000000000 : ℝ)|^5935 ≤ (5539527854849/12500000000000 : ℝ)^4911
        have hw : |(5099684633/10000000000 : ℝ)|=(5099684633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-314308747/2500000000 : ℝ)|^5935 ≤ (1631790592021/20000000000000 : ℝ)^4911
        have hw : |(-314308747/2500000000 : ℝ)|=(314308747/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1760_box_15 (p : ℝ) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1659356781/5000000000 : ℝ)*x 0 + (21871467/50000000 : ℝ)*x 1 + (4374296829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1659356781/5000000000 : ℝ)^5935 ≤ (1648035161691/6250000000000 : ℝ)^4911 := by
    have hnat : (1659356781 : ℕ)^5935*6250000000000^4911 ≤ 1648035161691^4911*5000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1659356781 5000000000 1648035161691 6250000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21871467/50000000 : ℝ)^5935 ≤ (36815701258217/100000000000000 : ℝ)^4911 := by
    have hnat : (21871467 : ℕ)^5935*100000000000000^4911 ≤ 36815701258217^4911*50000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21871467 50000000 36815701258217 100000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4374296829/10000000000 : ℝ)^5935 ≤ (18407868067783/50000000000000 : ℝ)^4911 := by
    have hnat : (4374296829 : ℕ)^5935*50000000000000^4911 ≤ 18407868067783^4911*10000000000^5935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4374296829 10000000000 18407868067783 50000000000000 5935 4911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5935/1024 : ℝ)) 5935 4911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1659356781/5000000000 : ℝ), (21871467/50000000 : ℝ), (4374296829/10000000000 : ℝ)] ![(1648035161691/6250000000000 : ℝ), (36815701258217/100000000000000 : ℝ), (18407868067783/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1659356781/5000000000 : ℝ)|^5935 ≤ (1648035161691/6250000000000 : ℝ)^4911
        have hw : |(1659356781/5000000000 : ℝ)|=(1659356781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(21871467/50000000 : ℝ)|^5935 ≤ (36815701258217/100000000000000 : ℝ)^4911
        have hw : |(21871467/50000000 : ℝ)|=(21871467/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4374296829/10000000000 : ℝ)|^5935 ≤ (18407868067783/50000000000000 : ℝ)^4911
        have hw : |(4374296829/10000000000 : ℝ)|=(4374296829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1760_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (27624673/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8891/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2289/25000 : ℝ)*pair X i i ≤ pair X i h) :
    -(17277/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29301/50000 : ℝ) ∧ (5133/6250 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (93081/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8891/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2289/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8891/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2289/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8891/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2289/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8891/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2289/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8891/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2289/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8891/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2289/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2289/25000 : ℝ) ^ (5919/1024 : ℝ) ≤ (24906662258163/25000000000000000000 : ℝ) := by
    have hpowers : (2289/25000 : ℝ)^5919 ≤ (24906662258163/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2289 : ℕ)^5919*25000000000000000000^1024 ≤ 24906662258163^1024*25000^5919 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2289 25000 24906662258163 25000000000000000000 5919 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2289/25000 : ℝ)) (X := (24906662258163/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5919 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8891/50000 : ℝ) ^ (5919/1024 : ℝ) ≤ (924086901556331/20000000000000000000 : ℝ) := by
    have hpowers : (8891/50000 : ℝ)^5919 ≤ (924086901556331/20000000000000000000 : ℝ)^1024 := by
      have hnat : (8891 : ℕ)^5919*20000000000000000000^1024 ≤ 924086901556331^1024*50000^5919 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8891 50000 924086901556331 20000000000000000000 5919 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8891/50000 : ℝ)) (X := (924086901556331/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5919 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500024906662258163/12500000000000000000 : ℝ) ≤ (10000003447122979/10000000000000000 : ℝ) ^ (5919/1024 : ℝ) := by
    have hpowers : (12500024906662258163/12500000000000000000 : ℝ)^1024 ≤ (10000003447122979/10000000000000000 : ℝ)^5919 := by
      have hnat : (12500024906662258163 : ℕ)^1024*10000000000000000^5919 ≤ 10000003447122979^5919*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500024906662258163 12500000000000000000 10000003447122979 10000000000000000 1024 5919 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000003447122979/10000000000000000 : ℝ)) (X := (12500024906662258163/12500000000000000000 : ℝ)) (by norm_num) 5919 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100004720061156814307/100000000000000000000 : ℝ) ≤ (500004082825049/500000000000000 : ℝ) ^ (5919/1024 : ℝ) := by
    have hpowers : (100004720061156814307/100000000000000000000 : ℝ)^1024 ≤ (500004082825049/500000000000000 : ℝ)^5919 := by
      have hnat : (100004720061156814307 : ℕ)^1024*500000000000000^5919 ≤ 500004082825049^5919*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100004720061156814307 100000000000000000000 500004082825049 500000000000000 1024 5919 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500004082825049/500000000000000 : ℝ)) (X := (100004720061156814307/100000000000000000000 : ℝ)) (by norm_num) 5919 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10000924086901556331/10000000000000000000 : ℝ) ≤ (10000159865878981/10000000000000000 : ℝ) ^ (5919/1024 : ℝ) := by
    have hpowers : (10000924086901556331/10000000000000000000 : ℝ)^1024 ≤ (10000159865878981/10000000000000000 : ℝ)^5919 := by
      have hnat : (10000924086901556331 : ℕ)^1024*10000000000000000^5919 ≤ 10000159865878981^5919*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000924086901556331 10000000000000000000 10000159865878981 10000000000000000 1024 5919 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000159865878981/10000000000000000 : ℝ)) (X := (10000924086901556331/10000000000000000000 : ℝ)) (by norm_num) 5919 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(24906662258163/25000000000000000000 : ℝ) ≤ ((43129298782376431271/43130000000000000000 : ℝ)+2*(78209378001/862600000000000 : ℝ)*(2289/25000 : ℝ))^(5919/1024 : ℝ) := by
    rw [show (43129298782376431271/43130000000000000000 : ℝ)+2*(78209378001/862600000000000 : ℝ)*(2289/25000 : ℝ)=(10000003447122979/10000000000000000 : ℝ) by norm_num, show 1+2*(24906662258163/25000000000000000000 : ℝ)=(12500024906662258163/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(924086901556331/20000000000000000000 : ℝ)+(24906662258163/25000000000000000000 : ℝ) ≤ ((43129298782376431271/43130000000000000000 : ℝ)+(78209378001/862600000000000 : ℝ)*((8891/50000 : ℝ)+(2289/25000 : ℝ)))^(5919/1024 : ℝ) := by
    rw [show (43129298782376431271/43130000000000000000 : ℝ)+(78209378001/862600000000000 : ℝ)*((8891/50000 : ℝ)+(2289/25000 : ℝ))=(500004082825049/500000000000000 : ℝ) by norm_num, show 1+(924086901556331/20000000000000000000 : ℝ)+(24906662258163/25000000000000000000 : ℝ)=(100004720061156814307/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(924086901556331/20000000000000000000 : ℝ) ≤ ((43129298782376431271/43130000000000000000 : ℝ)+2*(78209378001/862600000000000 : ℝ)*(8891/50000 : ℝ))^(5919/1024 : ℝ) := by
    rw [show (43129298782376431271/43130000000000000000 : ℝ)+2*(78209378001/862600000000000 : ℝ)*(8891/50000 : ℝ)=(10000159865878981/10000000000000000 : ℝ) by norm_num, show 1+2*(924086901556331/20000000000000000000 : ℝ)=(10000924086901556331/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (43129298782376431271/43130000000000000000 : ℝ)*(X 1 0+X 2 0)+(78209378001/862600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5919/1024 : ℝ)) (lo := (2289/25000 : ℝ)) (hi := (8891/50000 : ℝ)) (c := (43129298782376431271/43130000000000000000 : ℝ)) (alpha := (78209378001/862600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (43129298782376431271/43130000000000000000 : ℝ)*(X 0 1+X 2 1)+(78209378001/862600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5919/1024 : ℝ)) (lo := (2289/25000 : ℝ)) (hi := (8891/50000 : ℝ)) (c := (43129298782376431271/43130000000000000000 : ℝ)) (alpha := (78209378001/862600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (43129298782376431271/43130000000000000000 : ℝ)*(X 0 2+X 1 2)+(78209378001/862600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5919/1024 : ℝ)) (lo := (2289/25000 : ℝ)) (hi := (8891/50000 : ℝ)) (c := (43129298782376431271/43130000000000000000 : ℝ)) (alpha := (78209378001/862600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-398896781/5000000000 : ℝ)*X 0 0+(5414706567/10000000000 : ℝ)*X 0 1+(5414706209/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1760_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((207730893/400000000 : ℝ)*X 1 0+(-1114542901/10000000000 : ℝ)*X 1 1+(1353676653/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1760_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5193272069/10000000000 : ℝ)*X 2 0+(338419157/625000000 : ℝ)*X 2 1+(-1114543393/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1760_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4525444493/10000000000 : ℝ)*X 0 0+(3776029721/10000000000 : ℝ)*X 0 1+(377603173/1000000000 : ℝ)*X 0 2+(4525444493/10000000000 : ℝ)*X 1 0+(3776029721/10000000000 : ℝ)*X 1 1+(377603173/1000000000 : ℝ)*X 1 2+(4525444493/10000000000 : ℝ)*X 2 0+(3776029721/10000000000 : ℝ)*X 2 1+(377603173/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1760_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1578499501/10000000000 : ℝ)*X 0 0+(5129467989/10000000000 : ℝ)*X 0 1+(320591759/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1760_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1076684693/2000000000 : ℝ)*X 1 0+(-1244314421/10000000000 : ℝ)*X 1 1+(5129468147/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1760_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((269171181/500000000 : ℝ)*X 2 0+(641183509/1250000000 : ℝ)*X 2 1+(-1244314311/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1760_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((42968743/125000000 : ℝ)*X 0 0+(1079485577/2500000000 : ℝ)*X 0 1+(4317942561/10000000000 : ℝ)*X 0 2+(42968743/125000000 : ℝ)*X 1 0+(1079485577/2500000000 : ℝ)*X 1 1+(4317942561/10000000000 : ℝ)*X 1 2+(42968743/125000000 : ℝ)*X 2 0+(1079485577/2500000000 : ℝ)*X 2 1+(4317942561/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1760_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1408478103/10000000000 : ℝ)*X 0 0+(2455647403/5000000000 : ℝ)*X 0 1+(1095141797/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1760_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2576340227/5000000000 : ℝ)*X 1 0+(-542725217/5000000000 : ℝ)*X 1 1+(5475708843/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1760_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1288170077/2500000000 : ℝ)*X 2 0+(5475709273/10000000000 : ℝ)*X 2 1+(-1085450033/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1760_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((474763299/1000000000 : ℝ)*X 0 0+(3659703619/10000000000 : ℝ)*X 0 1+(3659702021/10000000000 : ℝ)*X 0 2+(474763299/1000000000 : ℝ)*X 1 0+(3659703619/10000000000 : ℝ)*X 1 1+(3659702021/10000000000 : ℝ)*X 1 2+(474763299/1000000000 : ℝ)*X 2 0+(3659703619/10000000000 : ℝ)*X 2 1+(3659702021/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1760_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-95356591/1000000000 : ℝ)*X 0 0+(1124092659/2000000000 : ℝ)*X 0 1+(5099685421/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1760_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((675419071/1250000000 : ℝ)*X 1 0+(-1257233601/10000000000 : ℝ)*X 1 1+(1274921389/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1760_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1080670491/2000000000 : ℝ)*X 2 0+(5099684633/10000000000 : ℝ)*X 2 1+(-314308747/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1760_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1659356781/5000000000 : ℝ)*X 0 0+(21871467/50000000 : ℝ)*X 0 1+(4374296829/10000000000 : ℝ)*X 0 2+(1659356781/5000000000 : ℝ)*X 1 0+(21871467/50000000 : ℝ)*X 1 1+(4374296829/10000000000 : ℝ)*X 1 2+(1659356781/5000000000 : ℝ)*X 2 0+(21871467/50000000 : ℝ)*X 2 1+(4374296829/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1760_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-17277/25000 : ℝ) ≤ (-186282153994821750972968911808037/269562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (283151/6250000000000 : ℝ)*(upper0) + (1023169/6250000000000 : ℝ)*(lower2) + (19315947/100000000000000 : ℝ)*(lower3) + (3434029/25000000000000 : ℝ)*(upper5) + (135479151394983/12500000000000 : ℝ)*(major0) + (135479151394983/12500000000000 : ℝ)*(major1) + (135479151394983/12500000000000 : ℝ)*(major2) + (56899751/50000000000000 : ℝ)*(sp3) + (850136735898719/50000000000000 : ℝ)*(sp4) + (850133407439333/50000000000000 : ℝ)*(sp5) + (850135912190999/50000000000000 : ℝ)*(sp6) + (245213979470893/50000000000000 : ℝ)*(sp7) + (6656918771/100000000000000 : ℝ)*(sp13) + (1647415439/100000000000000 : ℝ)*(sp14) + (61303509092661/12500000000000 : ℝ)*(f.failure) + (850136735898719/50000000000000 : ℝ)*(f.sum) + (11546413157803/5391250000000000000000000000 : ℝ)*base65 + (1563096091403363393/539125000000000000000000000000000 : ℝ)*base67 + (896050602746113393/539125000000000000000000000000000 : ℝ)*base69 + (2880339809263863393/539125000000000000000000000000000 : ℝ)*base71 + (80171006078687/21565000000000000000000000000 : ℝ)*base73 + (2939868891948863393/539125000000000000000000000000000 : ℝ)*base75 + (3560179729934988393/539125000000000000000000000000000 : ℝ)*base77 + (3830329907454238393/539125000000000000000000000000000 : ℝ)*base79 + (2742311014423/5391250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (675147/156250000000000000000 : ℝ)*base90 + (675147/156250000000000000000 : ℝ)*base92 + (675147/156250000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (29301/50000 : ℝ) ≤ (157975580896955632146294770187477/269562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (29516789/50000000000000 : ℝ)*(lower1) + (82593679/100000000000000 : ℝ)*(upper2) + (22668527/100000000000000 : ℝ)*(lower4) + (151666279815443/12500000000000 : ℝ)*(major0) + (151666279815443/12500000000000 : ℝ)*(major1) + (151666279815443/12500000000000 : ℝ)*(major2) + (29032809319113/1562500000000 : ℝ)*(sp0) + (1858099119440833/100000000000000 : ℝ)*(sp1) + (464523840652773/25000000000000 : ℝ)*(sp2) + (137256156254533/25000000000000 : ℝ)*(sp3) + (919750673/50000000000000 : ℝ)*(sp5) + (20330293/25000000000000 : ℝ)*(sp7) + (5596331087/100000000000000 : ℝ)*(sp10) + (1162518947/100000000000000 : ℝ)*(sp12) + (68628088292413/12500000000000 : ℝ)*(f.failure) + (1858100958942179/100000000000000 : ℝ)*(f.sum) + (38671239434679/10782500000000000000000000000 : ℝ)*base66 + (92291496529056947/539125000000000000000000000000000 : ℝ)*base68 + (1565066685855306947/539125000000000000000000000000000 : ℝ)*base70 + (3149378413314306947/539125000000000000000000000000000 : ℝ)*base72 + (10321459842587/21565000000000000000000000000 : ℝ)*base73 + (2052486624002681947/539125000000000000000000000000000 : ℝ)*base76 + (4538700049636431947/539125000000000000000000000000000 : ℝ)*base78 + (233858144666306947/539125000000000000000000000000000 : ℝ)*base80 + (14303179683353/21565000000000000000000000000 : ℝ)*base82 + (5949/156250000000000000000 : ℝ)*base89 + (5949/156250000000000000000 : ℝ)*base91 + (5949/156250000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (5133/6250 : ℝ) ≤ (88557082417502245732539864326619/107825000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (56313241/100000000000000 : ℝ)*(upper1) + (24207179/50000000000000 : ℝ)*(upper4) + (994473/10000000000000 : ℝ)*(lower5) + (116259848357863/10000000000000 : ℝ)*(major0) + (116259848357863/10000000000000 : ℝ)*(major1) + (116259848357863/10000000000000 : ℝ)*(major2) + (3107986201/25000000000000 : ℝ)*(sp1) + (7682933291/25000000000000 : ℝ)*(sp2) + (33867433/625000000000 : ℝ)*(sp3) + (51621021/4000000000000 : ℝ)*(sp4) + (177174999385701/10000000000000 : ℝ)*(sp8) + (177173885243773/10000000000000 : ℝ)*(sp9) + (1771720552649371/100000000000000 : ℝ)*(sp10) + (526063470595687/100000000000000 : ℝ)*(sp11) + (526068889384967/100000000000000 : ℝ)*(f.failure) + (354350256876507/20000000000000 : ℝ)*(f.sum) + (536351608467/1078250000000000000000000000 : ℝ)*base65 + (2565244086358316127/431300000000000000000000000000000 : ℝ)*base68 + (3903204339645016127/431300000000000000000000000000000 : ℝ)*base70 + (38282633268083873/431300000000000000000000000000000 : ℝ)*base71 + (3001651579327/2156500000000000000000000000 : ℝ)*base74 + (2409646938469416127/431300000000000000000000000000000 : ℝ)*base76 + (2367769213275116127/431300000000000000000000000000000 : ℝ)*base78 + (2161923365294116127/431300000000000000000000000000000 : ℝ)*base80 + (14110458846453/4313000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (9490791/1250000000000000000000 : ℝ)*base89 + (9490791/1250000000000000000000 : ℝ)*base91 + (9490791/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-93081/100000 : ℝ) ≤ (-501811192831383402536104034047239/539125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (111290943/100000000000000 : ℝ)*(upper3) + (10940389/4000000000000 : ℝ)*(lower4) + (197631349/100000000000000 : ℝ)*(upper5) + (305198188372799/25000000000000 : ℝ)*(major0) + (305198188372799/25000000000000 : ℝ)*(major1) + (305198188372799/25000000000000 : ℝ)*(major2) + (3698441109/100000000000000 : ℝ)*(sp4) + (6472443487/20000000000000 : ℝ)*(sp5) + (158717930477/100000000000000 : ℝ)*(sp6) + (7760276483/25000000000000 : ℝ)*(sp7) + (192020663223779/10000000000000 : ℝ)*(sp12) + (240022246057683/12500000000000 : ℝ)*(sp13) + (960025806374211/50000000000000 : ℝ)*(sp14) + (552370408809509/100000000000000 : ℝ)*(sp15) + (276200724957721/50000000000000 : ℝ)*(f.failure) + (960105165339449/50000000000000 : ℝ)*(f.sum) + (11911759880213/21565000000000000000000000000 : ℝ)*base65 + (5015534428033402471/1078250000000000000000000000000000 : ℝ)*base68 + (1336675456357402471/1078250000000000000000000000000000 : ℝ)*base70 + (5229137325121902471/1078250000000000000000000000000000 : ℝ)*base72 + (102171721736393/21565000000000000000000000000 : ℝ)*base73 + (4873514060922152471/1078250000000000000000000000000000 : ℝ)*base76 + (4351647687846652471/1078250000000000000000000000000000 : ℝ)*base78 + (5049554961220152471/1078250000000000000000000000000000 : ℝ)*base80 + (35700887153787/5391250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (6450233/625000000000000000000 : ℝ)*base89 + (6450233/625000000000000000000 : ℝ)*base91 + (6450233/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1760_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (27624673/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8891/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2289/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(17277/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(29301/50000 : ℝ) else (5133/6250 : ℝ) ≤ X j i ∧ X j i ≤ (93081/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1760_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1760_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (27624673/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17783/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1831/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(17277/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(29301/50000 : ℝ) else (5133/6250 : ℝ) ≤ X j i ∧ X j i ≤ (93081/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1760_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1760_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5919/1024 : ℝ) ≤ p) (hpb : p ≤ (5935/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (27624673/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17783/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1831/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(17277/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(29301/50000 : ℝ) else (5133/6250 : ℝ) ≤ X j i ∧ X j i ≤ (93081/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1760_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
