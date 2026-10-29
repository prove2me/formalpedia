-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1575_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:28:35.07513+00:00
-- url     : https://prove2.me/submissions/a1ecdde3-3fb9-4464-84bf-589c76217536

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
theorem support_rectangle_w1575_s0_0 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1621005573/10000000000 : ℝ)*x 0 + (5865941427/10000000000 : ℝ)*x 1 + (4881351797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1621005573/10000000000 : ℝ)^4647 ≤ (38770287551/400000000000 : ℝ)^3623 := by
    have hnat : (1621005573 : ℕ)^4647*400000000000^3623 ≤ 38770287551^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1621005573 10000000000 38770287551 400000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5865941427/10000000000 : ℝ)^4647 ≤ (25224989959407/50000000000000 : ℝ)^3623 := by
    have hnat : (5865941427 : ℕ)^4647*50000000000000^3623 ≤ 25224989959407^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5865941427 10000000000 25224989959407 50000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4881351797/10000000000 : ℝ)^4647 ≤ (4982181022827/12500000000000 : ℝ)^3623 := by
    have hnat : (4881351797 : ℕ)^4647*12500000000000^3623 ≤ 4982181022827^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4881351797 10000000000 4982181022827 12500000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1621005573/10000000000 : ℝ), (5865941427/10000000000 : ℝ), (4881351797/10000000000 : ℝ)] ![(38770287551/400000000000 : ℝ), (25224989959407/50000000000000 : ℝ), (4982181022827/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1621005573/10000000000 : ℝ)|^4647 ≤ (38770287551/400000000000 : ℝ)^3623
        have hw : |(-1621005573/10000000000 : ℝ)|=(1621005573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5865941427/10000000000 : ℝ)|^4647 ≤ (25224989959407/50000000000000 : ℝ)^3623
        have hw : |(5865941427/10000000000 : ℝ)|=(5865941427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4881351797/10000000000 : ℝ)|^4647 ≤ (4982181022827/12500000000000 : ℝ)^3623
        have hw : |(4881351797/10000000000 : ℝ)|=(4881351797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_s0_1 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5464412847/10000000000 : ℝ)*x 0 + (-542145151/2500000000 : ℝ)*x 1 + (4881351791/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5464412847/10000000000 : ℝ)^4647 ≤ (46064158461433/100000000000000 : ℝ)^3623 := by
    have hnat : (5464412847 : ℕ)^4647*100000000000000^3623 ≤ 46064158461433^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5464412847 10000000000 46064158461433 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (542145151/2500000000 : ℝ)^4647 ≤ (2815678679949/20000000000000 : ℝ)^3623 := by
    have hnat : (542145151 : ℕ)^4647*20000000000000^3623 ≤ 2815678679949^3623*2500000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542145151 2500000000 2815678679949 20000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4881351791/10000000000 : ℝ)^4647 ≤ (19928724059889/50000000000000 : ℝ)^3623 := by
    have hnat : (4881351791 : ℕ)^4647*50000000000000^3623 ≤ 19928724059889^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4881351791 10000000000 19928724059889 50000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5464412847/10000000000 : ℝ), (-542145151/2500000000 : ℝ), (4881351791/10000000000 : ℝ)] ![(46064158461433/100000000000000 : ℝ), (2815678679949/20000000000000 : ℝ), (19928724059889/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5464412847/10000000000 : ℝ)|^4647 ≤ (46064158461433/100000000000000 : ℝ)^3623
        have hw : |(5464412847/10000000000 : ℝ)|=(5464412847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-542145151/2500000000 : ℝ)|^4647 ≤ (2815678679949/20000000000000 : ℝ)^3623
        have hw : |(-542145151/2500000000 : ℝ)|=(542145151/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4881351791/10000000000 : ℝ)|^4647 ≤ (19928724059889/50000000000000 : ℝ)^3623
        have hw : |(4881351791/10000000000 : ℝ)|=(4881351791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_s0_2 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5464412909/10000000000 : ℝ)*x 0 + (2440675857/5000000000 : ℝ)*x 1 + (-2168580621/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5464412909/10000000000 : ℝ)^4647 ≤ (11516039782951/25000000000000 : ℝ)^3623 := by
    have hnat : (5464412909 : ℕ)^4647*25000000000000^3623 ≤ 11516039782951^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5464412909 10000000000 11516039782951 25000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2440675857/5000000000 : ℝ)^4647 ≤ (4982180914169/12500000000000 : ℝ)^3623 := by
    have hnat : (2440675857 : ℕ)^4647*12500000000000^3623 ≤ 4982180914169^3623*5000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2440675857 5000000000 4982180914169 12500000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2168580621/10000000000 : ℝ)^4647 ≤ (7039196770651/50000000000000 : ℝ)^3623 := by
    have hnat : (2168580621 : ℕ)^4647*50000000000000^3623 ≤ 7039196770651^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2168580621 10000000000 7039196770651 50000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5464412909/10000000000 : ℝ), (2440675857/5000000000 : ℝ), (-2168580621/10000000000 : ℝ)] ![(11516039782951/25000000000000 : ℝ), (4982180914169/12500000000000 : ℝ), (7039196770651/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5464412909/10000000000 : ℝ)|^4647 ≤ (11516039782951/25000000000000 : ℝ)^3623
        have hw : |(5464412909/10000000000 : ℝ)|=(5464412909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2440675857/5000000000 : ℝ)|^4647 ≤ (4982180914169/12500000000000 : ℝ)^3623
        have hw : |(2440675857/5000000000 : ℝ)|=(2440675857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2168580621/10000000000 : ℝ)|^4647 ≤ (7039196770651/50000000000000 : ℝ)^3623
        have hw : |(-2168580621/10000000000 : ℝ)|=(2168580621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_s0_3 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2064281443/5000000000 : ℝ)*x 0 + (3093448147/10000000000 : ℝ)*x 1 + (5425551691/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2064281443/5000000000 : ℝ)^4647 ≤ (32152060243333/100000000000000 : ℝ)^3623 := by
    have hnat : (2064281443 : ℕ)^4647*100000000000000^3623 ≤ 32152060243333^3623*5000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064281443 5000000000 32152060243333 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3093448147/10000000000 : ℝ)^4647 ≤ (5550885610039/25000000000000 : ℝ)^3623 := by
    have hnat : (3093448147 : ℕ)^4647*25000000000000^3623 ≤ 5550885610039^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3093448147 10000000000 5550885610039 25000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5425551691/10000000000 : ℝ)^4647 ≤ (22822198649863/50000000000000 : ℝ)^3623 := by
    have hnat : (5425551691 : ℕ)^4647*50000000000000^3623 ≤ 22822198649863^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425551691 10000000000 22822198649863 50000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2064281443/5000000000 : ℝ), (3093448147/10000000000 : ℝ), (5425551691/10000000000 : ℝ)] ![(32152060243333/100000000000000 : ℝ), (5550885610039/25000000000000 : ℝ), (22822198649863/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2064281443/5000000000 : ℝ)|^4647 ≤ (32152060243333/100000000000000 : ℝ)^3623
        have hw : |(2064281443/5000000000 : ℝ)|=(2064281443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3093448147/10000000000 : ℝ)|^4647 ≤ (5550885610039/25000000000000 : ℝ)^3623
        have hw : |(3093448147/10000000000 : ℝ)|=(3093448147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5425551691/10000000000 : ℝ)|^4647 ≤ (22822198649863/50000000000000 : ℝ)^3623
        have hw : |(5425551691/10000000000 : ℝ)|=(5425551691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_s0_4 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-50750719/312500000 : ℝ)*x 0 + (4906136557/10000000000 : ℝ)*x 1 + (5840279823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (50750719/312500000 : ℝ)^4647 ≤ (9715719754011/100000000000000 : ℝ)^3623 := by
    have hnat : (50750719 : ℕ)^4647*100000000000000^3623 ≤ 9715719754011^3623*312500000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50750719 312500000 9715719754011 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4906136557/10000000000 : ℝ)^4647 ≤ (40117206566113/100000000000000 : ℝ)^3623 := by
    have hnat : (4906136557 : ℕ)^4647*100000000000000^3623 ≤ 40117206566113^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4906136557 10000000000 40117206566113 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5840279823/10000000000 : ℝ)^4647 ≤ (3135442103739/6250000000000 : ℝ)^3623 := by
    have hnat : (5840279823 : ℕ)^4647*6250000000000^3623 ≤ 3135442103739^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5840279823 10000000000 3135442103739 6250000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-50750719/312500000 : ℝ), (4906136557/10000000000 : ℝ), (5840279823/10000000000 : ℝ)] ![(9715719754011/100000000000000 : ℝ), (40117206566113/100000000000000 : ℝ), (3135442103739/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-50750719/312500000 : ℝ)|^4647 ≤ (9715719754011/100000000000000 : ℝ)^3623
        have hw : |(-50750719/312500000 : ℝ)|=(50750719/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4906136557/10000000000 : ℝ)|^4647 ≤ (40117206566113/100000000000000 : ℝ)^3623
        have hw : |(4906136557/10000000000 : ℝ)|=(4906136557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5840279823/10000000000 : ℝ)|^4647 ≤ (3135442103739/6250000000000 : ℝ)^3623
        have hw : |(5840279823/10000000000 : ℝ)|=(5840279823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_s0_5 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (129881113/250000000 : ℝ)*x 0 + (-1209653073/10000000000 : ℝ)*x 1 + (5840279503/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (129881113/250000000 : ℝ)^4647 ≤ (674598338629/1562500000000 : ℝ)^3623 := by
    have hnat : (129881113 : ℕ)^4647*1562500000000^3623 ≤ 674598338629^3623*250000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129881113 250000000 674598338629 1562500000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1209653073/10000000000 : ℝ)^4647 ≤ (1664659044251/25000000000000 : ℝ)^3623 := by
    have hnat : (1209653073 : ℕ)^4647*25000000000000^3623 ≤ 1664659044251^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1209653073 10000000000 1664659044251 25000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5840279503/10000000000 : ℝ)^4647 ≤ (12541767533543/25000000000000 : ℝ)^3623 := by
    have hnat : (5840279503 : ℕ)^4647*25000000000000^3623 ≤ 12541767533543^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5840279503 10000000000 12541767533543 25000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(129881113/250000000 : ℝ), (-1209653073/10000000000 : ℝ), (5840279503/10000000000 : ℝ)] ![(674598338629/1562500000000 : ℝ), (1664659044251/25000000000000 : ℝ), (12541767533543/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(129881113/250000000 : ℝ)|^4647 ≤ (674598338629/1562500000000 : ℝ)^3623
        have hw : |(129881113/250000000 : ℝ)|=(129881113/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1209653073/10000000000 : ℝ)|^4647 ≤ (1664659044251/25000000000000 : ℝ)^3623
        have hw : |(-1209653073/10000000000 : ℝ)|=(1209653073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5840279503/10000000000 : ℝ)|^4647 ≤ (12541767533543/25000000000000 : ℝ)^3623
        have hw : |(5840279503/10000000000 : ℝ)|=(5840279503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_s0_6 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2597621967/5000000000 : ℝ)*x 0 + (4562719/7812500 : ℝ)*x 1 + (-302413171/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2597621967/5000000000 : ℝ)^4647 ≤ (2158714371299/5000000000000 : ℝ)^3623 := by
    have hnat : (2597621967 : ℕ)^4647*5000000000000^3623 ≤ 2158714371299^3623*5000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2597621967 5000000000 2158714371299 5000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4562719/7812500 : ℝ)^4647 ≤ (25083539567801/50000000000000 : ℝ)^3623 := by
    have hnat : (4562719 : ℕ)^4647*50000000000000^3623 ≤ 25083539567801^3623*7812500^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4562719 7812500 25083539567801 50000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (302413171/2500000000 : ℝ)^4647 ≤ (416164589407/6250000000000 : ℝ)^3623 := by
    have hnat : (302413171 : ℕ)^4647*6250000000000^3623 ≤ 416164589407^3623*2500000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      302413171 2500000000 416164589407 6250000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2597621967/5000000000 : ℝ), (4562719/7812500 : ℝ), (-302413171/2500000000 : ℝ)] ![(2158714371299/5000000000000 : ℝ), (25083539567801/50000000000000 : ℝ), (416164589407/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2597621967/5000000000 : ℝ)|^4647 ≤ (2158714371299/5000000000000 : ℝ)^3623
        have hw : |(2597621967/5000000000 : ℝ)|=(2597621967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4562719/7812500 : ℝ)|^4647 ≤ (25083539567801/50000000000000 : ℝ)^3623
        have hw : |(4562719/7812500 : ℝ)|=(4562719/7812500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-302413171/2500000000 : ℝ)|^4647 ≤ (416164589407/6250000000000 : ℝ)^3623
        have hw : |(-302413171/2500000000 : ℝ)|=(302413171/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_s0_7 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (413570843/1000000000 : ℝ)*x 0 + (1341711113/2500000000 : ℝ)*x 1 + (315423051/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (413570843/1000000000 : ℝ)^4647 ≤ (16111726627771/50000000000000 : ℝ)^3623 := by
    have hnat : (413570843 : ℕ)^4647*50000000000000^3623 ≤ 16111726627771^3623*1000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413570843 1000000000 16111726627771 50000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1341711113/2500000000 : ℝ)^4647 ≤ (45011878805629/100000000000000 : ℝ)^3623 := by
    have hnat : (1341711113 : ℕ)^4647*100000000000000^3623 ≤ 45011878805629^3623*2500000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1341711113 2500000000 45011878805629 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (315423051/1000000000 : ℝ)^4647 ≤ (182117343449/800000000000 : ℝ)^3623 := by
    have hnat : (315423051 : ℕ)^4647*800000000000^3623 ≤ 182117343449^3623*1000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      315423051 1000000000 182117343449 800000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(413570843/1000000000 : ℝ), (1341711113/2500000000 : ℝ), (315423051/1000000000 : ℝ)] ![(16111726627771/50000000000000 : ℝ), (45011878805629/100000000000000 : ℝ), (182117343449/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(413570843/1000000000 : ℝ)|^4647 ≤ (16111726627771/50000000000000 : ℝ)^3623
        have hw : |(413570843/1000000000 : ℝ)|=(413570843/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1341711113/2500000000 : ℝ)|^4647 ≤ (45011878805629/100000000000000 : ℝ)^3623
        have hw : |(1341711113/2500000000 : ℝ)|=(1341711113/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(315423051/1000000000 : ℝ)|^4647 ≤ (182117343449/800000000000 : ℝ)^3623
        have hw : |(315423051/1000000000 : ℝ)|=(315423051/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1575_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168430229/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (3603/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (24693/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4645/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4645 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4645*1^1024 ≤ 0^1024*1^4645 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4645 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4645 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4645/1024 : ℝ) ≤ (1566358864604841243/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4645 ≤ (1566358864604841243/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4645*100000000000000000000^1024 ≤ 1566358864604841243^1024*5^4645 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1566358864604841243 100000000000000000000 4645 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1566358864604841243/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4645 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4645/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4645 := by
      have hnat : (1 : ℕ)^1024*1^4645 ≤ 1^4645*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4645 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4645 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101566358864604841243/100000000000000000000 : ℝ) ≤ (10034321828757443/10000000000000000 : ℝ) ^ (4645/1024 : ℝ) := by
    have hpowers : (101566358864604841243/100000000000000000000 : ℝ)^1024 ≤ (10034321828757443/10000000000000000 : ℝ)^4645 := by
      have hnat : (101566358864604841243 : ℕ)^1024*10000000000000000^4645 ≤ 10034321828757443^4645*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101566358864604841243 100000000000000000000 10034321828757443 10000000000000000 1024 4645 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10034321828757443/10000000000000000 : ℝ)) (X := (101566358864604841243/100000000000000000000 : ℝ)) (by norm_num) 4645 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51566358864604841243/50000000000000000000 : ℝ) ≤ (5034321828757443/5000000000000000 : ℝ) ^ (4645/1024 : ℝ) := by
    have hpowers : (51566358864604841243/50000000000000000000 : ℝ)^1024 ≤ (5034321828757443/5000000000000000 : ℝ)^4645 := by
      have hnat : (51566358864604841243 : ℕ)^1024*5000000000000000^4645 ≤ 5034321828757443^4645*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51566358864604841243 50000000000000000000 5034321828757443 5000000000000000 1024 4645 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5034321828757443/5000000000000000 : ℝ)) (X := (51566358864604841243/50000000000000000000 : ℝ)) (by norm_num) 4645 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(34321828757443/4000000000000000 : ℝ)*(0 : ℝ))^(4645/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(34321828757443/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1566358864604841243/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(34321828757443/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4645/1024 : ℝ) := by
    rw [show (1 : ℝ)+(34321828757443/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10034321828757443/10000000000000000 : ℝ) by norm_num, show 1+(1566358864604841243/100000000000000000000 : ℝ)+(0 : ℝ)=(101566358864604841243/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1566358864604841243/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(34321828757443/4000000000000000 : ℝ)*(2/5 : ℝ))^(4645/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(34321828757443/4000000000000000 : ℝ)*(2/5 : ℝ)=(5034321828757443/5000000000000000 : ℝ) by norm_num, show 1+2*(1566358864604841243/100000000000000000000 : ℝ)=(51566358864604841243/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(34321828757443/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4645/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (34321828757443/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(34321828757443/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4645/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (34321828757443/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(34321828757443/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4645/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (34321828757443/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1621005573/10000000000 : ℝ)*X 0 0+(5865941427/10000000000 : ℝ)*X 0 1+(4881351797/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5464412847/10000000000 : ℝ)*X 1 0+(-542145151/2500000000 : ℝ)*X 1 1+(4881351791/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5464412909/10000000000 : ℝ)*X 2 0+(2440675857/5000000000 : ℝ)*X 2 1+(-2168580621/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2064281443/5000000000 : ℝ)*X 0 0+(3093448147/10000000000 : ℝ)*X 0 1+(5425551691/10000000000 : ℝ)*X 0 2+(2064281443/5000000000 : ℝ)*X 1 0+(3093448147/10000000000 : ℝ)*X 1 1+(5425551691/10000000000 : ℝ)*X 1 2+(2064281443/5000000000 : ℝ)*X 2 0+(3093448147/10000000000 : ℝ)*X 2 1+(5425551691/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-50750719/312500000 : ℝ)*X 0 0+(4906136557/10000000000 : ℝ)*X 0 1+(5840279823/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((129881113/250000000 : ℝ)*X 1 0+(-1209653073/10000000000 : ℝ)*X 1 1+(5840279503/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2597621967/5000000000 : ℝ)*X 2 0+(4562719/7812500 : ℝ)*X 2 1+(-302413171/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((413570843/1000000000 : ℝ)*X 0 0+(1341711113/2500000000 : ℝ)*X 0 1+(315423051/1000000000 : ℝ)*X 0 2+(413570843/1000000000 : ℝ)*X 1 0+(1341711113/2500000000 : ℝ)*X 1 1+(315423051/1000000000 : ℝ)*X 1 2+(413570843/1000000000 : ℝ)*X 2 0+(1341711113/2500000000 : ℝ)*X 2 1+(315423051/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (889449134837148907698801/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (82688937/100000000000000 : ℝ)*(base1) + (916273771/50000000000000 : ℝ)*(base19) + (922035699/50000000000000 : ℝ)*(base23) + (29975343/12500000000000 : ℝ)*(upper3) + (118943427/50000000000000 : ℝ)*(upper5) + (722234150128969/100000000000000 : ℝ)*(major0) + (722234150128969/100000000000000 : ℝ)*(major1) + (722234150128969/100000000000000 : ℝ)*(major2) + (1015658069116329/100000000000000 : ℝ)*(sp0) + (1015663007794631/100000000000000 : ℝ)*(sp1) + (40626519850831/4000000000000 : ℝ)*(sp2) + (428800173816391/100000000000000 : ℝ)*(sp3) + (6853914781/100000000000000 : ℝ)*(sp4) + (2906927389/100000000000000 : ℝ)*(sp7) + (428803163432717/100000000000000 : ℝ)*(f.failure) + (1015664840342173/100000000000000 : ℝ)*(f.sum) + (394122717533733/200000000000000000000000000000 : ℝ)*base66 + (2494262053333733/400000000000000000000000000000 : ℝ)*base68 + (1591626449866267/400000000000000000000000000000 : ℝ)*base69 + (834899792533733/400000000000000000000000000000 : ℝ)*base72 + (1162135767533733/200000000000000000000000000000 : ℝ)*base74 + (715595591866267/400000000000000000000000000000 : ℝ)*base75 + (433063799733733/400000000000000000000000000000 : ℝ)*base78 + (80001193333733/400000000000000000000000000000 : ℝ)*base80 + (469540609466267/200000000000000000000000000000 : ℝ)*base81 + (50402193/10000000000000000000000 : ℝ)*base89 + (50402193/10000000000000000000000 : ℝ)*base91 + (50402193/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (131359294901985865649739/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (78321149/25000000000000 : ℝ)*(base19) + (458712617/100000000000000 : ℝ)*(base23) + (248859421/100000000000000 : ℝ)*(base39) + (5421369/25000000000000 : ℝ)*(upper2) + (45985229/20000000000000 : ℝ)*(upper5) + (95153263824857/12500000000000 : ℝ)*(major0) + (95153263824857/12500000000000 : ℝ)*(major1) + (152245172347887/20000000000000 : ℝ)*(major2) + (500880727/50000000000000 : ℝ)*(sp1) + (609660083/100000000000000 : ℝ)*(sp2) + (1070498549922381/100000000000000 : ℝ)*(sp4) + (1070497234876331/100000000000000 : ℝ)*(sp5) + (1070497730409103/100000000000000 : ℝ)*(sp6) + (14123543082171/3125000000000 : ℝ)*(sp7) + (14123543082171/3125000000000 : ℝ)*(f.failure) + (535249399390901/50000000000000 : ℝ)*(f.sum) + (164682984650087/400000000000000000000000000000 : ℝ)*base66 + (914421588307059/80000000000000000000000000000 : ℝ)*base68 + (89210576989349/50000000000000000000000000000 : ℝ)*base70 + (391688232867059/80000000000000000000000000000 : ℝ)*base72 + (2476614605850087/400000000000000000000000000000 : ℝ)*base74 + (106530029189349/50000000000000000000000000000 : ℝ)*base76 + (289469693289349/50000000000000000000000000000 : ℝ)*base78 + (666113841139349/50000000000000000000000000000 : ℝ)*base80 + (4825969035651/25000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (2347159/312500000000000000000 : ℝ)*base89 + (2347159/312500000000000000000 : ℝ)*base91 + (2347159/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1575_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168430229/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3603/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (24693/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1575_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1575_s1_0 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-35167089/200000000 : ℝ)*x 0 + (1383002409/2500000000 : ℝ)*x 1 + (320420709/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (35167089/200000000 : ℝ)^4647 ≤ (2689578948953/25000000000000 : ℝ)^3623 := by
    have hnat : (35167089 : ℕ)^4647*25000000000000^3623 ≤ 2689578948953^3623*200000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35167089 200000000 2689578948953 25000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1383002409/2500000000 : ℝ)^4647 ≤ (46796319090073/100000000000000 : ℝ)^3623 := by
    have hnat : (1383002409 : ℕ)^4647*100000000000000^3623 ≤ 46796319090073^3623*2500000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1383002409 2500000000 46796319090073 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (320420709/625000000 : ℝ)^4647 ≤ (8489073018893/20000000000000 : ℝ)^3623 := by
    have hnat : (320420709 : ℕ)^4647*20000000000000^3623 ≤ 8489073018893^3623*625000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      320420709 625000000 8489073018893 20000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-35167089/200000000 : ℝ), (1383002409/2500000000 : ℝ), (320420709/625000000 : ℝ)] ![(2689578948953/25000000000000 : ℝ), (46796319090073/100000000000000 : ℝ), (8489073018893/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-35167089/200000000 : ℝ)|^4647 ≤ (2689578948953/25000000000000 : ℝ)^3623
        have hw : |(-35167089/200000000 : ℝ)|=(35167089/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1383002409/2500000000 : ℝ)|^4647 ≤ (46796319090073/100000000000000 : ℝ)^3623
        have hw : |(1383002409/2500000000 : ℝ)|=(1383002409/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(320420709/625000000 : ℝ)|^4647 ≤ (8489073018893/20000000000000 : ℝ)^3623
        have hw : |(320420709/625000000 : ℝ)|=(320420709/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_s1_1 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5375594797/10000000000 : ℝ)*x 0 + (-985116063/5000000000 : ℝ)*x 1 + (320420689/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5375594797/10000000000 : ℝ)^4647 ≤ (22553016282383/50000000000000 : ℝ)^3623 := by
    have hnat : (5375594797 : ℕ)^4647*50000000000000^3623 ≤ 22553016282383^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375594797 10000000000 22553016282383 50000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (985116063/5000000000 : ℝ)^4647 ≤ (1556075716169/12500000000000 : ℝ)^3623 := by
    have hnat : (985116063 : ℕ)^4647*12500000000000^3623 ≤ 1556075716169^3623*5000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      985116063 5000000000 1556075716169 12500000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (320420689/625000000 : ℝ)^4647 ≤ (42445361696303/100000000000000 : ℝ)^3623 := by
    have hnat : (320420689 : ℕ)^4647*100000000000000^3623 ≤ 42445361696303^3623*625000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      320420689 625000000 42445361696303 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5375594797/10000000000 : ℝ), (-985116063/5000000000 : ℝ), (320420689/625000000 : ℝ)] ![(22553016282383/50000000000000 : ℝ), (1556075716169/12500000000000 : ℝ), (42445361696303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5375594797/10000000000 : ℝ)|^4647 ≤ (22553016282383/50000000000000 : ℝ)^3623
        have hw : |(5375594797/10000000000 : ℝ)|=(5375594797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-985116063/5000000000 : ℝ)|^4647 ≤ (1556075716169/12500000000000 : ℝ)^3623
        have hw : |(-985116063/5000000000 : ℝ)|=(985116063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(320420689/625000000 : ℝ)|^4647 ≤ (42445361696303/100000000000000 : ℝ)^3623
        have hw : |(320420689/625000000 : ℝ)|=(320420689/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_s1_2 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5375594653/10000000000 : ℝ)*x 0 + (5126731231/10000000000 : ℝ)*x 1 + (-394046409/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5375594653/10000000000 : ℝ)^4647 ≤ (45106031014969/100000000000000 : ℝ)^3623 := by
    have hnat : (5375594653 : ℕ)^4647*100000000000000^3623 ≤ 45106031014969^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375594653 10000000000 45106031014969 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5126731231/10000000000 : ℝ)^4647 ≤ (42445363894489/100000000000000 : ℝ)^3623 := by
    have hnat : (5126731231 : ℕ)^4647*100000000000000^3623 ≤ 42445363894489^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5126731231 10000000000 42445363894489 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (394046409/2000000000 : ℝ)^4647 ≤ (2489721014583/20000000000000 : ℝ)^3623 := by
    have hnat : (394046409 : ℕ)^4647*20000000000000^3623 ≤ 2489721014583^3623*2000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      394046409 2000000000 2489721014583 20000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5375594653/10000000000 : ℝ), (5126731231/10000000000 : ℝ), (-394046409/2000000000 : ℝ)] ![(45106031014969/100000000000000 : ℝ), (42445363894489/100000000000000 : ℝ), (2489721014583/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5375594653/10000000000 : ℝ)|^4647 ≤ (45106031014969/100000000000000 : ℝ)^3623
        have hw : |(5375594653/10000000000 : ℝ)|=(5375594653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5126731231/10000000000 : ℝ)|^4647 ≤ (42445363894489/100000000000000 : ℝ)^3623
        have hw : |(5126731231/10000000000 : ℝ)|=(5126731231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-394046409/2000000000 : ℝ)|^4647 ≤ (2489721014583/20000000000000 : ℝ)^3623
        have hw : |(-394046409/2000000000 : ℝ)|=(394046409/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_s1_3 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4226641217/10000000000 : ℝ)*x 0 + (942138007/2500000000 : ℝ)*x 1 + (2364248637/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4226641217/10000000000 : ℝ)^4647 ≤ (33135017658553/100000000000000 : ℝ)^3623 := by
    have hnat : (4226641217 : ℕ)^4647*100000000000000^3623 ≤ 33135017658553^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4226641217 10000000000 33135017658553 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (942138007/2500000000 : ℝ)^4647 ≤ (3575156402543/12500000000000 : ℝ)^3623 := by
    have hnat : (942138007 : ℕ)^4647*12500000000000^3623 ≤ 3575156402543^3623*2500000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      942138007 2500000000 3575156402543 12500000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2364248637/5000000000 : ℝ)^4647 ≤ (2391483194037/6250000000000 : ℝ)^3623 := by
    have hnat : (2364248637 : ℕ)^4647*6250000000000^3623 ≤ 2391483194037^3623*5000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2364248637 5000000000 2391483194037 6250000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4226641217/10000000000 : ℝ), (942138007/2500000000 : ℝ), (2364248637/5000000000 : ℝ)] ![(33135017658553/100000000000000 : ℝ), (3575156402543/12500000000000 : ℝ), (2391483194037/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4226641217/10000000000 : ℝ)|^4647 ≤ (33135017658553/100000000000000 : ℝ)^3623
        have hw : |(4226641217/10000000000 : ℝ)|=(4226641217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(942138007/2500000000 : ℝ)|^4647 ≤ (3575156402543/12500000000000 : ℝ)^3623
        have hw : |(942138007/2500000000 : ℝ)|=(942138007/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2364248637/5000000000 : ℝ)|^4647 ≤ (2391483194037/6250000000000 : ℝ)^3623
        have hw : |(2364248637/5000000000 : ℝ)|=(2364248637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_s1_4 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-351711881/2000000000 : ℝ)*x 0 + (5130883949/10000000000 : ℝ)*x 1 + (2763898107/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (351711881/2000000000 : ℝ)^4647 ≤ (10759924246953/100000000000000 : ℝ)^3623 := by
    have hnat : (351711881 : ℕ)^4647*100000000000000^3623 ≤ 10759924246953^3623*2000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      351711881 2000000000 10759924246953 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5130883949/10000000000 : ℝ)^4647 ≤ (331948966507/781250000000 : ℝ)^3623 := by
    have hnat : (5130883949 : ℕ)^4647*781250000000^3623 ≤ 331948966507^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5130883949 10000000000 331948966507 781250000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2763898107/5000000000 : ℝ)^4647 ≤ (46750608028593/100000000000000 : ℝ)^3623 := by
    have hnat : (2763898107 : ℕ)^4647*100000000000000^3623 ≤ 46750608028593^3623*5000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2763898107 5000000000 46750608028593 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-351711881/2000000000 : ℝ), (5130883949/10000000000 : ℝ), (2763898107/5000000000 : ℝ)] ![(10759924246953/100000000000000 : ℝ), (331948966507/781250000000 : ℝ), (46750608028593/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-351711881/2000000000 : ℝ)|^4647 ≤ (10759924246953/100000000000000 : ℝ)^3623
        have hw : |(-351711881/2000000000 : ℝ)|=(351711881/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5130883949/10000000000 : ℝ)|^4647 ≤ (331948966507/781250000000 : ℝ)^3623
        have hw : |(5130883949/10000000000 : ℝ)|=(5130883949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2763898107/5000000000 : ℝ)|^4647 ≤ (46750608028593/100000000000000 : ℝ)^3623
        have hw : |(2763898107/5000000000 : ℝ)|=(2763898107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_s1_5 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5268115467/10000000000 : ℝ)*x 0 + (-78458347/500000000 : ℝ)*x 1 + (138194919/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5268115467/10000000000 : ℝ)^4647 ≤ (43952572376879/100000000000000 : ℝ)^3623 := by
    have hnat : (5268115467 : ℕ)^4647*100000000000000^3623 ≤ 43952572376879^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5268115467 10000000000 43952572376879 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (78458347/500000000 : ℝ)^4647 ≤ (9296813652353/100000000000000 : ℝ)^3623 := by
    have hnat : (78458347 : ℕ)^4647*100000000000000^3623 ≤ 9296813652353^3623*500000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      78458347 500000000 9296813652353 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (138194919/250000000 : ℝ)^4647 ≤ (5843826743933/12500000000000 : ℝ)^3623 := by
    have hnat : (138194919 : ℕ)^4647*12500000000000^3623 ≤ 5843826743933^3623*250000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138194919 250000000 5843826743933 12500000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5268115467/10000000000 : ℝ), (-78458347/500000000 : ℝ), (138194919/250000000 : ℝ)] ![(43952572376879/100000000000000 : ℝ), (9296813652353/100000000000000 : ℝ), (5843826743933/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5268115467/10000000000 : ℝ)|^4647 ≤ (43952572376879/100000000000000 : ℝ)^3623
        have hw : |(5268115467/10000000000 : ℝ)|=(5268115467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-78458347/500000000 : ℝ)|^4647 ≤ (9296813652353/100000000000000 : ℝ)^3623
        have hw : |(-78458347/500000000 : ℝ)|=(78458347/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(138194919/250000000 : ℝ)|^4647 ≤ (5843826743933/12500000000000 : ℝ)^3623
        have hw : |(138194919/250000000 : ℝ)|=(138194919/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_s1_6 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2634057413/5000000000 : ℝ)*x 0 + (1381949251/2500000000 : ℝ)*x 1 + (-196145937/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2634057413/5000000000 : ℝ)^4647 ≤ (10988141379349/25000000000000 : ℝ)^3623 := by
    have hnat : (2634057413 : ℕ)^4647*25000000000000^3623 ≤ 10988141379349^3623*5000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2634057413 5000000000 10988141379349 25000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1381949251/2500000000 : ℝ)^4647 ≤ (23375308299157/50000000000000 : ℝ)^3623 := by
    have hnat : (1381949251 : ℕ)^4647*50000000000000^3623 ≤ 23375308299157^3623*2500000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1381949251 2500000000 23375308299157 50000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (196145937/1250000000 : ℝ)^4647 ≤ (9296817877523/100000000000000 : ℝ)^3623 := by
    have hnat : (196145937 : ℕ)^4647*100000000000000^3623 ≤ 9296817877523^3623*1250000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      196145937 1250000000 9296817877523 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2634057413/5000000000 : ℝ), (1381949251/2500000000 : ℝ), (-196145937/1250000000 : ℝ)] ![(10988141379349/25000000000000 : ℝ), (23375308299157/50000000000000 : ℝ), (9296817877523/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2634057413/5000000000 : ℝ)|^4647 ≤ (10988141379349/25000000000000 : ℝ)^3623
        have hw : |(2634057413/5000000000 : ℝ)|=(2634057413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1381949251/2500000000 : ℝ)|^4647 ≤ (23375308299157/50000000000000 : ℝ)^3623
        have hw : |(1381949251/2500000000 : ℝ)|=(1381949251/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-196145937/1250000000 : ℝ)|^4647 ≤ (9296817877523/100000000000000 : ℝ)^3623
        have hw : |(-196145937/1250000000 : ℝ)|=(196145937/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_s1_7 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4227125731/10000000000 : ℝ)*x 0 + (4718661833/10000000000 : ℝ)*x 1 + (236158227/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4227125731/10000000000 : ℝ)^4647 ≤ (16569944841881/50000000000000 : ℝ)^3623 := by
    have hnat : (4227125731 : ℕ)^4647*50000000000000^3623 ≤ 16569944841881^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227125731 10000000000 16569944841881 50000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4718661833/10000000000 : ℝ)^4647 ≤ (38161676029639/100000000000000 : ℝ)^3623 := by
    have hnat : (4718661833 : ℕ)^4647*100000000000000^3623 ≤ 38161676029639^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4718661833 10000000000 38161676029639 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (236158227/625000000 : ℝ)^4647 ≤ (28698434277669/100000000000000 : ℝ)^3623 := by
    have hnat : (236158227 : ℕ)^4647*100000000000000^3623 ≤ 28698434277669^3623*625000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      236158227 625000000 28698434277669 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4227125731/10000000000 : ℝ), (4718661833/10000000000 : ℝ), (236158227/625000000 : ℝ)] ![(16569944841881/50000000000000 : ℝ), (38161676029639/100000000000000 : ℝ), (28698434277669/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4227125731/10000000000 : ℝ)|^4647 ≤ (16569944841881/50000000000000 : ℝ)^3623
        have hw : |(4227125731/10000000000 : ℝ)|=(4227125731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4718661833/10000000000 : ℝ)|^4647 ≤ (38161676029639/100000000000000 : ℝ)^3623
        have hw : |(4718661833/10000000000 : ℝ)|=(4718661833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(236158227/625000000 : ℝ)|^4647 ≤ (28698434277669/100000000000000 : ℝ)^3623
        have hw : |(236158227/625000000 : ℝ)|=(236158227/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1575_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168430229/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (24693/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3603/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (73/800 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1771/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (24693/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3603/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (24693/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3603/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (24693/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3603/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (24693/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3603/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (24693/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3603/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (24693/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3603/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3603/100000 : ℝ) ^ (4645/1024 : ℝ) ≤ (28368567092227/100000000000000000000 : ℝ) := by
    have hpowers : (3603/100000 : ℝ)^4645 ≤ (28368567092227/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3603 : ℕ)^4645*100000000000000000000^1024 ≤ 28368567092227^1024*100000^4645 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3603 100000 28368567092227 100000000000000000000 4645 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3603/100000 : ℝ)) (X := (28368567092227/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4645 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (24693/100000 : ℝ) ^ (4645/1024 : ℝ) ≤ (21955551565711369/12500000000000000000 : ℝ) := by
    have hpowers : (24693/100000 : ℝ)^4645 ≤ (21955551565711369/12500000000000000000 : ℝ)^1024 := by
      have hnat : (24693 : ℕ)^4645*12500000000000000000^1024 ≤ 21955551565711369^1024*100000^4645 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24693 100000 21955551565711369 12500000000000000000 4645 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (24693/100000 : ℝ)) (X := (21955551565711369/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4645 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000028368567092227/50000000000000000000 : ℝ) ≤ (2500000312695439/2500000000000000 : ℝ) ^ (4645/1024 : ℝ) := by
    have hpowers : (50000028368567092227/50000000000000000000 : ℝ)^1024 ≤ (2500000312695439/2500000000000000 : ℝ)^4645 := by
      have hnat : (50000028368567092227 : ℕ)^1024*2500000000000000^4645 ≤ 2500000312695439^4645*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000028368567092227 50000000000000000000 2500000312695439 2500000000000000 1024 4645 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000312695439/2500000000000000 : ℝ)) (X := (50000028368567092227/50000000000000000000 : ℝ)) (by norm_num) 4645 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100175672781092783179/100000000000000000000 : ℝ) ≤ (125048376179031/125000000000000 : ℝ) ^ (4645/1024 : ℝ) := by
    have hpowers : (100175672781092783179/100000000000000000000 : ℝ)^1024 ≤ (125048376179031/125000000000000 : ℝ)^4645 := by
      have hnat : (100175672781092783179 : ℕ)^1024*125000000000000^4645 ≤ 125048376179031^4645*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100175672781092783179 100000000000000000000 125048376179031 125000000000000 1024 4645 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125048376179031/125000000000000 : ℝ)) (X := (100175672781092783179/100000000000000000000 : ℝ)) (by norm_num) 4645 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6271955551565711369/6250000000000000000 : ℝ) ≤ (2501934734465801/2500000000000000 : ℝ) ^ (4645/1024 : ℝ) := by
    have hpowers : (6271955551565711369/6250000000000000000 : ℝ)^1024 ≤ (2501934734465801/2500000000000000 : ℝ)^4645 := by
      have hnat : (6271955551565711369 : ℕ)^1024*2500000000000000^4645 ≤ 2501934734465801^4645*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6271955551565711369 6250000000000000000 2501934734465801 2500000000000000 1024 4645 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501934734465801/2500000000000000 : ℝ)) (X := (6271955551565711369/6250000000000000000 : ℝ)) (by norm_num) 4645 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(28368567092227/100000000000000000000 : ℝ) ≤ ((1098292434856420713/1098437500000000000 : ℝ)+2*(967210885181/527250000000000 : ℝ)*(3603/100000 : ℝ))^(4645/1024 : ℝ) := by
    rw [show (1098292434856420713/1098437500000000000 : ℝ)+2*(967210885181/527250000000000 : ℝ)*(3603/100000 : ℝ)=(2500000312695439/2500000000000000 : ℝ) by norm_num, show 1+2*(28368567092227/100000000000000000000 : ℝ)=(50000028368567092227/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(21955551565711369/12500000000000000000 : ℝ)+(28368567092227/100000000000000000000 : ℝ) ≤ ((1098292434856420713/1098437500000000000 : ℝ)+(967210885181/527250000000000 : ℝ)*((24693/100000 : ℝ)+(3603/100000 : ℝ)))^(4645/1024 : ℝ) := by
    rw [show (1098292434856420713/1098437500000000000 : ℝ)+(967210885181/527250000000000 : ℝ)*((24693/100000 : ℝ)+(3603/100000 : ℝ))=(125048376179031/125000000000000 : ℝ) by norm_num, show 1+(21955551565711369/12500000000000000000 : ℝ)+(28368567092227/100000000000000000000 : ℝ)=(100175672781092783179/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(21955551565711369/12500000000000000000 : ℝ) ≤ ((1098292434856420713/1098437500000000000 : ℝ)+2*(967210885181/527250000000000 : ℝ)*(24693/100000 : ℝ))^(4645/1024 : ℝ) := by
    rw [show (1098292434856420713/1098437500000000000 : ℝ)+2*(967210885181/527250000000000 : ℝ)*(24693/100000 : ℝ)=(2501934734465801/2500000000000000 : ℝ) by norm_num, show 1+2*(21955551565711369/12500000000000000000 : ℝ)=(6271955551565711369/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1098292434856420713/1098437500000000000 : ℝ)*(X 1 0+X 2 0)+(967210885181/527250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4645/1024 : ℝ)) (lo := (3603/100000 : ℝ)) (hi := (24693/100000 : ℝ)) (c := (1098292434856420713/1098437500000000000 : ℝ)) (alpha := (967210885181/527250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1098292434856420713/1098437500000000000 : ℝ)*(X 0 1+X 2 1)+(967210885181/527250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4645/1024 : ℝ)) (lo := (3603/100000 : ℝ)) (hi := (24693/100000 : ℝ)) (c := (1098292434856420713/1098437500000000000 : ℝ)) (alpha := (967210885181/527250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1098292434856420713/1098437500000000000 : ℝ)*(X 0 2+X 1 2)+(967210885181/527250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4645/1024 : ℝ)) (lo := (3603/100000 : ℝ)) (hi := (24693/100000 : ℝ)) (c := (1098292434856420713/1098437500000000000 : ℝ)) (alpha := (967210885181/527250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-35167089/200000000 : ℝ)*X 0 0+(1383002409/2500000000 : ℝ)*X 0 1+(320420709/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5375594797/10000000000 : ℝ)*X 1 0+(-985116063/5000000000 : ℝ)*X 1 1+(320420689/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5375594653/10000000000 : ℝ)*X 2 0+(5126731231/10000000000 : ℝ)*X 2 1+(-394046409/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4226641217/10000000000 : ℝ)*X 0 0+(942138007/2500000000 : ℝ)*X 0 1+(2364248637/5000000000 : ℝ)*X 0 2+(4226641217/10000000000 : ℝ)*X 1 0+(942138007/2500000000 : ℝ)*X 1 1+(2364248637/5000000000 : ℝ)*X 1 2+(4226641217/10000000000 : ℝ)*X 2 0+(942138007/2500000000 : ℝ)*X 2 1+(2364248637/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-351711881/2000000000 : ℝ)*X 0 0+(5130883949/10000000000 : ℝ)*X 0 1+(2763898107/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5268115467/10000000000 : ℝ)*X 1 0+(-78458347/500000000 : ℝ)*X 1 1+(138194919/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2634057413/5000000000 : ℝ)*X 2 0+(1381949251/2500000000 : ℝ)*X 2 1+(-196145937/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4227125731/10000000000 : ℝ)*X 0 0+(4718661833/10000000000 : ℝ)*X 0 1+(236158227/625000000 : ℝ)*X 0 2+(4227125731/10000000000 : ℝ)*X 1 0+(4718661833/10000000000 : ℝ)*X 1 1+(236158227/625000000 : ℝ)*X 1 2+(4227125731/10000000000 : ℝ)*X 2 0+(4718661833/10000000000 : ℝ)*X 2 1+(236158227/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (690657315407328207357101/115625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (211299087/12500000000000 : ℝ)*(base19) + (1617878593/100000000000000 : ℝ)*(base23) + (71327079/50000000000000 : ℝ)*(upper3) + (3449103/100000000000000 : ℝ)*(upper4) + (86126323/50000000000000 : ℝ)*(upper5) + (35092097992651/2000000000000 : ℝ)*(major0) + (35092097992651/2000000000000 : ℝ)*(major1) + (35092097992651/2000000000000 : ℝ)*(major2) + (246745468582679/10000000000000 : ℝ)*(sp0) + (30843350118501/1250000000000 : ℝ)*(sp1) + (2467468081994183/100000000000000 : ℝ)*(sp2) + (520866522421099/50000000000000 : ℝ)*(sp3) + (7507022993/50000000000000 : ℝ)*(sp4) + (1371088341/20000000000000 : ℝ)*(sp7) + (1041739900283903/100000000000000 : ℝ)*(f.failure) + (308433712484097/12500000000000 : ℝ)*(f.sum) + (45937342781/22200000000000000000000000 : ℝ)*base66 + (691365675754439/86718750000000000000000000000 : ℝ)*base67 + (469817393991619/346875000000000000000000000000 : ℝ)*base70 + (862214174793253/173437500000000000000000000000 : ℝ)*base71 + (16222659677/111000000000000000000000000 : ℝ)*base73 + (513434773770881/346875000000000000000000000000 : ℝ)*base75 + (1381452315120881/346875000000000000000000000000 : ℝ)*base77 + (1820505092989631/346875000000000000000000000000 : ℝ)*base79 + (433073577451/111000000000000000000000000 : ℝ)*base82 + (52696213/10000000000000000000000 : ℝ)*base90 + (52696213/10000000000000000000000 : ℝ)*base92 + (52696213/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14990343285140034647670177/1484375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1790479991/100000000000000 : ℝ)*(base19) + (808186793/50000000000000 : ℝ)*(base23) + (4021981/5000000000000 : ℝ)*(upper2) + (342222199/100000000000000 : ℝ)*(upper3) + (177488257/100000000000000 : ℝ)*(upper5) + (895781729819217/50000000000000 : ℝ)*(major0) + (895781729819217/50000000000000 : ℝ)*(major1) + (895781729819217/50000000000000 : ℝ)*(major2) + (1486236339/10000000000000 : ℝ)*(sp1) + (13870048409/100000000000000 : ℝ)*(sp2) + (1259721866459477/50000000000000 : ℝ)*(sp4) + (1259713540037787/50000000000000 : ℝ)*(sp5) + (7873213270303/312500000000 : ℝ)*(sp6) + (1063682849732653/100000000000000 : ℝ)*(sp7) + (1063682849732653/100000000000000 : ℝ)*(f.failure) + (1259721866459477/50000000000000 : ℝ)*(f.sum) + (1416941702853/475000000000000000000000000 : ℝ)*base65 + (3208506648642329/742187500000000000000000000000 : ℝ)*base67 + (3627846611112783/1484375000000000000000000000000 : ℝ)*base69 + (493581702295171/742187500000000000000000000000 : ℝ)*base72 + (480901821753/475000000000000000000000000 : ℝ)*base73 + (5264946811425283/1484375000000000000000000000000 : ℝ)*base75 + (10166577077362783/1484375000000000000000000000000 : ℝ)*base77 + (6777299162637217/1484375000000000000000000000000 : ℝ)*base80 + (1522438647197/475000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (66432463/10000000000000000000000 : ℝ)*base90 + (66432463/10000000000000000000000 : ℝ)*base92 + (66432463/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1575_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168430229/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (24693/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3603/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (73/800 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1771/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1575_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1575_s2_0 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1776503569/10000000000 : ℝ)*x 0 + (5440203957/10000000000 : ℝ)*x 1 + (5206704249/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1776503569/10000000000 : ℝ)^4647 ≤ (340654744297/3125000000000 : ℝ)^3623 := by
    have hnat : (1776503569 : ℕ)^4647*3125000000000^3623 ≤ 340654744297^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1776503569 10000000000 340654744297 3125000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5440203957/10000000000 : ℝ)^4647 ≤ (45802565186839/100000000000000 : ℝ)^3623 := by
    have hnat : (5440203957 : ℕ)^4647*100000000000000^3623 ≤ 45802565186839^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5440203957 10000000000 45802565186839 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5206704249/10000000000 : ℝ)^4647 ≤ (43296482984927/100000000000000 : ℝ)^3623 := by
    have hnat : (5206704249 : ℕ)^4647*100000000000000^3623 ≤ 43296482984927^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5206704249 10000000000 43296482984927 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1776503569/10000000000 : ℝ), (5440203957/10000000000 : ℝ), (5206704249/10000000000 : ℝ)] ![(340654744297/3125000000000 : ℝ), (45802565186839/100000000000000 : ℝ), (43296482984927/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1776503569/10000000000 : ℝ)|^4647 ≤ (340654744297/3125000000000 : ℝ)^3623
        have hw : |(-1776503569/10000000000 : ℝ)|=(1776503569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5440203957/10000000000 : ℝ)|^4647 ≤ (45802565186839/100000000000000 : ℝ)^3623
        have hw : |(5440203957/10000000000 : ℝ)|=(5440203957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5206704249/10000000000 : ℝ)|^4647 ≤ (43296482984927/100000000000000 : ℝ)^3623
        have hw : |(5206704249/10000000000 : ℝ)|=(5206704249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_s2_1 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (133796351/250000000 : ℝ)*x 0 + (-1896322089/10000000000 : ℝ)*x 1 + (5206704481/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133796351/250000000 : ℝ)^4647 ≤ (22425341365049/50000000000000 : ℝ)^3623 := by
    have hnat : (133796351 : ℕ)^4647*50000000000000^3623 ≤ 22425341365049^3623*250000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133796351 250000000 22425341365049 50000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1896322089/10000000000 : ℝ)^4647 ≤ (11852831804197/100000000000000 : ℝ)^3623 := by
    have hnat : (1896322089 : ℕ)^4647*100000000000000^3623 ≤ 11852831804197^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1896322089 10000000000 11852831804197 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5206704481/10000000000 : ℝ)^4647 ≤ (10824121364849/25000000000000 : ℝ)^3623 := by
    have hnat : (5206704481 : ℕ)^4647*25000000000000^3623 ≤ 10824121364849^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5206704481 10000000000 10824121364849 25000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133796351/250000000 : ℝ), (-1896322089/10000000000 : ℝ), (5206704481/10000000000 : ℝ)] ![(22425341365049/50000000000000 : ℝ), (11852831804197/100000000000000 : ℝ), (10824121364849/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133796351/250000000 : ℝ)|^4647 ≤ (22425341365049/50000000000000 : ℝ)^3623
        have hw : |(133796351/250000000 : ℝ)|=(133796351/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1896322089/10000000000 : ℝ)|^4647 ≤ (11852831804197/100000000000000 : ℝ)^3623
        have hw : |(-1896322089/10000000000 : ℝ)|=(1896322089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5206704481/10000000000 : ℝ)|^4647 ≤ (10824121364849/25000000000000 : ℝ)^3623
        have hw : |(5206704481/10000000000 : ℝ)|=(5206704481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_s2_2 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351853739/10000000000 : ℝ)*x 0 + (5206704549/10000000000 : ℝ)*x 1 + (-1896322401/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351853739/10000000000 : ℝ)^4647 ≤ (44850679494641/100000000000000 : ℝ)^3623 := by
    have hnat : (5351853739 : ℕ)^4647*100000000000000^3623 ≤ 44850679494641^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351853739 10000000000 44850679494641 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5206704549/10000000000 : ℝ)^4647 ≤ (1353015193271/3125000000000 : ℝ)^3623 := by
    have hnat : (5206704549 : ℕ)^4647*3125000000000^3623 ≤ 1353015193271^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5206704549 10000000000 1353015193271 3125000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1896322401/10000000000 : ℝ)^4647 ≤ (2370566861103/20000000000000 : ℝ)^3623 := by
    have hnat : (1896322401 : ℕ)^4647*20000000000000^3623 ≤ 2370566861103^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1896322401 10000000000 2370566861103 20000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351853739/10000000000 : ℝ), (5206704549/10000000000 : ℝ), (-1896322401/10000000000 : ℝ)] ![(44850679494641/100000000000000 : ℝ), (1353015193271/3125000000000 : ℝ), (2370566861103/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351853739/10000000000 : ℝ)|^4647 ≤ (44850679494641/100000000000000 : ℝ)^3623
        have hw : |(5351853739/10000000000 : ℝ)|=(5351853739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5206704549/10000000000 : ℝ)|^4647 ≤ (1353015193271/3125000000000 : ℝ)^3623
        have hw : |(5206704549/10000000000 : ℝ)|=(5206704549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1896322401/10000000000 : ℝ)|^4647 ≤ (2370566861103/20000000000000 : ℝ)^3623
        have hw : |(-1896322401/10000000000 : ℝ)|=(1896322401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_s2_3 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1059951591/2500000000 : ℝ)*x 0 + (397054227/1000000000 : ℝ)*x 1 + (904722089/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059951591/2500000000 : ℝ)^4647 ≤ (33267455733059/100000000000000 : ℝ)^3623 := by
    have hnat : (1059951591 : ℕ)^4647*100000000000000^3623 ≤ 33267455733059^3623*2500000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059951591 2500000000 33267455733059 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (397054227/1000000000 : ℝ)^4647 ≤ (3058223777941/10000000000000 : ℝ)^3623 := by
    have hnat : (397054227 : ℕ)^4647*10000000000000^3623 ≤ 3058223777941^3623*1000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397054227 1000000000 3058223777941 10000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (904722089/2000000000 : ℝ)^4647 ≤ (1446012258733/4000000000000 : ℝ)^3623 := by
    have hnat : (904722089 : ℕ)^4647*4000000000000^3623 ≤ 1446012258733^3623*2000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      904722089 2000000000 1446012258733 4000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1059951591/2500000000 : ℝ), (397054227/1000000000 : ℝ), (904722089/2000000000 : ℝ)] ![(33267455733059/100000000000000 : ℝ), (3058223777941/10000000000000 : ℝ), (1446012258733/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1059951591/2500000000 : ℝ)|^4647 ≤ (33267455733059/100000000000000 : ℝ)^3623
        have hw : |(1059951591/2500000000 : ℝ)|=(1059951591/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(397054227/1000000000 : ℝ)|^4647 ≤ (3058223777941/10000000000000 : ℝ)^3623
        have hw : |(397054227/1000000000 : ℝ)|=(397054227/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(904722089/2000000000 : ℝ)|^4647 ≤ (1446012258733/4000000000000 : ℝ)^3623
        have hw : |(904722089/2000000000 : ℝ)|=(904722089/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_s2_4 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1776542267/10000000000 : ℝ)*x 0 + (5208091007/10000000000 : ℝ)*x 1 + (271940299/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1776542267/10000000000 : ℝ)^4647 ≤ (10901256391297/100000000000000 : ℝ)^3623 := by
    have hnat : (1776542267 : ℕ)^4647*100000000000000^3623 ≤ 10901256391297^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1776542267 10000000000 10901256391297 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5208091007/10000000000 : ℝ)^4647 ≤ (43311274445953/100000000000000 : ℝ)^3623 := by
    have hnat : (5208091007 : ℕ)^4647*100000000000000^3623 ≤ 43311274445953^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5208091007 10000000000 43311274445953 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (271940299/500000000 : ℝ)^4647 ≤ (45787469140803/100000000000000 : ℝ)^3623 := by
    have hnat : (271940299 : ℕ)^4647*100000000000000^3623 ≤ 45787469140803^3623*500000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271940299 500000000 45787469140803 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1776542267/10000000000 : ℝ), (5208091007/10000000000 : ℝ), (271940299/500000000 : ℝ)] ![(10901256391297/100000000000000 : ℝ), (43311274445953/100000000000000 : ℝ), (45787469140803/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1776542267/10000000000 : ℝ)|^4647 ≤ (10901256391297/100000000000000 : ℝ)^3623
        have hw : |(-1776542267/10000000000 : ℝ)|=(1776542267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5208091007/10000000000 : ℝ)|^4647 ≤ (43311274445953/100000000000000 : ℝ)^3623
        have hw : |(5208091007/10000000000 : ℝ)|=(5208091007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(271940299/500000000 : ℝ)|^4647 ≤ (45787469140803/100000000000000 : ℝ)^3623
        have hw : |(271940299/500000000 : ℝ)|=(271940299/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_s2_5 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1322508603/2500000000 : ℝ)*x 0 + (-1664221449/10000000000 : ℝ)*x 1 + (2719403479/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322508603/2500000000 : ℝ)^4647 ≤ (22093634820707/50000000000000 : ℝ)^3623 := by
    have hnat : (1322508603 : ℕ)^4647*50000000000000^3623 ≤ 22093634820707^3623*2500000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322508603 2500000000 22093634820707 50000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1664221449/10000000000 : ℝ)^4647 ≤ (10025250640283/100000000000000 : ℝ)^3623 := by
    have hnat : (1664221449 : ℕ)^4647*100000000000000^3623 ≤ 10025250640283^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1664221449 10000000000 10025250640283 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2719403479/5000000000 : ℝ)^4647 ≤ (45787479701347/100000000000000 : ℝ)^3623 := by
    have hnat : (2719403479 : ℕ)^4647*100000000000000^3623 ≤ 45787479701347^3623*5000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719403479 5000000000 45787479701347 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322508603/2500000000 : ℝ), (-1664221449/10000000000 : ℝ), (2719403479/5000000000 : ℝ)] ![(22093634820707/50000000000000 : ℝ), (10025250640283/100000000000000 : ℝ), (45787479701347/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322508603/2500000000 : ℝ)|^4647 ≤ (22093634820707/50000000000000 : ℝ)^3623
        have hw : |(1322508603/2500000000 : ℝ)|=(1322508603/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1664221449/10000000000 : ℝ)|^4647 ≤ (10025250640283/100000000000000 : ℝ)^3623
        have hw : |(-1664221449/10000000000 : ℝ)|=(1664221449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2719403479/5000000000 : ℝ)|^4647 ≤ (45787479701347/100000000000000 : ℝ)^3623
        have hw : |(2719403479/5000000000 : ℝ)|=(2719403479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_s2_6 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5290034833/10000000000 : ℝ)*x 0 + (5438808081/10000000000 : ℝ)*x 1 + (-52006853/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5290034833/10000000000 : ℝ)^4647 ≤ (44187274151919/100000000000000 : ℝ)^3623 := by
    have hnat : (5290034833 : ℕ)^4647*100000000000000^3623 ≤ 44187274151919^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5290034833 10000000000 44187274151919 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5438808081/10000000000 : ℝ)^4647 ≤ (1430859119613/3125000000000 : ℝ)^3623 := by
    have hnat : (5438808081 : ℕ)^4647*3125000000000^3623 ≤ 1430859119613^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438808081 10000000000 1430859119613 3125000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (52006853/312500000 : ℝ)^4647 ≤ (2005046800983/20000000000000 : ℝ)^3623 := by
    have hnat : (52006853 : ℕ)^4647*20000000000000^3623 ≤ 2005046800983^3623*312500000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52006853 312500000 2005046800983 20000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5290034833/10000000000 : ℝ), (5438808081/10000000000 : ℝ), (-52006853/312500000 : ℝ)] ![(44187274151919/100000000000000 : ℝ), (1430859119613/3125000000000 : ℝ), (2005046800983/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5290034833/10000000000 : ℝ)|^4647 ≤ (44187274151919/100000000000000 : ℝ)^3623
        have hw : |(5290034833/10000000000 : ℝ)|=(5290034833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5438808081/10000000000 : ℝ)|^4647 ≤ (1430859119613/3125000000000 : ℝ)^3623
        have hw : |(5438808081/10000000000 : ℝ)|=(5438808081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-52006853/312500000 : ℝ)|^4647 ≤ (2005046800983/20000000000000 : ℝ)^3623
        have hw : |(-52006853/312500000 : ℝ)|=(52006853/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_s2_7 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (105997479/250000000 : ℝ)*x 0 + (2260163583/5000000000 : ℝ)*x 1 + (79477071/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105997479/250000000 : ℝ)^4647 ≤ (33268389650537/100000000000000 : ℝ)^3623 := by
    have hnat : (105997479 : ℕ)^4647*100000000000000^3623 ≤ 33268389650537^3623*250000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105997479 250000000 33268389650537 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2260163583/5000000000 : ℝ)^4647 ≤ (36116655748661/100000000000000 : ℝ)^3623 := by
    have hnat : (2260163583 : ℕ)^4647*100000000000000^3623 ≤ 36116655748661^3623*5000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2260163583 5000000000 36116655748661 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (79477071/200000000 : ℝ)^4647 ≤ (3061495458187/10000000000000 : ℝ)^3623 := by
    have hnat : (79477071 : ℕ)^4647*10000000000000^3623 ≤ 3061495458187^3623*200000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79477071 200000000 3061495458187 10000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(105997479/250000000 : ℝ), (2260163583/5000000000 : ℝ), (79477071/200000000 : ℝ)] ![(33268389650537/100000000000000 : ℝ), (36116655748661/100000000000000 : ℝ), (3061495458187/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(105997479/250000000 : ℝ)|^4647 ≤ (33268389650537/100000000000000 : ℝ)^3623
        have hw : |(105997479/250000000 : ℝ)|=(105997479/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2260163583/5000000000 : ℝ)|^4647 ≤ (36116655748661/100000000000000 : ℝ)^3623
        have hw : |(2260163583/5000000000 : ℝ)|=(2260163583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(79477071/200000000 : ℝ)|^4647 ≤ (3061495458187/10000000000000 : ℝ)^3623
        have hw : |(79477071/200000000 : ℝ)|=(79477071/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1575_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168430229/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1771/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (73/800 : ℝ)*pair X i i ≤ pair X i h) :
    (10847/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15799/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1771/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (73/800 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1771/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (73/800 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1771/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (73/800 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1771/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (73/800 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1771/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (73/800 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1771/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (73/800 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (73/800 : ℝ) ^ (4645/1024 : ℝ) ≤ (480195656150689/25000000000000000000 : ℝ) := by
    have hpowers : (73/800 : ℝ)^4645 ≤ (480195656150689/25000000000000000000 : ℝ)^1024 := by
      have hnat : (73 : ℕ)^4645*25000000000000000000^1024 ≤ 480195656150689^1024*800^4645 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        73 800 480195656150689 25000000000000000000 4645 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (73/800 : ℝ)) (X := (480195656150689/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4645 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1771/10000 : ℝ) ^ (4645/1024 : ℝ) ≤ (38888352757701899/100000000000000000000 : ℝ) := by
    have hpowers : (1771/10000 : ℝ)^4645 ≤ (38888352757701899/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1771 : ℕ)^4645*100000000000000000000^1024 ≤ 38888352757701899^1024*10000^4645 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1771 10000 38888352757701899 100000000000000000000 4645 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1771/10000 : ℝ)) (X := (38888352757701899/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4645 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500480195656150689/12500000000000000000 : ℝ) ≤ (5000042343422117/5000000000000000 : ℝ) ^ (4645/1024 : ℝ) := by
    have hpowers : (12500480195656150689/12500000000000000000 : ℝ)^1024 ≤ (5000042343422117/5000000000000000 : ℝ)^4645 := by
      have hnat : (12500480195656150689 : ℕ)^1024*5000000000000000^4645 ≤ 5000042343422117^4645*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500480195656150689 12500000000000000000 5000042343422117 5000000000000000 1024 4645 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000042343422117/5000000000000000 : ℝ)) (X := (12500480195656150689/12500000000000000000 : ℝ)) (by norm_num) 4645 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20008161827076460931/20000000000000000000 : ℝ) ≤ (5000449751444687/5000000000000000 : ℝ) ^ (4645/1024 : ℝ) := by
    have hpowers : (20008161827076460931/20000000000000000000 : ℝ)^1024 ≤ (5000449751444687/5000000000000000 : ℝ)^4645 := by
      have hnat : (20008161827076460931 : ℕ)^1024*5000000000000000^4645 ≤ 5000449751444687^4645*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20008161827076460931 20000000000000000000 5000449751444687 5000000000000000 1024 4645 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000449751444687/5000000000000000 : ℝ)) (X := (20008161827076460931/20000000000000000000 : ℝ)) (by norm_num) 4645 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50038888352757701899/50000000000000000000 : ℝ) ≤ (5000857159467257/5000000000000000 : ℝ) ^ (4645/1024 : ℝ) := by
    have hpowers : (50038888352757701899/50000000000000000000 : ℝ)^1024 ≤ (5000857159467257/5000000000000000 : ℝ)^4645 := by
      have hnat : (50038888352757701899 : ℕ)^1024*5000000000000000^4645 ≤ 5000857159467257^4645*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50038888352757701899 50000000000000000000 5000857159467257 5000000000000000 1024 4645 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000857159467257/5000000000000000 : ℝ)) (X := (50038888352757701899/50000000000000000000 : ℝ)) (by norm_num) 4645 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(480195656150689/25000000000000000000 : ℝ) ≤ ((8583585664373394389/8585000000000000000 : ℝ)+2*(40740802257/42925000000000 : ℝ)*(73/800 : ℝ))^(4645/1024 : ℝ) := by
    rw [show (8583585664373394389/8585000000000000000 : ℝ)+2*(40740802257/42925000000000 : ℝ)*(73/800 : ℝ)=(5000042343422117/5000000000000000 : ℝ) by norm_num, show 1+2*(480195656150689/25000000000000000000 : ℝ)=(12500480195656150689/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(38888352757701899/100000000000000000000 : ℝ)+(480195656150689/25000000000000000000 : ℝ) ≤ ((8583585664373394389/8585000000000000000 : ℝ)+(40740802257/42925000000000 : ℝ)*((1771/10000 : ℝ)+(73/800 : ℝ)))^(4645/1024 : ℝ) := by
    rw [show (8583585664373394389/8585000000000000000 : ℝ)+(40740802257/42925000000000 : ℝ)*((1771/10000 : ℝ)+(73/800 : ℝ))=(5000449751444687/5000000000000000 : ℝ) by norm_num, show 1+(38888352757701899/100000000000000000000 : ℝ)+(480195656150689/25000000000000000000 : ℝ)=(20008161827076460931/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(38888352757701899/100000000000000000000 : ℝ) ≤ ((8583585664373394389/8585000000000000000 : ℝ)+2*(40740802257/42925000000000 : ℝ)*(1771/10000 : ℝ))^(4645/1024 : ℝ) := by
    rw [show (8583585664373394389/8585000000000000000 : ℝ)+2*(40740802257/42925000000000 : ℝ)*(1771/10000 : ℝ)=(5000857159467257/5000000000000000 : ℝ) by norm_num, show 1+2*(38888352757701899/100000000000000000000 : ℝ)=(50038888352757701899/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8583585664373394389/8585000000000000000 : ℝ)*(X 1 0+X 2 0)+(40740802257/42925000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4645/1024 : ℝ)) (lo := (73/800 : ℝ)) (hi := (1771/10000 : ℝ)) (c := (8583585664373394389/8585000000000000000 : ℝ)) (alpha := (40740802257/42925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8583585664373394389/8585000000000000000 : ℝ)*(X 0 1+X 2 1)+(40740802257/42925000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4645/1024 : ℝ)) (lo := (73/800 : ℝ)) (hi := (1771/10000 : ℝ)) (c := (8583585664373394389/8585000000000000000 : ℝ)) (alpha := (40740802257/42925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8583585664373394389/8585000000000000000 : ℝ)*(X 0 2+X 1 2)+(40740802257/42925000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4645/1024 : ℝ)) (lo := (73/800 : ℝ)) (hi := (1771/10000 : ℝ)) (c := (8583585664373394389/8585000000000000000 : ℝ)) (alpha := (40740802257/42925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1776503569/10000000000 : ℝ)*X 0 0+(5440203957/10000000000 : ℝ)*X 0 1+(5206704249/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((133796351/250000000 : ℝ)*X 1 0+(-1896322089/10000000000 : ℝ)*X 1 1+(5206704481/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351853739/10000000000 : ℝ)*X 2 0+(5206704549/10000000000 : ℝ)*X 2 1+(-1896322401/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1059951591/2500000000 : ℝ)*X 0 0+(397054227/1000000000 : ℝ)*X 0 1+(904722089/2000000000 : ℝ)*X 0 2+(1059951591/2500000000 : ℝ)*X 1 0+(397054227/1000000000 : ℝ)*X 1 1+(904722089/2000000000 : ℝ)*X 1 2+(1059951591/2500000000 : ℝ)*X 2 0+(397054227/1000000000 : ℝ)*X 2 1+(904722089/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1776542267/10000000000 : ℝ)*X 0 0+(5208091007/10000000000 : ℝ)*X 0 1+(271940299/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1322508603/2500000000 : ℝ)*X 1 0+(-1664221449/10000000000 : ℝ)*X 1 1+(2719403479/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5290034833/10000000000 : ℝ)*X 2 0+(5438808081/10000000000 : ℝ)*X 2 1+(-52006853/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((105997479/250000000 : ℝ)*X 0 0+(2260163583/5000000000 : ℝ)*X 0 1+(79477071/200000000 : ℝ)*X 0 2+(105997479/250000000 : ℝ)*X 1 0+(2260163583/5000000000 : ℝ)*X 1 1+(79477071/200000000 : ℝ)*X 1 2+(105997479/250000000 : ℝ)*X 2 0+(2260163583/5000000000 : ℝ)*X 2 1+(79477071/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (624891470996957757901507491/53656250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (465453221/20000000000000 : ℝ)*(base19) + (1987655849/100000000000000 : ℝ)*(base23) + (660551/1250000000000 : ℝ)*(lower2) + (436040229/100000000000000 : ℝ)*(upper3) + (38831547/100000000000000 : ℝ)*(upper5) + (761358306477723/25000000000000 : ℝ)*(major0) + (761358306477723/25000000000000 : ℝ)*(major1) + (761358306477723/25000000000000 : ℝ)*(major2) + (2141352522362523/50000000000000 : ℝ)*(sp0) + (4282736273724143/100000000000000 : ℝ)*(sp1) + (1338355191667/31250000000 : ℝ)*(sp2) + (1808109502612737/100000000000000 : ℝ)*(sp3) + (16778132601/50000000000000 : ℝ)*(sp4) + (8980006047/50000000000000 : ℝ)*(sp7) + (1808127462624831/100000000000000 : ℝ)*(f.failure) + (535342325123781/12500000000000 : ℝ)*(f.sum) + (463753211593/268281250000000000000000000 : ℝ)*base65 + (235901664654853753/214625000000000000000000000000000 : ℝ)*base68 + (122883584171478753/214625000000000000000000000000000 : ℝ)*base70 + (9950629399396247/214625000000000000000000000000000 : ℝ)*base71 + (13220742834781/8585000000000000000000000000 : ℝ)*base73 + (4150870369868103753/214625000000000000000000000000000 : ℝ)*base76 + (1135553192095603753/214625000000000000000000000000000 : ℝ)*base78 + (2439830022353353753/214625000000000000000000000000000 : ℝ)*base80 + (44023436112951/8585000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (26416299/10000000000000000000000 : ℝ)*base89 + (26416299/10000000000000000000000 : ℝ)*base91 + (26416299/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (845388109768743911148556431/53656250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (171395597/20000000000000 : ℝ)*(base23) + (146833047/100000000000000 : ℝ)*(lower2) + (243330181/100000000000000 : ℝ)*(upper3) + (68973693/50000000000000 : ℝ)*(lower4) + (65340457/100000000000000 : ℝ)*(upper5) + (385266934028293/12500000000000 : ℝ)*(major0) + (385266934028293/12500000000000 : ℝ)*(major1) + (385266934028293/12500000000000 : ℝ)*(major2) + (7779730053/100000000000000 : ℝ)*(sp1) + (1657299297/3125000000000 : ℝ)*(sp2) + (2167176092576851/50000000000000 : ℝ)*(sp4) + (86686888108473/2000000000000 : ℝ)*(sp5) + (2167149147299107/50000000000000 : ℝ)*(sp6) + (228739779263907/12500000000000 : ℝ)*(sp7) + (228739779263907/12500000000000 : ℝ)*(f.failure) + (2167176092576851/50000000000000 : ℝ)*(f.sum) + (74126468576039/4292500000000000000000000000 : ℝ)*base66 + (145588566860522977/107312500000000000000000000000000 : ℝ)*base67 + (1187951542676147977/107312500000000000000000000000000 : ℝ)*base69 + (1180623785951352023/107312500000000000000000000000000 : ℝ)*base72 + (27838425691833/8585000000000000000000000000 : ℝ)*base74 + (617740761202664523/107312500000000000000000000000000 : ℝ)*base76 + (422157042774227023/107312500000000000000000000000000 : ℝ)*base78 + (978324769025227023/107312500000000000000000000000000 : ℝ)*base80 + (290905679893/536562500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (7444703/1250000000000000000000 : ℝ)*base89 + (7444703/1250000000000000000000 : ℝ)*base91 + (7444703/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1575_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168430229/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1771/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (73/800 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10847/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15799/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1575_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1575_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168430229/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10847/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15799/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1575_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1575_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1575_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168430229/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10847/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15799/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1575_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
