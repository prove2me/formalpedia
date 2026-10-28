-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1155_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:37:11.012478+00:00
-- url     : https://prove2.me/submissions/a2f2c420-e28a-4851-ac6b-1f3830458536

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
theorem support_rectangle_w1155_s0_0 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-117981447/625000000 : ℝ)*x 0 + (6051330287/10000000000 : ℝ)*x 1 + (191284573/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (117981447/625000000 : ℝ)^2087 ≤ (10978795312817/100000000000000 : ℝ)^1575 := by
    have hnat : (117981447 : ℕ)^2087*100000000000000^1575 ≤ 10978795312817^1575*625000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117981447 625000000 10978795312817 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6051330287/10000000000 : ℝ)^2087 ≤ (51396680795697/100000000000000 : ℝ)^1575 := by
    have hnat : (6051330287 : ℕ)^2087*100000000000000^1575 ≤ 51396680795697^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6051330287 10000000000 51396680795697 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (191284573/400000000 : ℝ)^2087 ≤ (4703065483489/12500000000000 : ℝ)^1575 := by
    have hnat : (191284573 : ℕ)^2087*12500000000000^1575 ≤ 4703065483489^1575*400000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      191284573 400000000 4703065483489 12500000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-117981447/625000000 : ℝ), (6051330287/10000000000 : ℝ), (191284573/400000000 : ℝ)] ![(10978795312817/100000000000000 : ℝ), (51396680795697/100000000000000 : ℝ), (4703065483489/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-117981447/625000000 : ℝ)|^2087 ≤ (10978795312817/100000000000000 : ℝ)^1575
        have hw : |(-117981447/625000000 : ℝ)|=(117981447/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6051330287/10000000000 : ℝ)|^2087 ≤ (51396680795697/100000000000000 : ℝ)^1575
        have hw : |(6051330287/10000000000 : ℝ)|=(6051330287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(191284573/400000000 : ℝ)|^2087 ≤ (4703065483489/12500000000000 : ℝ)^1575
        have hw : |(191284573/400000000 : ℝ)|=(191284573/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s0_1 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (172376911/312500000 : ℝ)*x 0 + (-1307857691/5000000000 : ℝ)*x 1 + (149441071/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (172376911/312500000 : ℝ)^2087 ≤ (22730449252839/50000000000000 : ℝ)^1575 := by
    have hnat : (172376911 : ℕ)^2087*50000000000000^1575 ≤ 22730449252839^1575*312500000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172376911 312500000 22730449252839 50000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1307857691/5000000000 : ℝ)^2087 ≤ (8457289083479/50000000000000 : ℝ)^1575 := by
    have hnat : (1307857691 : ℕ)^2087*50000000000000^1575 ≤ 8457289083479^1575*5000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307857691 5000000000 8457289083479 50000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (149441071/312500000 : ℝ)^2087 ≤ (7524904663073/20000000000000 : ℝ)^1575 := by
    have hnat : (149441071 : ℕ)^2087*20000000000000^1575 ≤ 7524904663073^1575*312500000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      149441071 312500000 7524904663073 20000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(172376911/312500000 : ℝ), (-1307857691/5000000000 : ℝ), (149441071/312500000 : ℝ)] ![(22730449252839/50000000000000 : ℝ), (8457289083479/50000000000000 : ℝ), (7524904663073/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(172376911/312500000 : ℝ)|^2087 ≤ (22730449252839/50000000000000 : ℝ)^1575
        have hw : |(172376911/312500000 : ℝ)|=(172376911/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1307857691/5000000000 : ℝ)|^2087 ≤ (8457289083479/50000000000000 : ℝ)^1575
        have hw : |(-1307857691/5000000000 : ℝ)|=(1307857691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(149441071/312500000 : ℝ)|^2087 ≤ (7524904663073/20000000000000 : ℝ)^1575
        have hw : |(149441071/312500000 : ℝ)|=(149441071/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s0_2 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1379015303/2500000000 : ℝ)*x 0 + (956422821/2000000000 : ℝ)*x 1 + (-2615715507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1379015303/2500000000 : ℝ)^2087 ≤ (1136522479023/2500000000000 : ℝ)^1575 := by
    have hnat : (1379015303 : ℕ)^2087*2500000000000^1575 ≤ 1136522479023^1575*2500000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1379015303 2500000000 1136522479023 2500000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (956422821/2000000000 : ℝ)^2087 ≤ (37624521574323/100000000000000 : ℝ)^1575 := by
    have hnat : (956422821 : ℕ)^2087*100000000000000^1575 ≤ 37624521574323^1575*2000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      956422821 2000000000 37624521574323 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2615715507/10000000000 : ℝ)^2087 ≤ (422864480951/2500000000000 : ℝ)^1575 := by
    have hnat : (2615715507 : ℕ)^2087*2500000000000^1575 ≤ 422864480951^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615715507 10000000000 422864480951 2500000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1379015303/2500000000 : ℝ), (956422821/2000000000 : ℝ), (-2615715507/10000000000 : ℝ)] ![(1136522479023/2500000000000 : ℝ), (37624521574323/100000000000000 : ℝ), (422864480951/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1379015303/2500000000 : ℝ)|^2087 ≤ (1136522479023/2500000000000 : ℝ)^1575
        have hw : |(1379015303/2500000000 : ℝ)|=(1379015303/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(956422821/2000000000 : ℝ)|^2087 ≤ (37624521574323/100000000000000 : ℝ)^1575
        have hw : |(956422821/2000000000 : ℝ)|=(956422821/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2615715507/10000000000 : ℝ)|^2087 ≤ (422864480951/2500000000000 : ℝ)^1575
        have hw : |(-2615715507/10000000000 : ℝ)|=(2615715507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s0_3 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4199941399/10000000000 : ℝ)*x 0 + (312048379/1000000000 : ℝ)*x 1 + (706499621/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4199941399/10000000000 : ℝ)^2087 ≤ (15839351034637/50000000000000 : ℝ)^1575 := by
    have hnat : (4199941399 : ℕ)^2087*50000000000000^1575 ≤ 15839351034637^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4199941399 10000000000 15839351034637 50000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (312048379/1000000000 : ℝ)^2087 ≤ (10684985118779/50000000000000 : ℝ)^1575 := by
    have hnat : (312048379 : ℕ)^2087*50000000000000^1575 ≤ 10684985118779^1575*1000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      312048379 1000000000 10684985118779 50000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (706499621/1250000000 : ℝ)^2087 ≤ (46951327689221/100000000000000 : ℝ)^1575 := by
    have hnat : (706499621 : ℕ)^2087*100000000000000^1575 ≤ 46951327689221^1575*1250000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      706499621 1250000000 46951327689221 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4199941399/10000000000 : ℝ), (312048379/1000000000 : ℝ), (706499621/1250000000 : ℝ)] ![(15839351034637/50000000000000 : ℝ), (10684985118779/50000000000000 : ℝ), (46951327689221/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4199941399/10000000000 : ℝ)|^2087 ≤ (15839351034637/50000000000000 : ℝ)^1575
        have hw : |(4199941399/10000000000 : ℝ)|=(4199941399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(312048379/1000000000 : ℝ)|^2087 ≤ (10684985118779/50000000000000 : ℝ)^1575
        have hw : |(312048379/1000000000 : ℝ)|=(312048379/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(706499621/1250000000 : ℝ)|^2087 ≤ (46951327689221/100000000000000 : ℝ)^1575
        have hw : |(706499621/1250000000 : ℝ)|=(706499621/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s0_4 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-47320263/250000000 : ℝ)*x 0 + (4814849813/10000000000 : ℝ)*x 1 + (376090183/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (47320263/250000000 : ℝ)^2087 ≤ (5509086529699/50000000000000 : ℝ)^1575 := by
    have hnat : (47320263 : ℕ)^2087*50000000000000^1575 ≤ 5509086529699^1575*250000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47320263 250000000 5509086529699 50000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4814849813/10000000000 : ℝ)^2087 ≤ (37966183741787/100000000000000 : ℝ)^1575 := by
    have hnat : (4814849813 : ℕ)^2087*100000000000000^1575 ≤ 37966183741787^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4814849813 10000000000 37966183741787 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (376090183/625000000 : ℝ)^2087 ≤ (51015643183691/100000000000000 : ℝ)^1575 := by
    have hnat : (376090183 : ℕ)^2087*100000000000000^1575 ≤ 51015643183691^1575*625000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      376090183 625000000 51015643183691 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-47320263/250000000 : ℝ), (4814849813/10000000000 : ℝ), (376090183/625000000 : ℝ)] ![(5509086529699/50000000000000 : ℝ), (37966183741787/100000000000000 : ℝ), (51015643183691/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-47320263/250000000 : ℝ)|^2087 ≤ (5509086529699/50000000000000 : ℝ)^1575
        have hw : |(-47320263/250000000 : ℝ)|=(47320263/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4814849813/10000000000 : ℝ)|^2087 ≤ (37966183741787/100000000000000 : ℝ)^1575
        have hw : |(4814849813/10000000000 : ℝ)|=(4814849813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(376090183/625000000 : ℝ)|^2087 ≤ (51015643183691/100000000000000 : ℝ)^1575
        have hw : |(376090183/625000000 : ℝ)|=(376090183/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s0_5 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5171123577/10000000000 : ℝ)*x 0 + (-86274169/625000000 : ℝ)*x 1 + (6017442747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5171123577/10000000000 : ℝ)^2087 ≤ (41732776833501/100000000000000 : ℝ)^1575 := by
    have hnat : (5171123577 : ℕ)^2087*100000000000000^1575 ≤ 41732776833501^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5171123577 10000000000 41732776833501 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (86274169/625000000 : ℝ)^2087 ≤ (7251582011987/100000000000000 : ℝ)^1575 := by
    have hnat : (86274169 : ℕ)^2087*100000000000000^1575 ≤ 7251582011987^1575*625000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86274169 625000000 7251582011987 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6017442747/10000000000 : ℝ)^2087 ≤ (51015641150343/100000000000000 : ℝ)^1575 := by
    have hnat : (6017442747 : ℕ)^2087*100000000000000^1575 ≤ 51015641150343^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6017442747 10000000000 51015641150343 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5171123577/10000000000 : ℝ), (-86274169/625000000 : ℝ), (6017442747/10000000000 : ℝ)] ![(41732776833501/100000000000000 : ℝ), (7251582011987/100000000000000 : ℝ), (51015641150343/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5171123577/10000000000 : ℝ)|^2087 ≤ (41732776833501/100000000000000 : ℝ)^1575
        have hw : |(5171123577/10000000000 : ℝ)|=(5171123577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-86274169/625000000 : ℝ)|^2087 ≤ (7251582011987/100000000000000 : ℝ)^1575
        have hw : |(-86274169/625000000 : ℝ)|=(86274169/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6017442747/10000000000 : ℝ)|^2087 ≤ (51015641150343/100000000000000 : ℝ)^1575
        have hw : |(6017442747/10000000000 : ℝ)|=(6017442747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s0_6 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5171123559/10000000000 : ℝ)*x 0 + (3008721403/5000000000 : ℝ)*x 1 + (-276077327/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5171123559/10000000000 : ℝ)^2087 ≤ (41732776641011/100000000000000 : ℝ)^1575 := by
    have hnat : (5171123559 : ℕ)^2087*100000000000000^1575 ≤ 41732776641011^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5171123559 10000000000 41732776641011 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3008721403/5000000000 : ℝ)^2087 ≤ (51015641813147/100000000000000 : ℝ)^1575 := by
    have hnat : (3008721403 : ℕ)^2087*100000000000000^1575 ≤ 51015641813147^1575*5000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3008721403 5000000000 51015641813147 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (276077327/2000000000 : ℝ)^2087 ≤ (1812895382919/25000000000000 : ℝ)^1575 := by
    have hnat : (276077327 : ℕ)^2087*25000000000000^1575 ≤ 1812895382919^1575*2000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276077327 2000000000 1812895382919 25000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5171123559/10000000000 : ℝ), (3008721403/5000000000 : ℝ), (-276077327/2000000000 : ℝ)] ![(41732776641011/100000000000000 : ℝ), (51015641813147/100000000000000 : ℝ), (1812895382919/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5171123559/10000000000 : ℝ)|^2087 ≤ (41732776641011/100000000000000 : ℝ)^1575
        have hw : |(5171123559/10000000000 : ℝ)|=(5171123559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3008721403/5000000000 : ℝ)|^2087 ≤ (51015641813147/100000000000000 : ℝ)^1575
        have hw : |(3008721403/5000000000 : ℝ)|=(3008721403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-276077327/2000000000 : ℝ)|^2087 ≤ (1812895382919/25000000000000 : ℝ)^1575
        have hw : |(-276077327/2000000000 : ℝ)|=(276077327/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s0_7 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (842025729/2000000000 : ℝ)*x 0 + (5586703939/10000000000 : ℝ)*x 1 + (637614863/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (842025729/2000000000 : ℝ)^2087 ≤ (31780559783787/100000000000000 : ℝ)^1575 := by
    have hnat : (842025729 : ℕ)^2087*100000000000000^1575 ≤ 31780559783787^1575*2000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      842025729 2000000000 31780559783787 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5586703939/10000000000 : ℝ)^2087 ≤ (46233969115233/100000000000000 : ℝ)^1575 := by
    have hnat : (5586703939 : ℕ)^2087*100000000000000^1575 ≤ 46233969115233^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5586703939 10000000000 46233969115233 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (637614863/2000000000 : ℝ)^2087 ≤ (5496367770881/25000000000000 : ℝ)^1575 := by
    have hnat : (637614863 : ℕ)^2087*25000000000000^1575 ≤ 5496367770881^1575*2000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      637614863 2000000000 5496367770881 25000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(842025729/2000000000 : ℝ), (5586703939/10000000000 : ℝ), (637614863/2000000000 : ℝ)] ![(31780559783787/100000000000000 : ℝ), (46233969115233/100000000000000 : ℝ), (5496367770881/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(842025729/2000000000 : ℝ)|^2087 ≤ (31780559783787/100000000000000 : ℝ)^1575
        have hw : |(842025729/2000000000 : ℝ)|=(842025729/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5586703939/10000000000 : ℝ)|^2087 ≤ (46233969115233/100000000000000 : ℝ)^1575
        have hw : |(5586703939/10000000000 : ℝ)|=(5586703939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(637614863/2000000000 : ℝ)|^2087 ≤ (5496367770881/25000000000000 : ℝ)^1575
        have hw : |(637614863/2000000000 : ℝ)|=(637614863/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1155_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149727417/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (467/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5553/20000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (8347/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8347 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8347*1^2048 ≤ 0^2048*1^8347 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8347 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8347 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8347/2048 : ℝ) ≤ (477696908878047579/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8347 ≤ (477696908878047579/20000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8347*20000000000000000000^2048 ≤ 477696908878047579^2048*5^8347 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 477696908878047579 20000000000000000000 8347 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (477696908878047579/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8347 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8347/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8347 := by
      have hnat : (1 : ℕ)^2048*1^8347 ≤ 1^8347*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8347 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8347 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20477696908878047579/20000000000000000000 : ℝ) ≤ (10058082397701843/10000000000000000 : ℝ) ^ (8347/2048 : ℝ) := by
    have hpowers : (20477696908878047579/20000000000000000000 : ℝ)^2048 ≤ (10058082397701843/10000000000000000 : ℝ)^8347 := by
      have hnat : (20477696908878047579 : ℕ)^2048*10000000000000000^8347 ≤ 10058082397701843^8347*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20477696908878047579 20000000000000000000 10058082397701843 10000000000000000 2048 8347 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10058082397701843/10000000000000000 : ℝ)) (X := (20477696908878047579/20000000000000000000 : ℝ)) (by norm_num) 8347 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10477696908878047579/10000000000000000000 : ℝ) ≤ (5058082397701843/5000000000000000 : ℝ) ^ (8347/2048 : ℝ) := by
    have hpowers : (10477696908878047579/10000000000000000000 : ℝ)^2048 ≤ (5058082397701843/5000000000000000 : ℝ)^8347 := by
      have hnat : (10477696908878047579 : ℕ)^2048*5000000000000000^8347 ≤ 5058082397701843^8347*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10477696908878047579 10000000000000000000 5058082397701843 5000000000000000 2048 8347 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5058082397701843/5000000000000000 : ℝ)) (X := (10477696908878047579/10000000000000000000 : ℝ)) (by norm_num) 8347 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(58082397701843/4000000000000000 : ℝ)*(0 : ℝ))^(8347/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(58082397701843/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(477696908878047579/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(58082397701843/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8347/2048 : ℝ) := by
    rw [show (1 : ℝ)+(58082397701843/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10058082397701843/10000000000000000 : ℝ) by norm_num, show 1+(477696908878047579/20000000000000000000 : ℝ)+(0 : ℝ)=(20477696908878047579/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(477696908878047579/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(58082397701843/4000000000000000 : ℝ)*(2/5 : ℝ))^(8347/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(58082397701843/4000000000000000 : ℝ)*(2/5 : ℝ)=(5058082397701843/5000000000000000 : ℝ) by norm_num, show 1+2*(477696908878047579/20000000000000000000 : ℝ)=(10477696908878047579/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(58082397701843/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8347/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (58082397701843/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(58082397701843/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8347/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (58082397701843/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(58082397701843/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8347/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (58082397701843/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-117981447/625000000 : ℝ)*X 0 0+(6051330287/10000000000 : ℝ)*X 0 1+(191284573/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((172376911/312500000 : ℝ)*X 1 0+(-1307857691/5000000000 : ℝ)*X 1 1+(149441071/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1379015303/2500000000 : ℝ)*X 2 0+(956422821/2000000000 : ℝ)*X 2 1+(-2615715507/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4199941399/10000000000 : ℝ)*X 0 0+(312048379/1000000000 : ℝ)*X 0 1+(706499621/1250000000 : ℝ)*X 0 2+(4199941399/10000000000 : ℝ)*X 1 0+(312048379/1000000000 : ℝ)*X 1 1+(706499621/1250000000 : ℝ)*X 1 2+(4199941399/10000000000 : ℝ)*X 2 0+(312048379/1000000000 : ℝ)*X 2 1+(706499621/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-47320263/250000000 : ℝ)*X 0 0+(4814849813/10000000000 : ℝ)*X 0 1+(376090183/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5171123577/10000000000 : ℝ)*X 1 0+(-86274169/625000000 : ℝ)*X 1 1+(6017442747/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5171123559/10000000000 : ℝ)*X 2 0+(3008721403/5000000000 : ℝ)*X 2 1+(-276077327/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((842025729/2000000000 : ℝ)*X 0 0+(5586703939/10000000000 : ℝ)*X 0 1+(637614863/2000000000 : ℝ)*X 0 2+(842025729/2000000000 : ℝ)*X 1 0+(5586703939/10000000000 : ℝ)*X 1 1+(637614863/2000000000 : ℝ)*X 1 2+(842025729/2000000000 : ℝ)*X 2 0+(5586703939/10000000000 : ℝ)*X 2 1+(637614863/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (194462464330386067332483/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6219537/20000000000000 : ℝ)*(base1) + (185383077/20000000000000 : ℝ)*(base19) + (875830247/100000000000000 : ℝ)*(base23) + (59655297/100000000000000 : ℝ)*(base24) + (113002933/50000000000000 : ℝ)*(upper3) + (147864548663609/25000000000000 : ℝ)*(major0) + (147864548663609/25000000000000 : ℝ)*(major1) + (147864548663609/25000000000000 : ℝ)*(major2) + (196972762982569/25000000000000 : ℝ)*(sp0) + (393946012697143/50000000000000 : ℝ)*(sp1) + (787892016824127/100000000000000 : ℝ)*(sp2) + (395021609593159/100000000000000 : ℝ)*(sp3) + (48286927/2500000000000 : ℝ)*(sp4) + (166666671/10000000000000 : ℝ)*(sp7) + (197511653678777/50000000000000 : ℝ)*(f.failure) + (787892952309671/100000000000000 : ℝ)*(f.sum) + (125075805618613/50000000000000000000000000000 : ℝ)*base66 + (477623368868613/100000000000000000000000000000 : ℝ)*base68 + (95919536131387/100000000000000000000000000000 : ℝ)*base69 + (739938999968613/100000000000000000000000000000 : ℝ)*base72 + (64504316068613/50000000000000000000000000000 : ℝ)*base74 + (314776049068613/100000000000000000000000000000 : ℝ)*base76 + (728247445168613/100000000000000000000000000000 : ℝ)*base78 + (338438977168613/100000000000000000000000000000 : ℝ)*base80 + (240195577681387/50000000000000000000000000000 : ℝ)*base81 + (27929009/5000000000000000000000 : ℝ)*base89 + (27929009/5000000000000000000000 : ℝ)*base91 + (27929009/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (142276842997509109683627/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21381189/50000000000000 : ℝ)*(base1) + (706290843/100000000000000 : ℝ)*(base19) + (703034429/100000000000000 : ℝ)*(base23) + (2804343/4000000000000 : ℝ)*(upper3) + (87171727/100000000000000 : ℝ)*(upper5) + (624220655964237/100000000000000 : ℝ)*(major0) + (624220655964237/100000000000000 : ℝ)*(major1) + (624220655964237/100000000000000 : ℝ)*(major2) + (344833323/25000000000000 : ℝ)*(sp1) + (343476713/25000000000000 : ℝ)*(sp2) + (831536548283529/100000000000000 : ℝ)*(sp4) + (103941802487127/12500000000000 : ℝ)*(sp5) + (83153442857987/10000000000000 : ℝ)*(sp6) + (208452334396857/50000000000000 : ℝ)*(sp7) + (104226177889023/25000000000000 : ℝ)*(f.failure) + (831536505521151/100000000000000 : ℝ)*(f.sum) + (125602493011209/200000000000000000000000000000 : ℝ)*base66 + (1145532187788791/400000000000000000000000000000 : ℝ)*base67 + (1826364468188791/400000000000000000000000000000 : ℝ)*base69 + (961737538588791/400000000000000000000000000000 : ℝ)*base71 + (197586669388791/200000000000000000000000000000 : ℝ)*base73 + (1500703082588791/400000000000000000000000000000 : ℝ)*base75 + (1410792203388791/400000000000000000000000000000 : ℝ)*base77 + (1002879146588791/400000000000000000000000000000 : ℝ)*base79 + (307307097788791/200000000000000000000000000000 : ℝ)*base81 + (1443591/2500000000000000000000 : ℝ)*base89 + (1443591/2500000000000000000000 : ℝ)*base91 + (1443591/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1155_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149727417/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (467/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5553/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1155_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1155_s1_0 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1045715087/5000000000 : ℝ)*x 0 + (1424509763/2500000000 : ℝ)*x 1 + (625623063/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1045715087/5000000000 : ℝ)^2087 ≤ (12575739468331/100000000000000 : ℝ)^1575 := by
    have hnat : (1045715087 : ℕ)^2087*100000000000000^1575 ≤ 12575739468331^1575*5000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045715087 5000000000 12575739468331 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1424509763/2500000000 : ℝ)^2087 ≤ (11864701191749/25000000000000 : ℝ)^1575 := by
    have hnat : (1424509763 : ℕ)^2087*25000000000000^1575 ≤ 11864701191749^1575*2500000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1424509763 2500000000 11864701191749 25000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (625623063/1250000000 : ℝ)^2087 ≤ (39965455750039/100000000000000 : ℝ)^1575 := by
    have hnat : (625623063 : ℕ)^2087*100000000000000^1575 ≤ 39965455750039^1575*1250000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      625623063 1250000000 39965455750039 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1045715087/5000000000 : ℝ), (1424509763/2500000000 : ℝ), (625623063/1250000000 : ℝ)] ![(12575739468331/100000000000000 : ℝ), (11864701191749/25000000000000 : ℝ), (39965455750039/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1045715087/5000000000 : ℝ)|^2087 ≤ (12575739468331/100000000000000 : ℝ)^1575
        have hw : |(-1045715087/5000000000 : ℝ)|=(1045715087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1424509763/2500000000 : ℝ)|^2087 ≤ (11864701191749/25000000000000 : ℝ)^1575
        have hw : |(1424509763/2500000000 : ℝ)|=(1424509763/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(625623063/1250000000 : ℝ)|^2087 ≤ (39965455750039/100000000000000 : ℝ)^1575
        have hw : |(625623063/1250000000 : ℝ)|=(625623063/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s1_1 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5418406763/10000000000 : ℝ)*x 0 + (-154074573/625000000 : ℝ)*x 1 + (2502491803/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5418406763/10000000000 : ℝ)^2087 ≤ (2774845276863/6250000000000 : ℝ)^1575 := by
    have hnat : (5418406763 : ℕ)^2087*6250000000000^1575 ≤ 2774845276863^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418406763 10000000000 2774845276863 6250000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (154074573/625000000 : ℝ)^2087 ≤ (7818514654733/50000000000000 : ℝ)^1575 := by
    have hnat : (154074573 : ℕ)^2087*50000000000000^1575 ≤ 7818514654733^1575*625000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      154074573 625000000 7818514654733 50000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2502491803/5000000000 : ℝ)^2087 ≤ (39965446248363/100000000000000 : ℝ)^1575 := by
    have hnat : (2502491803 : ℕ)^2087*100000000000000^1575 ≤ 39965446248363^1575*5000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2502491803 5000000000 39965446248363 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5418406763/10000000000 : ℝ), (-154074573/625000000 : ℝ), (2502491803/5000000000 : ℝ)] ![(2774845276863/6250000000000 : ℝ), (7818514654733/50000000000000 : ℝ), (39965446248363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5418406763/10000000000 : ℝ)|^2087 ≤ (2774845276863/6250000000000 : ℝ)^1575
        have hw : |(5418406763/10000000000 : ℝ)|=(5418406763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-154074573/625000000 : ℝ)|^2087 ≤ (7818514654733/50000000000000 : ℝ)^1575
        have hw : |(-154074573/625000000 : ℝ)|=(154074573/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2502491803/5000000000 : ℝ)|^2087 ≤ (39965446248363/100000000000000 : ℝ)^1575
        have hw : |(2502491803/5000000000 : ℝ)|=(2502491803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s1_2 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1354602211/2500000000 : ℝ)*x 0 + (5004981739/10000000000 : ℝ)*x 1 + (-246519283/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1354602211/2500000000 : ℝ)^2087 ≤ (22198773512113/50000000000000 : ℝ)^1575 := by
    have hnat : (1354602211 : ℕ)^2087*50000000000000^1575 ≤ 22198773512113^1575*2500000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354602211 2500000000 22198773512113 50000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5004981739/10000000000 : ℝ)^2087 ≤ (7993085298753/20000000000000 : ℝ)^1575 := by
    have hnat : (5004981739 : ℕ)^2087*20000000000000^1575 ≤ 7993085298753^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5004981739 10000000000 7993085298753 20000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (246519283/1000000000 : ℝ)^2087 ≤ (15637026468527/100000000000000 : ℝ)^1575 := by
    have hnat : (246519283 : ℕ)^2087*100000000000000^1575 ≤ 15637026468527^1575*1000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      246519283 1000000000 15637026468527 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1354602211/2500000000 : ℝ), (5004981739/10000000000 : ℝ), (-246519283/1000000000 : ℝ)] ![(22198773512113/50000000000000 : ℝ), (7993085298753/20000000000000 : ℝ), (15637026468527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1354602211/2500000000 : ℝ)|^2087 ≤ (22198773512113/50000000000000 : ℝ)^1575
        have hw : |(1354602211/2500000000 : ℝ)|=(1354602211/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5004981739/10000000000 : ℝ)|^2087 ≤ (7993085298753/20000000000000 : ℝ)^1575
        have hw : |(5004981739/10000000000 : ℝ)|=(5004981739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-246519283/1000000000 : ℝ)|^2087 ≤ (15637026468527/100000000000000 : ℝ)^1575
        have hw : |(-246519283/1000000000 : ℝ)|=(246519283/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s1_3 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2158169161/5000000000 : ℝ)*x 0 + (1839744953/5000000000 : ℝ)*x 1 + (506181691/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2158169161/5000000000 : ℝ)^2087 ≤ (32847252531569/100000000000000 : ℝ)^1575 := by
    have hnat : (2158169161 : ℕ)^2087*100000000000000^1575 ≤ 32847252531569^1575*5000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158169161 5000000000 32847252531569 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1839744953/5000000000 : ℝ)^2087 ≤ (6646211206519/25000000000000 : ℝ)^1575 := by
    have hnat : (1839744953 : ℕ)^2087*25000000000000^1575 ≤ 6646211206519^1575*5000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1839744953 5000000000 6646211206519 25000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (506181691/1000000000 : ℝ)^2087 ≤ (20283951311623/50000000000000 : ℝ)^1575 := by
    have hnat : (506181691 : ℕ)^2087*50000000000000^1575 ≤ 20283951311623^1575*1000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      506181691 1000000000 20283951311623 50000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2158169161/5000000000 : ℝ), (1839744953/5000000000 : ℝ), (506181691/1000000000 : ℝ)] ![(32847252531569/100000000000000 : ℝ), (6646211206519/25000000000000 : ℝ), (20283951311623/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2158169161/5000000000 : ℝ)|^2087 ≤ (32847252531569/100000000000000 : ℝ)^1575
        have hw : |(2158169161/5000000000 : ℝ)|=(2158169161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1839744953/5000000000 : ℝ)|^2087 ≤ (6646211206519/25000000000000 : ℝ)^1575
        have hw : |(1839744953/5000000000 : ℝ)|=(1839744953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(506181691/1000000000 : ℝ)|^2087 ≤ (20283951311623/50000000000000 : ℝ)^1575
        have hw : |(506181691/1000000000 : ℝ)|=(506181691/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s1_4 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2092222847/10000000000 : ℝ)*x 0 + (5014400543/10000000000 : ℝ)*x 1 + (1422108511/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2092222847/10000000000 : ℝ)^2087 ≤ (1572756953081/12500000000000 : ℝ)^1575 := by
    have hnat : (2092222847 : ℕ)^2087*12500000000000^1575 ≤ 1572756953081^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2092222847 10000000000 1572756953081 12500000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5014400543/10000000000 : ℝ)^2087 ≤ (400651166717/1000000000000 : ℝ)^1575 := by
    have hnat : (5014400543 : ℕ)^2087*1000000000000^1575 ≤ 400651166717^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5014400543 10000000000 400651166717 1000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1422108511/2500000000 : ℝ)^2087 ≤ (2959551730517/6250000000000 : ℝ)^1575 := by
    have hnat : (1422108511 : ℕ)^2087*6250000000000^1575 ≤ 2959551730517^1575*2500000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1422108511 2500000000 2959551730517 6250000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2092222847/10000000000 : ℝ), (5014400543/10000000000 : ℝ), (1422108511/2500000000 : ℝ)] ![(1572756953081/12500000000000 : ℝ), (400651166717/1000000000000 : ℝ), (2959551730517/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2092222847/10000000000 : ℝ)|^2087 ≤ (1572756953081/12500000000000 : ℝ)^1575
        have hw : |(-2092222847/10000000000 : ℝ)|=(2092222847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5014400543/10000000000 : ℝ)|^2087 ≤ (400651166717/1000000000000 : ℝ)^1575
        have hw : |(5014400543/10000000000 : ℝ)|=(5014400543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1422108511/2500000000 : ℝ)|^2087 ≤ (2959551730517/6250000000000 : ℝ)^1575
        have hw : |(1422108511/2500000000 : ℝ)|=(1422108511/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s1_5 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5240604679/10000000000 : ℝ)*x 0 + (-1781738817/10000000000 : ℝ)*x 1 + (5688437593/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5240604679/10000000000 : ℝ)^2087 ≤ (8495483088541/20000000000000 : ℝ)^1575 := by
    have hnat : (5240604679 : ℕ)^2087*20000000000000^1575 ≤ 8495483088541^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240604679 10000000000 8495483088541 20000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1781738817/10000000000 : ℝ)^2087 ≤ (10169717718777/100000000000000 : ℝ)^1575 := by
    have hnat : (1781738817 : ℕ)^2087*100000000000000^1575 ≤ 10169717718777^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1781738817 10000000000 10169717718777 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5688437593/10000000000 : ℝ)^2087 ≤ (4735286683551/10000000000000 : ℝ)^1575 := by
    have hnat : (5688437593 : ℕ)^2087*10000000000000^1575 ≤ 4735286683551^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5688437593 10000000000 4735286683551 10000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5240604679/10000000000 : ℝ), (-1781738817/10000000000 : ℝ), (5688437593/10000000000 : ℝ)] ![(8495483088541/20000000000000 : ℝ), (10169717718777/100000000000000 : ℝ), (4735286683551/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5240604679/10000000000 : ℝ)|^2087 ≤ (8495483088541/20000000000000 : ℝ)^1575
        have hw : |(5240604679/10000000000 : ℝ)|=(5240604679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1781738817/10000000000 : ℝ)|^2087 ≤ (10169717718777/100000000000000 : ℝ)^1575
        have hw : |(-1781738817/10000000000 : ℝ)|=(1781738817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5688437593/10000000000 : ℝ)|^2087 ≤ (4735286683551/10000000000000 : ℝ)^1575
        have hw : |(5688437593/10000000000 : ℝ)|=(5688437593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s1_6 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5240603527/10000000000 : ℝ)*x 0 + (88881863/156250000 : ℝ)*x 1 + (-890869031/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5240603527/10000000000 : ℝ)^2087 ≤ (21238701534909/50000000000000 : ℝ)^1575 := by
    have hnat : (5240603527 : ℕ)^2087*50000000000000^1575 ≤ 21238701534909^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240603527 10000000000 21238701534909 50000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (88881863/156250000 : ℝ)^2087 ≤ (47352884914499/100000000000000 : ℝ)^1575 := by
    have hnat : (88881863 : ℕ)^2087*100000000000000^1575 ≤ 47352884914499^1575*156250000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88881863 156250000 47352884914499 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (890869031/5000000000 : ℝ)^2087 ≤ (5084856004273/50000000000000 : ℝ)^1575 := by
    have hnat : (890869031 : ℕ)^2087*50000000000000^1575 ≤ 5084856004273^1575*5000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      890869031 5000000000 5084856004273 50000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5240603527/10000000000 : ℝ), (88881863/156250000 : ℝ), (-890869031/5000000000 : ℝ)] ![(21238701534909/50000000000000 : ℝ), (47352884914499/100000000000000 : ℝ), (5084856004273/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5240603527/10000000000 : ℝ)|^2087 ≤ (21238701534909/50000000000000 : ℝ)^1575
        have hw : |(5240603527/10000000000 : ℝ)|=(5240603527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(88881863/156250000 : ℝ)|^2087 ≤ (47352884914499/100000000000000 : ℝ)^1575
        have hw : |(88881863/156250000 : ℝ)|=(88881863/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-890869031/5000000000 : ℝ)|^2087 ≤ (5084856004273/50000000000000 : ℝ)^1575
        have hw : |(-890869031/5000000000 : ℝ)|=(890869031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s1_7 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4317907971/10000000000 : ℝ)*x 0 + (1008607499/2000000000 : ℝ)*x 1 + (3698638877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4317907971/10000000000 : ℝ)^2087 ≤ (6572616307759/20000000000000 : ℝ)^1575 := by
    have hnat : (4317907971 : ℕ)^2087*20000000000000^1575 ≤ 6572616307759^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4317907971 10000000000 6572616307759 20000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1008607499/2000000000 : ℝ)^2087 ≤ (5046073573331/12500000000000 : ℝ)^1575 := by
    have hnat : (1008607499 : ℕ)^2087*12500000000000^1575 ≤ 5046073573331^1575*2000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1008607499 2000000000 5046073573331 12500000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3698638877/10000000000 : ℝ)^2087 ≤ (26768329853147/100000000000000 : ℝ)^1575 := by
    have hnat : (3698638877 : ℕ)^2087*100000000000000^1575 ≤ 26768329853147^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3698638877 10000000000 26768329853147 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4317907971/10000000000 : ℝ), (1008607499/2000000000 : ℝ), (3698638877/10000000000 : ℝ)] ![(6572616307759/20000000000000 : ℝ), (5046073573331/12500000000000 : ℝ), (26768329853147/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4317907971/10000000000 : ℝ)|^2087 ≤ (6572616307759/20000000000000 : ℝ)^1575
        have hw : |(4317907971/10000000000 : ℝ)|=(4317907971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1008607499/2000000000 : ℝ)|^2087 ≤ (5046073573331/12500000000000 : ℝ)^1575
        have hw : |(1008607499/2000000000 : ℝ)|=(1008607499/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3698638877/10000000000 : ℝ)|^2087 ≤ (26768329853147/100000000000000 : ℝ)^1575
        have hw : |(3698638877/10000000000 : ℝ)|=(3698638877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s1_8 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1429451/2500000000 : ℝ)*x 0 + (5490432007/10000000000 : ℝ)*x 1 + (794067067/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1429451/2500000000 : ℝ)^2087 ≤ (5047442873/100000000000000 : ℝ)^1575 := by
    have hnat : (1429451 : ℕ)^2087*100000000000000^1575 ≤ 5047442873^1575*2500000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1429451 2500000000 5047442873 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5490432007/10000000000 : ℝ)^2087 ≤ (45181221666187/100000000000000 : ℝ)^1575 := by
    have hnat : (5490432007 : ℕ)^2087*100000000000000^1575 ≤ 45181221666187^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5490432007 10000000000 45181221666187 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (794067067/1250000000 : ℝ)^2087 ≤ (1712929089867/3125000000000 : ℝ)^1575 := by
    have hnat : (794067067 : ℕ)^2087*3125000000000^1575 ≤ 1712929089867^1575*1250000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      794067067 1250000000 1712929089867 3125000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1429451/2500000000 : ℝ), (5490432007/10000000000 : ℝ), (794067067/1250000000 : ℝ)] ![(5047442873/100000000000000 : ℝ), (45181221666187/100000000000000 : ℝ), (1712929089867/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1429451/2500000000 : ℝ)|^2087 ≤ (5047442873/100000000000000 : ℝ)^1575
        have hw : |(1429451/2500000000 : ℝ)|=(1429451/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5490432007/10000000000 : ℝ)|^2087 ≤ (45181221666187/100000000000000 : ℝ)^1575
        have hw : |(5490432007/10000000000 : ℝ)|=(5490432007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(794067067/1250000000 : ℝ)|^2087 ≤ (1712929089867/3125000000000 : ℝ)^1575
        have hw : |(794067067/1250000000 : ℝ)|=(794067067/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s1_9 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (982539027/10000000000 : ℝ)*x 0 + (-110027231/250000000 : ℝ)*x 1 + (6943773151/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (982539027/10000000000 : ℝ)^2087 ≤ (4621506048449/100000000000000 : ℝ)^1575 := by
    have hnat : (982539027 : ℕ)^2087*100000000000000^1575 ≤ 4621506048449^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      982539027 10000000000 4621506048449 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (110027231/250000000 : ℝ)^2087 ≤ (16852290892571/50000000000000 : ℝ)^1575 := by
    have hnat : (110027231 : ℕ)^2087*50000000000000^1575 ≤ 16852290892571^1575*250000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110027231 250000000 16852290892571 50000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6943773151/10000000000 : ℝ)^2087 ≤ (2466956486171/4000000000000 : ℝ)^1575 := by
    have hnat : (6943773151 : ℕ)^2087*4000000000000^1575 ≤ 2466956486171^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6943773151 10000000000 2466956486171 4000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(982539027/10000000000 : ℝ), (-110027231/250000000 : ℝ), (6943773151/10000000000 : ℝ)] ![(4621506048449/100000000000000 : ℝ), (16852290892571/50000000000000 : ℝ), (2466956486171/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(982539027/10000000000 : ℝ)|^2087 ≤ (4621506048449/100000000000000 : ℝ)^1575
        have hw : |(982539027/10000000000 : ℝ)|=(982539027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-110027231/250000000 : ℝ)|^2087 ≤ (16852290892571/50000000000000 : ℝ)^1575
        have hw : |(-110027231/250000000 : ℝ)|=(110027231/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6943773151/10000000000 : ℝ)|^2087 ≤ (2466956486171/4000000000000 : ℝ)^1575
        have hw : |(6943773151/10000000000 : ℝ)|=(6943773151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s1_10 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (982531591/10000000000 : ℝ)*x 0 + (3471877681/5000000000 : ℝ)*x 1 + (-2200557219/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (982531591/10000000000 : ℝ)^2087 ≤ (924291940443/20000000000000 : ℝ)^1575 := by
    have hnat : (982531591 : ℕ)^2087*20000000000000^1575 ≤ 924291940443^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      982531591 10000000000 924291940443 20000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3471877681/5000000000 : ℝ)^2087 ≤ (61673702791619/100000000000000 : ℝ)^1575 := by
    have hnat : (3471877681 : ℕ)^2087*100000000000000^1575 ≤ 61673702791619^1575*5000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3471877681 5000000000 61673702791619 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2200557219/5000000000 : ℝ)^2087 ≤ (16852418744457/50000000000000 : ℝ)^1575 := by
    have hnat : (2200557219 : ℕ)^2087*50000000000000^1575 ≤ 16852418744457^1575*5000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2200557219 5000000000 16852418744457 50000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(982531591/10000000000 : ℝ), (3471877681/5000000000 : ℝ), (-2200557219/5000000000 : ℝ)] ![(924291940443/20000000000000 : ℝ), (61673702791619/100000000000000 : ℝ), (16852418744457/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(982531591/10000000000 : ℝ)|^2087 ≤ (924291940443/20000000000000 : ℝ)^1575
        have hw : |(982531591/10000000000 : ℝ)|=(982531591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3471877681/5000000000 : ℝ)|^2087 ≤ (61673702791619/100000000000000 : ℝ)^1575
        have hw : |(3471877681/5000000000 : ℝ)|=(3471877681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2200557219/5000000000 : ℝ)|^2087 ≤ (16852418744457/50000000000000 : ℝ)^1575
        have hw : |(-2200557219/5000000000 : ℝ)|=(2200557219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s1_11 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1914384401/10000000000 : ℝ)*x 0 + (5808816947/10000000000 : ℝ)*x 1 + (5020513991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1914384401/10000000000 : ℝ)^2087 ≤ (11184887951709/100000000000000 : ℝ)^1575 := by
    have hnat : (1914384401 : ℕ)^2087*100000000000000^1575 ≤ 11184887951709^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1914384401 10000000000 11184887951709 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5808816947/10000000000 : ℝ)^2087 ≤ (48685257021421/100000000000000 : ℝ)^1575 := by
    have hnat : (5808816947 : ℕ)^2087*100000000000000^1575 ≤ 48685257021421^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5808816947 10000000000 48685257021421 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5020513991/10000000000 : ℝ)^2087 ≤ (10032463751957/25000000000000 : ℝ)^1575 := by
    have hnat : (5020513991 : ℕ)^2087*25000000000000^1575 ≤ 10032463751957^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5020513991 10000000000 10032463751957 25000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1914384401/10000000000 : ℝ), (5808816947/10000000000 : ℝ), (5020513991/10000000000 : ℝ)] ![(11184887951709/100000000000000 : ℝ), (48685257021421/100000000000000 : ℝ), (10032463751957/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1914384401/10000000000 : ℝ)|^2087 ≤ (11184887951709/100000000000000 : ℝ)^1575
        have hw : |(1914384401/10000000000 : ℝ)|=(1914384401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5808816947/10000000000 : ℝ)|^2087 ≤ (48685257021421/100000000000000 : ℝ)^1575
        have hw : |(5808816947/10000000000 : ℝ)|=(5808816947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5020513991/10000000000 : ℝ)|^2087 ≤ (10032463751957/25000000000000 : ℝ)^1575
        have hw : |(5020513991/10000000000 : ℝ)|=(5020513991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1155_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149727417/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5553/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (467/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2861/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (10189/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5553/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (467/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5553/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (467/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5553/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (467/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5553/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (467/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5553/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (467/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5553/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (467/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (467/100000 : ℝ) ^ (8347/2048 : ℝ) ≤ (1980400673/6250000000000000000 : ℝ) := by
    have hpowers : (467/100000 : ℝ)^8347 ≤ (1980400673/6250000000000000000 : ℝ)^2048 := by
      have hnat : (467 : ℕ)^8347*6250000000000000000^2048 ≤ 1980400673^2048*100000^8347 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        467 100000 1980400673 6250000000000000000 8347 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (467/100000 : ℝ)) (X := (1980400673/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 8347 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (5553/20000 : ℝ) ^ (8347/2048 : ℝ) ≤ (539352399965718483/100000000000000000000 : ℝ) := by
    have hpowers : (5553/20000 : ℝ)^8347 ≤ (539352399965718483/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5553 : ℕ)^8347*100000000000000000000^2048 ≤ 539352399965718483^2048*20000^8347 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5553 20000 539352399965718483 100000000000000000000 8347 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5553/20000 : ℝ)) (X := (539352399965718483/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8347 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125000001980400673/3125000000000000000 : ℝ) ≤ (10000000001554901/10000000000000000 : ℝ) ^ (8347/2048 : ℝ) := by
    have hpowers : (3125000001980400673/3125000000000000000 : ℝ)^2048 ≤ (10000000001554901/10000000000000000 : ℝ)^8347 := by
      have hnat : (3125000001980400673 : ℕ)^2048*10000000000000000^8347 ≤ 10000000001554901^8347*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125000001980400673 3125000000000000000 10000000001554901 10000000000000000 2048 8347 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000001554901/10000000000000000 : ℝ)) (X := (3125000001980400673/3125000000000000000 : ℝ)) (by norm_num) 8347 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100539352431652129251/100000000000000000000 : ℝ) ≤ (80105652607759/80000000000000 : ℝ) ^ (8347/2048 : ℝ) := by
    have hpowers : (100539352431652129251/100000000000000000000 : ℝ)^2048 ≤ (80105652607759/80000000000000 : ℝ)^8347 := by
      have hnat : (100539352431652129251 : ℕ)^2048*80000000000000^8347 ≤ 80105652607759^8347*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100539352431652129251 100000000000000000000 80105652607759 80000000000000 2048 8347 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (80105652607759/80000000000000 : ℝ)) (X := (100539352431652129251/100000000000000000000 : ℝ)) (by norm_num) 8347 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50539352399965718483/50000000000000000000 : ℝ) ≤ (10026413150384849/10000000000000000 : ℝ) ^ (8347/2048 : ℝ) := by
    have hpowers : (50539352399965718483/50000000000000000000 : ℝ)^2048 ≤ (10026413150384849/10000000000000000 : ℝ)^8347 := by
      have hnat : (50539352399965718483 : ℕ)^2048*10000000000000000^8347 ≤ 10026413150384849^8347*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50539352399965718483 50000000000000000000 10026413150384849 10000000000000000 2048 8347 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10026413150384849/10000000000000000 : ℝ)) (X := (50539352399965718483/50000000000000000000 : ℝ)) (by norm_num) 8347 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1980400673/6250000000000000000 : ℝ) ≤ ((136483832550971050891/136490000000000000000 : ℝ)+2*(6603287207487/1364900000000000 : ℝ)*(467/100000 : ℝ))^(8347/2048 : ℝ) := by
    rw [show (136483832550971050891/136490000000000000000 : ℝ)+2*(6603287207487/1364900000000000 : ℝ)*(467/100000 : ℝ)=(10000000001554901/10000000000000000 : ℝ) by norm_num, show 1+2*(1980400673/6250000000000000000 : ℝ)=(3125000001980400673/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(539352399965718483/100000000000000000000 : ℝ)+(1980400673/6250000000000000000 : ℝ) ≤ ((136483832550971050891/136490000000000000000 : ℝ)+(6603287207487/1364900000000000 : ℝ)*((5553/20000 : ℝ)+(467/100000 : ℝ)))^(8347/2048 : ℝ) := by
    rw [show (136483832550971050891/136490000000000000000 : ℝ)+(6603287207487/1364900000000000 : ℝ)*((5553/20000 : ℝ)+(467/100000 : ℝ))=(80105652607759/80000000000000 : ℝ) by norm_num, show 1+(539352399965718483/100000000000000000000 : ℝ)+(1980400673/6250000000000000000 : ℝ)=(100539352431652129251/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(539352399965718483/100000000000000000000 : ℝ) ≤ ((136483832550971050891/136490000000000000000 : ℝ)+2*(6603287207487/1364900000000000 : ℝ)*(5553/20000 : ℝ))^(8347/2048 : ℝ) := by
    rw [show (136483832550971050891/136490000000000000000 : ℝ)+2*(6603287207487/1364900000000000 : ℝ)*(5553/20000 : ℝ)=(10026413150384849/10000000000000000 : ℝ) by norm_num, show 1+2*(539352399965718483/100000000000000000000 : ℝ)=(50539352399965718483/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (136483832550971050891/136490000000000000000 : ℝ)*(X 1 0+X 2 0)+(6603287207487/1364900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8347/2048 : ℝ)) (lo := (467/100000 : ℝ)) (hi := (5553/20000 : ℝ)) (c := (136483832550971050891/136490000000000000000 : ℝ)) (alpha := (6603287207487/1364900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (136483832550971050891/136490000000000000000 : ℝ)*(X 0 1+X 2 1)+(6603287207487/1364900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8347/2048 : ℝ)) (lo := (467/100000 : ℝ)) (hi := (5553/20000 : ℝ)) (c := (136483832550971050891/136490000000000000000 : ℝ)) (alpha := (6603287207487/1364900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (136483832550971050891/136490000000000000000 : ℝ)*(X 0 2+X 1 2)+(6603287207487/1364900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8347/2048 : ℝ)) (lo := (467/100000 : ℝ)) (hi := (5553/20000 : ℝ)) (c := (136483832550971050891/136490000000000000000 : ℝ)) (alpha := (6603287207487/1364900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1045715087/5000000000 : ℝ)*X 0 0+(1424509763/2500000000 : ℝ)*X 0 1+(625623063/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5418406763/10000000000 : ℝ)*X 1 0+(-154074573/625000000 : ℝ)*X 1 1+(2502491803/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1354602211/2500000000 : ℝ)*X 2 0+(5004981739/10000000000 : ℝ)*X 2 1+(-246519283/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2158169161/5000000000 : ℝ)*X 0 0+(1839744953/5000000000 : ℝ)*X 0 1+(506181691/1000000000 : ℝ)*X 0 2+(2158169161/5000000000 : ℝ)*X 1 0+(1839744953/5000000000 : ℝ)*X 1 1+(506181691/1000000000 : ℝ)*X 1 2+(2158169161/5000000000 : ℝ)*X 2 0+(1839744953/5000000000 : ℝ)*X 2 1+(506181691/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2092222847/10000000000 : ℝ)*X 0 0+(5014400543/10000000000 : ℝ)*X 0 1+(1422108511/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5240604679/10000000000 : ℝ)*X 1 0+(-1781738817/10000000000 : ℝ)*X 1 1+(5688437593/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5240603527/10000000000 : ℝ)*X 2 0+(88881863/156250000 : ℝ)*X 2 1+(-890869031/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4317907971/10000000000 : ℝ)*X 0 0+(1008607499/2000000000 : ℝ)*X 0 1+(3698638877/10000000000 : ℝ)*X 0 2+(4317907971/10000000000 : ℝ)*X 1 0+(1008607499/2000000000 : ℝ)*X 1 1+(3698638877/10000000000 : ℝ)*X 1 2+(4317907971/10000000000 : ℝ)*X 2 0+(1008607499/2000000000 : ℝ)*X 2 1+(3698638877/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((1429451/2500000000 : ℝ)*X 0 0+(5490432007/10000000000 : ℝ)*X 0 1+(794067067/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s1_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((982539027/10000000000 : ℝ)*X 1 0+(-110027231/250000000 : ℝ)*X 1 1+(6943773151/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s1_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((982531591/10000000000 : ℝ)*X 2 0+(3471877681/5000000000 : ℝ)*X 2 1+(-2200557219/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s1_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1914384401/10000000000 : ℝ)*X 0 0+(5808816947/10000000000 : ℝ)*X 0 1+(5020513991/10000000000 : ℝ)*X 0 2+(1914384401/10000000000 : ℝ)*X 1 0+(5808816947/10000000000 : ℝ)*X 1 1+(5020513991/10000000000 : ℝ)*X 1 2+(1914384401/10000000000 : ℝ)*X 2 0+(5808816947/10000000000 : ℝ)*X 2 1+(5020513991/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s1_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (35615898411791590283440946109/3412250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8112717/10000000000000 : ℝ)*(lower2) + (541578967225889/50000000000000 : ℝ)*(major0) + (541578967225889/50000000000000 : ℝ)*(major1) + (541578967225889/50000000000000 : ℝ)*(major2) + (721445566700127/50000000000000 : ℝ)*(sp0) + (721445314397783/50000000000000 : ℝ)*(sp1) + (1442888588995681/100000000000000 : ℝ)*(sp2) + (144683646668299/20000000000000 : ℝ)*(sp3) + (2242415583/50000000000000 : ℝ)*(sp4) + (1058001977/25000000000000 : ℝ)*(sp5) + (5842344423/100000000000000 : ℝ)*(sp6) + (378713973/50000000000000 : ℝ)*(sp9) + (1186891317/100000000000000 : ℝ)*(sp10) + (1669408699/100000000000000 : ℝ)*(sp11) + (361709951375097/50000000000000 : ℝ)*(f.failure) + (72144780911571/5000000000000 : ℝ)*(f.sum) + (65996372310591/68245000000000000000000000000 : ℝ)*base65 + (68857763795865517099/6824500000000000000000000000000000 : ℝ)*base67 + (54299373851970517099/6824500000000000000000000000000000 : ℝ)*base69 + (93021101343391517099/6824500000000000000000000000000000 : ℝ)*base71 + (18535335702569/68245000000000000000000000000 : ℝ)*base74 + (68074115496503517099/6824500000000000000000000000000000 : ℝ)*base75 + (69184384693441517099/6824500000000000000000000000000000 : ℝ)*base77 + (27623986001292017099/6824500000000000000000000000000000 : ℝ)*base79 + (79700243610921/68245000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (28065551/5000000000000000000000 : ℝ)*base90 + (28065551/5000000000000000000000 : ℝ)*base92 + (28065551/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (138760625507214982015151073/34122500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9306953/50000000000000 : ℝ)*(lower4) + (11137172748301/1000000000000 : ℝ)*(major0) + (11137172748301/1000000000000 : ℝ)*(major1) + (11137172748301/1000000000000 : ℝ)*(major2) + (2384947249/50000000000000 : ℝ)*(sp1) + (1901583499/25000000000000 : ℝ)*(sp2) + (153025907/12500000000000 : ℝ)*(sp3) + (1483601056570491/100000000000000 : ℝ)*(sp4) + (29671990384539/2000000000000 : ℝ)*(sp5) + (741798461004837/50000000000000 : ℝ)*(sp6) + (743827359220351/100000000000000 : ℝ)*(sp7) + (3471773179/100000000000000 : ℝ)*(sp8) + (119611111/50000000000000 : ℝ)*(sp9) + (1302337471/100000000000000 : ℝ)*(sp11) + (743829885765077/100000000000000 : ℝ)*(f.failure) + (148360452834367/10000000000000 : ℝ)*(f.sum) + (26726164040047/13649000000000000000000000000 : ℝ)*base66 + (1427190683586673809/136490000000000000000000000000000 : ℝ)*base68 + (1251070608989553809/136490000000000000000000000000000 : ℝ)*base70 + (949214518871906191/136490000000000000000000000000000 : ℝ)*base71 + (16868463496309/3412250000000000000000000000 : ℝ)*base74 + (1329133213486433809/136490000000000000000000000000000 : ℝ)*base76 + (1125915810036053809/136490000000000000000000000000000 : ℝ)*base78 + (1122287384990213809/136490000000000000000000000000000 : ℝ)*base80 + (3448312093459/682450000000000000000000000 : ℝ)*base82 + (48016109/10000000000000000000000 : ℝ)*base89 + (48016109/10000000000000000000000 : ℝ)*base91 + (48016109/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1155_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149727417/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5553/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (467/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2861/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (10189/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1155_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1155_s2_0 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2143967717/10000000000 : ℝ)*x 0 + (86067871/156250000 : ℝ)*x 1 + (2580629551/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2143967717/10000000000 : ℝ)^2087 ≤ (12996041582453/100000000000000 : ℝ)^1575 := by
    have hnat : (2143967717 : ℕ)^2087*100000000000000^1575 ≤ 12996041582453^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2143967717 10000000000 12996041582453 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (86067871/156250000 : ℝ)^2087 ≤ (2268831905529/5000000000000 : ℝ)^1575 := by
    have hnat : (86067871 : ℕ)^2087*5000000000000^1575 ≤ 2268831905529^1575*156250000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86067871 156250000 2268831905529 5000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2580629551/5000000000 : ℝ)^2087 ≤ (10406830074659/25000000000000 : ℝ)^1575 := by
    have hnat : (2580629551 : ℕ)^2087*25000000000000^1575 ≤ 10406830074659^1575*5000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2580629551 5000000000 10406830074659 25000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2143967717/10000000000 : ℝ), (86067871/156250000 : ℝ), (2580629551/5000000000 : ℝ)] ![(12996041582453/100000000000000 : ℝ), (2268831905529/5000000000000 : ℝ), (10406830074659/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2143967717/10000000000 : ℝ)|^2087 ≤ (12996041582453/100000000000000 : ℝ)^1575
        have hw : |(-2143967717/10000000000 : ℝ)|=(2143967717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(86067871/156250000 : ℝ)|^2087 ≤ (2268831905529/5000000000000 : ℝ)^1575
        have hw : |(86067871/156250000 : ℝ)|=(86067871/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2580629551/5000000000 : ℝ)|^2087 ≤ (10406830074659/25000000000000 : ℝ)^1575
        have hw : |(2580629551/5000000000 : ℝ)|=(2580629551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s2_1 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2686652353/5000000000 : ℝ)*x 0 + (-11621629/50000000 : ℝ)*x 1 + (1032252299/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2686652353/5000000000 : ℝ)^2087 ≤ (21954246762799/50000000000000 : ℝ)^1575 := by
    have hnat : (2686652353 : ℕ)^2087*50000000000000^1575 ≤ 21954246762799^1575*5000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2686652353 5000000000 21954246762799 50000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (11621629/50000000 : ℝ)^2087 ≤ (14464160589851/100000000000000 : ℝ)^1575 := by
    have hnat : (11621629 : ℕ)^2087*100000000000000^1575 ≤ 14464160589851^1575*50000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11621629 50000000 14464160589851 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1032252299/2000000000 : ℝ)^2087 ≤ (41627345873151/100000000000000 : ℝ)^1575 := by
    have hnat : (1032252299 : ℕ)^2087*100000000000000^1575 ≤ 41627345873151^1575*2000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1032252299 2000000000 41627345873151 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2686652353/5000000000 : ℝ), (-11621629/50000000 : ℝ), (1032252299/2000000000 : ℝ)] ![(21954246762799/50000000000000 : ℝ), (14464160589851/100000000000000 : ℝ), (41627345873151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2686652353/5000000000 : ℝ)|^2087 ≤ (21954246762799/50000000000000 : ℝ)^1575
        have hw : |(2686652353/5000000000 : ℝ)|=(2686652353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-11621629/50000000 : ℝ)|^2087 ≤ (14464160589851/100000000000000 : ℝ)^1575
        have hw : |(-11621629/50000000 : ℝ)|=(11621629/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1032252299/2000000000 : ℝ)|^2087 ≤ (41627345873151/100000000000000 : ℝ)^1575
        have hw : |(1032252299/2000000000 : ℝ)|=(1032252299/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s2_2 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2686652449/5000000000 : ℝ)*x 0 + (5161261049/10000000000 : ℝ)*x 1 + (-1162163063/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2686652449/5000000000 : ℝ)^2087 ≤ (21954247802289/50000000000000 : ℝ)^1575 := by
    have hnat : (2686652449 : ℕ)^2087*50000000000000^1575 ≤ 21954247802289^1575*5000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2686652449 5000000000 21954247802289 50000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5161261049/10000000000 : ℝ)^2087 ≤ (41627341106651/100000000000000 : ℝ)^1575 := by
    have hnat : (5161261049 : ℕ)^2087*100000000000000^1575 ≤ 41627341106651^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5161261049 10000000000 41627341106651 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1162163063/5000000000 : ℝ)^2087 ≤ (7232081639007/50000000000000 : ℝ)^1575 := by
    have hnat : (1162163063 : ℕ)^2087*50000000000000^1575 ≤ 7232081639007^1575*5000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1162163063 5000000000 7232081639007 50000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2686652449/5000000000 : ℝ), (5161261049/10000000000 : ℝ), (-1162163063/5000000000 : ℝ)] ![(21954247802289/50000000000000 : ℝ), (41627341106651/100000000000000 : ℝ), (7232081639007/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2686652449/5000000000 : ℝ)|^2087 ≤ (21954247802289/50000000000000 : ℝ)^1575
        have hw : |(2686652449/5000000000 : ℝ)|=(2686652449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5161261049/10000000000 : ℝ)|^2087 ≤ (41627341106651/100000000000000 : ℝ)^1575
        have hw : |(5161261049/10000000000 : ℝ)|=(5161261049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1162163063/5000000000 : ℝ)|^2087 ≤ (7232081639007/50000000000000 : ℝ)^1575
        have hw : |(-1162163063/5000000000 : ℝ)|=(1162163063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s2_3 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4352411669/10000000000 : ℝ)*x 0 + (1004968697/2500000000 : ℝ)*x 1 + (2356073491/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4352411669/10000000000 : ℝ)^2087 ≤ (33211503191051/100000000000000 : ℝ)^1575 := by
    have hnat : (4352411669 : ℕ)^2087*100000000000000^1575 ≤ 33211503191051^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4352411669 10000000000 33211503191051 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1004968697/2500000000 : ℝ)^2087 ≤ (29891670406639/100000000000000 : ℝ)^1575 := by
    have hnat : (1004968697 : ℕ)^2087*100000000000000^1575 ≤ 29891670406639^1575*2500000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004968697 2500000000 29891670406639 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2356073491/5000000000 : ℝ)^2087 ≤ (36896826397231/100000000000000 : ℝ)^1575 := by
    have hnat : (2356073491 : ℕ)^2087*100000000000000^1575 ≤ 36896826397231^1575*5000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2356073491 5000000000 36896826397231 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4352411669/10000000000 : ℝ), (1004968697/2500000000 : ℝ), (2356073491/5000000000 : ℝ)] ![(33211503191051/100000000000000 : ℝ), (29891670406639/100000000000000 : ℝ), (36896826397231/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4352411669/10000000000 : ℝ)|^2087 ≤ (33211503191051/100000000000000 : ℝ)^1575
        have hw : |(4352411669/10000000000 : ℝ)|=(4352411669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1004968697/2500000000 : ℝ)|^2087 ≤ (29891670406639/100000000000000 : ℝ)^1575
        have hw : |(1004968697/2500000000 : ℝ)|=(1004968697/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2356073491/5000000000 : ℝ)|^2087 ≤ (36896826397231/100000000000000 : ℝ)^1575
        have hw : |(2356073491/5000000000 : ℝ)|=(2356073491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s2_4 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2144066841/10000000000 : ℝ)*x 0 + (5163630849/10000000000 : ℝ)*x 1 + (5505948367/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2144066841/10000000000 : ℝ)^2087 ≤ (12996837772647/100000000000000 : ℝ)^1575 := by
    have hnat : (2144066841 : ℕ)^2087*100000000000000^1575 ≤ 12996837772647^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2144066841 10000000000 12996837772647 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5163630849/10000000000 : ℝ)^2087 ≤ (8330533913963/20000000000000 : ℝ)^1575 := by
    have hnat : (5163630849 : ℕ)^2087*20000000000000^1575 ≤ 8330533913963^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5163630849 10000000000 8330533913963 20000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5505948367/10000000000 : ℝ)^2087 ≤ (45350492646961/100000000000000 : ℝ)^1575 := by
    have hnat : (5505948367 : ℕ)^2087*100000000000000^1575 ≤ 45350492646961^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5505948367 10000000000 45350492646961 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2144066841/10000000000 : ℝ), (5163630849/10000000000 : ℝ), (5505948367/10000000000 : ℝ)] ![(12996837772647/100000000000000 : ℝ), (8330533913963/20000000000000 : ℝ), (45350492646961/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2144066841/10000000000 : ℝ)|^2087 ≤ (12996837772647/100000000000000 : ℝ)^1575
        have hw : |(-2144066841/10000000000 : ℝ)|=(2144066841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5163630849/10000000000 : ℝ)|^2087 ≤ (8330533913963/20000000000000 : ℝ)^1575
        have hw : |(5163630849/10000000000 : ℝ)|=(5163630849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5505948367/10000000000 : ℝ)|^2087 ≤ (45350492646961/100000000000000 : ℝ)^1575
        have hw : |(5505948367/10000000000 : ℝ)|=(5505948367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s2_5 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (660645533/1250000000 : ℝ)*x 0 + (-989818259/5000000000 : ℝ)*x 1 + (688243647/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (660645533/1250000000 : ℝ)^2087 ≤ (5369582662247/12500000000000 : ℝ)^1575 := by
    have hnat : (660645533 : ℕ)^2087*12500000000000^1575 ≤ 5369582662247^1575*1250000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660645533 1250000000 5369582662247 12500000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (989818259/5000000000 : ℝ)^2087 ≤ (1169283721023/10000000000000 : ℝ)^1575 := by
    have hnat : (989818259 : ℕ)^2087*10000000000000^1575 ≤ 1169283721023^1575*5000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      989818259 5000000000 1169283721023 10000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (688243647/1250000000 : ℝ)^2087 ≤ (45350501476547/100000000000000 : ℝ)^1575 := by
    have hnat : (688243647 : ℕ)^2087*100000000000000^1575 ≤ 45350501476547^1575*1250000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      688243647 1250000000 45350501476547 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(660645533/1250000000 : ℝ), (-989818259/5000000000 : ℝ), (688243647/1250000000 : ℝ)] ![(5369582662247/12500000000000 : ℝ), (1169283721023/10000000000000 : ℝ), (45350501476547/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(660645533/1250000000 : ℝ)|^2087 ≤ (5369582662247/12500000000000 : ℝ)^1575
        have hw : |(660645533/1250000000 : ℝ)|=(660645533/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-989818259/5000000000 : ℝ)|^2087 ≤ (1169283721023/10000000000000 : ℝ)^1575
        have hw : |(-989818259/5000000000 : ℝ)|=(989818259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(688243647/1250000000 : ℝ)|^2087 ≤ (45350501476547/100000000000000 : ℝ)^1575
        have hw : |(688243647/1250000000 : ℝ)|=(688243647/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s2_6 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1321290631/2500000000 : ℝ)*x 0 + (550594887/1000000000 : ℝ)*x 1 + (-98981967/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1321290631/2500000000 : ℝ)^2087 ≤ (21478321279127/50000000000000 : ℝ)^1575 := by
    have hnat : (1321290631 : ℕ)^2087*50000000000000^1575 ≤ 21478321279127^1575*2500000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321290631 2500000000 21478321279127 50000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (550594887/1000000000 : ℝ)^2087 ≤ (22675249068401/50000000000000 : ℝ)^1575 := by
    have hnat : (550594887 : ℕ)^2087*50000000000000^1575 ≤ 22675249068401^1575*1000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550594887 1000000000 22675249068401 50000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (98981967/500000000 : ℝ)^2087 ≤ (11692859297063/100000000000000 : ℝ)^1575 := by
    have hnat : (98981967 : ℕ)^2087*100000000000000^1575 ≤ 11692859297063^1575*500000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      98981967 500000000 11692859297063 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1321290631/2500000000 : ℝ), (550594887/1000000000 : ℝ), (-98981967/500000000 : ℝ)] ![(21478321279127/50000000000000 : ℝ), (22675249068401/50000000000000 : ℝ), (11692859297063/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1321290631/2500000000 : ℝ)|^2087 ≤ (21478321279127/50000000000000 : ℝ)^1575
        have hw : |(1321290631/2500000000 : ℝ)|=(1321290631/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(550594887/1000000000 : ℝ)|^2087 ≤ (22675249068401/50000000000000 : ℝ)^1575
        have hw : |(550594887/1000000000 : ℝ)|=(550594887/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-98981967/500000000 : ℝ)|^2087 ≤ (11692859297063/100000000000000 : ℝ)^1575
        have hw : |(-98981967/500000000 : ℝ)|=(98981967/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s2_7 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4352608027/10000000000 : ℝ)*x 0 + (4707418449/10000000000 : ℝ)*x 1 + (2012325373/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4352608027/10000000000 : ℝ)^2087 ≤ (8303372152591/25000000000000 : ℝ)^1575 := by
    have hnat : (4352608027 : ℕ)^2087*25000000000000^1575 ≤ 8303372152591^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4352608027 10000000000 8303372152591 25000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4707418449/10000000000 : ℝ)^2087 ≤ (736955463271/2000000000000 : ℝ)^1575 := by
    have hnat : (4707418449 : ℕ)^2087*2000000000000^1575 ≤ 736955463271^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4707418449 10000000000 736955463271 2000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2012325373/5000000000 : ℝ)^2087 ≤ (935585568911/3125000000000 : ℝ)^1575 := by
    have hnat : (2012325373 : ℕ)^2087*3125000000000^1575 ≤ 935585568911^1575*5000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2012325373 5000000000 935585568911 3125000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4352608027/10000000000 : ℝ), (4707418449/10000000000 : ℝ), (2012325373/5000000000 : ℝ)] ![(8303372152591/25000000000000 : ℝ), (736955463271/2000000000000 : ℝ), (935585568911/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4352608027/10000000000 : ℝ)|^2087 ≤ (8303372152591/25000000000000 : ℝ)^1575
        have hw : |(4352608027/10000000000 : ℝ)|=(4352608027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4707418449/10000000000 : ℝ)|^2087 ≤ (736955463271/2000000000000 : ℝ)^1575
        have hw : |(4707418449/10000000000 : ℝ)|=(4707418449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2012325373/5000000000 : ℝ)|^2087 ≤ (935585568911/3125000000000 : ℝ)^1575
        have hw : |(2012325373/5000000000 : ℝ)|=(2012325373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1155_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149727417/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10189/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2861/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (9129/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1029/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (10189/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2861/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (10189/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2861/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (10189/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2861/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (10189/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2861/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (10189/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2861/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (10189/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2861/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2861/50000 : ℝ) ^ (8347/2048 : ℝ) ≤ (26977903200633/3125000000000000000 : ℝ) := by
    have hpowers : (2861/50000 : ℝ)^8347 ≤ (26977903200633/3125000000000000000 : ℝ)^2048 := by
      have hnat : (2861 : ℕ)^8347*3125000000000000000^2048 ≤ 26977903200633^2048*50000^8347 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2861 50000 26977903200633 3125000000000000000 8347 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2861/50000 : ℝ)) (X := (26977903200633/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 8347 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (10189/50000 : ℝ) ^ (8347/2048 : ℝ) ≤ (76441834318984153/50000000000000000000 : ℝ) := by
    have hpowers : (10189/50000 : ℝ)^8347 ≤ (76441834318984153/50000000000000000000 : ℝ)^2048 := by
      have hnat : (10189 : ℕ)^8347*50000000000000000000^2048 ≤ 76441834318984153^2048*50000^8347 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10189 50000 76441834318984153 50000000000000000000 8347 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10189/50000 : ℝ)) (X := (76441834318984153/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8347 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562526977903200633/1562500000000000000 : ℝ) ≤ (5000021181410639/5000000000000000 : ℝ) ^ (8347/2048 : ℝ) := by
    have hpowers : (1562526977903200633/1562500000000000000 : ℝ)^2048 ≤ (5000021181410639/5000000000000000 : ℝ)^8347 := by
      have hnat : (1562526977903200633 : ℕ)^2048*5000000000000000^8347 ≤ 5000021181410639^8347*1562500000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562526977903200633 1562500000000000000 5000021181410639 5000000000000000 2048 8347 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000021181410639/5000000000000000 : ℝ)) (X := (1562526977903200633/1562500000000000000 : ℝ)) (by norm_num) 8347 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50076873480770194281/50000000000000000000 : ℝ) ≤ (10003770112337187/10000000000000000 : ℝ) ^ (8347/2048 : ℝ) := by
    have hpowers : (50076873480770194281/50000000000000000000 : ℝ)^2048 ≤ (10003770112337187/10000000000000000 : ℝ)^8347 := by
      have hnat : (50076873480770194281 : ℕ)^2048*10000000000000000^8347 ≤ 10003770112337187^8347*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50076873480770194281 50000000000000000000 10003770112337187 10000000000000000 2048 8347 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003770112337187/10000000000000000 : ℝ)) (X := (50076873480770194281/50000000000000000000 : ℝ)) (by norm_num) 8347 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25076441834318984153/25000000000000000000 : ℝ) ≤ (1250937232731637/1250000000000000 : ℝ) ^ (8347/2048 : ℝ) := by
    have hpowers : (25076441834318984153/25000000000000000000 : ℝ)^2048 ≤ (1250937232731637/1250000000000000 : ℝ)^8347 := by
      have hnat : (25076441834318984153 : ℕ)^2048*1250000000000000^8347 ≤ 1250937232731637^8347*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25076441834318984153 25000000000000000000 1250937232731637 1250000000000000 2048 8347 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250937232731637/1250000000000000 : ℝ)) (X := (25076441834318984153/25000000000000000000 : ℝ)) (by norm_num) 8347 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(26977903200633/3125000000000000000 : ℝ) ≤ ((36629490126012146943/36640000000000000000 : ℝ)+2*(3727749515909/1465600000000000 : ℝ)*(2861/50000 : ℝ))^(8347/2048 : ℝ) := by
    rw [show (36629490126012146943/36640000000000000000 : ℝ)+2*(3727749515909/1465600000000000 : ℝ)*(2861/50000 : ℝ)=(5000021181410639/5000000000000000 : ℝ) by norm_num, show 1+2*(26977903200633/3125000000000000000 : ℝ)=(1562526977903200633/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(76441834318984153/50000000000000000000 : ℝ)+(26977903200633/3125000000000000000 : ℝ) ≤ ((36629490126012146943/36640000000000000000 : ℝ)+(3727749515909/1465600000000000 : ℝ)*((10189/50000 : ℝ)+(2861/50000 : ℝ)))^(8347/2048 : ℝ) := by
    rw [show (36629490126012146943/36640000000000000000 : ℝ)+(3727749515909/1465600000000000 : ℝ)*((10189/50000 : ℝ)+(2861/50000 : ℝ))=(10003770112337187/10000000000000000 : ℝ) by norm_num, show 1+(76441834318984153/50000000000000000000 : ℝ)+(26977903200633/3125000000000000000 : ℝ)=(50076873480770194281/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(76441834318984153/50000000000000000000 : ℝ) ≤ ((36629490126012146943/36640000000000000000 : ℝ)+2*(3727749515909/1465600000000000 : ℝ)*(10189/50000 : ℝ))^(8347/2048 : ℝ) := by
    rw [show (36629490126012146943/36640000000000000000 : ℝ)+2*(3727749515909/1465600000000000 : ℝ)*(10189/50000 : ℝ)=(1250937232731637/1250000000000000 : ℝ) by norm_num, show 1+2*(76441834318984153/50000000000000000000 : ℝ)=(25076441834318984153/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (36629490126012146943/36640000000000000000 : ℝ)*(X 1 0+X 2 0)+(3727749515909/1465600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8347/2048 : ℝ)) (lo := (2861/50000 : ℝ)) (hi := (10189/50000 : ℝ)) (c := (36629490126012146943/36640000000000000000 : ℝ)) (alpha := (3727749515909/1465600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (36629490126012146943/36640000000000000000 : ℝ)*(X 0 1+X 2 1)+(3727749515909/1465600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8347/2048 : ℝ)) (lo := (2861/50000 : ℝ)) (hi := (10189/50000 : ℝ)) (c := (36629490126012146943/36640000000000000000 : ℝ)) (alpha := (3727749515909/1465600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (36629490126012146943/36640000000000000000 : ℝ)*(X 0 2+X 1 2)+(3727749515909/1465600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8347/2048 : ℝ)) (lo := (2861/50000 : ℝ)) (hi := (10189/50000 : ℝ)) (c := (36629490126012146943/36640000000000000000 : ℝ)) (alpha := (3727749515909/1465600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2143967717/10000000000 : ℝ)*X 0 0+(86067871/156250000 : ℝ)*X 0 1+(2580629551/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2686652353/5000000000 : ℝ)*X 1 0+(-11621629/50000000 : ℝ)*X 1 1+(1032252299/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2686652449/5000000000 : ℝ)*X 2 0+(5161261049/10000000000 : ℝ)*X 2 1+(-1162163063/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4352411669/10000000000 : ℝ)*X 0 0+(1004968697/2500000000 : ℝ)*X 0 1+(2356073491/5000000000 : ℝ)*X 0 2+(4352411669/10000000000 : ℝ)*X 1 0+(1004968697/2500000000 : ℝ)*X 1 1+(2356073491/5000000000 : ℝ)*X 1 2+(4352411669/10000000000 : ℝ)*X 2 0+(1004968697/2500000000 : ℝ)*X 2 1+(2356073491/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2144066841/10000000000 : ℝ)*X 0 0+(5163630849/10000000000 : ℝ)*X 0 1+(5505948367/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((660645533/1250000000 : ℝ)*X 1 0+(-989818259/5000000000 : ℝ)*X 1 1+(688243647/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1321290631/2500000000 : ℝ)*X 2 0+(550594887/1000000000 : ℝ)*X 2 1+(-98981967/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4352608027/10000000000 : ℝ)*X 0 0+(4707418449/10000000000 : ℝ)*X 0 1+(2012325373/5000000000 : ℝ)*X 0 2+(4352608027/10000000000 : ℝ)*X 1 0+(4707418449/10000000000 : ℝ)*X 1 1+(2012325373/5000000000 : ℝ)*X 1 2+(4352608027/10000000000 : ℝ)*X 2 0+(4707418449/10000000000 : ℝ)*X 2 1+(2012325373/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10323511021184190794943360873/1832000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (33356379/20000000000000 : ℝ)*(base19) + (12311023/6250000000000 : ℝ)*(base23) + (92921467/100000000000000 : ℝ)*(upper2) + (121091939/50000000000000 : ℝ)*(upper3) + (66007813/50000000000000 : ℝ)*(upper4) + (2162850695553837/100000000000000 : ℝ)*(major0) + (2162850695553837/100000000000000 : ℝ)*(major1) + (2162850695553837/100000000000000 : ℝ)*(major2) + (1440580200660053/50000000000000 : ℝ)*(sp0) + (1440587776092911/50000000000000 : ℝ)*(sp1) + (720293880497837/25000000000000 : ℝ)*(sp2) + (1444520845117899/100000000000000 : ℝ)*(sp3) + (1531764761/10000000000000 : ℝ)*(sp4) + (1159796311/25000000000000 : ℝ)*(sp7) + (1444525484303143/100000000000000 : ℝ)*(f.failure) + (720293929741929/25000000000000 : ℝ)*(f.sum) + (80095633740127/73280000000000000000000000000 : ℝ)*base66 + (11688965980724295291/3664000000000000000000000000000000 : ℝ)*base67 + (5918920237803704709/3664000000000000000000000000000000 : ℝ)*base70 + (9186163363931704709/3664000000000000000000000000000000 : ℝ)*base72 + (238585136605793/73280000000000000000000000000 : ℝ)*base73 + (12164084423915704709/3664000000000000000000000000000000 : ℝ)*base76 + (12787670810139704709/3664000000000000000000000000000000 : ℝ)*base78 + (15302526264852295291/3664000000000000000000000000000000 : ℝ)*base79 + (58819957267487/73280000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (53628369/10000000000000000000000 : ℝ)*base90 + (53628369/10000000000000000000000 : ℝ)*base92 + (53628369/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (637540459439448116093211/73280000000000000000000000000 : ℝ) := by norm_num
    linear_combination (292202939/20000000000000 : ℝ)*(base19) + (5604741/625000000000 : ℝ)*(base23) + (101081253/25000000000000 : ℝ)*(upper2) + (3435901/4000000000000 : ℝ)*(upper3) + (142051229/50000000000000 : ℝ)*(upper5) + (2192939932304053/100000000000000 : ℝ)*(major0) + (2192939932304053/100000000000000 : ℝ)*(major1) + (2192939932304053/100000000000000 : ℝ)*(major2) + (11706535037/50000000000000 : ℝ)*(sp1) + (137492743/10000000000000 : ℝ)*(sp2) + (730314520066189/25000000000000 : ℝ)*(sp4) + (730308301544997/25000000000000 : ℝ)*(sp5) + (1460627904289383/50000000000000 : ℝ)*(sp6) + (366155373585329/25000000000000 : ℝ)*(sp7) + (366155373585329/25000000000000 : ℝ)*(f.failure) + (730314520066189/25000000000000 : ℝ)*(f.sum) + (429522216614903/73280000000000000000000000000 : ℝ)*base66 + (1463261304777884979/3664000000000000000000000000000000 : ℝ)*base67 + (18978359427337884979/3664000000000000000000000000000000 : ℝ)*base69 + (27295708751542115021/3664000000000000000000000000000000 : ℝ)*base72 + (66847783832823/73280000000000000000000000000 : ℝ)*base74 + (8440953982486115021/3664000000000000000000000000000000 : ℝ)*base76 + (22596263993014115021/3664000000000000000000000000000000 : ℝ)*base78 + (36435003097833884979/3664000000000000000000000000000000 : ℝ)*base79 + (54569612498697/73280000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (15265193/2500000000000000000000 : ℝ)*base89 + (15265193/2500000000000000000000 : ℝ)*base91 + (15265193/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1155_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149727417/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10189/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2861/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9129/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1029/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1155_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1155_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149727417/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9129/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1029/6250 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1155_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1155_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1155_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149727417/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9129/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1029/6250 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1155_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
