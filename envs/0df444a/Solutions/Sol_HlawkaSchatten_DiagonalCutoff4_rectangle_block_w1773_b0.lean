-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1773_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:34:38.942995+00:00
-- url     : https://prove2.me/submissions/1611977f-5646-4ffa-a46b-a461287d7da8

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
theorem support_rectangle_w1773_s0_0 (p : ℝ) (hpa : (6143/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (-1078426067/10000000000 : ℝ)*x 0 + (5493999893/10000000000 : ℝ)*x 1 + (2539504869/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1078426067/10000000000 : ℝ)^6 ≤ (1381587667171/20000000000000 : ℝ)^5 := by
    have hnat : (1078426067 : ℕ)^6*20000000000000^5 ≤ 1381587667171^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078426067 10000000000 1381587667171 20000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5493999893/10000000000 : ℝ)^6 ≤ (9747570201/20000000000 : ℝ)^5 := by
    have hnat : (5493999893 : ℕ)^6*20000000000^5 ≤ 9747570201^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5493999893 10000000000 9747570201 20000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2539504869/5000000000 : ℝ)^6 ≤ (22177105318779/50000000000000 : ℝ)^5 := by
    have hnat : (2539504869 : ℕ)^6*50000000000000^5 ≤ 22177105318779^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2539504869 5000000000 22177105318779 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1078426067/10000000000 : ℝ), (5493999893/10000000000 : ℝ), (2539504869/5000000000 : ℝ)] ![(1381587667171/20000000000000 : ℝ), (9747570201/20000000000 : ℝ), (22177105318779/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1078426067/10000000000 : ℝ)|^6 ≤ (1381587667171/20000000000000 : ℝ)^5
        have hw : |(-1078426067/10000000000 : ℝ)|=(1078426067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5493999893/10000000000 : ℝ)|^6 ≤ (9747570201/20000000000 : ℝ)^5
        have hw : |(5493999893/10000000000 : ℝ)|=(5493999893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2539504869/5000000000 : ℝ)|^6 ≤ (22177105318779/50000000000000 : ℝ)^5
        have hw : |(2539504869/5000000000 : ℝ)|=(2539504869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1773_s0_1 (p : ℝ) (hpa : (6143/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (666717951/1250000000 : ℝ)*x 0 + (-80972277/625000000 : ℝ)*x 1 + (5079010171/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (666717951/1250000000 : ℝ)^6 ≤ (940737720481/2000000000000 : ℝ)^5 := by
    have hnat : (666717951 : ℕ)^6*2000000000000^5 ≤ 940737720481^5*1250000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      666717951 1250000000 940737720481 2000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (80972277/625000000 : ℝ)^6 ≤ (8608898783063/100000000000000 : ℝ)^5 := by
    have hnat : (80972277 : ℕ)^6*100000000000000^5 ≤ 8608898783063^5*625000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80972277 625000000 8608898783063 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5079010171/10000000000 : ℝ)^6 ≤ (5544276896893/12500000000000 : ℝ)^5 := by
    have hnat : (5079010171 : ℕ)^6*12500000000000^5 ≤ 5544276896893^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5079010171 10000000000 5544276896893 12500000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(666717951/1250000000 : ℝ), (-80972277/625000000 : ℝ), (5079010171/10000000000 : ℝ)] ![(940737720481/2000000000000 : ℝ), (8608898783063/100000000000000 : ℝ), (5544276896893/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(666717951/1250000000 : ℝ)|^6 ≤ (940737720481/2000000000000 : ℝ)^5
        have hw : |(666717951/1250000000 : ℝ)|=(666717951/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-80972277/625000000 : ℝ)|^6 ≤ (8608898783063/100000000000000 : ℝ)^5
        have hw : |(-80972277/625000000 : ℝ)|=(80972277/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5079010171/10000000000 : ℝ)|^6 ≤ (5544276896893/12500000000000 : ℝ)^5
        have hw : |(5079010171/10000000000 : ℝ)|=(5079010171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1773_s0_2 (p : ℝ) (hpa : (6143/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (2666871503/5000000000 : ℝ)*x 0 + (2539505303/5000000000 : ℝ)*x 1 + (-64777833/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2666871503/5000000000 : ℝ)^6 ≤ (23518439826697/50000000000000 : ℝ)^5 := by
    have hnat : (2666871503 : ℕ)^6*50000000000000^5 ≤ 23518439826697^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2666871503 5000000000 23518439826697 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2539505303/5000000000 : ℝ)^6 ≤ (4435421973369/10000000000000 : ℝ)^5 := by
    have hnat : (2539505303 : ℕ)^6*10000000000000^5 ≤ 4435421973369^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2539505303 5000000000 4435421973369 10000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (64777833/500000000 : ℝ)^6 ≤ (53805628757/625000000000 : ℝ)^5 := by
    have hnat : (64777833 : ℕ)^6*625000000000^5 ≤ 53805628757^5*500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64777833 500000000 53805628757 625000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2666871503/5000000000 : ℝ), (2539505303/5000000000 : ℝ), (-64777833/500000000 : ℝ)] ![(23518439826697/50000000000000 : ℝ), (4435421973369/10000000000000 : ℝ), (53805628757/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2666871503/5000000000 : ℝ)|^6 ≤ (23518439826697/50000000000000 : ℝ)^5
        have hw : |(2666871503/5000000000 : ℝ)|=(2666871503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2539505303/5000000000 : ℝ)|^6 ≤ (4435421973369/10000000000000 : ℝ)^5
        have hw : |(2539505303/5000000000 : ℝ)|=(2539505303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-64777833/500000000 : ℝ)|^6 ≤ (53805628757/625000000000 : ℝ)^5
        have hw : |(-64777833/500000000 : ℝ)|=(64777833/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1773_s0_3 (p : ℝ) (hpa : (6143/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (1985279109/5000000000 : ℝ)*x 0 + (101765583/312500000 : ℝ)*x 1 + (1188540917/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1985279109/5000000000 : ℝ)^6 ≤ (3300820302377/10000000000000 : ℝ)^5 := by
    have hnat : (1985279109 : ℕ)^6*10000000000000^5 ≤ 3300820302377^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1985279109 5000000000 3300820302377 10000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (101765583/312500000 : ℝ)^6 ≤ (41631404869/160000000000 : ℝ)^5 := by
    have hnat : (101765583 : ℕ)^6*160000000000^5 ≤ 41631404869^5*312500000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      101765583 312500000 41631404869 160000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1188540917/2500000000 : ℝ)^6 ≤ (40972168917697/100000000000000 : ℝ)^5 := by
    have hnat : (1188540917 : ℕ)^6*100000000000000^5 ≤ 40972168917697^5*2500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1188540917 2500000000 40972168917697 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1985279109/5000000000 : ℝ), (101765583/312500000 : ℝ), (1188540917/2500000000 : ℝ)] ![(3300820302377/10000000000000 : ℝ), (41631404869/160000000000 : ℝ), (40972168917697/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1985279109/5000000000 : ℝ)|^6 ≤ (3300820302377/10000000000000 : ℝ)^5
        have hw : |(1985279109/5000000000 : ℝ)|=(1985279109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(101765583/312500000 : ℝ)|^6 ≤ (41631404869/160000000000 : ℝ)^5
        have hw : |(101765583/312500000 : ℝ)|=(101765583/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1188540917/2500000000 : ℝ)|^6 ≤ (40972168917697/100000000000000 : ℝ)^5
        have hw : |(1188540917/2500000000 : ℝ)|=(1188540917/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1773_s0_4 (p : ℝ) (hpa : (6143/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (-215766683/2000000000 : ℝ)*x 0 + (5086791857/10000000000 : ℝ)*x 1 + (548604259/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215766683/2000000000 : ℝ)^6 ≤ (6911069611587/100000000000000 : ℝ)^5 := by
    have hnat : (215766683 : ℕ)^6*100000000000000^5 ≤ 6911069611587^5*2000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215766683 2000000000 6911069611587 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5086791857/10000000000 : ℝ)^6 ≤ (22217887592749/50000000000000 : ℝ)^5 := by
    have hnat : (5086791857 : ℕ)^6*50000000000000^5 ≤ 22217887592749^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5086791857 10000000000 22217887592749 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (548604259/1000000000 : ℝ)^6 ≤ (24326577596071/50000000000000 : ℝ)^5 := by
    have hnat : (548604259 : ℕ)^6*50000000000000^5 ≤ 24326577596071^5*1000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548604259 1000000000 24326577596071 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-215766683/2000000000 : ℝ), (5086791857/10000000000 : ℝ), (548604259/1000000000 : ℝ)] ![(6911069611587/100000000000000 : ℝ), (22217887592749/50000000000000 : ℝ), (24326577596071/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-215766683/2000000000 : ℝ)|^6 ≤ (6911069611587/100000000000000 : ℝ)^5
        have hw : |(-215766683/2000000000 : ℝ)|=(215766683/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5086791857/10000000000 : ℝ)|^6 ≤ (22217887592749/50000000000000 : ℝ)^5
        have hw : |(5086791857/10000000000 : ℝ)|=(5086791857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(548604259/1000000000 : ℝ)|^6 ≤ (24326577596071/50000000000000 : ℝ)^5
        have hw : |(548604259/1000000000 : ℝ)|=(548604259/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1773_s0_5 (p : ℝ) (hpa : (6143/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (2611700053/5000000000 : ℝ)*x 0 + (-177704729/2000000000 : ℝ)*x 1 + (109720857/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2611700053/5000000000 : ℝ)^6 ≤ (22935803362223/50000000000000 : ℝ)^5 := by
    have hnat : (2611700053 : ℕ)^6*50000000000000^5 ≤ 22935803362223^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2611700053 5000000000 22935803362223 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (177704729/2000000000 : ℝ)^6 ≤ (5475235294957/100000000000000 : ℝ)^5 := by
    have hnat : (177704729 : ℕ)^6*100000000000000^5 ≤ 5475235294957^5*2000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      177704729 2000000000 5475235294957 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (109720857/200000000 : ℝ)^6 ≤ (389225263673/800000000000 : ℝ)^5 := by
    have hnat : (109720857 : ℕ)^6*800000000000^5 ≤ 389225263673^5*200000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109720857 200000000 389225263673 800000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2611700053/5000000000 : ℝ), (-177704729/2000000000 : ℝ), (109720857/200000000 : ℝ)] ![(22935803362223/50000000000000 : ℝ), (5475235294957/100000000000000 : ℝ), (389225263673/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2611700053/5000000000 : ℝ)|^6 ≤ (22935803362223/50000000000000 : ℝ)^5
        have hw : |(2611700053/5000000000 : ℝ)|=(2611700053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-177704729/2000000000 : ℝ)|^6 ≤ (5475235294957/100000000000000 : ℝ)^5
        have hw : |(-177704729/2000000000 : ℝ)|=(177704729/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(109720857/200000000 : ℝ)|^6 ≤ (389225263673/800000000000 : ℝ)^5
        have hw : |(109720857/200000000 : ℝ)|=(109720857/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1773_s0_6 (p : ℝ) (hpa : (6143/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (5223400773/10000000000 : ℝ)*x 0 + (1097208511/2000000000 : ℝ)*x 1 + (-888523119/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5223400773/10000000000 : ℝ)^6 ≤ (22935806876757/50000000000000 : ℝ)^5 := by
    have hnat : (5223400773 : ℕ)^6*50000000000000^5 ≤ 22935806876757^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5223400773 10000000000 22935806876757 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1097208511/2000000000 : ℝ)^6 ≤ (3040822176229/6250000000000 : ℝ)^5 := by
    have hnat : (1097208511 : ℕ)^6*6250000000000^5 ≤ 3040822176229^5*2000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097208511 2000000000 3040822176229 6250000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (888523119/10000000000 : ℝ)^6 ≤ (2737615702697/50000000000000 : ℝ)^5 := by
    have hnat : (888523119 : ℕ)^6*50000000000000^5 ≤ 2737615702697^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      888523119 10000000000 2737615702697 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5223400773/10000000000 : ℝ), (1097208511/2000000000 : ℝ), (-888523119/10000000000 : ℝ)] ![(22935806876757/50000000000000 : ℝ), (3040822176229/6250000000000 : ℝ), (2737615702697/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5223400773/10000000000 : ℝ)|^6 ≤ (22935806876757/50000000000000 : ℝ)^5
        have hw : |(5223400773/10000000000 : ℝ)|=(5223400773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1097208511/2000000000 : ℝ)|^6 ≤ (3040822176229/6250000000000 : ℝ)^5
        have hw : |(1097208511/2000000000 : ℝ)|=(1097208511/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-888523119/10000000000 : ℝ)|^6 ≤ (2737615702697/50000000000000 : ℝ)^5
        have hw : |(-888523119/10000000000 : ℝ)|=(888523119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1773_s0_7 (p : ℝ) (hpa : (6143/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (248251847/625000000 : ℝ)*x 0 + (4726078811/10000000000 : ℝ)*x 1 + (657043437/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (248251847/625000000 : ℝ)^6 ≤ (4127860178831/12500000000000 : ℝ)^5 := by
    have hnat : (248251847 : ℕ)^6*12500000000000^5 ≤ 4127860178831^5*625000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      248251847 625000000 4127860178831 12500000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4726078811/10000000000 : ℝ)^6 ≤ (20340946418269/50000000000000 : ℝ)^5 := by
    have hnat : (4726078811 : ℕ)^6*50000000000000^5 ≤ 20340946418269^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4726078811 10000000000 20340946418269 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (657043437/2000000000 : ℝ)^6 ≤ (26295225718343/100000000000000 : ℝ)^5 := by
    have hnat : (657043437 : ℕ)^6*100000000000000^5 ≤ 26295225718343^5*2000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657043437 2000000000 26295225718343 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(248251847/625000000 : ℝ), (4726078811/10000000000 : ℝ), (657043437/2000000000 : ℝ)] ![(4127860178831/12500000000000 : ℝ), (20340946418269/50000000000000 : ℝ), (26295225718343/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(248251847/625000000 : ℝ)|^6 ≤ (4127860178831/12500000000000 : ℝ)^5
        have hw : |(248251847/625000000 : ℝ)|=(248251847/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4726078811/10000000000 : ℝ)|^6 ≤ (20340946418269/50000000000000 : ℝ)^5
        have hw : |(4726078811/10000000000 : ℝ)|=(4726078811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(657043437/2000000000 : ℝ)|^6 ≤ (26295225718343/100000000000000 : ℝ)^5
        have hw : |(657043437/2000000000 : ℝ)|=(657043437/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1773_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6143/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (230445923/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (9061/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9059/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (6143/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^6143 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^6143*1^1024 ≤ 0^1024*1^6143 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 6143 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 6143 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (6143/1024 : ℝ) ≤ (204983340161920429/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^6143 ≤ (204983340161920429/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^6143*50000000000000000000^1024 ≤ 204983340161920429^1024*5^6143 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 204983340161920429 50000000000000000000 6143 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (204983340161920429/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 6143 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (6143/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^6143 := by
      have hnat : (1 : ℕ)^1024*1^6143 ≤ 1^6143*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 6143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 6143 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50204983340161920429/50000000000000000000 : ℝ) ≤ (10006822246218939/10000000000000000 : ℝ) ^ (6143/1024 : ℝ) := by
    have hpowers : (50204983340161920429/50000000000000000000 : ℝ)^1024 ≤ (10006822246218939/10000000000000000 : ℝ)^6143 := by
      have hnat : (50204983340161920429 : ℕ)^1024*10000000000000000^6143 ≤ 10006822246218939^6143*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50204983340161920429 50000000000000000000 10006822246218939 10000000000000000 1024 6143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006822246218939/10000000000000000 : ℝ)) (X := (50204983340161920429/50000000000000000000 : ℝ)) (by norm_num) 6143 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25204983340161920429/25000000000000000000 : ℝ) ≤ (5006822246218939/5000000000000000 : ℝ) ^ (6143/1024 : ℝ) := by
    have hpowers : (25204983340161920429/25000000000000000000 : ℝ)^1024 ≤ (5006822246218939/5000000000000000 : ℝ)^6143 := by
      have hnat : (25204983340161920429 : ℕ)^1024*5000000000000000^6143 ≤ 5006822246218939^6143*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25204983340161920429 25000000000000000000 5006822246218939 5000000000000000 1024 6143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5006822246218939/5000000000000000 : ℝ)) (X := (25204983340161920429/25000000000000000000 : ℝ)) (by norm_num) 6143 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(6822246218939/4000000000000000 : ℝ)*(0 : ℝ))^(6143/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(6822246218939/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(204983340161920429/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(6822246218939/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(6143/1024 : ℝ) := by
    rw [show (1 : ℝ)+(6822246218939/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10006822246218939/10000000000000000 : ℝ) by norm_num, show 1+(204983340161920429/50000000000000000000 : ℝ)+(0 : ℝ)=(50204983340161920429/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(204983340161920429/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(6822246218939/4000000000000000 : ℝ)*(2/5 : ℝ))^(6143/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(6822246218939/4000000000000000 : ℝ)*(2/5 : ℝ)=(5006822246218939/5000000000000000 : ℝ) by norm_num, show 1+2*(204983340161920429/50000000000000000000 : ℝ)=(25204983340161920429/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(6822246218939/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6143/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (6822246218939/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(6822246218939/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6143/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (6822246218939/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(6822246218939/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6143/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (6822246218939/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1078426067/10000000000 : ℝ)*X 0 0+(5493999893/10000000000 : ℝ)*X 0 1+(2539504869/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1773_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((666717951/1250000000 : ℝ)*X 1 0+(-80972277/625000000 : ℝ)*X 1 1+(5079010171/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1773_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2666871503/5000000000 : ℝ)*X 2 0+(2539505303/5000000000 : ℝ)*X 2 1+(-64777833/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1773_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1985279109/5000000000 : ℝ)*X 0 0+(101765583/312500000 : ℝ)*X 0 1+(1188540917/2500000000 : ℝ)*X 0 2+(1985279109/5000000000 : ℝ)*X 1 0+(101765583/312500000 : ℝ)*X 1 1+(1188540917/2500000000 : ℝ)*X 1 2+(1985279109/5000000000 : ℝ)*X 2 0+(101765583/312500000 : ℝ)*X 2 1+(1188540917/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1773_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-215766683/2000000000 : ℝ)*X 0 0+(5086791857/10000000000 : ℝ)*X 0 1+(548604259/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1773_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2611700053/5000000000 : ℝ)*X 1 0+(-177704729/2000000000 : ℝ)*X 1 1+(109720857/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1773_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5223400773/10000000000 : ℝ)*X 2 0+(1097208511/2000000000 : ℝ)*X 2 1+(-888523119/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1773_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((248251847/625000000 : ℝ)*X 0 0+(4726078811/10000000000 : ℝ)*X 0 1+(657043437/2000000000 : ℝ)*X 0 2+(248251847/625000000 : ℝ)*X 1 0+(4726078811/10000000000 : ℝ)*X 1 1+(657043437/2000000000 : ℝ)*X 1 2+(248251847/625000000 : ℝ)*X 2 0+(4726078811/10000000000 : ℝ)*X 2 1+(657043437/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1773_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (236712354463277565893091/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (570529327/100000000000000 : ℝ)*(base19) + (36872091/25000000000000 : ℝ)*(base23) + (43620553/12500000000000 : ℝ)*(upper3) + (40287569/50000000000000 : ℝ)*(upper4) + (47506949/100000000000000 : ℝ)*(upper5) + (384676252815359/25000000000000 : ℝ)*(major0) + (384676252815359/25000000000000 : ℝ)*(major1) + (384676252815359/25000000000000 : ℝ)*(major2) + (1927761077479/80000000000 : ℝ)*(sp0) + (2409701664026257/100000000000000 : ℝ)*(sp1) + (120485104353361/5000000000000 : ℝ)*(sp2) + (667706176020833/100000000000000 : ℝ)*(sp3) + (443853417/50000000000000 : ℝ)*(sp4) + (1454138211/100000000000000 : ℝ)*(sp7) + (166926907539761/25000000000000 : ℝ)*(f.failure) + (37651597414931/1562500000000 : ℝ)*(f.sum) + (6325679415899/50000000000000000000000000000 : ℝ)*base66 + (571123250184101/100000000000000000000000000000 : ℝ)*base67 + (723467551984101/100000000000000000000000000000 : ℝ)*base69 + (44823223684101/100000000000000000000000000000 : ℝ)*base71 + (251200828634101/50000000000000000000000000000 : ℝ)*base73 + (874180313284101/100000000000000000000000000000 : ℝ)*base75 + (453928417284101/100000000000000000000000000000 : ℝ)*base77 + (712206833015899/100000000000000000000000000000 : ℝ)*base80 + (182623141934101/50000000000000000000000000000 : ℝ)*base81 + (17155597/2500000000000000000000 : ℝ)*base90 + (17155597/2500000000000000000000 : ℝ)*base92 + (17155597/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (512414649427818280385469/40000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (799021263/50000000000000 : ℝ)*(base19) + (396592339/20000000000000 : ℝ)*(base23) + (7823809/10000000000000 : ℝ)*(base32) + (300744023/100000000000000 : ℝ)*(upper3) + (325727697/100000000000000 : ℝ)*(upper5) + (1599361107024243/100000000000000 : ℝ)*(major0) + (1599361107024243/100000000000000 : ℝ)*(major1) + (1599361107024243/100000000000000 : ℝ)*(major2) + (11933379497/100000000000000 : ℝ)*(sp1) + (15014458033/100000000000000 : ℝ)*(sp2) + (100187718909023/4000000000000 : ℝ)*(sp4) + (1222988008449/48828125000 : ℝ)*(sp5) + (1252337987652923/50000000000000 : ℝ)*(sp6) + (694028736072607/100000000000000 : ℝ)*(sp7) + (347014407155349/50000000000000 : ℝ)*(f.failure) + (100187718909023/4000000000000 : ℝ)*(f.sum) + (337801870938177/200000000000000000000000000000 : ℝ)*base65 + (112771337938177/400000000000000000000000000000 : ℝ)*base67 + (1132564340738177/400000000000000000000000000000 : ℝ)*base69 + (1563655057938177/400000000000000000000000000000 : ℝ)*base71 + (57026852138177/200000000000000000000000000000 : ℝ)*base73 + (52566834061823/400000000000000000000000000000 : ℝ)*base76 + (1945613270738177/400000000000000000000000000000 : ℝ)*base77 + (2016958636738177/400000000000000000000000000000 : ℝ)*base79 + (292390990538177/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (54692127/5000000000000000000000 : ℝ)*base89 + (54692127/5000000000000000000000 : ℝ)*base91 + (54692127/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1773_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6143/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (230445923/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9061/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9059/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1773_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1773_s1_0 (p : ℝ) (hpa : (6143/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (-276969247/2500000000 : ℝ)*x 0 + (5326969037/10000000000 : ℝ)*x 1 + (326630087/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (276969247/2500000000 : ℝ)^6 ≤ (3567466094883/50000000000000 : ℝ)^5 := by
    have hnat : (276969247 : ℕ)^6*50000000000000^5 ≤ 3567466094883^5*2500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276969247 2500000000 3567466094883 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5326969037/10000000000 : ℝ)^6 ≤ (46965203335059/100000000000000 : ℝ)^5 := by
    have hnat : (5326969037 : ℕ)^6*100000000000000^5 ≤ 46965203335059^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5326969037 10000000000 46965203335059 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (326630087/625000000 : ℝ)^6 ≤ (45899864458599/100000000000000 : ℝ)^5 := by
    have hnat : (326630087 : ℕ)^6*100000000000000^5 ≤ 45899864458599^5*625000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326630087 625000000 45899864458599 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-276969247/2500000000 : ℝ), (5326969037/10000000000 : ℝ), (326630087/625000000 : ℝ)] ![(3567466094883/50000000000000 : ℝ), (46965203335059/100000000000000 : ℝ), (45899864458599/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-276969247/2500000000 : ℝ)|^6 ≤ (3567466094883/50000000000000 : ℝ)^5
        have hw : |(-276969247/2500000000 : ℝ)|=(276969247/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5326969037/10000000000 : ℝ)|^6 ≤ (46965203335059/100000000000000 : ℝ)^5
        have hw : |(5326969037/10000000000 : ℝ)|=(5326969037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(326630087/625000000 : ℝ)|^6 ≤ (45899864458599/100000000000000 : ℝ)^5
        have hw : |(326630087/625000000 : ℝ)|=(326630087/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1773_s1_1 (p : ℝ) (hpa : (6143/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (5289508213/10000000000 : ℝ)*x 0 + (-1158892083/10000000000 : ℝ)*x 1 + (653260163/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289508213/10000000000 : ℝ)^6 ≤ (46569154704967/100000000000000 : ℝ)^5 := by
    have hnat : (5289508213 : ℕ)^6*100000000000000^5 ≤ 46569154704967^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289508213 10000000000 46569154704967 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1158892083/10000000000 : ℝ)^6 ≤ (7530981750181/100000000000000 : ℝ)^5 := by
    have hnat : (1158892083 : ℕ)^6*100000000000000^5 ≤ 7530981750181^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1158892083 10000000000 7530981750181 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (653260163/1250000000 : ℝ)^6 ≤ (4589986353113/10000000000000 : ℝ)^5 := by
    have hnat : (653260163 : ℕ)^6*10000000000000^5 ≤ 4589986353113^5*1250000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      653260163 1250000000 4589986353113 10000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289508213/10000000000 : ℝ), (-1158892083/10000000000 : ℝ), (653260163/1250000000 : ℝ)] ![(46569154704967/100000000000000 : ℝ), (7530981750181/100000000000000 : ℝ), (4589986353113/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289508213/10000000000 : ℝ)|^6 ≤ (46569154704967/100000000000000 : ℝ)^5
        have hw : |(5289508213/10000000000 : ℝ)|=(5289508213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1158892083/10000000000 : ℝ)|^6 ≤ (7530981750181/100000000000000 : ℝ)^5
        have hw : |(-1158892083/10000000000 : ℝ)|=(1158892083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(653260163/1250000000 : ℝ)|^6 ≤ (4589986353113/10000000000000 : ℝ)^5
        have hw : |(653260163/1250000000 : ℝ)|=(653260163/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1773_s1_2 (p : ℝ) (hpa : (6143/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (1057901657/2000000000 : ℝ)*x 0 + (5226080981/10000000000 : ℝ)*x 1 + (-579446211/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057901657/2000000000 : ℝ)^6 ≤ (23284577732819/50000000000000 : ℝ)^5 := by
    have hnat : (1057901657 : ℕ)^6*50000000000000^5 ≤ 23284577732819^5*2000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057901657 2000000000 23284577732819 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5226080981/10000000000 : ℝ)^6 ≤ (45899860126899/100000000000000 : ℝ)^5 := by
    have hnat : (5226080981 : ℕ)^6*100000000000000^5 ≤ 45899860126899^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5226080981 10000000000 45899860126899 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (579446211/5000000000 : ℝ)^6 ≤ (470686524609/6250000000000 : ℝ)^5 := by
    have hnat : (579446211 : ℕ)^6*6250000000000^5 ≤ 470686524609^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      579446211 5000000000 470686524609 6250000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057901657/2000000000 : ℝ), (5226080981/10000000000 : ℝ), (-579446211/5000000000 : ℝ)] ![(23284577732819/50000000000000 : ℝ), (45899860126899/100000000000000 : ℝ), (470686524609/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057901657/2000000000 : ℝ)|^6 ≤ (23284577732819/50000000000000 : ℝ)^5
        have hw : |(1057901657/2000000000 : ℝ)|=(1057901657/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5226080981/10000000000 : ℝ)|^6 ≤ (45899860126899/100000000000000 : ℝ)^5
        have hw : |(5226080981/10000000000 : ℝ)|=(5226080981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-579446211/5000000000 : ℝ)|^6 ≤ (470686524609/6250000000000 : ℝ)^5
        have hw : |(-579446211/5000000000 : ℝ)|=(579446211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1773_s1_3 (p : ℝ) (hpa : (6143/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (4001196353/10000000000 : ℝ)*x 0 + (238825663/625000000 : ℝ)*x 1 + (4185306351/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4001196353/10000000000 : ℝ)^6 ≤ (6662816196771/20000000000000 : ℝ)^5 := by
    have hnat : (4001196353 : ℕ)^6*20000000000000^5 ≤ 6662816196771^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4001196353 10000000000 6662816196771 20000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (238825663/625000000 : ℝ)^6 ≤ (3940498646459/12500000000000 : ℝ)^5 := by
    have hnat : (238825663 : ℕ)^6*12500000000000^5 ≤ 3940498646459^5*625000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      238825663 625000000 3940498646459 12500000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4185306351/10000000000 : ℝ)^6 ≤ (17580964916623/50000000000000 : ℝ)^5 := by
    have hnat : (4185306351 : ℕ)^6*50000000000000^5 ≤ 17580964916623^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4185306351 10000000000 17580964916623 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4001196353/10000000000 : ℝ), (238825663/625000000 : ℝ), (4185306351/10000000000 : ℝ)] ![(6662816196771/20000000000000 : ℝ), (3940498646459/12500000000000 : ℝ), (17580964916623/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4001196353/10000000000 : ℝ)|^6 ≤ (6662816196771/20000000000000 : ℝ)^5
        have hw : |(4001196353/10000000000 : ℝ)|=(4001196353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(238825663/625000000 : ℝ)|^6 ≤ (3940498646459/12500000000000 : ℝ)^5
        have hw : |(238825663/625000000 : ℝ)|=(238825663/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4185306351/10000000000 : ℝ)|^6 ≤ (17580964916623/50000000000000 : ℝ)^5
        have hw : |(4185306351/10000000000 : ℝ)|=(4185306351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1773_s1_4 (p : ℝ) (hpa : (6143/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (-1107882133/10000000000 : ℝ)*x 0 + (653318733/1250000000 : ℝ)*x 1 + (2663249293/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1107882133/10000000000 : ℝ)^6 ≤ (7134971951483/100000000000000 : ℝ)^5 := by
    have hnat : (1107882133 : ℕ)^6*100000000000000^5 ≤ 7134971951483^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1107882133 10000000000 7134971951483 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (653318733/1250000000 : ℝ)^6 ≤ (45904801923389/100000000000000 : ℝ)^5 := by
    have hnat : (653318733 : ℕ)^6*100000000000000^5 ≤ 45904801923389^5*1250000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      653318733 1250000000 45904801923389 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2663249293/5000000000 : ℝ)^6 ≤ (46960226103559/100000000000000 : ℝ)^5 := by
    have hnat : (2663249293 : ℕ)^6*100000000000000^5 ≤ 46960226103559^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2663249293 5000000000 46960226103559 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1107882133/10000000000 : ℝ), (653318733/1250000000 : ℝ), (2663249293/5000000000 : ℝ)] ![(7134971951483/100000000000000 : ℝ), (45904801923389/100000000000000 : ℝ), (46960226103559/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1107882133/10000000000 : ℝ)|^6 ≤ (7134971951483/100000000000000 : ℝ)^5
        have hw : |(-1107882133/10000000000 : ℝ)|=(1107882133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(653318733/1250000000 : ℝ)|^6 ≤ (45904801923389/100000000000000 : ℝ)^5
        have hw : |(653318733/1250000000 : ℝ)|=(653318733/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2663249293/5000000000 : ℝ)|^6 ≤ (46960226103559/100000000000000 : ℝ)^5
        have hw : |(2663249293/5000000000 : ℝ)|=(2663249293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1773_s1_5 (p : ℝ) (hpa : (6143/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (5262590431/10000000000 : ℝ)*x 0 + (-529238447/5000000000 : ℝ)*x 1 + (5326496403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5262590431/10000000000 : ℝ)^6 ≤ (5785614582151/12500000000000 : ℝ)^5 := by
    have hnat : (5262590431 : ℕ)^6*12500000000000^5 ≤ 5785614582151^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262590431 10000000000 5785614582151 12500000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (529238447/5000000000 : ℝ)^6 ≤ (135097606293/2000000000000 : ℝ)^5 := by
    have hnat : (529238447 : ℕ)^6*2000000000000^5 ≤ 135097606293^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529238447 5000000000 135097606293 2000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5326496403/10000000000 : ℝ)^6 ≤ (23480101504137/50000000000000 : ℝ)^5 := by
    have hnat : (5326496403 : ℕ)^6*50000000000000^5 ≤ 23480101504137^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5326496403 10000000000 23480101504137 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5262590431/10000000000 : ℝ), (-529238447/5000000000 : ℝ), (5326496403/10000000000 : ℝ)] ![(5785614582151/12500000000000 : ℝ), (135097606293/2000000000000 : ℝ), (23480101504137/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5262590431/10000000000 : ℝ)|^6 ≤ (5785614582151/12500000000000 : ℝ)^5
        have hw : |(5262590431/10000000000 : ℝ)|=(5262590431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-529238447/5000000000 : ℝ)|^6 ≤ (135097606293/2000000000000 : ℝ)^5
        have hw : |(-529238447/5000000000 : ℝ)|=(529238447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5326496403/10000000000 : ℝ)|^6 ≤ (23480101504137/50000000000000 : ℝ)^5
        have hw : |(5326496403/10000000000 : ℝ)|=(5326496403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1773_s1_6 (p : ℝ) (hpa : (6143/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (1052518113/2000000000 : ℝ)*x 0 + (2663248213/5000000000 : ℝ)*x 1 + (-529238339/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1052518113/2000000000 : ℝ)^6 ≤ (46284918071457/100000000000000 : ℝ)^5 := by
    have hnat : (1052518113 : ℕ)^6*100000000000000^5 ≤ 46284918071457^5*2000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052518113 2000000000 46284918071457 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2663248213/5000000000 : ℝ)^6 ≤ (9392040650321/20000000000000 : ℝ)^5 := by
    have hnat : (2663248213 : ℕ)^6*20000000000000^5 ≤ 9392040650321^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2663248213 5000000000 9392040650321 20000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (529238339/5000000000 : ℝ)^6 ≤ (3377439330257/50000000000000 : ℝ)^5 := by
    have hnat : (529238339 : ℕ)^6*50000000000000^5 ≤ 3377439330257^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529238339 5000000000 3377439330257 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1052518113/2000000000 : ℝ), (2663248213/5000000000 : ℝ), (-529238339/5000000000 : ℝ)] ![(46284918071457/100000000000000 : ℝ), (9392040650321/20000000000000 : ℝ), (3377439330257/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1052518113/2000000000 : ℝ)|^6 ≤ (46284918071457/100000000000000 : ℝ)^5
        have hw : |(1052518113/2000000000 : ℝ)|=(1052518113/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2663248213/5000000000 : ℝ)|^6 ≤ (9392040650321/20000000000000 : ℝ)^5
        have hw : |(2663248213/5000000000 : ℝ)|=(2663248213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-529238339/5000000000 : ℝ)|^6 ≤ (3377439330257/50000000000000 : ℝ)^5
        have hw : |(-529238339/5000000000 : ℝ)|=(529238339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1773_s1_7 (p : ℝ) (hpa : (6143/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (4001216009/10000000000 : ℝ)*x 0 + (836722619/2000000000 : ℝ)*x 1 + (3822914983/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4001216009/10000000000 : ℝ)^6 ≤ (33314277371687/100000000000000 : ℝ)^5 := by
    have hnat : (4001216009 : ℕ)^6*100000000000000^5 ≤ 33314277371687^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4001216009 10000000000 33314277371687 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (836722619/2000000000 : ℝ)^6 ≤ (35144859902971/100000000000000 : ℝ)^5 := by
    have hnat : (836722619 : ℕ)^6*100000000000000^5 ≤ 35144859902971^5*2000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      836722619 2000000000 35144859902971 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3822914983/10000000000 : ℝ)^6 ≤ (3154086270231/10000000000000 : ℝ)^5 := by
    have hnat : (3822914983 : ℕ)^6*10000000000000^5 ≤ 3154086270231^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3822914983 10000000000 3154086270231 10000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4001216009/10000000000 : ℝ), (836722619/2000000000 : ℝ), (3822914983/10000000000 : ℝ)] ![(33314277371687/100000000000000 : ℝ), (35144859902971/100000000000000 : ℝ), (3154086270231/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4001216009/10000000000 : ℝ)|^6 ≤ (33314277371687/100000000000000 : ℝ)^5
        have hw : |(4001216009/10000000000 : ℝ)|=(4001216009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(836722619/2000000000 : ℝ)|^6 ≤ (35144859902971/100000000000000 : ℝ)^5
        have hw : |(836722619/2000000000 : ℝ)|=(836722619/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3822914983/10000000000 : ℝ)|^6 ≤ (3154086270231/10000000000000 : ℝ)^5
        have hw : |(3822914983/10000000000 : ℝ)|=(3822914983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1773_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6143/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (230445923/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9059/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9061/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (12301/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14509/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9059/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9061/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9059/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9061/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9059/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9061/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9059/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9061/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9059/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9061/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9059/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9061/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9061/100000 : ℝ) ^ (6143/1024 : ℝ) ≤ (1733505351861/3125000000000000000 : ℝ) := by
    have hpowers : (9061/100000 : ℝ)^6143 ≤ (1733505351861/3125000000000000000 : ℝ)^1024 := by
      have hnat : (9061 : ℕ)^6143*3125000000000000000^1024 ≤ 1733505351861^1024*100000^6143 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9061 100000 1733505351861 3125000000000000000 6143 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9061/100000 : ℝ)) (X := (1733505351861/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 6143 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (9059/50000 : ℝ) ^ (6143/1024 : ℝ) ≤ (3543121404618617/100000000000000000000 : ℝ) := by
    have hpowers : (9059/50000 : ℝ)^6143 ≤ (3543121404618617/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9059 : ℕ)^6143*100000000000000000000^1024 ≤ 3543121404618617^1024*50000^6143 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9059 50000 3543121404618617 100000000000000000000 6143 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9059/50000 : ℝ)) (X := (3543121404618617/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 6143 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562501733505351861/1562500000000000000 : ℝ) ≤ (5000000924686263/5000000000000000 : ℝ) ^ (6143/1024 : ℝ) := by
    have hpowers : (1562501733505351861/1562500000000000000 : ℝ)^1024 ≤ (5000000924686263/5000000000000000 : ℝ)^6143 := by
      have hnat : (1562501733505351861 : ℕ)^1024*5000000000000000^6143 ≤ 5000000924686263^6143*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562501733505351861 1562500000000000000 5000000924686263 5000000000000000 1024 6143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000924686263/5000000000000000 : ℝ)) (X := (1562501733505351861/1562500000000000000 : ℝ)) (by norm_num) 6143 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100003598593575878169/100000000000000000000 : ℝ) ≤ (10000059985423603/10000000000000000 : ℝ) ^ (6143/1024 : ℝ) := by
    have hpowers : (100003598593575878169/100000000000000000000 : ℝ)^1024 ≤ (10000059985423603/10000000000000000 : ℝ)^6143 := by
      have hnat : (100003598593575878169 : ℕ)^1024*10000000000000000^6143 ≤ 10000059985423603^6143*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100003598593575878169 100000000000000000000 10000059985423603 10000000000000000 1024 6143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000059985423603/10000000000000000 : ℝ)) (X := (100003598593575878169/100000000000000000000 : ℝ)) (by norm_num) 6143 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50003543121404618617/50000000000000000000 : ℝ) ≤ (250002953036867/250000000000000 : ℝ) ^ (6143/1024 : ℝ) := by
    have hpowers : (50003543121404618617/50000000000000000000 : ℝ)^1024 ≤ (250002953036867/250000000000000 : ℝ)^6143 := by
      have hnat : (50003543121404618617 : ℕ)^1024*250000000000000^6143 ≤ 250002953036867^6143*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50003543121404618617 50000000000000000000 250002953036867 250000000000000 1024 6143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250002953036867/250000000000000 : ℝ)) (X := (50003543121404618617/50000000000000000000 : ℝ)) (by norm_num) 6143 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1733505351861/3125000000000000000 : ℝ) ≤ ((22642240802062337647/22642500000000000000 : ℝ)+2*(58136051077/905700000000000 : ℝ)*(9061/100000 : ℝ))^(6143/1024 : ℝ) := by
    rw [show (22642240802062337647/22642500000000000000 : ℝ)+2*(58136051077/905700000000000 : ℝ)*(9061/100000 : ℝ)=(5000000924686263/5000000000000000 : ℝ) by norm_num, show 1+2*(1733505351861/3125000000000000000 : ℝ)=(1562501733505351861/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3543121404618617/100000000000000000000 : ℝ)+(1733505351861/3125000000000000000 : ℝ) ≤ ((22642240802062337647/22642500000000000000 : ℝ)+(58136051077/905700000000000 : ℝ)*((9059/50000 : ℝ)+(9061/100000 : ℝ)))^(6143/1024 : ℝ) := by
    rw [show (22642240802062337647/22642500000000000000 : ℝ)+(58136051077/905700000000000 : ℝ)*((9059/50000 : ℝ)+(9061/100000 : ℝ))=(10000059985423603/10000000000000000 : ℝ) by norm_num, show 1+(3543121404618617/100000000000000000000 : ℝ)+(1733505351861/3125000000000000000 : ℝ)=(100003598593575878169/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3543121404618617/100000000000000000000 : ℝ) ≤ ((22642240802062337647/22642500000000000000 : ℝ)+2*(58136051077/905700000000000 : ℝ)*(9059/50000 : ℝ))^(6143/1024 : ℝ) := by
    rw [show (22642240802062337647/22642500000000000000 : ℝ)+2*(58136051077/905700000000000 : ℝ)*(9059/50000 : ℝ)=(250002953036867/250000000000000 : ℝ) by norm_num, show 1+2*(3543121404618617/100000000000000000000 : ℝ)=(50003543121404618617/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (22642240802062337647/22642500000000000000 : ℝ)*(X 1 0+X 2 0)+(58136051077/905700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6143/1024 : ℝ)) (lo := (9061/100000 : ℝ)) (hi := (9059/50000 : ℝ)) (c := (22642240802062337647/22642500000000000000 : ℝ)) (alpha := (58136051077/905700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (22642240802062337647/22642500000000000000 : ℝ)*(X 0 1+X 2 1)+(58136051077/905700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6143/1024 : ℝ)) (lo := (9061/100000 : ℝ)) (hi := (9059/50000 : ℝ)) (c := (22642240802062337647/22642500000000000000 : ℝ)) (alpha := (58136051077/905700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (22642240802062337647/22642500000000000000 : ℝ)*(X 0 2+X 1 2)+(58136051077/905700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6143/1024 : ℝ)) (lo := (9061/100000 : ℝ)) (hi := (9059/50000 : ℝ)) (c := (22642240802062337647/22642500000000000000 : ℝ)) (alpha := (58136051077/905700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-276969247/2500000000 : ℝ)*X 0 0+(5326969037/10000000000 : ℝ)*X 0 1+(326630087/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1773_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5289508213/10000000000 : ℝ)*X 1 0+(-1158892083/10000000000 : ℝ)*X 1 1+(653260163/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1773_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1057901657/2000000000 : ℝ)*X 2 0+(5226080981/10000000000 : ℝ)*X 2 1+(-579446211/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1773_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4001196353/10000000000 : ℝ)*X 0 0+(238825663/625000000 : ℝ)*X 0 1+(4185306351/10000000000 : ℝ)*X 0 2+(4001196353/10000000000 : ℝ)*X 1 0+(238825663/625000000 : ℝ)*X 1 1+(4185306351/10000000000 : ℝ)*X 1 2+(4001196353/10000000000 : ℝ)*X 2 0+(238825663/625000000 : ℝ)*X 2 1+(4185306351/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1773_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1107882133/10000000000 : ℝ)*X 0 0+(653318733/1250000000 : ℝ)*X 0 1+(2663249293/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1773_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5262590431/10000000000 : ℝ)*X 1 0+(-529238447/5000000000 : ℝ)*X 1 1+(5326496403/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1773_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1052518113/2000000000 : ℝ)*X 2 0+(2663248213/5000000000 : ℝ)*X 2 1+(-529238339/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1773_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4001216009/10000000000 : ℝ)*X 0 0+(836722619/2000000000 : ℝ)*X 0 1+(3822914983/10000000000 : ℝ)*X 0 2+(4001216009/10000000000 : ℝ)*X 1 0+(836722619/2000000000 : ℝ)*X 1 1+(3822914983/10000000000 : ℝ)*X 1 2+(4001216009/10000000000 : ℝ)*X 2 0+(836722619/2000000000 : ℝ)*X 2 1+(3822914983/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1773_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2627806971420447698061867447/188687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2286145357/100000000000000 : ℝ)*(base19) + (1309121263/50000000000000 : ℝ)*(base23) + (68063/2000000000000 : ℝ)*(lower2) + (57229543/10000000000000 : ℝ)*(upper3) + (53849407/50000000000000 : ℝ)*(lower4) + (6329356091131599/100000000000000 : ℝ)*(major0) + (6329356091131599/100000000000000 : ℝ)*(major1) + (6329356091131599/100000000000000 : ℝ)*(major2) + (991209979417691/10000000000000 : ℝ)*(sp0) + (619508782193787/6250000000000 : ℝ)*(sp1) + (309754380718857/3125000000000 : ℝ)*(sp2) + (343318217557369/12500000000000 : ℝ)*(sp3) + (43007069039/100000000000000 : ℝ)*(sp4) + (1448520793/6250000000000 : ℝ)*(sp7) + (1373284458395821/50000000000000 : ℝ)*(f.failure) + (2478035700311487/25000000000000 : ℝ)*(f.sum) + (50318925932923/7547500000000000000000000000 : ℝ)*base65 + (12446754470092860851/754750000000000000000000000000000 : ℝ)*base67 + (13111766591024860851/754750000000000000000000000000000 : ℝ)*base69 + (25179645244033360851/754750000000000000000000000000000 : ℝ)*base71 + (50549289885241/15095000000000000000000000000 : ℝ)*base73 + (13122639222153360851/754750000000000000000000000000000 : ℝ)*base75 + (1633758541250639149/754750000000000000000000000000000 : ℝ)*base78 + (9178775594347360851/754750000000000000000000000000000 : ℝ)*base79 + (44696709498881/15095000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/50000000000000 : ℝ)*base87 + (119687783/5000000000000000000000 : ℝ)*base89 + (119687783/5000000000000000000000 : ℝ)*base91 + (119687783/5000000000000000000000 : ℝ)*base93 + (1/50000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (724245814535200192649464979/94343750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (200869377/50000000000000 : ℝ)*(base19) + (183945161/50000000000000 : ℝ)*(lower2) + (126375213/25000000000000 : ℝ)*(lower3) + (4479729/20000000000000 : ℝ)*(lower4) + (14416877/3125000000000 : ℝ)*(lower5) + (3194468328737143/50000000000000 : ℝ)*(major0) + (3194468328737143/50000000000000 : ℝ)*(major1) + (3194468328737143/50000000000000 : ℝ)*(major2) + (148474180843/100000000000000 : ℝ)*(sp0) + (567924621/6250000000000 : ℝ)*(sp3) + (2501325300138573/25000000000000 : ℝ)*(sp4) + (500272463649819/5000000000000 : ℝ)*(sp5) + (5002724837367567/50000000000000 : ℝ)*(sp6) + (2772414297530501/100000000000000 : ℝ)*(sp7) + (2772423384324437/100000000000000 : ℝ)*(f.failure) + (5002724837367567/50000000000000 : ℝ)*(f.sum) + (108250000684877/45285000000000000000000000000 : ℝ)*base65 + (20777244200852852479/1132125000000000000000000000000000 : ℝ)*base68 + (11229253654244022521/1132125000000000000000000000000000 : ℝ)*base69 + (21109809936085272521/1132125000000000000000000000000000 : ℝ)*base71 + (149142683118433/45285000000000000000000000000 : ℝ)*base74 + (1829653867668522521/1132125000000000000000000000000000 : ℝ)*base75 + (10946983146959022521/1132125000000000000000000000000000 : ℝ)*base77 + (4615349765211522521/1132125000000000000000000000000000 : ℝ)*base79 + (174548193028427/45285000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (15920351/10000000000000000000000 : ℝ)*base89 + (15920351/10000000000000000000000 : ℝ)*base91 + (15920351/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1773_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6143/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (230445923/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9059/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9061/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (12301/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14509/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1773_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1773_s2_0 (p : ℝ) (hpa : (6143/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (-1108197607/10000000000 : ℝ)*x 0 + (1064716139/2000000000 : ℝ)*x 1 + (2614623601/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1108197607/10000000000 : ℝ)^6 ≤ (89217625951/1250000000000 : ℝ)^5 := by
    have hnat : (1108197607 : ℕ)^6*1250000000000^5 ≤ 89217625951^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1108197607 10000000000 89217625951 1250000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1064716139/2000000000 : ℝ)^6 ≤ (23464678824793/50000000000000 : ℝ)^5 := by
    have hnat : (1064716139 : ℕ)^6*50000000000000^5 ≤ 23464678824793^5*2000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064716139 2000000000 23464678824793 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2614623601/5000000000 : ℝ)^6 ≤ (459332322629/1000000000000 : ℝ)^5 := by
    have hnat : (2614623601 : ℕ)^6*1000000000000^5 ≤ 459332322629^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614623601 5000000000 459332322629 1000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1108197607/10000000000 : ℝ), (1064716139/2000000000 : ℝ), (2614623601/5000000000 : ℝ)] ![(89217625951/1250000000000 : ℝ), (23464678824793/50000000000000 : ℝ), (459332322629/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1108197607/10000000000 : ℝ)|^6 ≤ (89217625951/1250000000000 : ℝ)^5
        have hw : |(-1108197607/10000000000 : ℝ)|=(1108197607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1064716139/2000000000 : ℝ)|^6 ≤ (23464678824793/50000000000000 : ℝ)^5
        have hw : |(1064716139/2000000000 : ℝ)|=(1064716139/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2614623601/5000000000 : ℝ)|^6 ≤ (459332322629/1000000000000 : ℝ)^5
        have hw : |(2614623601/5000000000 : ℝ)|=(2614623601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1773_s2_1 (p : ℝ) (hpa : (6143/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (1322146079/2500000000 : ℝ)*x 0 + (-288965947/2500000000 : ℝ)*x 1 + (1307311819/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322146079/2500000000 : ℝ)^6 ≤ (11639848505111/25000000000000 : ℝ)^5 := by
    have hnat : (1322146079 : ℕ)^6*25000000000000^5 ≤ 11639848505111^5*2500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322146079 2500000000 11639848505111 25000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (288965947/2500000000 : ℝ)^6 ≤ (7507372921243/100000000000000 : ℝ)^5 := by
    have hnat : (288965947 : ℕ)^6*100000000000000^5 ≤ 7507372921243^5*2500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      288965947 2500000000 7507372921243 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1307311819/2500000000 : ℝ)^6 ≤ (45933233042911/100000000000000 : ℝ)^5 := by
    have hnat : (1307311819 : ℕ)^6*100000000000000^5 ≤ 45933233042911^5*2500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307311819 2500000000 45933233042911 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322146079/2500000000 : ℝ), (-288965947/2500000000 : ℝ), (1307311819/2500000000 : ℝ)] ![(11639848505111/25000000000000 : ℝ), (7507372921243/100000000000000 : ℝ), (45933233042911/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322146079/2500000000 : ℝ)|^6 ≤ (11639848505111/25000000000000 : ℝ)^5
        have hw : |(1322146079/2500000000 : ℝ)|=(1322146079/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-288965947/2500000000 : ℝ)|^6 ≤ (7507372921243/100000000000000 : ℝ)^5
        have hw : |(-288965947/2500000000 : ℝ)|=(288965947/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1307311819/2500000000 : ℝ)|^6 ≤ (45933233042911/100000000000000 : ℝ)^5
        have hw : |(1307311819/2500000000 : ℝ)|=(1307311819/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1773_s2_2 (p : ℝ) (hpa : (6143/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (5288584793/10000000000 : ℝ)*x 0 + (5229246863/10000000000 : ℝ)*x 1 + (-11558637/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288584793/10000000000 : ℝ)^6 ≤ (46559399059713/100000000000000 : ℝ)^5 := by
    have hnat : (5288584793 : ℕ)^6*100000000000000^5 ≤ 46559399059713^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288584793 10000000000 46559399059713 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5229246863/10000000000 : ℝ)^6 ≤ (9186645737921/20000000000000 : ℝ)^5 := by
    have hnat : (5229246863 : ℕ)^6*20000000000000^5 ≤ 9186645737921^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229246863 10000000000 9186645737921 20000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (11558637/100000000 : ℝ)^6 ≤ (7507372235367/100000000000000 : ℝ)^5 := by
    have hnat : (11558637 : ℕ)^6*100000000000000^5 ≤ 7507372235367^5*100000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11558637 100000000 7507372235367 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288584793/10000000000 : ℝ), (5229246863/10000000000 : ℝ), (-11558637/100000000 : ℝ)] ![(46559399059713/100000000000000 : ℝ), (9186645737921/20000000000000 : ℝ), (7507372235367/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288584793/10000000000 : ℝ)|^6 ≤ (46559399059713/100000000000000 : ℝ)^5
        have hw : |(5288584793/10000000000 : ℝ)|=(5288584793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5229246863/10000000000 : ℝ)|^6 ≤ (9186645737921/20000000000000 : ℝ)^5
        have hw : |(5229246863/10000000000 : ℝ)|=(5229246863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-11558637/100000000 : ℝ)|^6 ≤ (7507372235367/100000000000000 : ℝ)^5
        have hw : |(-11558637/100000000 : ℝ)|=(11558637/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1773_s2_3 (p : ℝ) (hpa : (6143/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (4001437699/10000000000 : ℝ)*x 0 + (239563841/625000000 : ℝ)*x 1 + (2086731211/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4001437699/10000000000 : ℝ)^6 ≤ (8329123085813/25000000000000 : ℝ)^5 := by
    have hnat : (4001437699 : ℕ)^6*25000000000000^5 ≤ 8329123085813^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4001437699 10000000000 8329123085813 25000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (239563841/625000000 : ℝ)^6 ≤ (31640948973769/100000000000000 : ℝ)^5 := by
    have hnat : (239563841 : ℕ)^6*100000000000000^5 ≤ 31640948973769^5*625000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      239563841 625000000 31640948973769 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2086731211/5000000000 : ℝ)^6 ≤ (17521279327403/50000000000000 : ℝ)^5 := by
    have hnat : (2086731211 : ℕ)^6*50000000000000^5 ≤ 17521279327403^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086731211 5000000000 17521279327403 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4001437699/10000000000 : ℝ), (239563841/625000000 : ℝ), (2086731211/5000000000 : ℝ)] ![(8329123085813/25000000000000 : ℝ), (31640948973769/100000000000000 : ℝ), (17521279327403/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4001437699/10000000000 : ℝ)|^6 ≤ (8329123085813/25000000000000 : ℝ)^5
        have hw : |(4001437699/10000000000 : ℝ)|=(4001437699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(239563841/625000000 : ℝ)|^6 ≤ (31640948973769/100000000000000 : ℝ)^5
        have hw : |(239563841/625000000 : ℝ)|=(239563841/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2086731211/5000000000 : ℝ)|^6 ≤ (17521279327403/50000000000000 : ℝ)^5
        have hw : |(2086731211/5000000000 : ℝ)|=(2086731211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1773_s2_4 (p : ℝ) (hpa : (6143/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (-221640443/2000000000 : ℝ)*x 0 + (5229658611/10000000000 : ℝ)*x 1 + (5323167381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (221640443/2000000000 : ℝ)^6 ≤ (35687228449/500000000000 : ℝ)^5 := by
    have hnat : (221640443 : ℕ)^6*500000000000^5 ≤ 35687228449^5*2000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221640443 2000000000 35687228449 500000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5229658611/10000000000 : ℝ)^6 ≤ (2871098052009/6250000000000 : ℝ)^5 := by
    have hnat : (5229658611 : ℕ)^6*6250000000000^5 ≤ 2871098052009^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229658611 10000000000 2871098052009 6250000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5323167381/10000000000 : ℝ)^6 ≤ (11731246365571/25000000000000 : ℝ)^5 := by
    have hnat : (5323167381 : ℕ)^6*25000000000000^5 ≤ 11731246365571^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5323167381 10000000000 11731246365571 25000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-221640443/2000000000 : ℝ), (5229658611/10000000000 : ℝ), (5323167381/10000000000 : ℝ)] ![(35687228449/500000000000 : ℝ), (2871098052009/6250000000000 : ℝ), (11731246365571/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-221640443/2000000000 : ℝ)|^6 ≤ (35687228449/500000000000 : ℝ)^5
        have hw : |(-221640443/2000000000 : ℝ)|=(221640443/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5229658611/10000000000 : ℝ)|^6 ≤ (2871098052009/6250000000000 : ℝ)^5
        have hw : |(5229658611/10000000000 : ℝ)|=(5229658611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5323167381/10000000000 : ℝ)|^6 ≤ (11731246365571/25000000000000 : ℝ)^5
        have hw : |(5323167381/10000000000 : ℝ)|=(5323167381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1773_s2_5 (p : ℝ) (hpa : (6143/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (164481597/312500000 : ℝ)*x 0 + (-10619433/100000000 : ℝ)*x 1 + (5323167513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (164481597/312500000 : ℝ)^6 ≤ (46293578256297/100000000000000 : ℝ)^5 := by
    have hnat : (164481597 : ℕ)^6*100000000000000^5 ≤ 46293578256297^5*312500000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164481597 312500000 46293578256297 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (10619433/100000000 : ℝ)^6 ≤ (6781434869779/100000000000000 : ℝ)^5 := by
    have hnat : (10619433 : ℕ)^6*100000000000000^5 ≤ 6781434869779^5*100000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10619433 100000000 6781434869779 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5323167513/10000000000 : ℝ)^6 ≤ (46924986858617/100000000000000 : ℝ)^5 := by
    have hnat : (5323167513 : ℕ)^6*100000000000000^5 ≤ 46924986858617^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5323167513 10000000000 46924986858617 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(164481597/312500000 : ℝ), (-10619433/100000000 : ℝ), (5323167513/10000000000 : ℝ)] ![(46293578256297/100000000000000 : ℝ), (6781434869779/100000000000000 : ℝ), (46924986858617/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(164481597/312500000 : ℝ)|^6 ≤ (46293578256297/100000000000000 : ℝ)^5
        have hw : |(164481597/312500000 : ℝ)|=(164481597/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-10619433/100000000 : ℝ)|^6 ≤ (6781434869779/100000000000000 : ℝ)^5
        have hw : |(-10619433/100000000 : ℝ)|=(10619433/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5323167513/10000000000 : ℝ)|^6 ≤ (46924986858617/100000000000000 : ℝ)^5
        have hw : |(5323167513/10000000000 : ℝ)|=(5323167513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1773_s2_6 (p : ℝ) (hpa : (6143/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (1315852631/2500000000 : ℝ)*x 0 + (2661584013/5000000000 : ℝ)*x 1 + (-1061943391/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1315852631/2500000000 : ℝ)^6 ≤ (5786696516841/12500000000000 : ℝ)^5 := by
    have hnat : (1315852631 : ℕ)^6*12500000000000^5 ≤ 5786696516841^5*2500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315852631 2500000000 5786696516841 12500000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2661584013/5000000000 : ℝ)^6 ≤ (23462496142639/50000000000000 : ℝ)^5 := by
    have hnat : (2661584013 : ℕ)^6*50000000000000^5 ≤ 23462496142639^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2661584013 5000000000 23462496142639 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1061943391/10000000000 : ℝ)^6 ≤ (1695358891779/25000000000000 : ℝ)^5 := by
    have hnat : (1061943391 : ℕ)^6*25000000000000^5 ≤ 1695358891779^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061943391 10000000000 1695358891779 25000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1315852631/2500000000 : ℝ), (2661584013/5000000000 : ℝ), (-1061943391/10000000000 : ℝ)] ![(5786696516841/12500000000000 : ℝ), (23462496142639/50000000000000 : ℝ), (1695358891779/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1315852631/2500000000 : ℝ)|^6 ≤ (5786696516841/12500000000000 : ℝ)^5
        have hw : |(1315852631/2500000000 : ℝ)|=(1315852631/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2661584013/5000000000 : ℝ)|^6 ≤ (23462496142639/50000000000000 : ℝ)^5
        have hw : |(2661584013/5000000000 : ℝ)|=(2661584013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1061943391/10000000000 : ℝ)|^6 ≤ (1695358891779/25000000000000 : ℝ)^5
        have hw : |(-1061943391/10000000000 : ℝ)|=(1061943391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1773_s2_7 (p : ℝ) (hpa : (6143/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (800291521/2000000000 : ℝ)*x 0 + (4171979973/10000000000 : ℝ)*x 1 + (1917254581/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (800291521/2000000000 : ℝ)^6 ≤ (16658345615647/50000000000000 : ℝ)^5 := by
    have hnat : (800291521 : ℕ)^6*50000000000000^5 ≤ 16658345615647^5*2000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      800291521 2000000000 16658345615647 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4171979973/10000000000 : ℝ)^6 ≤ (8756905572771/25000000000000 : ℝ)^5 := by
    have hnat : (4171979973 : ℕ)^6*25000000000000^5 ≤ 8756905572771^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171979973 10000000000 8756905572771 25000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1917254581/5000000000 : ℝ)^6 ≤ (1582784323089/5000000000000 : ℝ)^5 := by
    have hnat : (1917254581 : ℕ)^6*5000000000000^5 ≤ 1582784323089^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1917254581 5000000000 1582784323089 5000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(800291521/2000000000 : ℝ), (4171979973/10000000000 : ℝ), (1917254581/5000000000 : ℝ)] ![(16658345615647/50000000000000 : ℝ), (8756905572771/25000000000000 : ℝ), (1582784323089/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(800291521/2000000000 : ℝ)|^6 ≤ (16658345615647/50000000000000 : ℝ)^5
        have hw : |(800291521/2000000000 : ℝ)|=(800291521/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4171979973/10000000000 : ℝ)|^6 ≤ (8756905572771/25000000000000 : ℝ)^5
        have hw : |(4171979973/10000000000 : ℝ)|=(4171979973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1917254581/5000000000 : ℝ)|^6 ≤ (1582784323089/5000000000000 : ℝ)^5
        have hw : |(1917254581/5000000000 : ℝ)|=(1917254581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1773_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6143/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (230445923/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14509/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (12301/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (12371/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3609/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14509/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (12301/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14509/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (12301/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14509/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (12301/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14509/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (12301/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14509/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (12301/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14509/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (12301/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (12301/100000 : ℝ) ^ (6143/1024 : ℝ) ≤ (2169757800603/625000000000000000 : ℝ) := by
    have hpowers : (12301/100000 : ℝ)^6143 ≤ (2169757800603/625000000000000000 : ℝ)^1024 := by
      have hnat : (12301 : ℕ)^6143*625000000000000000^1024 ≤ 2169757800603^1024*100000^6143 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12301 100000 2169757800603 625000000000000000 6143 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (12301/100000 : ℝ)) (X := (2169757800603/625000000000000000 : ℝ)) (by norm_num) (by norm_num) 6143 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14509/100000 : ℝ) ^ (6143/1024 : ℝ) ≤ (467319175686243/50000000000000000000 : ℝ) := by
    have hpowers : (14509/100000 : ℝ)^6143 ≤ (467319175686243/50000000000000000000 : ℝ)^1024 := by
      have hnat : (14509 : ℕ)^6143*50000000000000000000^1024 ≤ 467319175686243^1024*100000^6143 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14509 100000 467319175686243 50000000000000000000 6143 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14509/100000 : ℝ)) (X := (467319175686243/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 6143 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (312502169757800603/312500000000000000 : ℝ) ≤ (5000005786945949/5000000000000000 : ℝ) ^ (6143/1024 : ℝ) := by
    have hpowers : (312502169757800603/312500000000000000 : ℝ)^1024 ≤ (5000005786945949/5000000000000000 : ℝ)^6143 := by
      have hnat : (312502169757800603 : ℕ)^1024*5000000000000000^6143 ≤ 5000005786945949^6143*312500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        312502169757800603 312500000000000000 5000005786945949 5000000000000000 1024 6143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000005786945949/5000000000000000 : ℝ)) (X := (312502169757800603/312500000000000000 : ℝ)) (by norm_num) 6143 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50000640899799734483/50000000000000000000 : ℝ) ≤ (1250002670836277/1250000000000000 : ℝ) ^ (6143/1024 : ℝ) := by
    have hpowers : (50000640899799734483/50000000000000000000 : ℝ)^1024 ≤ (1250002670836277/1250000000000000 : ℝ)^6143 := by
      have hnat : (50000640899799734483 : ℕ)^1024*1250000000000000^6143 ≤ 1250002670836277^6143*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000640899799734483 50000000000000000000 1250002670836277 1250000000000000 1024 6143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250002670836277/1250000000000000 : ℝ)) (X := (50000640899799734483/50000000000000000000 : ℝ)) (by norm_num) 6143 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25000467319175686243/25000000000000000000 : ℝ) ≤ (5000015579744267/5000000000000000 : ℝ) ^ (6143/1024 : ℝ) := by
    have hpowers : (25000467319175686243/25000000000000000000 : ℝ)^1024 ≤ (5000015579744267/5000000000000000 : ℝ)^6143 := by
      have hnat : (25000467319175686243 : ℕ)^1024*5000000000000000^6143 ≤ 5000015579744267^6143*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000467319175686243 25000000000000000000 5000015579744267 5000000000000000 1024 6143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000015579744267/5000000000000000 : ℝ)) (X := (25000467319175686243/25000000000000000000 : ℝ)) (by norm_num) 6143 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2169757800603/625000000000000000 : ℝ) ≤ ((1839982052727424279/1840000000000000000 : ℝ)+2*(1632133053/36800000000000 : ℝ)*(12301/100000 : ℝ))^(6143/1024 : ℝ) := by
    rw [show (1839982052727424279/1840000000000000000 : ℝ)+2*(1632133053/36800000000000 : ℝ)*(12301/100000 : ℝ)=(5000005786945949/5000000000000000 : ℝ) by norm_num, show 1+2*(2169757800603/625000000000000000 : ℝ)=(312502169757800603/312500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(467319175686243/50000000000000000000 : ℝ)+(2169757800603/625000000000000000 : ℝ) ≤ ((1839982052727424279/1840000000000000000 : ℝ)+(1632133053/36800000000000 : ℝ)*((14509/100000 : ℝ)+(12301/100000 : ℝ)))^(6143/1024 : ℝ) := by
    rw [show (1839982052727424279/1840000000000000000 : ℝ)+(1632133053/36800000000000 : ℝ)*((14509/100000 : ℝ)+(12301/100000 : ℝ))=(1250002670836277/1250000000000000 : ℝ) by norm_num, show 1+(467319175686243/50000000000000000000 : ℝ)+(2169757800603/625000000000000000 : ℝ)=(50000640899799734483/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(467319175686243/50000000000000000000 : ℝ) ≤ ((1839982052727424279/1840000000000000000 : ℝ)+2*(1632133053/36800000000000 : ℝ)*(14509/100000 : ℝ))^(6143/1024 : ℝ) := by
    rw [show (1839982052727424279/1840000000000000000 : ℝ)+2*(1632133053/36800000000000 : ℝ)*(14509/100000 : ℝ)=(5000015579744267/5000000000000000 : ℝ) by norm_num, show 1+2*(467319175686243/50000000000000000000 : ℝ)=(25000467319175686243/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1839982052727424279/1840000000000000000 : ℝ)*(X 1 0+X 2 0)+(1632133053/36800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6143/1024 : ℝ)) (lo := (12301/100000 : ℝ)) (hi := (14509/100000 : ℝ)) (c := (1839982052727424279/1840000000000000000 : ℝ)) (alpha := (1632133053/36800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1839982052727424279/1840000000000000000 : ℝ)*(X 0 1+X 2 1)+(1632133053/36800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6143/1024 : ℝ)) (lo := (12301/100000 : ℝ)) (hi := (14509/100000 : ℝ)) (c := (1839982052727424279/1840000000000000000 : ℝ)) (alpha := (1632133053/36800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1839982052727424279/1840000000000000000 : ℝ)*(X 0 2+X 1 2)+(1632133053/36800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6143/1024 : ℝ)) (lo := (12301/100000 : ℝ)) (hi := (14509/100000 : ℝ)) (c := (1839982052727424279/1840000000000000000 : ℝ)) (alpha := (1632133053/36800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1108197607/10000000000 : ℝ)*X 0 0+(1064716139/2000000000 : ℝ)*X 0 1+(2614623601/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1773_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1322146079/2500000000 : ℝ)*X 1 0+(-288965947/2500000000 : ℝ)*X 1 1+(1307311819/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1773_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5288584793/10000000000 : ℝ)*X 2 0+(5229246863/10000000000 : ℝ)*X 2 1+(-11558637/100000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1773_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4001437699/10000000000 : ℝ)*X 0 0+(239563841/625000000 : ℝ)*X 0 1+(2086731211/5000000000 : ℝ)*X 0 2+(4001437699/10000000000 : ℝ)*X 1 0+(239563841/625000000 : ℝ)*X 1 1+(2086731211/5000000000 : ℝ)*X 1 2+(4001437699/10000000000 : ℝ)*X 2 0+(239563841/625000000 : ℝ)*X 2 1+(2086731211/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1773_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-221640443/2000000000 : ℝ)*X 0 0+(5229658611/10000000000 : ℝ)*X 0 1+(5323167381/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1773_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((164481597/312500000 : ℝ)*X 1 0+(-10619433/100000000 : ℝ)*X 1 1+(5323167513/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1773_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1315852631/2500000000 : ℝ)*X 2 0+(2661584013/5000000000 : ℝ)*X 2 1+(-1061943391/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1773_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((800291521/2000000000 : ℝ)*X 0 0+(4171979973/10000000000 : ℝ)*X 0 1+(1917254581/5000000000 : ℝ)*X 0 2+(800291521/2000000000 : ℝ)*X 1 0+(4171979973/10000000000 : ℝ)*X 1 1+(1917254581/5000000000 : ℝ)*X 1 2+(800291521/2000000000 : ℝ)*X 2 0+(4171979973/10000000000 : ℝ)*X 2 1+(1917254581/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1773_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10610890890280742542479/1840000000000000000000000000 : ℝ) := by norm_num
    linear_combination (403480383/25000000000000 : ℝ)*(base19) + (15443951/800000000000 : ℝ)*(base23) + (95702997/50000000000000 : ℝ)*(upper3) + (338236641/100000000000000 : ℝ)*(upper4) + (4079643/6250000000000 : ℝ)*(upper5) + (6769102031763161/100000000000000 : ℝ)*(major0) + (6769102031763161/100000000000000 : ℝ)*(major1) + (6769102031763161/100000000000000 : ℝ)*(major2) + (5300370541311693/50000000000000 : ℝ)*(sp0) + (1325101177742443/12500000000000 : ℝ)*(sp1) + (5300404552683601/50000000000000 : ℝ)*(sp2) + (734343999417789/25000000000000 : ℝ)*(sp3) + (69953237689/100000000000000 : ℝ)*(sp4) + (3367553559/20000000000000 : ℝ)*(sp7) + (2937392835438951/100000000000000 : ℝ)*(f.failure) + (2650202758965269/25000000000000 : ℝ)*(f.sum) + (4498881690347/1840000000000000000000000000 : ℝ)*base66 + (661683788235835919/184000000000000000000000000000000 : ℝ)*base67 + (3070186714563835919/184000000000000000000000000000000 : ℝ)*base69 + (1264299059683835919/184000000000000000000000000000000 : ℝ)*base71 + (5931206537627/1840000000000000000000000000 : ℝ)*base74 + (906751319428164081/184000000000000000000000000000000 : ℝ)*base76 + (663941320204164081/184000000000000000000000000000000 : ℝ)*base78 + (7111923201932164081/184000000000000000000000000000000 : ℝ)*base80 + (392670652053/1840000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base87 + (73346773/10000000000000000000000 : ℝ)*base89 + (73346773/10000000000000000000000 : ℝ)*base91 + (73346773/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (605200678123795231922247183/46000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (513403083/25000000000000 : ℝ)*(base19) + (124612031/5000000000000 : ℝ)*(base23) + (30291567/3125000000000 : ℝ)*(upper3) + (65667247/10000000000000 : ℝ)*(lower4) + (3414328510465153/50000000000000 : ℝ)*(major0) + (3414328510465153/50000000000000 : ℝ)*(major1) + (3414328510465153/50000000000000 : ℝ)*(major2) + (7041707323/50000000000000 : ℝ)*(sp1) + (91325175213/100000000000000 : ℝ)*(sp2) + (2797982047/50000000000000 : ℝ)*(sp3) + (534703869966503/5000000000000 : ℝ)*(sp4) + (5347030631151541/50000000000000 : ℝ)*(sp5) + (2673495895478557/25000000000000 : ℝ)*(sp6) + (1481615304007613/50000000000000 : ℝ)*(sp7) + (74080905099483/2500000000000 : ℝ)*(f.failure) + (534703869966503/5000000000000 : ℝ)*(f.sum) + (3494183291011/920000000000000000000000000 : ℝ)*base66 + (1448348896842900313/92000000000000000000000000000000 : ℝ)*base68 + (1858239506898900313/92000000000000000000000000000000 : ℝ)*base70 + (1038835891218900313/92000000000000000000000000000000 : ℝ)*base72 + (1885829702771/920000000000000000000000000 : ℝ)*base74 + (2354248905082900313/92000000000000000000000000000000 : ℝ)*base76 + (1248628709182900313/92000000000000000000000000000000 : ℝ)*base78 + (4388626032846900313/92000000000000000000000000000000 : ℝ)*base80 + (2490002252669/920000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (1757809/250000000000000000000 : ℝ)*base89 + (1757809/250000000000000000000 : ℝ)*base91 + (1757809/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1773_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6143/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (230445923/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14509/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (12301/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (12371/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3609/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1773_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1773_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6143/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (230445923/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (12371/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3609/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1773_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1773_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1773_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (6143/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (230445923/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (12371/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3609/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1773_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
