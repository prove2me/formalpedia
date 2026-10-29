-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1349_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:07:17.869384+00:00
-- url     : https://prove2.me/submissions/84970d84-0e28-44fb-887e-c84984e2a2bf

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
theorem support_rectangle_w1349_s0_0 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-451253823/2500000000 : ℝ)*x 0 + (5993898859/10000000000 : ℝ)*x 1 + (601572061/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (451253823/2500000000 : ℝ)^4309 ≤ (5292747270219/50000000000000 : ℝ)^3285 := by
    have hnat : (451253823 : ℕ)^4309*50000000000000^3285 ≤ 5292747270219^3285*2500000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451253823 2500000000 5292747270219 50000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5993898859/10000000000 : ℝ)^4309 ≤ (638744265757/1250000000000 : ℝ)^3285 := by
    have hnat : (5993898859 : ℕ)^4309*1250000000000^3285 ≤ 638744265757^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5993898859 10000000000 638744265757 1250000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (601572061/1250000000 : ℝ)^4309 ≤ (19157482086383/50000000000000 : ℝ)^3285 := by
    have hnat : (601572061 : ℕ)^4309*50000000000000^3285 ≤ 19157482086383^3285*1250000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      601572061 1250000000 19157482086383 50000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-451253823/2500000000 : ℝ), (5993898859/10000000000 : ℝ), (601572061/1250000000 : ℝ)] ![(5292747270219/50000000000000 : ℝ), (638744265757/1250000000000 : ℝ), (19157482086383/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-451253823/2500000000 : ℝ)|^4309 ≤ (5292747270219/50000000000000 : ℝ)^3285
        have hw : |(-451253823/2500000000 : ℝ)|=(451253823/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5993898859/10000000000 : ℝ)|^4309 ≤ (638744265757/1250000000000 : ℝ)^3285
        have hw : |(5993898859/10000000000 : ℝ)|=(5993898859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(601572061/1250000000 : ℝ)|^4309 ≤ (19157482086383/50000000000000 : ℝ)^3285
        have hw : |(601572061/1250000000 : ℝ)|=(601572061/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_s0_1 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2750514409/5000000000 : ℝ)*x 0 + (-1238066317/5000000000 : ℝ)*x 1 + (150393029/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2750514409/5000000000 : ℝ)^4309 ≤ (45659916678661/100000000000000 : ℝ)^3285 := by
    have hnat : (2750514409 : ℕ)^4309*100000000000000^3285 ≤ 45659916678661^3285*5000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2750514409 5000000000 45659916678661 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1238066317/5000000000 : ℝ)^4309 ≤ (16025114534809/100000000000000 : ℝ)^3285 := by
    have hnat : (1238066317 : ℕ)^4309*100000000000000^3285 ≤ 16025114534809^3285*5000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1238066317 5000000000 16025114534809 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (150393029/312500000 : ℝ)^4309 ≤ (38314968767757/100000000000000 : ℝ)^3285 := by
    have hnat : (150393029 : ℕ)^4309*100000000000000^3285 ≤ 38314968767757^3285*312500000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      150393029 312500000 38314968767757 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2750514409/5000000000 : ℝ), (-1238066317/5000000000 : ℝ), (150393029/312500000 : ℝ)] ![(45659916678661/100000000000000 : ℝ), (16025114534809/100000000000000 : ℝ), (38314968767757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2750514409/5000000000 : ℝ)|^4309 ≤ (45659916678661/100000000000000 : ℝ)^3285
        have hw : |(2750514409/5000000000 : ℝ)|=(2750514409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1238066317/5000000000 : ℝ)|^4309 ≤ (16025114534809/100000000000000 : ℝ)^3285
        have hw : |(-1238066317/5000000000 : ℝ)|=(1238066317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(150393029/312500000 : ℝ)|^4309 ≤ (38314968767757/100000000000000 : ℝ)^3285
        have hw : |(150393029/312500000 : ℝ)|=(150393029/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_s0_2 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5501028601/10000000000 : ℝ)*x 0 + (962515321/2000000000 : ℝ)*x 1 + (-247613331/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5501028601/10000000000 : ℝ)^4309 ≤ (45659914316051/100000000000000 : ℝ)^3285 := by
    have hnat : (5501028601 : ℕ)^4309*100000000000000^3285 ≤ 45659914316051^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5501028601 10000000000 45659914316051 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (962515321/2000000000 : ℝ)^4309 ≤ (4789370674327/12500000000000 : ℝ)^3285 := by
    have hnat : (962515321 : ℕ)^4309*12500000000000^3285 ≤ 4789370674327^3285*2000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      962515321 2000000000 4789370674327 12500000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (247613331/1000000000 : ℝ)^4309 ≤ (16025120273529/100000000000000 : ℝ)^3285 := by
    have hnat : (247613331 : ℕ)^4309*100000000000000^3285 ≤ 16025120273529^3285*1000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      247613331 1000000000 16025120273529 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5501028601/10000000000 : ℝ), (962515321/2000000000 : ℝ), (-247613331/1000000000 : ℝ)] ![(45659914316051/100000000000000 : ℝ), (4789370674327/12500000000000 : ℝ), (16025120273529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5501028601/10000000000 : ℝ)|^4309 ≤ (45659914316051/100000000000000 : ℝ)^3285
        have hw : |(5501028601/10000000000 : ℝ)|=(5501028601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(962515321/2000000000 : ℝ)|^4309 ≤ (4789370674327/12500000000000 : ℝ)^3285
        have hw : |(962515321/2000000000 : ℝ)|=(962515321/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-247613331/1000000000 : ℝ)|^4309 ≤ (16025120273529/100000000000000 : ℝ)^3285
        have hw : |(-247613331/1000000000 : ℝ)|=(247613331/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_s0_3 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167108029/400000000 : ℝ)*x 0 + (6066847/19531250 : ℝ)*x 1 + (5587108361/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167108029/400000000 : ℝ)^4309 ≤ (31825551022637/100000000000000 : ℝ)^3285 := by
    have hnat : (167108029 : ℕ)^4309*100000000000000^3285 ≤ 31825551022637^3285*400000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167108029 400000000 31825551022637 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6066847/19531250 : ℝ)^4309 ≤ (21575054744171/100000000000000 : ℝ)^3285 := by
    have hnat : (6066847 : ℕ)^4309*100000000000000^3285 ≤ 21575054744171^3285*19531250^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6066847 19531250 21575054744171 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5587108361/10000000000 : ℝ)^4309 ≤ (46599394218799/100000000000000 : ℝ)^3285 := by
    have hnat : (5587108361 : ℕ)^4309*100000000000000^3285 ≤ 46599394218799^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5587108361 10000000000 46599394218799 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167108029/400000000 : ℝ), (6066847/19531250 : ℝ), (5587108361/10000000000 : ℝ)] ![(31825551022637/100000000000000 : ℝ), (21575054744171/100000000000000 : ℝ), (46599394218799/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167108029/400000000 : ℝ)|^4309 ≤ (31825551022637/100000000000000 : ℝ)^3285
        have hw : |(167108029/400000000 : ℝ)|=(167108029/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6066847/19531250 : ℝ)|^4309 ≤ (21575054744171/100000000000000 : ℝ)^3285
        have hw : |(6066847/19531250 : ℝ)|=(6066847/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5587108361/10000000000 : ℝ)|^4309 ≤ (46599394218799/100000000000000 : ℝ)^3285
        have hw : |(5587108361/10000000000 : ℝ)|=(5587108361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_s0_4 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-113089707/625000000 : ℝ)*x 0 + (4842968189/10000000000 : ℝ)*x 1 + (5962421811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (113089707/625000000 : ℝ)^4309 ≤ (5309754408961/50000000000000 : ℝ)^3285 := by
    have hnat : (113089707 : ℕ)^4309*50000000000000^3285 ≤ 5309754408961^3285*625000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113089707 625000000 5309754408961 50000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4842968189/10000000000 : ℝ)^4309 ≤ (6036353357/15625000000 : ℝ)^3285 := by
    have hnat : (4842968189 : ℕ)^4309*15625000000^3285 ≤ 6036353357^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4842968189 10000000000 6036353357 15625000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5962421811/10000000000 : ℝ)^4309 ≤ (50747829685169/100000000000000 : ℝ)^3285 := by
    have hnat : (5962421811 : ℕ)^4309*100000000000000^3285 ≤ 50747829685169^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5962421811 10000000000 50747829685169 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-113089707/625000000 : ℝ), (4842968189/10000000000 : ℝ), (5962421811/10000000000 : ℝ)] ![(5309754408961/50000000000000 : ℝ), (6036353357/15625000000 : ℝ), (50747829685169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-113089707/625000000 : ℝ)|^4309 ≤ (5309754408961/50000000000000 : ℝ)^3285
        have hw : |(-113089707/625000000 : ℝ)|=(113089707/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4842968189/10000000000 : ℝ)|^4309 ≤ (6036353357/15625000000 : ℝ)^3285
        have hw : |(4842968189/10000000000 : ℝ)|=(4842968189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5962421811/10000000000 : ℝ)|^4309 ≤ (50747829685169/100000000000000 : ℝ)^3285
        have hw : |(5962421811/10000000000 : ℝ)|=(5962421811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_s0_5 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (517903587/1000000000 : ℝ)*x 0 + (-1326288889/10000000000 : ℝ)*x 1 + (1490605371/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (517903587/1000000000 : ℝ)^4309 ≤ (8437321636533/20000000000000 : ℝ)^3285 := by
    have hnat : (517903587 : ℕ)^4309*20000000000000^3285 ≤ 8437321636533^3285*1000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517903587 1000000000 8437321636533 20000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1326288889/10000000000 : ℝ)^4309 ≤ (7065565764473/100000000000000 : ℝ)^3285 := by
    have hnat : (1326288889 : ℕ)^4309*100000000000000^3285 ≤ 7065565764473^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326288889 10000000000 7065565764473 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1490605371/2500000000 : ℝ)^4309 ≤ (25373913017203/50000000000000 : ℝ)^3285 := by
    have hnat : (1490605371 : ℕ)^4309*50000000000000^3285 ≤ 25373913017203^3285*2500000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1490605371 2500000000 25373913017203 50000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(517903587/1000000000 : ℝ), (-1326288889/10000000000 : ℝ), (1490605371/2500000000 : ℝ)] ![(8437321636533/20000000000000 : ℝ), (7065565764473/100000000000000 : ℝ), (25373913017203/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(517903587/1000000000 : ℝ)|^4309 ≤ (8437321636533/20000000000000 : ℝ)^3285
        have hw : |(517903587/1000000000 : ℝ)|=(517903587/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1326288889/10000000000 : ℝ)|^4309 ≤ (7065565764473/100000000000000 : ℝ)^3285
        have hw : |(-1326288889/10000000000 : ℝ)|=(1326288889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1490605371/2500000000 : ℝ)|^4309 ≤ (25373913017203/50000000000000 : ℝ)^3285
        have hw : |(1490605371/2500000000 : ℝ)|=(1490605371/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_s0_6 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5179035823/10000000000 : ℝ)*x 0 + (5962421847/10000000000 : ℝ)*x 1 + (-663144191/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5179035823/10000000000 : ℝ)^4309 ≤ (42186607680479/100000000000000 : ℝ)^3285 := by
    have hnat : (5179035823 : ℕ)^4309*100000000000000^3285 ≤ 42186607680479^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179035823 10000000000 42186607680479 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5962421847/10000000000 : ℝ)^4309 ≤ (3171739380443/6250000000000 : ℝ)^3285 := by
    have hnat : (5962421847 : ℕ)^4309*6250000000000^3285 ≤ 3171739380443^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5962421847 10000000000 3171739380443 6250000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (663144191/5000000000 : ℝ)^4309 ≤ (3532781110791/50000000000000 : ℝ)^3285 := by
    have hnat : (663144191 : ℕ)^4309*50000000000000^3285 ≤ 3532781110791^3285*5000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663144191 5000000000 3532781110791 50000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5179035823/10000000000 : ℝ), (5962421847/10000000000 : ℝ), (-663144191/5000000000 : ℝ)] ![(42186607680479/100000000000000 : ℝ), (3171739380443/6250000000000 : ℝ), (3532781110791/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5179035823/10000000000 : ℝ)|^4309 ≤ (42186607680479/100000000000000 : ℝ)^3285
        have hw : |(5179035823/10000000000 : ℝ)|=(5179035823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5962421847/10000000000 : ℝ)|^4309 ≤ (3171739380443/6250000000000 : ℝ)^3285
        have hw : |(5962421847/10000000000 : ℝ)|=(5962421847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-663144191/5000000000 : ℝ)|^4309 ≤ (3532781110791/50000000000000 : ℝ)^3285
        have hw : |(-663144191/5000000000 : ℝ)|=(663144191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_s0_7 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4186980689/10000000000 : ℝ)*x 0 + (1380821029/2500000000 : ℝ)*x 1 + (3172329831/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4186980689/10000000000 : ℝ)^4309 ≤ (31918314340521/100000000000000 : ℝ)^3285 := by
    have hnat : (4186980689 : ℕ)^4309*100000000000000^3285 ≤ 31918314340521^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4186980689 10000000000 31918314340521 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1380821029/2500000000 : ℝ)^4309 ≤ (11475594048963/25000000000000 : ℝ)^3285 := by
    have hnat : (1380821029 : ℕ)^4309*25000000000000^3285 ≤ 11475594048963^3285*2500000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1380821029 2500000000 11475594048963 25000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3172329831/10000000000 : ℝ)^4309 ≤ (11089654719411/50000000000000 : ℝ)^3285 := by
    have hnat : (3172329831 : ℕ)^4309*50000000000000^3285 ≤ 11089654719411^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3172329831 10000000000 11089654719411 50000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4186980689/10000000000 : ℝ), (1380821029/2500000000 : ℝ), (3172329831/10000000000 : ℝ)] ![(31918314340521/100000000000000 : ℝ), (11475594048963/25000000000000 : ℝ), (11089654719411/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4186980689/10000000000 : ℝ)|^4309 ≤ (31918314340521/100000000000000 : ℝ)^3285
        have hw : |(4186980689/10000000000 : ℝ)|=(4186980689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1380821029/2500000000 : ℝ)|^4309 ≤ (11475594048963/25000000000000 : ℝ)^3285
        have hw : |(1380821029/2500000000 : ℝ)|=(1380821029/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3172329831/10000000000 : ℝ)|^4309 ≤ (11089654719411/50000000000000 : ℝ)^3285
        have hw : |(3172329831/10000000000 : ℝ)|=(3172329831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1349_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4843891/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1467/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (26821/100000 : ℝ)*pair X 0 0 := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
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
  have hpowlo : (0 : ℝ) ^ (1077/256 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^1077 ≤ (0 : ℝ)^256 := by
      have hnat : (0 : ℕ)^1077*1^256 ≤ 0^256*1^1077 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 1077 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 1077 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (1077/256 : ℝ) ≤ (1058824427832652239/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^1077 ≤ (1058824427832652239/50000000000000000000 : ℝ)^256 := by
      have hnat : (2 : ℕ)^1077*50000000000000000000^256 ≤ 1058824427832652239^256*5^1077 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1058824427832652239 50000000000000000000 1077 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1058824427832652239/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1077 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (1077/256 : ℝ) := by
    have hpowers : (1 : ℝ)^256 ≤ (1 : ℝ)^1077 := by
      have hnat : (1 : ℕ)^256*1^1077 ≤ 1^1077*1^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 256 1077 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 1077 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (51058824427832652239/50000000000000000000 : ℝ) ≤ (2009986928103973/2000000000000000 : ℝ) ^ (1077/256 : ℝ) := by
    have hpowers : (51058824427832652239/50000000000000000000 : ℝ)^256 ≤ (2009986928103973/2000000000000000 : ℝ)^1077 := by
      have hnat : (51058824427832652239 : ℕ)^256*2000000000000000^1077 ≤ 2009986928103973^1077*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51058824427832652239 50000000000000000000 2009986928103973 2000000000000000 256 1077 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2009986928103973/2000000000000000 : ℝ)) (X := (51058824427832652239/50000000000000000000 : ℝ)) (by norm_num) 1077 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (26058824427832652239/25000000000000000000 : ℝ) ≤ (1009986928103973/1000000000000000 : ℝ) ^ (1077/256 : ℝ) := by
    have hpowers : (26058824427832652239/25000000000000000000 : ℝ)^256 ≤ (1009986928103973/1000000000000000 : ℝ)^1077 := by
      have hnat : (26058824427832652239 : ℕ)^256*1000000000000000^1077 ≤ 1009986928103973^1077*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26058824427832652239 25000000000000000000 1009986928103973 1000000000000000 256 1077 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1009986928103973/1000000000000000 : ℝ)) (X := (26058824427832652239/25000000000000000000 : ℝ)) (by norm_num) 1077 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(9986928103973/800000000000000 : ℝ)*(0 : ℝ))^(1077/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(9986928103973/800000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1058824427832652239/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(9986928103973/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(1077/256 : ℝ) := by
    rw [show (1 : ℝ)+(9986928103973/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2009986928103973/2000000000000000 : ℝ) by norm_num, show 1+(1058824427832652239/50000000000000000000 : ℝ)+(0 : ℝ)=(51058824427832652239/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1058824427832652239/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(9986928103973/800000000000000 : ℝ)*(2/5 : ℝ))^(1077/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(9986928103973/800000000000000 : ℝ)*(2/5 : ℝ)=(1009986928103973/1000000000000000 : ℝ) by norm_num, show 1+2*(1058824427832652239/50000000000000000000 : ℝ)=(26058824427832652239/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(9986928103973/800000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1077/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (9986928103973/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(9986928103973/800000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1077/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (9986928103973/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(9986928103973/800000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1077/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (9986928103973/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-451253823/2500000000 : ℝ)*X 0 0+(5993898859/10000000000 : ℝ)*X 0 1+(601572061/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2750514409/5000000000 : ℝ)*X 1 0+(-1238066317/5000000000 : ℝ)*X 1 1+(150393029/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5501028601/10000000000 : ℝ)*X 2 0+(962515321/2000000000 : ℝ)*X 2 1+(-247613331/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((167108029/400000000 : ℝ)*X 0 0+(6066847/19531250 : ℝ)*X 0 1+(5587108361/10000000000 : ℝ)*X 0 2+(167108029/400000000 : ℝ)*X 1 0+(6066847/19531250 : ℝ)*X 1 1+(5587108361/10000000000 : ℝ)*X 1 2+(167108029/400000000 : ℝ)*X 2 0+(6066847/19531250 : ℝ)*X 2 1+(5587108361/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-113089707/625000000 : ℝ)*X 0 0+(4842968189/10000000000 : ℝ)*X 0 1+(5962421811/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((517903587/1000000000 : ℝ)*X 1 0+(-1326288889/10000000000 : ℝ)*X 1 1+(1490605371/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5179035823/10000000000 : ℝ)*X 2 0+(5962421847/10000000000 : ℝ)*X 2 1+(-663144191/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4186980689/10000000000 : ℝ)*X 0 0+(1380821029/2500000000 : ℝ)*X 0 1+(3172329831/10000000000 : ℝ)*X 0 2+(4186980689/10000000000 : ℝ)*X 1 0+(1380821029/2500000000 : ℝ)*X 1 1+(3172329831/10000000000 : ℝ)*X 1 2+(4186980689/10000000000 : ℝ)*X 2 0+(1380821029/2500000000 : ℝ)*X 2 1+(3172329831/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (47698390694013254119083/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18287207/20000000000000 : ℝ)*(base1) + (13931193/50000000000000 : ℝ)*(base16) + (533600803/100000000000000 : ℝ)*(base19) + (528070697/100000000000000 : ℝ)*(base23) + (45360233/50000000000000 : ℝ)*(upper3) + (624798116807881/100000000000000 : ℝ)*(major0) + (624798116807881/100000000000000 : ℝ)*(major1) + (624798116807881/100000000000000 : ℝ)*(major2) + (169302195407651/20000000000000 : ℝ)*(sp0) + (423255883532247/50000000000000 : ℝ)*(sp1) + (423255900228493/50000000000000 : ℝ)*(sp2) + (403082907883281/100000000000000 : ℝ)*(sp3) + (1442925463/100000000000000 : ℝ)*(sp4) + (413135719/50000000000000 : ℝ)*(sp7) + (80616765118151/20000000000000 : ℝ)*(f.failure) + (846512328527683/100000000000000 : ℝ)*(f.sum) + (50090650171213/40000000000000000000000000000 : ℝ)*base65 + (542414438291213/80000000000000000000000000000 : ℝ)*base67 + (473106325651213/80000000000000000000000000000 : ℝ)*base69 + (369104225891213/80000000000000000000000000000 : ℝ)*base71 + (256278225971213/40000000000000000000000000000 : ℝ)*base73 + (634356525731213/80000000000000000000000000000 : ℝ)*base75 + (361290746371213/80000000000000000000000000000 : ℝ)*base77 + (471897240051213/80000000000000000000000000000 : ℝ)*base79 + (147935403451213/40000000000000000000000000000 : ℝ)*base81 + (59459/62500000000000000000 : ℝ)*base90 + (59459/62500000000000000000 : ℝ)*base92 + (59459/62500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (144888658777593318423609/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1453046481/100000000000000 : ℝ)*(base19) + (155995389/10000000000000 : ℝ)*(base23) + (6208099/6250000000000 : ℝ)*(base39) + (89960113/50000000000000 : ℝ)*(upper3) + (202701129/100000000000000 : ℝ)*(upper5) + (659325856257281/100000000000000 : ℝ)*(major0) + (659325856257281/100000000000000 : ℝ)*(major1) + (659325756927697/100000000000000 : ℝ)*(major2) + (820867571/25000000000000 : ℝ)*(sp1) + (1787128183/50000000000000 : ℝ)*(sp2) + (893292233605183/100000000000000 : ℝ)*(sp4) + (446643748544209/50000000000000 : ℝ)*(sp5) + (27915224960141/3125000000000 : ℝ)*(sp6) + (42535913809869/10000000000000 : ℝ)*(sp7) + (42535913809869/10000000000000 : ℝ)*(f.failure) + (893292332934767/100000000000000 : ℝ)*(f.sum) + (74281620298797/40000000000000000000000000000 : ℝ)*base65 + (170315329280181/80000000000000000000000000000 : ℝ)*base67 + (126805982037413/80000000000000000000000000000 : ℝ)*base69 + (65561771119819/80000000000000000000000000000 : ℝ)*base72 + (263401737578797/40000000000000000000000000000 : ℝ)*base73 + (129268694042587/80000000000000000000000000000 : ℝ)*base76 + (372701773882587/80000000000000000000000000000 : ℝ)*base78 + (824687724442587/80000000000000000000000000000 : ℝ)*base80 + (258369392437413/40000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (152221/31250000000000000000 : ℝ)*base90 + (152221/31250000000000000000 : ℝ)*base92 + (152221/31250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1349_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4843891/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1467/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (26821/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1349_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1349_s1_0 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1988819011/10000000000 : ℝ)*x 0 + (5639008607/10000000000 : ℝ)*x 1 + (2524875027/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1988819011/10000000000 : ℝ)^4309 ≤ (3005338738313/25000000000000 : ℝ)^3285 := by
    have hnat : (1988819011 : ℕ)^4309*25000000000000^3285 ≤ 3005338738313^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1988819011 10000000000 3005338738313 25000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5639008607/10000000000 : ℝ)^4309 ≤ (47168025450031/100000000000000 : ℝ)^3285 := by
    have hnat : (5639008607 : ℕ)^4309*100000000000000^3285 ≤ 47168025450031^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5639008607 10000000000 47168025450031 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2524875027/5000000000 : ℝ)^4309 ≤ (1275331862269/3125000000000 : ℝ)^3285 := by
    have hnat : (2524875027 : ℕ)^4309*3125000000000^3285 ≤ 1275331862269^3285*5000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2524875027 5000000000 1275331862269 3125000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1988819011/10000000000 : ℝ), (5639008607/10000000000 : ℝ), (2524875027/5000000000 : ℝ)] ![(3005338738313/25000000000000 : ℝ), (47168025450031/100000000000000 : ℝ), (1275331862269/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1988819011/10000000000 : ℝ)|^4309 ≤ (3005338738313/25000000000000 : ℝ)^3285
        have hw : |(-1988819011/10000000000 : ℝ)|=(1988819011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5639008607/10000000000 : ℝ)|^4309 ≤ (47168025450031/100000000000000 : ℝ)^3285
        have hw : |(5639008607/10000000000 : ℝ)|=(5639008607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2524875027/5000000000 : ℝ)|^4309 ≤ (1275331862269/3125000000000 : ℝ)^3285
        have hw : |(2524875027/5000000000 : ℝ)|=(2524875027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_s1_1 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5404989231/10000000000 : ℝ)*x 0 + (-2303073553/10000000000 : ℝ)*x 1 + (5049750419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5404989231/10000000000 : ℝ)^4309 ≤ (44617132442981/100000000000000 : ℝ)^3285 := by
    have hnat : (5404989231 : ℕ)^4309*100000000000000^3285 ≤ 44617132442981^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404989231 10000000000 44617132442981 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2303073553/10000000000 : ℝ)^4309 ≤ (3643061020707/25000000000000 : ℝ)^3285 := by
    have hnat : (2303073553 : ℕ)^4309*25000000000000^3285 ≤ 3643061020707^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2303073553 10000000000 3643061020707 25000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5049750419/10000000000 : ℝ)^4309 ≤ (637665991593/1562500000000 : ℝ)^3285 := by
    have hnat : (5049750419 : ℕ)^4309*1562500000000^3285 ≤ 637665991593^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5049750419 10000000000 637665991593 1562500000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5404989231/10000000000 : ℝ), (-2303073553/10000000000 : ℝ), (5049750419/10000000000 : ℝ)] ![(44617132442981/100000000000000 : ℝ), (3643061020707/25000000000000 : ℝ), (637665991593/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5404989231/10000000000 : ℝ)|^4309 ≤ (44617132442981/100000000000000 : ℝ)^3285
        have hw : |(5404989231/10000000000 : ℝ)|=(5404989231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2303073553/10000000000 : ℝ)|^4309 ≤ (3643061020707/25000000000000 : ℝ)^3285
        have hw : |(-2303073553/10000000000 : ℝ)|=(2303073553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5049750419/10000000000 : ℝ)|^4309 ≤ (637665991593/1562500000000 : ℝ)^3285
        have hw : |(5049750419/10000000000 : ℝ)|=(5049750419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_s1_2 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1080997839/2000000000 : ℝ)*x 0 + (5049750073/10000000000 : ℝ)*x 1 + (-1151537021/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1080997839/2000000000 : ℝ)^4309 ≤ (44617132053173/100000000000000 : ℝ)^3285 := by
    have hnat : (1080997839 : ℕ)^4309*100000000000000^3285 ≤ 44617132053173^3285*2000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080997839 2000000000 44617132053173 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5049750073/10000000000 : ℝ)^4309 ≤ (20405309897013/50000000000000 : ℝ)^3285 := by
    have hnat : (5049750073 : ℕ)^4309*50000000000000^3285 ≤ 20405309897013^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5049750073 10000000000 20405309897013 50000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1151537021/5000000000 : ℝ)^4309 ≤ (14572248141357/100000000000000 : ℝ)^3285 := by
    have hnat : (1151537021 : ℕ)^4309*100000000000000^3285 ≤ 14572248141357^3285*5000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1151537021 5000000000 14572248141357 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1080997839/2000000000 : ℝ), (5049750073/10000000000 : ℝ), (-1151537021/5000000000 : ℝ)] ![(44617132053173/100000000000000 : ℝ), (20405309897013/50000000000000 : ℝ), (14572248141357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1080997839/2000000000 : ℝ)|^4309 ≤ (44617132053173/100000000000000 : ℝ)^3285
        have hw : |(1080997839/2000000000 : ℝ)|=(1080997839/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5049750073/10000000000 : ℝ)|^4309 ≤ (20405309897013/50000000000000 : ℝ)^3285
        have hw : |(5049750073/10000000000 : ℝ)|=(5049750073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1151537021/5000000000 : ℝ)|^4309 ≤ (14572248141357/100000000000000 : ℝ)^3285
        have hw : |(-1151537021/5000000000 : ℝ)|=(1151537021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_s1_3 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (536382411/1250000000 : ℝ)*x 0 + (1856764187/5000000000 : ℝ)*x 1 + (2475511179/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536382411/1250000000 : ℝ)^4309 ≤ (16481531028423/50000000000000 : ℝ)^3285 := by
    have hnat : (536382411 : ℕ)^4309*50000000000000^3285 ≤ 16481531028423^3285*1250000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536382411 1250000000 16481531028423 50000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1856764187/5000000000 : ℝ)^4309 ≤ (27269721174481/100000000000000 : ℝ)^3285 := by
    have hnat : (1856764187 : ℕ)^4309*100000000000000^3285 ≤ 27269721174481^3285*5000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1856764187 5000000000 27269721174481 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2475511179/5000000000 : ℝ)^4309 ≤ (3976721675573/10000000000000 : ℝ)^3285 := by
    have hnat : (2475511179 : ℕ)^4309*10000000000000^3285 ≤ 3976721675573^3285*5000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2475511179 5000000000 3976721675573 10000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(536382411/1250000000 : ℝ), (1856764187/5000000000 : ℝ), (2475511179/5000000000 : ℝ)] ![(16481531028423/50000000000000 : ℝ), (27269721174481/100000000000000 : ℝ), (3976721675573/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(536382411/1250000000 : ℝ)|^4309 ≤ (16481531028423/50000000000000 : ℝ)^3285
        have hw : |(536382411/1250000000 : ℝ)|=(536382411/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1856764187/5000000000 : ℝ)|^4309 ≤ (27269721174481/100000000000000 : ℝ)^3285
        have hw : |(1856764187/5000000000 : ℝ)|=(1856764187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2475511179/5000000000 : ℝ)|^4309 ≤ (3976721675573/10000000000000 : ℝ)^3285
        have hw : |(2475511179/5000000000 : ℝ)|=(2475511179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_s1_4 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1989342933/10000000000 : ℝ)*x 0 + (5057104329/10000000000 : ℝ)*x 1 + (563152127/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1989342933/10000000000 : ℝ)^4309 ≤ (1503188639783/12500000000000 : ℝ)^3285 := by
    have hnat : (1989342933 : ℕ)^4309*12500000000000^3285 ≤ 1503188639783^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1989342933 10000000000 1503188639783 12500000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5057104329/10000000000 : ℝ)^4309 ≤ (2555537470011/6250000000000 : ℝ)^3285 := by
    have hnat : (5057104329 : ℕ)^4309*6250000000000^3285 ≤ 2555537470011^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5057104329 10000000000 2555537470011 6250000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (563152127/1000000000 : ℝ)^4309 ≤ (47085891345403/100000000000000 : ℝ)^3285 := by
    have hnat : (563152127 : ℕ)^4309*100000000000000^3285 ≤ 47085891345403^3285*1000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563152127 1000000000 47085891345403 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1989342933/10000000000 : ℝ), (5057104329/10000000000 : ℝ), (563152127/1000000000 : ℝ)] ![(1503188639783/12500000000000 : ℝ), (2555537470011/6250000000000 : ℝ), (47085891345403/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1989342933/10000000000 : ℝ)|^4309 ≤ (1503188639783/12500000000000 : ℝ)^3285
        have hw : |(-1989342933/10000000000 : ℝ)|=(1989342933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5057104329/10000000000 : ℝ)|^4309 ≤ (2555537470011/6250000000000 : ℝ)^3285
        have hw : |(5057104329/10000000000 : ℝ)|=(5057104329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(563152127/1000000000 : ℝ)|^4309 ≤ (47085891345403/100000000000000 : ℝ)^3285
        have hw : |(563152127/1000000000 : ℝ)|=(563152127/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_s1_5 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5251995581/10000000000 : ℝ)*x 0 + (-1721302443/10000000000 : ℝ)*x 1 + (5631521317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5251995581/10000000000 : ℝ)^4309 ≤ (42967875009649/100000000000000 : ℝ)^3285 := by
    have hnat : (5251995581 : ℕ)^4309*100000000000000^3285 ≤ 42967875009649^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251995581 10000000000 42967875009649 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1721302443/10000000000 : ℝ)^4309 ≤ (1989246621217/20000000000000 : ℝ)^3285 := by
    have hnat : (1721302443 : ℕ)^4309*20000000000000^3285 ≤ 1989246621217^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1721302443 10000000000 1989246621217 20000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5631521317/10000000000 : ℝ)^4309 ≤ (23542945930437/50000000000000 : ℝ)^3285 := by
    have hnat : (5631521317 : ℕ)^4309*50000000000000^3285 ≤ 23542945930437^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5631521317 10000000000 23542945930437 50000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5251995581/10000000000 : ℝ), (-1721302443/10000000000 : ℝ), (5631521317/10000000000 : ℝ)] ![(42967875009649/100000000000000 : ℝ), (1989246621217/20000000000000 : ℝ), (23542945930437/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5251995581/10000000000 : ℝ)|^4309 ≤ (42967875009649/100000000000000 : ℝ)^3285
        have hw : |(5251995581/10000000000 : ℝ)|=(5251995581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1721302443/10000000000 : ℝ)|^4309 ≤ (1989246621217/20000000000000 : ℝ)^3285
        have hw : |(-1721302443/10000000000 : ℝ)|=(1721302443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5631521317/10000000000 : ℝ)|^4309 ≤ (23542945930437/50000000000000 : ℝ)^3285
        have hw : |(5631521317/10000000000 : ℝ)|=(5631521317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_s1_6 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (131299887/250000000 : ℝ)*x 0 + (1407880347/2500000000 : ℝ)*x 1 + (-344260497/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (131299887/250000000 : ℝ)^4309 ≤ (42967873925767/100000000000000 : ℝ)^3285 := by
    have hnat : (131299887 : ℕ)^4309*100000000000000^3285 ≤ 42967873925767^3285*250000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131299887 250000000 42967873925767 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1407880347/2500000000 : ℝ)^4309 ≤ (11771473159891/25000000000000 : ℝ)^3285 := by
    have hnat : (1407880347 : ℕ)^4309*25000000000000^3285 ≤ 11771473159891^3285*2500000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1407880347 2500000000 11771473159891 25000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (344260497/2000000000 : ℝ)^4309 ≤ (4973116712213/50000000000000 : ℝ)^3285 := by
    have hnat : (344260497 : ℕ)^4309*50000000000000^3285 ≤ 4973116712213^3285*2000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      344260497 2000000000 4973116712213 50000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(131299887/250000000 : ℝ), (1407880347/2500000000 : ℝ), (-344260497/2000000000 : ℝ)] ![(42967873925767/100000000000000 : ℝ), (11771473159891/25000000000000 : ℝ), (4973116712213/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(131299887/250000000 : ℝ)|^4309 ≤ (42967873925767/100000000000000 : ℝ)^3285
        have hw : |(131299887/250000000 : ℝ)|=(131299887/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1407880347/2500000000 : ℝ)|^4309 ≤ (11771473159891/25000000000000 : ℝ)^3285
        have hw : |(1407880347/2500000000 : ℝ)|=(1407880347/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-344260497/2000000000 : ℝ)|^4309 ≤ (4973116712213/50000000000000 : ℝ)^3285
        have hw : |(-344260497/2000000000 : ℝ)|=(344260497/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_s1_7 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (171686397/400000000 : ℝ)*x 0 + (493557843/1000000000 : ℝ)*x 1 + (1864625443/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (171686397/400000000 : ℝ)^4309 ≤ (32974152927033/100000000000000 : ℝ)^3285 := by
    have hnat : (171686397 : ℕ)^4309*100000000000000^3285 ≤ 32974152927033^3285*400000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171686397 400000000 32974152927033 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (493557843/1000000000 : ℝ)^4309 ≤ (39604580319527/100000000000000 : ℝ)^3285 := by
    have hnat : (493557843 : ℕ)^4309*100000000000000^3285 ≤ 39604580319527^3285*1000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      493557843 1000000000 39604580319527 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1864625443/5000000000 : ℝ)^4309 ≤ (13710633367629/50000000000000 : ℝ)^3285 := by
    have hnat : (1864625443 : ℕ)^4309*50000000000000^3285 ≤ 13710633367629^3285*5000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1864625443 5000000000 13710633367629 50000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(171686397/400000000 : ℝ), (493557843/1000000000 : ℝ), (1864625443/5000000000 : ℝ)] ![(32974152927033/100000000000000 : ℝ), (39604580319527/100000000000000 : ℝ), (13710633367629/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(171686397/400000000 : ℝ)|^4309 ≤ (32974152927033/100000000000000 : ℝ)^3285
        have hw : |(171686397/400000000 : ℝ)|=(171686397/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(493557843/1000000000 : ℝ)|^4309 ≤ (39604580319527/100000000000000 : ℝ)^3285
        have hw : |(493557843/1000000000 : ℝ)|=(493557843/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1864625443/5000000000 : ℝ)|^4309 ≤ (13710633367629/50000000000000 : ℝ)^3285
        have hw : |(1864625443/5000000000 : ℝ)|=(1864625443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1349_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4843891/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26821/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1467/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1391/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (19409/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (26821/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1467/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (26821/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1467/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (26821/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1467/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (26821/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1467/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (26821/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1467/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (26821/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1467/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
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
  have hpowlo : (1467/100000 : ℝ) ^ (1077/256 : ℝ) ≤ (966238179967/50000000000000000000 : ℝ) := by
    have hpowers : (1467/100000 : ℝ)^1077 ≤ (966238179967/50000000000000000000 : ℝ)^256 := by
      have hnat : (1467 : ℕ)^1077*50000000000000000000^256 ≤ 966238179967^256*100000^1077 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1467 100000 966238179967 50000000000000000000 1077 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1467/100000 : ℝ)) (X := (966238179967/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1077 256 (by norm_num) hpowers
    exact h
  have hpowhi : (26821/100000 : ℝ) ^ (1077/256 : ℝ) ≤ (98518168862379031/25000000000000000000 : ℝ) := by
    have hpowers : (26821/100000 : ℝ)^1077 ≤ (98518168862379031/25000000000000000000 : ℝ)^256 := by
      have hnat : (26821 : ℕ)^1077*25000000000000000000^256 ≤ 98518168862379031^256*100000^1077 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26821 100000 98518168862379031 25000000000000000000 1077 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26821/100000 : ℝ)) (X := (98518168862379031/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1077 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000966238179967/25000000000000000000 : ℝ) ≤ (2000000018373777/2000000000000000 : ℝ) ^ (1077/256 : ℝ) := by
    have hpowers : (25000000966238179967/25000000000000000000 : ℝ)^256 ≤ (2000000018373777/2000000000000000 : ℝ)^1077 := by
      have hnat : (25000000966238179967 : ℕ)^256*2000000000000000^1077 ≤ 2000000018373777^1077*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000966238179967 25000000000000000000 2000000018373777 2000000000000000 256 1077 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000000018373777/2000000000000000 : ℝ)) (X := (25000000966238179967/25000000000000000000 : ℝ)) (by norm_num) 1077 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50197037303962938029/50000000000000000000 : ℝ) ≤ (1000935301030211/1000000000000000 : ℝ) ^ (1077/256 : ℝ) := by
    have hpowers : (50197037303962938029/50000000000000000000 : ℝ)^256 ≤ (1000935301030211/1000000000000000 : ℝ)^1077 := by
      have hnat : (50197037303962938029 : ℕ)^256*1000000000000000^1077 ≤ 1000935301030211^1077*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50197037303962938029 50000000000000000000 1000935301030211 1000000000000000 256 1077 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000935301030211/1000000000000000 : ℝ)) (X := (50197037303962938029/50000000000000000000 : ℝ)) (by norm_num) 1077 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (12598518168862379031/12500000000000000000 : ℝ) ≤ (2003741185747067/2000000000000000 : ℝ) ^ (1077/256 : ℝ) := by
    have hpowers : (12598518168862379031/12500000000000000000 : ℝ)^256 ≤ (2003741185747067/2000000000000000 : ℝ)^1077 := by
      have hnat : (12598518168862379031 : ℕ)^256*2000000000000000^1077 ≤ 2003741185747067^1077*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12598518168862379031 12500000000000000000 2003741185747067 2000000000000000 256 1077 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2003741185747067/2000000000000000 : ℝ)) (X := (12598518168862379031/12500000000000000000 : ℝ)) (by norm_num) 1077 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(966238179967/50000000000000000000 : ℝ) ≤ ((12675628043328031407/12677000000000000000 : ℝ)+2*(374116737329/101416000000000 : ℝ)*(1467/100000 : ℝ))^(1077/256 : ℝ) := by
    rw [show (12675628043328031407/12677000000000000000 : ℝ)+2*(374116737329/101416000000000 : ℝ)*(1467/100000 : ℝ)=(2000000018373777/2000000000000000 : ℝ) by norm_num, show 1+2*(966238179967/50000000000000000000 : ℝ)=(25000000966238179967/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(98518168862379031/25000000000000000000 : ℝ)+(966238179967/50000000000000000000 : ℝ) ≤ ((12675628043328031407/12677000000000000000 : ℝ)+(374116737329/101416000000000 : ℝ)*((26821/100000 : ℝ)+(1467/100000 : ℝ)))^(1077/256 : ℝ) := by
    rw [show (12675628043328031407/12677000000000000000 : ℝ)+(374116737329/101416000000000 : ℝ)*((26821/100000 : ℝ)+(1467/100000 : ℝ))=(1000935301030211/1000000000000000 : ℝ) by norm_num, show 1+(98518168862379031/25000000000000000000 : ℝ)+(966238179967/50000000000000000000 : ℝ)=(50197037303962938029/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(98518168862379031/25000000000000000000 : ℝ) ≤ ((12675628043328031407/12677000000000000000 : ℝ)+2*(374116737329/101416000000000 : ℝ)*(26821/100000 : ℝ))^(1077/256 : ℝ) := by
    rw [show (12675628043328031407/12677000000000000000 : ℝ)+2*(374116737329/101416000000000 : ℝ)*(26821/100000 : ℝ)=(2003741185747067/2000000000000000 : ℝ) by norm_num, show 1+2*(98518168862379031/25000000000000000000 : ℝ)=(12598518168862379031/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (12675628043328031407/12677000000000000000 : ℝ)*(X 1 0+X 2 0)+(374116737329/101416000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1077/256 : ℝ)) (lo := (1467/100000 : ℝ)) (hi := (26821/100000 : ℝ)) (c := (12675628043328031407/12677000000000000000 : ℝ)) (alpha := (374116737329/101416000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (12675628043328031407/12677000000000000000 : ℝ)*(X 0 1+X 2 1)+(374116737329/101416000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1077/256 : ℝ)) (lo := (1467/100000 : ℝ)) (hi := (26821/100000 : ℝ)) (c := (12675628043328031407/12677000000000000000 : ℝ)) (alpha := (374116737329/101416000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (12675628043328031407/12677000000000000000 : ℝ)*(X 0 2+X 1 2)+(374116737329/101416000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1077/256 : ℝ)) (lo := (1467/100000 : ℝ)) (hi := (26821/100000 : ℝ)) (c := (12675628043328031407/12677000000000000000 : ℝ)) (alpha := (374116737329/101416000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1988819011/10000000000 : ℝ)*X 0 0+(5639008607/10000000000 : ℝ)*X 0 1+(2524875027/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5404989231/10000000000 : ℝ)*X 1 0+(-2303073553/10000000000 : ℝ)*X 1 1+(5049750419/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1080997839/2000000000 : ℝ)*X 2 0+(5049750073/10000000000 : ℝ)*X 2 1+(-1151537021/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((536382411/1250000000 : ℝ)*X 0 0+(1856764187/5000000000 : ℝ)*X 0 1+(2475511179/5000000000 : ℝ)*X 0 2+(536382411/1250000000 : ℝ)*X 1 0+(1856764187/5000000000 : ℝ)*X 1 1+(2475511179/5000000000 : ℝ)*X 1 2+(536382411/1250000000 : ℝ)*X 2 0+(1856764187/5000000000 : ℝ)*X 2 1+(2475511179/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1989342933/10000000000 : ℝ)*X 0 0+(5057104329/10000000000 : ℝ)*X 0 1+(563152127/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5251995581/10000000000 : ℝ)*X 1 0+(-1721302443/10000000000 : ℝ)*X 1 1+(5631521317/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((131299887/250000000 : ℝ)*X 2 0+(1407880347/2500000000 : ℝ)*X 2 1+(-344260497/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((171686397/400000000 : ℝ)*X 0 0+(493557843/1000000000 : ℝ)*X 0 1+(1864625443/5000000000 : ℝ)*X 0 2+(171686397/400000000 : ℝ)*X 1 0+(493557843/1000000000 : ℝ)*X 1 1+(1864625443/5000000000 : ℝ)*X 1 2+(171686397/400000000 : ℝ)*X 2 0+(493557843/1000000000 : ℝ)*X 2 1+(1864625443/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (85370399484019513390197/25354000000000000000000000000 : ℝ) := by norm_num
    linear_combination (48146781/100000000000000 : ℝ)*(base16) + (145961753/50000000000000 : ℝ)*(base19) + (336867103/100000000000000 : ℝ)*(base23) + (547259/12500000000000 : ℝ)*(upper2) + (66833283/100000000000000 : ℝ)*(upper3) + (1252569280767691/100000000000000 : ℝ)*(major0) + (1252569280767691/100000000000000 : ℝ)*(major1) + (1252569280767691/100000000000000 : ℝ)*(major2) + (424262694259259/25000000000000 : ℝ)*(sp0) + (424263104735609/25000000000000 : ℝ)*(sp1) + (84852621107281/5000000000000 : ℝ)*(sp2) + (202021269854561/25000000000000 : ℝ)*(sp3) + (1981975687/100000000000000 : ℝ)*(sp4) + (122173299/20000000000000 : ℝ)*(sp7) + (808085690284739/100000000000000 : ℝ)*(f.failure) + (424263189753181/25000000000000 : ℝ)*(f.sum) + (4917394301737/1014160000000000000000000000 : ℝ)*base66 + (8780738080272546237/1267700000000000000000000000000000 : ℝ)*base67 + (843957720114953763/1267700000000000000000000000000000 : ℝ)*base70 + (1617860526061146237/1267700000000000000000000000000000 : ℝ)*base71 + (150825809664597/25354000000000000000000000000 : ℝ)*base74 + (10051919805639953763/1267700000000000000000000000000000 : ℝ)*base76 + (8305275698495653763/1267700000000000000000000000000000 : ℝ)*base78 + (20507707999808046237/1267700000000000000000000000000000 : ℝ)*base79 + (94022831893533/25354000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (304449/312500000000000000000 : ℝ)*base89 + (304449/312500000000000000000 : ℝ)*base91 + (304449/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (317757197102985317631400149/63385000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7003889/12500000000000 : ℝ)*(base1) + (41210433/4000000000000 : ℝ)*(base19) + (248514659/25000000000000 : ℝ)*(base23) + (29110751/25000000000000 : ℝ)*(upper3) + (108079989/100000000000000 : ℝ)*(upper5) + (256985797346531/20000000000000 : ℝ)*(major0) + (256985797346531/20000000000000 : ℝ)*(major1) + (256985797346531/20000000000000 : ℝ)*(major2) + (5332896689/100000000000000 : ℝ)*(sp1) + (654925541/12500000000000 : ℝ)*(sp2) + (870447775082143/50000000000000 : ℝ)*(sp4) + (87044456548783/5000000000000 : ℝ)*(sp5) + (1740889260670211/100000000000000 : ℝ)*(sp6) + (103620282024589/12500000000000 : ℝ)*(sp7) + (51810144514239/6250000000000 : ℝ)*(f.failure) + (870447747066587/50000000000000 : ℝ)*(f.sum) + (49269291977273/25354000000000000000000000000 : ℝ)*base66 + (216492705853714117/253540000000000000000000000000000 : ℝ)*base67 + (1389055928708794117/253540000000000000000000000000000 : ℝ)*base69 + (511926396627614117/253540000000000000000000000000000 : ℝ)*base71 + (21768898424627/25354000000000000000000000000 : ℝ)*base74 + (5679903292654117/253540000000000000000000000000000 : ℝ)*base75 + (410569313999274117/253540000000000000000000000000000 : ℝ)*base77 + (2537888452948005883/253540000000000000000000000000000 : ℝ)*base80 + (50189811280241/25354000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (31477/39062500000000000000 : ℝ)*base90 + (31477/39062500000000000000 : ℝ)*base92 + (31477/39062500000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1349_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4843891/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26821/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1467/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1391/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (19409/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1349_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1349_s2_0 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2028369691/10000000000 : ℝ)*x 0 + (2738922011/5000000000 : ℝ)*x 1 + (5185570031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2028369691/10000000000 : ℝ)^4309 ≤ (48187132941/390625000000 : ℝ)^3285 := by
    have hnat : (2028369691 : ℕ)^4309*390625000000^3285 ≤ 48187132941^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2028369691 10000000000 48187132941 390625000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2738922011/5000000000 : ℝ)^4309 ≤ (227038278899/500000000000 : ℝ)^3285 := by
    have hnat : (2738922011 : ℕ)^4309*500000000000^3285 ≤ 227038278899^3285*5000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2738922011 5000000000 227038278899 500000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5185570031/10000000000 : ℝ)^4309 ≤ (21128219088681/50000000000000 : ℝ)^3285 := by
    have hnat : (5185570031 : ℕ)^4309*50000000000000^3285 ≤ 21128219088681^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5185570031 10000000000 21128219088681 50000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2028369691/10000000000 : ℝ), (2738922011/5000000000 : ℝ), (5185570031/10000000000 : ℝ)] ![(48187132941/390625000000 : ℝ), (227038278899/500000000000 : ℝ), (21128219088681/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2028369691/10000000000 : ℝ)|^4309 ≤ (48187132941/390625000000 : ℝ)^3285
        have hw : |(-2028369691/10000000000 : ℝ)|=(2028369691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2738922011/5000000000 : ℝ)|^4309 ≤ (227038278899/500000000000 : ℝ)^3285
        have hw : |(2738922011/5000000000 : ℝ)|=(2738922011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5185570031/10000000000 : ℝ)|^4309 ≤ (21128219088681/50000000000000 : ℝ)^3285
        have hw : |(5185570031/10000000000 : ℝ)|=(5185570031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_s2_1 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (335341353/625000000 : ℝ)*x 0 + (-544832983/2500000000 : ℝ)*x 1 + (5185570421/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (335341353/625000000 : ℝ)^4309 ≤ (5523702093543/12500000000000 : ℝ)^3285 := by
    have hnat : (335341353 : ℕ)^4309*12500000000000^3285 ≤ 5523702093543^3285*625000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335341353 625000000 5523702093543 12500000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (544832983/2500000000 : ℝ)^4309 ≤ (13553940888909/100000000000000 : ℝ)^3285 := by
    have hnat : (544832983 : ℕ)^4309*100000000000000^3285 ≤ 13553940888909^3285*2500000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544832983 2500000000 13553940888909 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5185570421/10000000000 : ℝ)^4309 ≤ (10564110586519/25000000000000 : ℝ)^3285 := by
    have hnat : (5185570421 : ℕ)^4309*25000000000000^3285 ≤ 10564110586519^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5185570421 10000000000 10564110586519 25000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(335341353/625000000 : ℝ), (-544832983/2500000000 : ℝ), (5185570421/10000000000 : ℝ)] ![(5523702093543/12500000000000 : ℝ), (13553940888909/100000000000000 : ℝ), (10564110586519/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(335341353/625000000 : ℝ)|^4309 ≤ (5523702093543/12500000000000 : ℝ)^3285
        have hw : |(335341353/625000000 : ℝ)|=(335341353/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-544832983/2500000000 : ℝ)|^4309 ≤ (13553940888909/100000000000000 : ℝ)^3285
        have hw : |(-544832983/2500000000 : ℝ)|=(544832983/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5185570421/10000000000 : ℝ)|^4309 ≤ (10564110586519/25000000000000 : ℝ)^3285
        have hw : |(5185570421/10000000000 : ℝ)|=(5185570421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_s2_2 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (214618469/400000000 : ℝ)*x 0 + (5185570333/10000000000 : ℝ)*x 1 + (-1089665973/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214618469/400000000 : ℝ)^4309 ≤ (22094808790097/50000000000000 : ℝ)^3285 := by
    have hnat : (214618469 : ℕ)^4309*50000000000000^3285 ≤ 22094808790097^3285*400000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214618469 400000000 22094808790097 50000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5185570333/10000000000 : ℝ)^4309 ≤ (42256441405443/100000000000000 : ℝ)^3285 := by
    have hnat : (5185570333 : ℕ)^4309*100000000000000^3285 ≤ 42256441405443^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5185570333 10000000000 42256441405443 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1089665973/5000000000 : ℝ)^4309 ≤ (13553941003121/100000000000000 : ℝ)^3285 := by
    have hnat : (1089665973 : ℕ)^4309*100000000000000^3285 ≤ 13553941003121^3285*5000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089665973 5000000000 13553941003121 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214618469/400000000 : ℝ), (5185570333/10000000000 : ℝ), (-1089665973/5000000000 : ℝ)] ![(22094808790097/50000000000000 : ℝ), (42256441405443/100000000000000 : ℝ), (13553941003121/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214618469/400000000 : ℝ)|^4309 ≤ (22094808790097/50000000000000 : ℝ)^3285
        have hw : |(214618469/400000000 : ℝ)|=(214618469/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5185570333/10000000000 : ℝ)|^4309 ≤ (42256441405443/100000000000000 : ℝ)^3285
        have hw : |(5185570333/10000000000 : ℝ)|=(5185570333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1089665973/5000000000 : ℝ)|^4309 ≤ (13553941003121/100000000000000 : ℝ)^3285
        have hw : |(-1089665973/5000000000 : ℝ)|=(1089665973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_s2_3 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1079684427/2500000000 : ℝ)*x 0 + (2010985723/5000000000 : ℝ)*x 1 + (4635772423/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079684427/2500000000 : ℝ)^4309 ≤ (4155280007557/12500000000000 : ℝ)^3285 := by
    have hnat : (1079684427 : ℕ)^4309*12500000000000^3285 ≤ 4155280007557^3285*2500000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079684427 2500000000 4155280007557 12500000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2010985723/5000000000 : ℝ)^4309 ≤ (3784815728779/12500000000000 : ℝ)^3285 := by
    have hnat : (2010985723 : ℕ)^4309*12500000000000^3285 ≤ 3784815728779^3285*5000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2010985723 5000000000 3784815728779 12500000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4635772423/10000000000 : ℝ)^4309 ≤ (36479234087719/100000000000000 : ℝ)^3285 := by
    have hnat : (4635772423 : ℕ)^4309*100000000000000^3285 ≤ 36479234087719^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4635772423 10000000000 36479234087719 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1079684427/2500000000 : ℝ), (2010985723/5000000000 : ℝ), (4635772423/10000000000 : ℝ)] ![(4155280007557/12500000000000 : ℝ), (3784815728779/12500000000000 : ℝ), (36479234087719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1079684427/2500000000 : ℝ)|^4309 ≤ (4155280007557/12500000000000 : ℝ)^3285
        have hw : |(1079684427/2500000000 : ℝ)|=(1079684427/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2010985723/5000000000 : ℝ)|^4309 ≤ (3784815728779/12500000000000 : ℝ)^3285
        have hw : |(2010985723/5000000000 : ℝ)|=(2010985723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4635772423/10000000000 : ℝ)|^4309 ≤ (36479234087719/100000000000000 : ℝ)^3285
        have hw : |(4635772423/10000000000 : ℝ)|=(4635772423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_s2_4 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2028433631/10000000000 : ℝ)*x 0 + (1296847343/2500000000 : ℝ)*x 1 + (684501051/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2028433631/10000000000 : ℝ)^4309 ≤ (12336416114693/100000000000000 : ℝ)^3285 := by
    have hnat : (2028433631 : ℕ)^4309*100000000000000^3285 ≤ 12336416114693^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2028433631 10000000000 12336416114693 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1296847343/2500000000 : ℝ)^4309 ≤ (42275886195747/100000000000000 : ℝ)^3285 := by
    have hnat : (1296847343 : ℕ)^4309*100000000000000^3285 ≤ 42275886195747^3285*2500000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296847343 2500000000 42275886195747 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (684501051/1250000000 : ℝ)^4309 ≤ (709182776231/1562500000000 : ℝ)^3285 := by
    have hnat : (684501051 : ℕ)^4309*1562500000000^3285 ≤ 709182776231^3285*1250000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      684501051 1250000000 709182776231 1562500000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2028433631/10000000000 : ℝ), (1296847343/2500000000 : ℝ), (684501051/1250000000 : ℝ)] ![(12336416114693/100000000000000 : ℝ), (42275886195747/100000000000000 : ℝ), (709182776231/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2028433631/10000000000 : ℝ)|^4309 ≤ (12336416114693/100000000000000 : ℝ)^3285
        have hw : |(-2028433631/10000000000 : ℝ)|=(2028433631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1296847343/2500000000 : ℝ)|^4309 ≤ (42275886195747/100000000000000 : ℝ)^3285
        have hw : |(1296847343/2500000000 : ℝ)|=(1296847343/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(684501051/1250000000 : ℝ)|^4309 ≤ (709182776231/1562500000000 : ℝ)^3285
        have hw : |(684501051/1250000000 : ℝ)|=(684501051/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_s2_5 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058014219/2000000000 : ℝ)*x 0 + (-1888893647/10000000000 : ℝ)*x 1 + (1369002097/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058014219/2000000000 : ℝ)^4309 ≤ (433769435269/1000000000000 : ℝ)^3285 := by
    have hnat : (1058014219 : ℕ)^4309*1000000000000^3285 ≤ 433769435269^3285*2000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058014219 2000000000 433769435269 1000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1888893647/10000000000 : ℝ)^4309 ≤ (2808839749243/25000000000000 : ℝ)^3285 := by
    have hnat : (1888893647 : ℕ)^4309*25000000000000^3285 ≤ 2808839749243^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1888893647 10000000000 2808839749243 25000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1369002097/2500000000 : ℝ)^4309 ≤ (45387697461341/100000000000000 : ℝ)^3285 := by
    have hnat : (1369002097 : ℕ)^4309*100000000000000^3285 ≤ 45387697461341^3285*2500000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1369002097 2500000000 45387697461341 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058014219/2000000000 : ℝ), (-1888893647/10000000000 : ℝ), (1369002097/2500000000 : ℝ)] ![(433769435269/1000000000000 : ℝ), (2808839749243/25000000000000 : ℝ), (45387697461341/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058014219/2000000000 : ℝ)|^4309 ≤ (433769435269/1000000000000 : ℝ)^3285
        have hw : |(1058014219/2000000000 : ℝ)|=(1058014219/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1888893647/10000000000 : ℝ)|^4309 ≤ (2808839749243/25000000000000 : ℝ)^3285
        have hw : |(-1888893647/10000000000 : ℝ)|=(1888893647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1369002097/2500000000 : ℝ)|^4309 ≤ (45387697461341/100000000000000 : ℝ)^3285
        have hw : |(1369002097/2500000000 : ℝ)|=(1369002097/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_s2_6 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (529007109/1000000000 : ℝ)*x 0 + (2738004207/5000000000 : ℝ)*x 1 + (-944446809/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529007109/1000000000 : ℝ)^4309 ≤ (43376943473121/100000000000000 : ℝ)^3285 := by
    have hnat : (529007109 : ℕ)^4309*100000000000000^3285 ≤ 43376943473121^3285*1000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529007109 1000000000 43376943473121 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2738004207/5000000000 : ℝ)^4309 ≤ (45387697744017/100000000000000 : ℝ)^3285 := by
    have hnat : (2738004207 : ℕ)^4309*100000000000000^3285 ≤ 45387697744017^3285*5000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2738004207 5000000000 45387697744017 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (944446809/5000000000 : ℝ)^4309 ≤ (11235358770707/100000000000000 : ℝ)^3285 := by
    have hnat : (944446809 : ℕ)^4309*100000000000000^3285 ≤ 11235358770707^3285*5000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      944446809 5000000000 11235358770707 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529007109/1000000000 : ℝ), (2738004207/5000000000 : ℝ), (-944446809/5000000000 : ℝ)] ![(43376943473121/100000000000000 : ℝ), (45387697744017/100000000000000 : ℝ), (11235358770707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529007109/1000000000 : ℝ)|^4309 ≤ (43376943473121/100000000000000 : ℝ)^3285
        have hw : |(529007109/1000000000 : ℝ)|=(529007109/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2738004207/5000000000 : ℝ)|^4309 ≤ (45387697744017/100000000000000 : ℝ)^3285
        have hw : |(2738004207/5000000000 : ℝ)|=(2738004207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-944446809/5000000000 : ℝ)|^4309 ≤ (11235358770707/100000000000000 : ℝ)^3285
        have hw : |(-944446809/5000000000 : ℝ)|=(944446809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_s2_7 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4318872327/10000000000 : ℝ)*x 0 + (289497017/625000000 : ℝ)*x 1 + (4025825801/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4318872327/10000000000 : ℝ)^4309 ≤ (6648719851889/20000000000000 : ℝ)^3285 := by
    have hnat : (4318872327 : ℕ)^4309*20000000000000^3285 ≤ 6648719851889^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4318872327 10000000000 6648719851889 20000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (289497017/625000000 : ℝ)^4309 ≤ (18219903737829/50000000000000 : ℝ)^3285 := by
    have hnat : (289497017 : ℕ)^4309*50000000000000^3285 ≤ 18219903737829^3285*625000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      289497017 625000000 18219903737829 50000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4025825801/10000000000 : ℝ)^4309 ≤ (30316593248623/100000000000000 : ℝ)^3285 := by
    have hnat : (4025825801 : ℕ)^4309*100000000000000^3285 ≤ 30316593248623^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4025825801 10000000000 30316593248623 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4318872327/10000000000 : ℝ), (289497017/625000000 : ℝ), (4025825801/10000000000 : ℝ)] ![(6648719851889/20000000000000 : ℝ), (18219903737829/50000000000000 : ℝ), (30316593248623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4318872327/10000000000 : ℝ)|^4309 ≤ (6648719851889/20000000000000 : ℝ)^3285
        have hw : |(4318872327/10000000000 : ℝ)|=(4318872327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(289497017/625000000 : ℝ)|^4309 ≤ (18219903737829/50000000000000 : ℝ)^3285
        have hw : |(289497017/625000000 : ℝ)|=(289497017/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4025825801/10000000000 : ℝ)|^4309 ≤ (30316593248623/100000000000000 : ℝ)^3285
        have hw : |(4025825801/10000000000 : ℝ)|=(4025825801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1349_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4843891/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19409/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1391/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (9897/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4019/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (19409/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1391/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (19409/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1391/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (19409/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1391/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (19409/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1391/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (19409/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1391/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (19409/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1391/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1391/20000 : ℝ) ^ (1077/256 : ℝ) ≤ (1347435129750453/100000000000000000000 : ℝ) := by
    have hpowers : (1391/20000 : ℝ)^1077 ≤ (1347435129750453/100000000000000000000 : ℝ)^256 := by
      have hnat : (1391 : ℕ)^1077*100000000000000000000^256 ≤ 1347435129750453^256*20000^1077 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1391 20000 1347435129750453 100000000000000000000 1077 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1391/20000 : ℝ)) (X := (1347435129750453/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1077 256 (by norm_num) hpowers
    exact h
  have hpowhi : (19409/100000 : ℝ) ^ (1077/256 : ℝ) ≤ (101066457715338627/100000000000000000000 : ℝ) := by
    have hpowers : (19409/100000 : ℝ)^1077 ≤ (101066457715338627/100000000000000000000 : ℝ)^256 := by
      have hnat : (19409 : ℕ)^1077*100000000000000000000^256 ≤ 101066457715338627^256*100000^1077 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19409 100000 101066457715338627 100000000000000000000 1077 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19409/100000 : ℝ)) (X := (101066457715338627/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1077 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001347435129750453/50000000000000000000 : ℝ) ≤ (2500016013920621/2500000000000000 : ℝ) ^ (1077/256 : ℝ) := by
    have hpowers : (50001347435129750453/50000000000000000000 : ℝ)^256 ≤ (2500016013920621/2500000000000000 : ℝ)^1077 := by
      have hnat : (50001347435129750453 : ℕ)^256*2500000000000000^1077 ≤ 2500016013920621^1077*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001347435129750453 50000000000000000000 2500016013920621 2500000000000000 256 1077 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500016013920621/2500000000000000 : ℝ)) (X := (50001347435129750453/50000000000000000000 : ℝ)) (by norm_num) 1077 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (2502560347321127227/2500000000000000000 : ℝ) ≤ (10002433400974101/10000000000000000 : ℝ) ^ (1077/256 : ℝ) := by
    have hpowers : (2502560347321127227/2500000000000000000 : ℝ)^256 ≤ (10002433400974101/10000000000000000 : ℝ)^1077 := by
      have hnat : (2502560347321127227 : ℕ)^256*10000000000000000^1077 ≤ 10002433400974101^1077*2500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2502560347321127227 2500000000000000000 10002433400974101 10000000000000000 256 1077 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002433400974101/10000000000000000 : ℝ)) (X := (2502560347321127227/2500000000000000000 : ℝ)) (by norm_num) 1077 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50101066457715338627/50000000000000000000 : ℝ) ≤ (5002401373132859/5000000000000000 : ℝ) ^ (1077/256 : ℝ) := by
    have hpowers : (50101066457715338627/50000000000000000000 : ℝ)^256 ≤ (5002401373132859/5000000000000000 : ℝ)^1077 := by
      have hnat : (50101066457715338627 : ℕ)^256*5000000000000000^1077 ≤ 5002401373132859^1077*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50101066457715338627 50000000000000000000 5002401373132859 5000000000000000 256 1077 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002401373132859/5000000000000000 : ℝ)) (X := (50101066457715338627/50000000000000000000 : ℝ)) (by norm_num) 1077 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1347435129750453/100000000000000000000 : ℝ) ≤ ((4788763082940894741/4790000000000000000 : ℝ)+2*(2369345291617/1245400000000000 : ℝ)*(1391/20000 : ℝ))^(1077/256 : ℝ) := by
    rw [show (4788763082940894741/4790000000000000000 : ℝ)+2*(2369345291617/1245400000000000 : ℝ)*(1391/20000 : ℝ)=(2500016013920621/2500000000000000 : ℝ) by norm_num, show 1+2*(1347435129750453/100000000000000000000 : ℝ)=(50001347435129750453/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(101066457715338627/100000000000000000000 : ℝ)+(1347435129750453/100000000000000000000 : ℝ) ≤ ((4788763082940894741/4790000000000000000 : ℝ)+(2369345291617/1245400000000000 : ℝ)*((19409/100000 : ℝ)+(1391/20000 : ℝ)))^(1077/256 : ℝ) := by
    rw [show (4788763082940894741/4790000000000000000 : ℝ)+(2369345291617/1245400000000000 : ℝ)*((19409/100000 : ℝ)+(1391/20000 : ℝ))=(10002433400974101/10000000000000000 : ℝ) by norm_num, show 1+(101066457715338627/100000000000000000000 : ℝ)+(1347435129750453/100000000000000000000 : ℝ)=(2502560347321127227/2500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(101066457715338627/100000000000000000000 : ℝ) ≤ ((4788763082940894741/4790000000000000000 : ℝ)+2*(2369345291617/1245400000000000 : ℝ)*(19409/100000 : ℝ))^(1077/256 : ℝ) := by
    rw [show (4788763082940894741/4790000000000000000 : ℝ)+2*(2369345291617/1245400000000000 : ℝ)*(19409/100000 : ℝ)=(5002401373132859/5000000000000000 : ℝ) by norm_num, show 1+2*(101066457715338627/100000000000000000000 : ℝ)=(50101066457715338627/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4788763082940894741/4790000000000000000 : ℝ)*(X 1 0+X 2 0)+(2369345291617/1245400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1077/256 : ℝ)) (lo := (1391/20000 : ℝ)) (hi := (19409/100000 : ℝ)) (c := (4788763082940894741/4790000000000000000 : ℝ)) (alpha := (2369345291617/1245400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4788763082940894741/4790000000000000000 : ℝ)*(X 0 1+X 2 1)+(2369345291617/1245400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1077/256 : ℝ)) (lo := (1391/20000 : ℝ)) (hi := (19409/100000 : ℝ)) (c := (4788763082940894741/4790000000000000000 : ℝ)) (alpha := (2369345291617/1245400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4788763082940894741/4790000000000000000 : ℝ)*(X 0 2+X 1 2)+(2369345291617/1245400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1077/256 : ℝ)) (lo := (1391/20000 : ℝ)) (hi := (19409/100000 : ℝ)) (c := (4788763082940894741/4790000000000000000 : ℝ)) (alpha := (2369345291617/1245400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2028369691/10000000000 : ℝ)*X 0 0+(2738922011/5000000000 : ℝ)*X 0 1+(5185570031/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((335341353/625000000 : ℝ)*X 1 0+(-544832983/2500000000 : ℝ)*X 1 1+(5185570421/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((214618469/400000000 : ℝ)*X 2 0+(5185570333/10000000000 : ℝ)*X 2 1+(-1089665973/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1079684427/2500000000 : ℝ)*X 0 0+(2010985723/5000000000 : ℝ)*X 0 1+(4635772423/10000000000 : ℝ)*X 0 2+(1079684427/2500000000 : ℝ)*X 1 0+(2010985723/5000000000 : ℝ)*X 1 1+(4635772423/10000000000 : ℝ)*X 1 2+(1079684427/2500000000 : ℝ)*X 2 0+(2010985723/5000000000 : ℝ)*X 2 1+(4635772423/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2028433631/10000000000 : ℝ)*X 0 0+(1296847343/2500000000 : ℝ)*X 0 1+(684501051/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1058014219/2000000000 : ℝ)*X 1 0+(-1888893647/10000000000 : ℝ)*X 1 1+(1369002097/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((529007109/1000000000 : ℝ)*X 2 0+(2738004207/5000000000 : ℝ)*X 2 1+(-944446809/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4318872327/10000000000 : ℝ)*X 0 0+(289497017/625000000 : ℝ)*X 0 1+(4025825801/10000000000 : ℝ)*X 0 2+(4318872327/10000000000 : ℝ)*X 1 0+(289497017/625000000 : ℝ)*X 1 1+(4025825801/10000000000 : ℝ)*X 1 2+(4318872327/10000000000 : ℝ)*X 2 0+(289497017/625000000 : ℝ)*X 2 1+(4025825801/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (145862880584713655957337/15567500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1652361309/100000000000000 : ℝ)*(base19) + (1643473153/100000000000000 : ℝ)*(base23) + (31114411/100000000000000 : ℝ)*(lower2) + (22286689/10000000000000 : ℝ)*(upper3) + (174534697/100000000000000 : ℝ)*(upper5) + (2525355055982791/100000000000000 : ℝ)*(major0) + (2525355055982791/100000000000000 : ℝ)*(major1) + (315669381997849/12500000000000 : ℝ)*(major2) + (1710735793970127/50000000000000 : ℝ)*(sp0) + (68429884934627/2000000000000 : ℝ)*(sp1) + (1710747127809753/50000000000000 : ℝ)*(sp2) + (407300708589639/25000000000000 : ℝ)*(sp3) + (6077788101/25000000000000 : ℝ)*(sp4) + (5533095431/50000000000000 : ℝ)*(sp7) + (814606950274709/50000000000000 : ℝ)*(f.failure) + (3421495899092659/100000000000000 : ℝ)*(f.sum) + (15923632087973/9580000000000000000000000000 : ℝ)*base66 + (85309652089300427703/6227000000000000000000000000000000 : ℝ)*base67 + (8955300180483901167/778375000000000000000000000000000 : ℝ)*base69 + (23766791295938427703/6227000000000000000000000000000000 : ℝ)*base71 + (61725169157547/9580000000000000000000000000 : ℝ)*base73 + (6502493813164598833/778375000000000000000000000000000 : ℝ)*base76 + (25060160740992422297/6227000000000000000000000000000000 : ℝ)*base78 + (36863019329474422297/6227000000000000000000000000000000 : ℝ)*base80 + (121150818072067/62270000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (484781/156250000000000000000 : ℝ)*base90 + (484781/156250000000000000000 : ℝ)*base92 + (2047281/156250000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3620462331896078679186776871/1556750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9212859/1562500000000 : ℝ)*(base19) + (21644119/3125000000000 : ℝ)*(base23) + (70858211/100000000000000 : ℝ)*(upper3) + (19527073/50000000000000 : ℝ)*(lower4) + (1805379/20000000000000 : ℝ)*(upper5) + (2557297173369771/100000000000000 : ℝ)*(major0) + (2557297173369771/100000000000000 : ℝ)*(major1) + (2557297173369771/100000000000000 : ℝ)*(major2) + (6505939461/100000000000000 : ℝ)*(sp1) + (8782085627/100000000000000 : ℝ)*(sp2) + (3464773150868753/100000000000000 : ℝ)*(sp4) + (866191513826579/25000000000000 : ℝ)*(sp5) + (1732381838085659/50000000000000 : ℝ)*(sp6) + (65992844733959/4000000000000 : ℝ)*(sp7) + (65992844733959/4000000000000 : ℝ)*(f.failure) + (3464773150868753/100000000000000 : ℝ)*(f.sum) + (143819661098433/62270000000000000000000000000 : ℝ)*base66 + (46379264191922916043/6227000000000000000000000000000000 : ℝ)*base67 + (19867407665481916043/6227000000000000000000000000000000 : ℝ)*base69 + (16605771364416083957/6227000000000000000000000000000000 : ℝ)*base72 + (162019729471787/62270000000000000000000000000 : ℝ)*base73 + (56163429547926916043/6227000000000000000000000000000000 : ℝ)*base75 + (28650224887114916043/6227000000000000000000000000000000 : ℝ)*base77 + (8822481595693916043/6227000000000000000000000000000000 : ℝ)*base79 + (318140330781723/62270000000000000000000000000 : ℝ)*base82 + (19469/12500000000000000000 : ℝ)*base89 + (19469/12500000000000000000 : ℝ)*base91 + (19469/12500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1349_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4843891/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19409/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1391/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9897/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4019/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1349_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1349_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4843891/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9897/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4019/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1349_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1349_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1349_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4843891/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9897/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4019/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1349_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
