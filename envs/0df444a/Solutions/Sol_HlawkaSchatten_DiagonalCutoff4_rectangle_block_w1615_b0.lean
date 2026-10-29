-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1615_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:52:28.346286+00:00
-- url     : https://prove2.me/submissions/030540c4-f758-4c9b-9861-9fdd25baa3dc

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
theorem support_rectangle_w1615_s0_0 (p : ℝ) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-311222129/2000000000 : ℝ)*x 0 + (5830389081/10000000000 : ℝ)*x 1 + (195869329/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (311222129/2000000000 : ℝ)^4779 ≤ (9369306284381/100000000000000 : ℝ)^3755 := by
    have hnat : (311222129 : ℕ)^4779*100000000000000^3755 ≤ 9369306284381^3755*2000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      311222129 2000000000 9369306284381 100000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5830389081/10000000000 : ℝ)^4779 ≤ (50327173331269/100000000000000 : ℝ)^3755 := by
    have hnat : (5830389081 : ℕ)^4779*100000000000000^3755 ≤ 50327173331269^3755*10000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5830389081 10000000000 50327173331269 100000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (195869329/400000000 : ℝ)^4779 ≤ (20151760183941/50000000000000 : ℝ)^3755 := by
    have hnat : (195869329 : ℕ)^4779*50000000000000^3755 ≤ 20151760183941^3755*400000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      195869329 400000000 20151760183941 50000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4779/1024 : ℝ)) 4779 3755 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-311222129/2000000000 : ℝ), (5830389081/10000000000 : ℝ), (195869329/400000000 : ℝ)] ![(9369306284381/100000000000000 : ℝ), (50327173331269/100000000000000 : ℝ), (20151760183941/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-311222129/2000000000 : ℝ)|^4779 ≤ (9369306284381/100000000000000 : ℝ)^3755
        have hw : |(-311222129/2000000000 : ℝ)|=(311222129/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5830389081/10000000000 : ℝ)|^4779 ≤ (50327173331269/100000000000000 : ℝ)^3755
        have hw : |(5830389081/10000000000 : ℝ)|=(5830389081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(195869329/400000000 : ℝ)|^4779 ≤ (20151760183941/50000000000000 : ℝ)^3755
        have hw : |(195869329/400000000 : ℝ)|=(195869329/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1615_s0_1 (p : ℝ) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1362915337/2500000000 : ℝ)*x 0 + (-103623411/500000000 : ℝ)*x 1 + (4896733359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1362915337/2500000000 : ℝ)^4779 ≤ (46203990512009/100000000000000 : ℝ)^3755 := by
    have hnat : (1362915337 : ℕ)^4779*100000000000000^3755 ≤ 46203990512009^3755*2500000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1362915337 2500000000 46203990512009 100000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (103623411/500000000 : ℝ)^4779 ≤ (269849754173/2000000000000 : ℝ)^3755 := by
    have hnat : (103623411 : ℕ)^4779*2000000000000^3755 ≤ 269849754173^3755*500000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103623411 500000000 269849754173 2000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4896733359/10000000000 : ℝ)^4779 ≤ (40303521771563/100000000000000 : ℝ)^3755 := by
    have hnat : (4896733359 : ℕ)^4779*100000000000000^3755 ≤ 40303521771563^3755*10000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4896733359 10000000000 40303521771563 100000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4779/1024 : ℝ)) 4779 3755 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1362915337/2500000000 : ℝ), (-103623411/500000000 : ℝ), (4896733359/10000000000 : ℝ)] ![(46203990512009/100000000000000 : ℝ), (269849754173/2000000000000 : ℝ), (40303521771563/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1362915337/2500000000 : ℝ)|^4779 ≤ (46203990512009/100000000000000 : ℝ)^3755
        have hw : |(1362915337/2500000000 : ℝ)|=(1362915337/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-103623411/500000000 : ℝ)|^4779 ≤ (269849754173/2000000000000 : ℝ)^3755
        have hw : |(-103623411/500000000 : ℝ)|=(103623411/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4896733359/10000000000 : ℝ)|^4779 ≤ (40303521771563/100000000000000 : ℝ)^3755
        have hw : |(4896733359/10000000000 : ℝ)|=(4896733359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1615_s0_2 (p : ℝ) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5451661517/10000000000 : ℝ)*x 0 + (2448366621/5000000000 : ℝ)*x 1 + (-2072468147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5451661517/10000000000 : ℝ)^4779 ≤ (11550998083729/25000000000000 : ℝ)^3755 := by
    have hnat : (5451661517 : ℕ)^4779*25000000000000^3755 ≤ 11550998083729^3755*10000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5451661517 10000000000 11550998083729 25000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2448366621/5000000000 : ℝ)^4779 ≤ (40303520545961/100000000000000 : ℝ)^3755 := by
    have hnat : (2448366621 : ℕ)^4779*100000000000000^3755 ≤ 40303520545961^3755*5000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2448366621 5000000000 40303520545961 100000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2072468147/10000000000 : ℝ)^4779 ≤ (13492487103791/100000000000000 : ℝ)^3755 := by
    have hnat : (2072468147 : ℕ)^4779*100000000000000^3755 ≤ 13492487103791^3755*10000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2072468147 10000000000 13492487103791 100000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4779/1024 : ℝ)) 4779 3755 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5451661517/10000000000 : ℝ), (2448366621/5000000000 : ℝ), (-2072468147/10000000000 : ℝ)] ![(11550998083729/25000000000000 : ℝ), (40303520545961/100000000000000 : ℝ), (13492487103791/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5451661517/10000000000 : ℝ)|^4779 ≤ (11550998083729/25000000000000 : ℝ)^3755
        have hw : |(5451661517/10000000000 : ℝ)|=(5451661517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2448366621/5000000000 : ℝ)|^4779 ≤ (40303520545961/100000000000000 : ℝ)^3755
        have hw : |(2448366621/5000000000 : ℝ)|=(2448366621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2072468147/10000000000 : ℝ)|^4779 ≤ (13492487103791/100000000000000 : ℝ)^3755
        have hw : |(-2072468147/10000000000 : ℝ)|=(2072468147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1615_s0_3 (p : ℝ) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (821466941/2000000000 : ℝ)*x 0 + (1537568163/5000000000 : ℝ)*x 1 + (67306981/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (821466941/2000000000 : ℝ)^4779 ≤ (32223799682429/100000000000000 : ℝ)^3755 := by
    have hnat : (821466941 : ℕ)^4779*100000000000000^3755 ≤ 32223799682429^3755*2000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      821466941 2000000000 32223799682429 100000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1537568163/5000000000 : ℝ)^4779 ≤ (22294791733911/100000000000000 : ℝ)^3755 := by
    have hnat : (1537568163 : ℕ)^4779*100000000000000^3755 ≤ 22294791733911^3755*5000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1537568163 5000000000 22294791733911 100000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (67306981/125000000 : ℝ)^4779 ≤ (181925634279/400000000000 : ℝ)^3755 := by
    have hnat : (67306981 : ℕ)^4779*400000000000^3755 ≤ 181925634279^3755*125000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67306981 125000000 181925634279 400000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4779/1024 : ℝ)) 4779 3755 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(821466941/2000000000 : ℝ), (1537568163/5000000000 : ℝ), (67306981/125000000 : ℝ)] ![(32223799682429/100000000000000 : ℝ), (22294791733911/100000000000000 : ℝ), (181925634279/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(821466941/2000000000 : ℝ)|^4779 ≤ (32223799682429/100000000000000 : ℝ)^3755
        have hw : |(821466941/2000000000 : ℝ)|=(821466941/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1537568163/5000000000 : ℝ)|^4779 ≤ (22294791733911/100000000000000 : ℝ)^3755
        have hw : |(1537568163/5000000000 : ℝ)|=(1537568163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(67306981/125000000 : ℝ)|^4779 ≤ (181925634279/400000000000 : ℝ)^3755
        have hw : |(67306981/125000000 : ℝ)|=(67306981/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1615_s0_4 (p : ℝ) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1558837469/10000000000 : ℝ)*x 0 + (2460154901/5000000000 : ℝ)*x 1 + (580597707/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1558837469/10000000000 : ℝ)^4779 ≤ (9390206697507/100000000000000 : ℝ)^3755 := by
    have hnat : (1558837469 : ℕ)^4779*100000000000000^3755 ≤ 9390206697507^3755*10000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1558837469 10000000000 9390206697507 100000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2460154901/5000000000 : ℝ)^4779 ≤ (40550652415251/100000000000000 : ℝ)^3755 := by
    have hnat : (2460154901 : ℕ)^4779*100000000000000^3755 ≤ 40550652415251^3755*5000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2460154901 5000000000 40550652415251 100000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (580597707/1000000000 : ℝ)^4779 ≤ (2002365635109/4000000000000 : ℝ)^3755 := by
    have hnat : (580597707 : ℕ)^4779*4000000000000^3755 ≤ 2002365635109^3755*1000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      580597707 1000000000 2002365635109 4000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4779/1024 : ℝ)) 4779 3755 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1558837469/10000000000 : ℝ), (2460154901/5000000000 : ℝ), (580597707/1000000000 : ℝ)] ![(9390206697507/100000000000000 : ℝ), (40550652415251/100000000000000 : ℝ), (2002365635109/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1558837469/10000000000 : ℝ)|^4779 ≤ (9390206697507/100000000000000 : ℝ)^3755
        have hw : |(-1558837469/10000000000 : ℝ)|=(1558837469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2460154901/5000000000 : ℝ)|^4779 ≤ (40550652415251/100000000000000 : ℝ)^3755
        have hw : |(2460154901/5000000000 : ℝ)|=(2460154901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(580597707/1000000000 : ℝ)|^4779 ≤ (2002365635109/4000000000000 : ℝ)^3755
        have hw : |(580597707/1000000000 : ℝ)|=(580597707/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1615_s0_5 (p : ℝ) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5196681423/10000000000 : ℝ)*x 0 + (-1163224697/10000000000 : ℝ)*x 1 + (145149429/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5196681423/10000000000 : ℝ)^4779 ≤ (10867852550173/25000000000000 : ℝ)^3755 := by
    have hnat : (5196681423 : ℕ)^4779*25000000000000^3755 ≤ 10867852550173^3755*10000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196681423 10000000000 10867852550173 25000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1163224697/10000000000 : ℝ)^4779 ≤ (10108512361/156250000000 : ℝ)^3755 := by
    have hnat : (1163224697 : ℕ)^4779*156250000000^3755 ≤ 10108512361^3755*10000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1163224697 10000000000 10108512361 156250000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (145149429/250000000 : ℝ)^4779 ≤ (50059141865317/100000000000000 : ℝ)^3755 := by
    have hnat : (145149429 : ℕ)^4779*100000000000000^3755 ≤ 50059141865317^3755*250000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      145149429 250000000 50059141865317 100000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4779/1024 : ℝ)) 4779 3755 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5196681423/10000000000 : ℝ), (-1163224697/10000000000 : ℝ), (145149429/250000000 : ℝ)] ![(10867852550173/25000000000000 : ℝ), (10108512361/156250000000 : ℝ), (50059141865317/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5196681423/10000000000 : ℝ)|^4779 ≤ (10867852550173/25000000000000 : ℝ)^3755
        have hw : |(5196681423/10000000000 : ℝ)|=(5196681423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1163224697/10000000000 : ℝ)|^4779 ≤ (10108512361/156250000000 : ℝ)^3755
        have hw : |(-1163224697/10000000000 : ℝ)|=(1163224697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(145149429/250000000 : ℝ)|^4779 ≤ (50059141865317/100000000000000 : ℝ)^3755
        have hw : |(145149429/250000000 : ℝ)|=(145149429/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1615_s0_6 (p : ℝ) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5196681469/10000000000 : ℝ)*x 0 + (5805977573/10000000000 : ℝ)*x 1 + (-116322399/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5196681469/10000000000 : ℝ)^4779 ≤ (43471410690429/100000000000000 : ℝ)^3755 := by
    have hnat : (5196681469 : ℕ)^4779*100000000000000^3755 ≤ 43471410690429^3755*10000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196681469 10000000000 43471410690429 100000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5805977573/10000000000 : ℝ)^4779 ≤ (12514786599317/25000000000000 : ℝ)^3755 := by
    have hnat : (5805977573 : ℕ)^4779*25000000000000^3755 ≤ 12514786599317^3755*10000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5805977573 10000000000 12514786599317 25000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (116322399/1000000000 : ℝ)^4779 ≤ (3234721453331/50000000000000 : ℝ)^3755 := by
    have hnat : (116322399 : ℕ)^4779*50000000000000^3755 ≤ 3234721453331^3755*1000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      116322399 1000000000 3234721453331 50000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4779/1024 : ℝ)) 4779 3755 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5196681469/10000000000 : ℝ), (5805977573/10000000000 : ℝ), (-116322399/1000000000 : ℝ)] ![(43471410690429/100000000000000 : ℝ), (12514786599317/25000000000000 : ℝ), (3234721453331/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5196681469/10000000000 : ℝ)|^4779 ≤ (43471410690429/100000000000000 : ℝ)^3755
        have hw : |(5196681469/10000000000 : ℝ)|=(5196681469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5805977573/10000000000 : ℝ)|^4779 ≤ (12514786599317/25000000000000 : ℝ)^3755
        have hw : |(5805977573/10000000000 : ℝ)|=(5805977573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-116322399/1000000000 : ℝ)|^4779 ≤ (3234721453331/50000000000000 : ℝ)^3755
        have hw : |(-116322399/1000000000 : ℝ)|=(116322399/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1615_s0_7 (p : ℝ) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (822815403/2000000000 : ℝ)*x 0 + (1065248339/2000000000 : ℝ)*x 1 + (48992487/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (822815403/2000000000 : ℝ)^4779 ≤ (32291136039437/100000000000000 : ℝ)^3755 := by
    have hnat : (822815403 : ℕ)^4779*100000000000000^3755 ≤ 32291136039437^3755*2000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      822815403 2000000000 32291136039437 100000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1065248339/2000000000 : ℝ)^4779 ≤ (44855427841083/100000000000000 : ℝ)^3755 := by
    have hnat : (1065248339 : ℕ)^4779*100000000000000^3755 ≤ 44855427841083^3755*2000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065248339 2000000000 44855427841083 100000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (48992487/156250000 : ℝ)^4779 ≤ (4570687220811/20000000000000 : ℝ)^3755 := by
    have hnat : (48992487 : ℕ)^4779*20000000000000^3755 ≤ 4570687220811^3755*156250000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48992487 156250000 4570687220811 20000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4779/1024 : ℝ)) 4779 3755 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(822815403/2000000000 : ℝ), (1065248339/2000000000 : ℝ), (48992487/156250000 : ℝ)] ![(32291136039437/100000000000000 : ℝ), (44855427841083/100000000000000 : ℝ), (4570687220811/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(822815403/2000000000 : ℝ)|^4779 ≤ (32291136039437/100000000000000 : ℝ)^3755
        have hw : |(822815403/2000000000 : ℝ)|=(822815403/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1065248339/2000000000 : ℝ)|^4779 ≤ (44855427841083/100000000000000 : ℝ)^3755
        have hw : |(1065248339/2000000000 : ℝ)|=(1065248339/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(48992487/156250000 : ℝ)|^4779 ≤ (4570687220811/20000000000000 : ℝ)^3755
        have hw : |(48992487/156250000 : ℝ)|=(48992487/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1615_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (173676369/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (413/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (754/3125 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4775/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4775 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4775*1^1024 ≤ 0^1024*1^4775 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4775 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4775 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4775/1024 : ℝ) ≤ (1394349167099143977/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4775 ≤ (1394349167099143977/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4775*100000000000000000000^1024 ≤ 1394349167099143977^1024*5^4775 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1394349167099143977 100000000000000000000 4775 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1394349167099143977/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4775 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4775/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4775 := by
      have hnat : (1 : ℕ)^1024*1^4775 ≤ 1^4775*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4775 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4775 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101394349167099143977/100000000000000000000 : ℝ) ≤ (2507434859574379/2500000000000000 : ℝ) ^ (4775/1024 : ℝ) := by
    have hpowers : (101394349167099143977/100000000000000000000 : ℝ)^1024 ≤ (2507434859574379/2500000000000000 : ℝ)^4775 := by
      have hnat : (101394349167099143977 : ℕ)^1024*2500000000000000^4775 ≤ 2507434859574379^4775*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101394349167099143977 100000000000000000000 2507434859574379 2500000000000000 1024 4775 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2507434859574379/2500000000000000 : ℝ)) (X := (101394349167099143977/100000000000000000000 : ℝ)) (by norm_num) 4775 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51394349167099143977/50000000000000000000 : ℝ) ≤ (1257434859574379/1250000000000000 : ℝ) ^ (4775/1024 : ℝ) := by
    have hpowers : (51394349167099143977/50000000000000000000 : ℝ)^1024 ≤ (1257434859574379/1250000000000000 : ℝ)^4775 := by
      have hnat : (51394349167099143977 : ℕ)^1024*1250000000000000^4775 ≤ 1257434859574379^4775*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51394349167099143977 50000000000000000000 1257434859574379 1250000000000000 1024 4775 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1257434859574379/1250000000000000 : ℝ)) (X := (51394349167099143977/50000000000000000000 : ℝ)) (by norm_num) 4775 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(7434859574379/1000000000000000 : ℝ)*(0 : ℝ))^(4775/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(7434859574379/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1394349167099143977/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(7434859574379/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4775/1024 : ℝ) := by
    rw [show (1 : ℝ)+(7434859574379/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2507434859574379/2500000000000000 : ℝ) by norm_num, show 1+(1394349167099143977/100000000000000000000 : ℝ)+(0 : ℝ)=(101394349167099143977/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1394349167099143977/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(7434859574379/1000000000000000 : ℝ)*(2/5 : ℝ))^(4775/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(7434859574379/1000000000000000 : ℝ)*(2/5 : ℝ)=(1257434859574379/1250000000000000 : ℝ) by norm_num, show 1+2*(1394349167099143977/100000000000000000000 : ℝ)=(51394349167099143977/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(7434859574379/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4775/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (7434859574379/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(7434859574379/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4775/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (7434859574379/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(7434859574379/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4775/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (7434859574379/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-311222129/2000000000 : ℝ)*X 0 0+(5830389081/10000000000 : ℝ)*X 0 1+(195869329/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1615_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1362915337/2500000000 : ℝ)*X 1 0+(-103623411/500000000 : ℝ)*X 1 1+(4896733359/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1615_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5451661517/10000000000 : ℝ)*X 2 0+(2448366621/5000000000 : ℝ)*X 2 1+(-2072468147/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1615_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((821466941/2000000000 : ℝ)*X 0 0+(1537568163/5000000000 : ℝ)*X 0 1+(67306981/125000000 : ℝ)*X 0 2+(821466941/2000000000 : ℝ)*X 1 0+(1537568163/5000000000 : ℝ)*X 1 1+(67306981/125000000 : ℝ)*X 1 2+(821466941/2000000000 : ℝ)*X 2 0+(1537568163/5000000000 : ℝ)*X 2 1+(67306981/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1615_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1558837469/10000000000 : ℝ)*X 0 0+(2460154901/5000000000 : ℝ)*X 0 1+(580597707/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1615_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5196681423/10000000000 : ℝ)*X 1 0+(-1163224697/10000000000 : ℝ)*X 1 1+(145149429/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1615_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5196681469/10000000000 : ℝ)*X 2 0+(5805977573/10000000000 : ℝ)*X 2 1+(-116322399/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1615_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((822815403/2000000000 : ℝ)*X 0 0+(1065248339/2000000000 : ℝ)*X 0 1+(48992487/156250000 : ℝ)*X 0 2+(822815403/2000000000 : ℝ)*X 1 0+(1065248339/2000000000 : ℝ)*X 1 1+(48992487/156250000 : ℝ)*X 1 2+(822815403/2000000000 : ℝ)*X 2 0+(1065248339/2000000000 : ℝ)*X 2 1+(48992487/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1615_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (108908467034907815291649/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (60220413/50000000000000 : ℝ)*(base1) + (90416403/5000000000000 : ℝ)*(base19) + (92076547/5000000000000 : ℝ)*(base23) + (226186269/100000000000000 : ℝ)*(upper3) + (64510233/25000000000000 : ℝ)*(upper5) + (752043218000123/100000000000000 : ℝ)*(major0) + (752043218000123/100000000000000 : ℝ)*(major1) + (752043218000123/100000000000000 : ℝ)*(major2) + (1071064965061443/100000000000000 : ℝ)*(sp0) + (535535103694131/50000000000000 : ℝ)*(sp1) + (535535087092691/50000000000000 : ℝ)*(sp2) + (433011348439067/100000000000000 : ℝ)*(sp3) + (1434219141/20000000000000 : ℝ)*(sp4) + (2660981449/100000000000000 : ℝ)*(sp7) + (216507064930671/50000000000000 : ℝ)*(f.failure) + (535536007858161/50000000000000 : ℝ)*(f.sum) + (35444829851383/50000000000000000000000000000 : ℝ)*base66 + (231252530648617/100000000000000000000000000000 : ℝ)*base67 + (395991287948617/100000000000000000000000000000 : ℝ)*base69 + (396648135048617/100000000000000000000000000000 : ℝ)*base71 + (37072836798617/50000000000000000000000000000 : ℝ)*base73 + (526950884648617/100000000000000000000000000000 : ℝ)*base75 + (206743403248617/100000000000000000000000000000 : ℝ)*base77 + (415556115548617/100000000000000000000000000000 : ℝ)*base79 + (200898077748617/50000000000000000000000000000 : ℝ)*base81 + (26013599/5000000000000000000000 : ℝ)*base89 + (26013599/5000000000000000000000 : ℝ)*base91 + (26013599/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (502017532646603184788499/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2012274947/100000000000000 : ℝ)*(base19) + (228219609/10000000000000 : ℝ)*(base23) + (49504509/20000000000000 : ℝ)*(base39) + (53833109/20000000000000 : ℝ)*(upper3) + (199182601/50000000000000 : ℝ)*(upper5) + (792780606032559/100000000000000 : ℝ)*(major0) + (792780606032559/100000000000000 : ℝ)*(major1) + (396390179255007/50000000000000 : ℝ)*(major2) + (251303/3906250000 : ℝ)*(sp1) + (3379166539/50000000000000 : ℝ)*(sp2) + (564545290617267/50000000000000 : ℝ)*(sp4) + (1129082135602787/100000000000000 : ℝ)*(sp5) + (141135223528489/12500000000000 : ℝ)*(sp6) + (228235024314839/50000000000000 : ℝ)*(sp7) + (228235024314839/50000000000000 : ℝ)*(f.failure) + (28227270718927/2500000000000 : ℝ)*(f.sum) + (112064466862833/100000000000000000000000000000 : ℝ)*base66 + (222903000765653/50000000000000000000000000000 : ℝ)*base67 + (537406227805861/100000000000000000000000000000 : ℝ)*base69 + (143382151115653/50000000000000000000000000000 : ℝ)*base71 + (167335438437167/100000000000000000000000000000 : ℝ)*base73 + (500636153805861/100000000000000000000000000000 : ℝ)*base75 + (197350766194139/100000000000000000000000000000 : ℝ)*base78 + (304055509994139/100000000000000000000000000000 : ℝ)*base80 + (172026928305861/50000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (339591/5000000000000000000000 : ℝ)*base89 + (339591/5000000000000000000000 : ℝ)*base91 + (339591/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1615_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (173676369/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (413/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (754/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1615_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1615_s1_0 (p : ℝ) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1677215447/10000000000 : ℝ)*x 0 + (2762640701/5000000000 : ℝ)*x 1 + (5123469379/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1677215447/10000000000 : ℝ)^4779 ≤ (2576747526583/25000000000000 : ℝ)^3755 := by
    have hnat : (1677215447 : ℕ)^4779*25000000000000^3755 ≤ 2576747526583^3755*10000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1677215447 10000000000 2576747526583 25000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2762640701/5000000000 : ℝ)^4779 ≤ (9399909089681/20000000000000 : ℝ)^3755 := by
    have hnat : (2762640701 : ℕ)^4779*20000000000000^3755 ≤ 9399909089681^3755*5000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2762640701 5000000000 9399909089681 20000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5123469379/10000000000 : ℝ)^4779 ≤ (10673366108017/25000000000000 : ℝ)^3755 := by
    have hnat : (5123469379 : ℕ)^4779*25000000000000^3755 ≤ 10673366108017^3755*10000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5123469379 10000000000 10673366108017 25000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4779/1024 : ℝ)) 4779 3755 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1677215447/10000000000 : ℝ), (2762640701/5000000000 : ℝ), (5123469379/10000000000 : ℝ)] ![(2576747526583/25000000000000 : ℝ), (9399909089681/20000000000000 : ℝ), (10673366108017/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1677215447/10000000000 : ℝ)|^4779 ≤ (2576747526583/25000000000000 : ℝ)^3755
        have hw : |(-1677215447/10000000000 : ℝ)|=(1677215447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2762640701/5000000000 : ℝ)|^4779 ≤ (9399909089681/20000000000000 : ℝ)^3755
        have hw : |(2762640701/5000000000 : ℝ)|=(2762640701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5123469379/10000000000 : ℝ)|^4779 ≤ (10673366108017/25000000000000 : ℝ)^3755
        have hw : |(5123469379/10000000000 : ℝ)|=(5123469379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1615_s1_1 (p : ℝ) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167827553/312500000 : ℝ)*x 0 + (-943591587/5000000000 : ℝ)*x 1 + (5123469213/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167827553/312500000 : ℝ)^4779 ≤ (45330136270201/100000000000000 : ℝ)^3755 := by
    have hnat : (167827553 : ℕ)^4779*100000000000000^3755 ≤ 45330136270201^3755*312500000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167827553 312500000 45330136270201 100000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (943591587/5000000000 : ℝ)^4779 ≤ (2395280211193/20000000000000 : ℝ)^3755 := by
    have hnat : (943591587 : ℕ)^4779*20000000000000^3755 ≤ 2395280211193^3755*5000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      943591587 5000000000 2395280211193 20000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5123469213/10000000000 : ℝ)^4779 ≤ (21346731335791/50000000000000 : ℝ)^3755 := by
    have hnat : (5123469213 : ℕ)^4779*50000000000000^3755 ≤ 21346731335791^3755*10000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5123469213 10000000000 21346731335791 50000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4779/1024 : ℝ)) 4779 3755 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167827553/312500000 : ℝ), (-943591587/5000000000 : ℝ), (5123469213/10000000000 : ℝ)] ![(45330136270201/100000000000000 : ℝ), (2395280211193/20000000000000 : ℝ), (21346731335791/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167827553/312500000 : ℝ)|^4779 ≤ (45330136270201/100000000000000 : ℝ)^3755
        have hw : |(167827553/312500000 : ℝ)|=(167827553/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-943591587/5000000000 : ℝ)|^4779 ≤ (2395280211193/20000000000000 : ℝ)^3755
        have hw : |(-943591587/5000000000 : ℝ)|=(943591587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5123469213/10000000000 : ℝ)|^4779 ≤ (21346731335791/50000000000000 : ℝ)^3755
        have hw : |(5123469213/10000000000 : ℝ)|=(5123469213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1615_s1_2 (p : ℝ) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167827551/312500000 : ℝ)*x 0 + (640433649/1250000000 : ℝ)*x 1 + (-377436657/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167827551/312500000 : ℝ)^4779 ≤ (1416566736959/3125000000000 : ℝ)^3755 := by
    have hnat : (167827551 : ℕ)^4779*3125000000000^3755 ≤ 1416566736959^3755*312500000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167827551 312500000 1416566736959 3125000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (640433649/1250000000 : ℝ)^4779 ≤ (4269346244887/10000000000000 : ℝ)^3755 := by
    have hnat : (640433649 : ℕ)^4779*10000000000000^3755 ≤ 4269346244887^3755*1250000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      640433649 1250000000 4269346244887 10000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (377436657/2000000000 : ℝ)^4779 ≤ (1197640195249/10000000000000 : ℝ)^3755 := by
    have hnat : (377436657 : ℕ)^4779*10000000000000^3755 ≤ 1197640195249^3755*2000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      377436657 2000000000 1197640195249 10000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4779/1024 : ℝ)) 4779 3755 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167827551/312500000 : ℝ), (640433649/1250000000 : ℝ), (-377436657/2000000000 : ℝ)] ![(1416566736959/3125000000000 : ℝ), (4269346244887/10000000000000 : ℝ), (1197640195249/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167827551/312500000 : ℝ)|^4779 ≤ (1416566736959/3125000000000 : ℝ)^3755
        have hw : |(167827551/312500000 : ℝ)|=(167827551/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(640433649/1250000000 : ℝ)|^4779 ≤ (4269346244887/10000000000000 : ℝ)^3755
        have hw : |(640433649/1250000000 : ℝ)|=(640433649/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-377436657/2000000000 : ℝ)|^4779 ≤ (1197640195249/10000000000000 : ℝ)^3755
        have hw : |(-377436657/2000000000 : ℝ)|=(377436657/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1615_s1_3 (p : ℝ) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2098888359/5000000000 : ℝ)*x 0 + (1861621753/5000000000 : ℝ)*x 1 + (943427471/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2098888359/5000000000 : ℝ)^4779 ≤ (662591023809/2000000000000 : ℝ)^3755 := by
    have hnat : (2098888359 : ℕ)^4779*2000000000000^3755 ≤ 662591023809^3755*5000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2098888359 5000000000 662591023809 2000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1861621753/5000000000 : ℝ)^4779 ≤ (28438743453731/100000000000000 : ℝ)^3755 := by
    have hnat : (1861621753 : ℕ)^4779*100000000000000^3755 ≤ 28438743453731^3755*5000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1861621753 5000000000 28438743453731 100000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (943427471/2000000000 : ℝ)^4779 ≤ (19215852672143/50000000000000 : ℝ)^3755 := by
    have hnat : (943427471 : ℕ)^4779*50000000000000^3755 ≤ 19215852672143^3755*2000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      943427471 2000000000 19215852672143 50000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4779/1024 : ℝ)) 4779 3755 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2098888359/5000000000 : ℝ), (1861621753/5000000000 : ℝ), (943427471/2000000000 : ℝ)] ![(662591023809/2000000000000 : ℝ), (28438743453731/100000000000000 : ℝ), (19215852672143/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2098888359/5000000000 : ℝ)|^4779 ≤ (662591023809/2000000000000 : ℝ)^3755
        have hw : |(2098888359/5000000000 : ℝ)|=(2098888359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1861621753/5000000000 : ℝ)|^4779 ≤ (28438743453731/100000000000000 : ℝ)^3755
        have hw : |(1861621753/5000000000 : ℝ)|=(1861621753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(943427471/2000000000 : ℝ)|^4779 ≤ (19215852672143/50000000000000 : ℝ)^3755
        have hw : |(943427471/2000000000 : ℝ)|=(943427471/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1615_s1_4 (p : ℝ) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-104839257/625000000 : ℝ)*x 0 + (5127800959/10000000000 : ℝ)*x 1 + (172527609/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (104839257/625000000 : ℝ)^4779 ≤ (10308653417959/100000000000000 : ℝ)^3755 := by
    have hnat : (104839257 : ℕ)^4779*100000000000000^3755 ≤ 10308653417959^3755*625000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104839257 625000000 10308653417959 100000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5127800959/10000000000 : ℝ)^4779 ≤ (427394075783/1000000000000 : ℝ)^3755 := by
    have hnat : (5127800959 : ℕ)^4779*1000000000000^3755 ≤ 427394075783^3755*10000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5127800959 10000000000 427394075783 1000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (172527609/312500000 : ℝ)^4779 ≤ (46951938983647/100000000000000 : ℝ)^3755 := by
    have hnat : (172527609 : ℕ)^4779*100000000000000^3755 ≤ 46951938983647^3755*312500000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172527609 312500000 46951938983647 100000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4779/1024 : ℝ)) 4779 3755 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-104839257/625000000 : ℝ), (5127800959/10000000000 : ℝ), (172527609/312500000 : ℝ)] ![(10308653417959/100000000000000 : ℝ), (427394075783/1000000000000 : ℝ), (46951938983647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-104839257/625000000 : ℝ)|^4779 ≤ (10308653417959/100000000000000 : ℝ)^3755
        have hw : |(-104839257/625000000 : ℝ)|=(104839257/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5127800959/10000000000 : ℝ)|^4779 ≤ (427394075783/1000000000000 : ℝ)^3755
        have hw : |(5127800959/10000000000 : ℝ)|=(5127800959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(172527609/312500000 : ℝ)|^4779 ≤ (46951938983647/100000000000000 : ℝ)^3755
        have hw : |(172527609/312500000 : ℝ)|=(172527609/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1615_s1_5 (p : ℝ) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (42108079/80000000 : ℝ)*x 0 + (-1489768431/10000000000 : ℝ)*x 1 + (220835353/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42108079/80000000 : ℝ)^4779 ≤ (5523017438839/12500000000000 : ℝ)^3755 := by
    have hnat : (42108079 : ℕ)^4779*12500000000000^3755 ≤ 5523017438839^3755*80000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42108079 80000000 5523017438839 12500000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1489768431/10000000000 : ℝ)^4779 ≤ (553994865747/6250000000000 : ℝ)^3755 := by
    have hnat : (1489768431 : ℕ)^4779*6250000000000^3755 ≤ 553994865747^3755*10000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1489768431 10000000000 553994865747 6250000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (220835353/400000000 : ℝ)^4779 ≤ (46951942631203/100000000000000 : ℝ)^3755 := by
    have hnat : (220835353 : ℕ)^4779*100000000000000^3755 ≤ 46951942631203^3755*400000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220835353 400000000 46951942631203 100000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4779/1024 : ℝ)) 4779 3755 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42108079/80000000 : ℝ), (-1489768431/10000000000 : ℝ), (220835353/400000000 : ℝ)] ![(5523017438839/12500000000000 : ℝ), (553994865747/6250000000000 : ℝ), (46951942631203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42108079/80000000 : ℝ)|^4779 ≤ (5523017438839/12500000000000 : ℝ)^3755
        have hw : |(42108079/80000000 : ℝ)|=(42108079/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1489768431/10000000000 : ℝ)|^4779 ≤ (553994865747/6250000000000 : ℝ)^3755
        have hw : |(-1489768431/10000000000 : ℝ)|=(1489768431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(220835353/400000000 : ℝ)|^4779 ≤ (46951942631203/100000000000000 : ℝ)^3755
        have hw : |(220835353/400000000 : ℝ)|=(220835353/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1615_s1_6 (p : ℝ) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2631754613/5000000000 : ℝ)*x 0 + (5520884071/10000000000 : ℝ)*x 1 + (-297953799/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2631754613/5000000000 : ℝ)^4779 ≤ (44184132577049/100000000000000 : ℝ)^3755 := by
    have hnat : (2631754613 : ℕ)^4779*100000000000000^3755 ≤ 44184132577049^3755*5000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631754613 5000000000 44184132577049 100000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5520884071/10000000000 : ℝ)^4779 ≤ (46951945293811/100000000000000 : ℝ)^3755 := by
    have hnat : (5520884071 : ℕ)^4779*100000000000000^3755 ≤ 46951945293811^3755*10000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5520884071 10000000000 46951945293811 100000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (297953799/2000000000 : ℝ)^4779 ≤ (8863922122791/100000000000000 : ℝ)^3755 := by
    have hnat : (297953799 : ℕ)^4779*100000000000000^3755 ≤ 8863922122791^3755*2000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      297953799 2000000000 8863922122791 100000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4779/1024 : ℝ)) 4779 3755 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2631754613/5000000000 : ℝ), (5520884071/10000000000 : ℝ), (-297953799/2000000000 : ℝ)] ![(44184132577049/100000000000000 : ℝ), (46951945293811/100000000000000 : ℝ), (8863922122791/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2631754613/5000000000 : ℝ)|^4779 ≤ (44184132577049/100000000000000 : ℝ)^3755
        have hw : |(2631754613/5000000000 : ℝ)|=(2631754613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5520884071/10000000000 : ℝ)|^4779 ≤ (46951945293811/100000000000000 : ℝ)^3755
        have hw : |(5520884071/10000000000 : ℝ)|=(5520884071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-297953799/2000000000 : ℝ)|^4779 ≤ (8863922122791/100000000000000 : ℝ)^3755
        have hw : |(-297953799/2000000000 : ℝ)|=(297953799/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1615_s1_7 (p : ℝ) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4198301123/10000000000 : ℝ)*x 0 + (588303031/1250000000 : ℝ)*x 1 + (933530231/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4198301123/10000000000 : ℝ)^4779 ≤ (6626963721071/20000000000000 : ℝ)^3755 := by
    have hnat : (4198301123 : ℕ)^4779*20000000000000^3755 ≤ 6626963721071^3755*10000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4198301123 10000000000 6626963721071 20000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (588303031/1250000000 : ℝ)^4779 ≤ (4790081901407/12500000000000 : ℝ)^3755 := by
    have hnat : (588303031 : ℕ)^4779*12500000000000^3755 ≤ 4790081901407^3755*1250000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      588303031 1250000000 4790081901407 12500000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (933530231/2500000000 : ℝ)^4779 ≤ (14272263084963/50000000000000 : ℝ)^3755 := by
    have hnat : (933530231 : ℕ)^4779*50000000000000^3755 ≤ 14272263084963^3755*2500000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      933530231 2500000000 14272263084963 50000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4779/1024 : ℝ)) 4779 3755 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4198301123/10000000000 : ℝ), (588303031/1250000000 : ℝ), (933530231/2500000000 : ℝ)] ![(6626963721071/20000000000000 : ℝ), (4790081901407/12500000000000 : ℝ), (14272263084963/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4198301123/10000000000 : ℝ)|^4779 ≤ (6626963721071/20000000000000 : ℝ)^3755
        have hw : |(4198301123/10000000000 : ℝ)|=(4198301123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(588303031/1250000000 : ℝ)|^4779 ≤ (4790081901407/12500000000000 : ℝ)^3755
        have hw : |(588303031/1250000000 : ℝ)|=(588303031/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(933530231/2500000000 : ℝ)|^4779 ≤ (14272263084963/50000000000000 : ℝ)^3755
        have hw : |(933530231/2500000000 : ℝ)|=(933530231/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1615_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (173676369/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (754/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (413/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (9219/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2217/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (754/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (413/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (754/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (413/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (754/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (413/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (754/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (413/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (754/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (413/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (754/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (413/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (413/10000 : ℝ) ^ (4775/1024 : ℝ) ≤ (35160589602617/100000000000000000000 : ℝ) := by
    have hpowers : (413/10000 : ℝ)^4775 ≤ (35160589602617/100000000000000000000 : ℝ)^1024 := by
      have hnat : (413 : ℕ)^4775*100000000000000000000^1024 ≤ 35160589602617^1024*10000^4775 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        413 10000 35160589602617 100000000000000000000 4775 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (413/10000 : ℝ)) (X := (35160589602617/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4775 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (754/3125 : ℝ) ^ (4775/1024 : ℝ) ≤ (26404251806465797/20000000000000000000 : ℝ) := by
    have hpowers : (754/3125 : ℝ)^4775 ≤ (26404251806465797/20000000000000000000 : ℝ)^1024 := by
      have hnat : (754 : ℕ)^4775*20000000000000000000^1024 ≤ 26404251806465797^1024*3125^4775 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        754 3125 26404251806465797 20000000000000000000 4775 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (754/3125 : ℝ)) (X := (26404251806465797/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4775 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000035160589602617/50000000000000000000 : ℝ) ≤ (10000001508039113/10000000000000000 : ℝ) ^ (4775/1024 : ℝ) := by
    have hpowers : (50000035160589602617/50000000000000000000 : ℝ)^1024 ≤ (10000001508039113/10000000000000000 : ℝ)^4775 := by
      have hnat : (50000035160589602617 : ℕ)^1024*10000000000000000^4775 ≤ 10000001508039113^4775*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000035160589602617 50000000000000000000 10000001508039113 10000000000000000 1024 4775 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001508039113/10000000000000000 : ℝ)) (X := (50000035160589602617/50000000000000000000 : ℝ)) (by norm_num) 4775 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50066028209810965801/50000000000000000000 : ℝ) ≤ (10002830485639101/10000000000000000 : ℝ) ^ (4775/1024 : ℝ) := by
    have hpowers : (50066028209810965801/50000000000000000000 : ℝ)^1024 ≤ (10002830485639101/10000000000000000 : ℝ)^4775 := by
      have hnat : (50066028209810965801 : ℕ)^1024*10000000000000000^4775 ≤ 10002830485639101^4775*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50066028209810965801 50000000000000000000 10002830485639101 10000000000000000 1024 4775 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002830485639101/10000000000000000 : ℝ)) (X := (50066028209810965801/50000000000000000000 : ℝ)) (by norm_num) 4775 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10026404251806465797/10000000000000000000 : ℝ) ≤ (10005659463239089/10000000000000000 : ℝ) ^ (4775/1024 : ℝ) := by
    have hpowers : (10026404251806465797/10000000000000000000 : ℝ)^1024 ≤ (10005659463239089/10000000000000000 : ℝ)^4775 := by
      have hnat : (10026404251806465797 : ℕ)^1024*10000000000000000^4775 ≤ 10005659463239089^4775*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10026404251806465797 10000000000000000000 10005659463239089 10000000000000000 1024 4775 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005659463239089/10000000000000000 : ℝ)) (X := (10026404251806465797/10000000000000000000 : ℝ)) (by norm_num) 4775 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(35160589602617/100000000000000000000 : ℝ) ≤ ((99978331401395140447/99990000000000000000 : ℝ)+2*(707244399997/499950000000000 : ℝ)*(413/10000 : ℝ))^(4775/1024 : ℝ) := by
    rw [show (99978331401395140447/99990000000000000000 : ℝ)+2*(707244399997/499950000000000 : ℝ)*(413/10000 : ℝ)=(10000001508039113/10000000000000000 : ℝ) by norm_num, show 1+2*(35160589602617/100000000000000000000 : ℝ)=(50000035160589602617/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26404251806465797/20000000000000000000 : ℝ)+(35160589602617/100000000000000000000 : ℝ) ≤ ((99978331401395140447/99990000000000000000 : ℝ)+(707244399997/499950000000000 : ℝ)*((754/3125 : ℝ)+(413/10000 : ℝ)))^(4775/1024 : ℝ) := by
    rw [show (99978331401395140447/99990000000000000000 : ℝ)+(707244399997/499950000000000 : ℝ)*((754/3125 : ℝ)+(413/10000 : ℝ))=(10002830485639101/10000000000000000 : ℝ) by norm_num, show 1+(26404251806465797/20000000000000000000 : ℝ)+(35160589602617/100000000000000000000 : ℝ)=(50066028209810965801/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26404251806465797/20000000000000000000 : ℝ) ≤ ((99978331401395140447/99990000000000000000 : ℝ)+2*(707244399997/499950000000000 : ℝ)*(754/3125 : ℝ))^(4775/1024 : ℝ) := by
    rw [show (99978331401395140447/99990000000000000000 : ℝ)+2*(707244399997/499950000000000 : ℝ)*(754/3125 : ℝ)=(10005659463239089/10000000000000000 : ℝ) by norm_num, show 1+2*(26404251806465797/20000000000000000000 : ℝ)=(10026404251806465797/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (99978331401395140447/99990000000000000000 : ℝ)*(X 1 0+X 2 0)+(707244399997/499950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4775/1024 : ℝ)) (lo := (413/10000 : ℝ)) (hi := (754/3125 : ℝ)) (c := (99978331401395140447/99990000000000000000 : ℝ)) (alpha := (707244399997/499950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (99978331401395140447/99990000000000000000 : ℝ)*(X 0 1+X 2 1)+(707244399997/499950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4775/1024 : ℝ)) (lo := (413/10000 : ℝ)) (hi := (754/3125 : ℝ)) (c := (99978331401395140447/99990000000000000000 : ℝ)) (alpha := (707244399997/499950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (99978331401395140447/99990000000000000000 : ℝ)*(X 0 2+X 1 2)+(707244399997/499950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4775/1024 : ℝ)) (lo := (413/10000 : ℝ)) (hi := (754/3125 : ℝ)) (c := (99978331401395140447/99990000000000000000 : ℝ)) (alpha := (707244399997/499950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1677215447/10000000000 : ℝ)*X 0 0+(2762640701/5000000000 : ℝ)*X 0 1+(5123469379/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1615_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((167827553/312500000 : ℝ)*X 1 0+(-943591587/5000000000 : ℝ)*X 1 1+(5123469213/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1615_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((167827551/312500000 : ℝ)*X 2 0+(640433649/1250000000 : ℝ)*X 2 1+(-377436657/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1615_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2098888359/5000000000 : ℝ)*X 0 0+(1861621753/5000000000 : ℝ)*X 0 1+(943427471/2000000000 : ℝ)*X 0 2+(2098888359/5000000000 : ℝ)*X 1 0+(1861621753/5000000000 : ℝ)*X 1 1+(943427471/2000000000 : ℝ)*X 1 2+(2098888359/5000000000 : ℝ)*X 2 0+(1861621753/5000000000 : ℝ)*X 2 1+(943427471/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1615_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-104839257/625000000 : ℝ)*X 0 0+(5127800959/10000000000 : ℝ)*X 0 1+(172527609/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1615_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((42108079/80000000 : ℝ)*X 1 0+(-1489768431/10000000000 : ℝ)*X 1 1+(220835353/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1615_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2631754613/5000000000 : ℝ)*X 2 0+(5520884071/10000000000 : ℝ)*X 2 1+(-297953799/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1615_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4198301123/10000000000 : ℝ)*X 0 0+(588303031/1250000000 : ℝ)*X 0 1+(933530231/2500000000 : ℝ)*X 0 2+(4198301123/10000000000 : ℝ)*X 1 0+(588303031/1250000000 : ℝ)*X 1 1+(933530231/2500000000 : ℝ)*X 1 2+(4198301123/10000000000 : ℝ)*X 2 0+(588303031/1250000000 : ℝ)*X 2 1+(933530231/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1615_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1999287413088070233921224831/833250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (40754991/25000000000000 : ℝ)*(base1) + (160644503/25000000000000 : ℝ)*(base19) + (76614977/12500000000000 : ℝ)*(base23) + (91389671/100000000000000 : ℝ)*(upper3) + (21652209/100000000000000 : ℝ)*(upper5) + (873719708560891/50000000000000 : ℝ)*(major0) + (873719708560891/50000000000000 : ℝ)*(major1) + (873719708560891/50000000000000 : ℝ)*(major2) + (1244364782475733/50000000000000 : ℝ)*(sp0) + (2488731203397227/100000000000000 : ℝ)*(sp1) + (38886425516491/1562500000000 : ℝ)*(sp2) + (1006145002580413/100000000000000 : ℝ)*(sp3) + (305505467/12500000000000 : ℝ)*(sp4) + (348537689/20000000000000 : ℝ)*(sp7) + (50307345414441/5000000000000 : ℝ)*(f.failure) + (2488731845975239/100000000000000 : ℝ)*(f.sum) + (219858825648017/49995000000000000000000000000 : ℝ)*base66 + (783925041063367931/151500000000000000000000000000000 : ℝ)*base68 + (243903455137867931/151500000000000000000000000000000 : ℝ)*base70 + (1160048753263867931/151500000000000000000000000000000 : ℝ)*base72 + (14685701027873/12498750000000000000000000000 : ℝ)*base74 + (1734615212841367931/151500000000000000000000000000000 : ℝ)*base76 + (1949259972127867931/151500000000000000000000000000000 : ℝ)*base78 + (1915829907741367931/151500000000000000000000000000000 : ℝ)*base80 + (110242339934083/49995000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base87 + (3044729/500000000000000000000 : ℝ)*base89 + (3044729/500000000000000000000 : ℝ)*base91 + (3044729/500000000000000000000 : ℝ)*base93 + (1/50000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1645738770833151620754477313/333300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1086899447/100000000000000 : ℝ)*(base19) + (13550827/1562500000000 : ℝ)*(base23) + (13912439/25000000000000 : ℝ)*(upper2) + (251700721/100000000000000 : ℝ)*(upper3) + (7436551/50000000000000 : ℝ)*(upper5) + (357247599031307/20000000000000 : ℝ)*(major0) + (357247599031307/20000000000000 : ℝ)*(major1) + (357247599031307/20000000000000 : ℝ)*(major2) + (8073850309/100000000000000 : ℝ)*(sp1) + (749832441/10000000000000 : ℝ)*(sp2) + (317998666701273/12500000000000 : ℝ)*(sp4) + (2543980172860429/100000000000000 : ℝ)*(sp5) + (1271990484016423/50000000000000 : ℝ)*(sp6) + (514243246056271/50000000000000 : ℝ)*(sp7) + (514243246056271/50000000000000 : ℝ)*(f.failure) + (317998666701273/12500000000000 : ℝ)*(f.sum) + (4634627909473/1249875000000000000000000000 : ℝ)*base66 + (101657276018338613/60600000000000000000000000000000 : ℝ)*base67 + (595051220901538613/60600000000000000000000000000000 : ℝ)*base69 + (8807153898538613/60600000000000000000000000000000 : ℝ)*base71 + (28587959197091/9999000000000000000000000000 : ℝ)*base74 + (188639990331538613/60600000000000000000000000000000 : ℝ)*base75 + (317406964952338613/60600000000000000000000000000000 : ℝ)*base77 + (495835652420338613/60600000000000000000000000000000 : ℝ)*base79 + (5242909332173/4999500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (33040001/5000000000000000000000 : ℝ)*base90 + (33040001/5000000000000000000000 : ℝ)*base92 + (33040001/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1615_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (173676369/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (754/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (413/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9219/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2217/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1615_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1615_s2_0 (p : ℝ) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-67617929/400000000 : ℝ)*x 0 + (2732299259/5000000000 : ℝ)*x 1 + (5175480543/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67617929/400000000 : ℝ)^4779 ≤ (5205298324853/50000000000000 : ℝ)^3755 := by
    have hnat : (67617929 : ℕ)^4779*50000000000000^3755 ≤ 5205298324853^3755*400000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67617929 400000000 5205298324853 50000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2732299259/5000000000 : ℝ)^4779 ≤ (46343581509949/100000000000000 : ℝ)^3755 := by
    have hnat : (2732299259 : ℕ)^4779*100000000000000^3755 ≤ 46343581509949^3755*5000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2732299259 5000000000 46343581509949 100000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5175480543/10000000000 : ℝ)^4779 ≤ (21622910911961/50000000000000 : ℝ)^3755 := by
    have hnat : (5175480543 : ℕ)^4779*50000000000000^3755 ≤ 21622910911961^3755*10000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5175480543 10000000000 21622910911961 50000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4779/1024 : ℝ)) 4779 3755 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-67617929/400000000 : ℝ), (2732299259/5000000000 : ℝ), (5175480543/10000000000 : ℝ)] ![(5205298324853/50000000000000 : ℝ), (46343581509949/100000000000000 : ℝ), (21622910911961/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-67617929/400000000 : ℝ)|^4779 ≤ (5205298324853/50000000000000 : ℝ)^3755
        have hw : |(-67617929/400000000 : ℝ)|=(67617929/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2732299259/5000000000 : ℝ)|^4779 ≤ (46343581509949/100000000000000 : ℝ)^3755
        have hw : |(2732299259/5000000000 : ℝ)|=(2732299259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5175480543/10000000000 : ℝ)|^4779 ≤ (21622910911961/50000000000000 : ℝ)^3755
        have hw : |(5175480543/10000000000 : ℝ)|=(5175480543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1615_s2_1 (p : ℝ) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535463427/1000000000 : ℝ)*x 0 + (-459924999/2500000000 : ℝ)*x 1 + (5175480527/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535463427/1000000000 : ℝ)^4779 ≤ (45159965601209/100000000000000 : ℝ)^3755 := by
    have hnat : (535463427 : ℕ)^4779*100000000000000^3755 ≤ 45159965601209^3755*1000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535463427 1000000000 45159965601209 100000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (459924999/2500000000 : ℝ)^4779 ≤ (1159421273097/10000000000000 : ℝ)^3755 := by
    have hnat : (459924999 : ℕ)^4779*10000000000000^3755 ≤ 1159421273097^3755*2500000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      459924999 2500000000 1159421273097 10000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5175480527/10000000000 : ℝ)^4779 ≤ (43245821653769/100000000000000 : ℝ)^3755 := by
    have hnat : (5175480527 : ℕ)^4779*100000000000000^3755 ≤ 43245821653769^3755*10000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5175480527 10000000000 43245821653769 100000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4779/1024 : ℝ)) 4779 3755 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535463427/1000000000 : ℝ), (-459924999/2500000000 : ℝ), (5175480527/10000000000 : ℝ)] ![(45159965601209/100000000000000 : ℝ), (1159421273097/10000000000000 : ℝ), (43245821653769/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535463427/1000000000 : ℝ)|^4779 ≤ (45159965601209/100000000000000 : ℝ)^3755
        have hw : |(535463427/1000000000 : ℝ)|=(535463427/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-459924999/2500000000 : ℝ)|^4779 ≤ (1159421273097/10000000000000 : ℝ)^3755
        have hw : |(-459924999/2500000000 : ℝ)|=(459924999/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5175480527/10000000000 : ℝ)|^4779 ≤ (43245821653769/100000000000000 : ℝ)^3755
        have hw : |(5175480527/10000000000 : ℝ)|=(5175480527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1615_s2_2 (p : ℝ) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070926847/2000000000 : ℝ)*x 0 + (5175480491/10000000000 : ℝ)*x 1 + (-183970009/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070926847/2000000000 : ℝ)^4779 ≤ (5644995653191/12500000000000 : ℝ)^3755 := by
    have hnat : (1070926847 : ℕ)^4779*12500000000000^3755 ≤ 5644995653191^3755*2000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070926847 2000000000 5644995653191 12500000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5175480491/10000000000 : ℝ)^4779 ≤ (10811455317731/25000000000000 : ℝ)^3755 := by
    have hnat : (5175480491 : ℕ)^4779*25000000000000^3755 ≤ 10811455317731^3755*10000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5175480491 10000000000 10811455317731 25000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (183970009/1000000000 : ℝ)^4779 ≤ (11594213484931/100000000000000 : ℝ)^3755 := by
    have hnat : (183970009 : ℕ)^4779*100000000000000^3755 ≤ 11594213484931^3755*1000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      183970009 1000000000 11594213484931 100000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4779/1024 : ℝ)) 4779 3755 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070926847/2000000000 : ℝ), (5175480491/10000000000 : ℝ), (-183970009/1000000000 : ℝ)] ![(5644995653191/12500000000000 : ℝ), (10811455317731/25000000000000 : ℝ), (11594213484931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070926847/2000000000 : ℝ)|^4779 ≤ (5644995653191/12500000000000 : ℝ)^3755
        have hw : |(1070926847/2000000000 : ℝ)|=(1070926847/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5175480491/10000000000 : ℝ)|^4779 ≤ (10811455317731/25000000000000 : ℝ)^3755
        have hw : |(5175480491/10000000000 : ℝ)|=(5175480491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-183970009/1000000000 : ℝ)|^4779 ≤ (11594213484931/100000000000000 : ℝ)^3755
        have hw : |(-183970009/1000000000 : ℝ)|=(183970009/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1615_s2_3 (p : ℝ) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4207554891/10000000000 : ℝ)*x 0 + (965397997/2500000000 : ℝ)*x 1 + (4576733351/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4207554891/10000000000 : ℝ)^4779 ≤ (33227798091789/100000000000000 : ℝ)^3755 := by
    have hnat : (4207554891 : ℕ)^4779*100000000000000^3755 ≤ 33227798091789^3755*10000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4207554891 10000000000 33227798091789 100000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (965397997/2500000000 : ℝ)^4779 ≤ (7447599617729/25000000000000 : ℝ)^3755 := by
    have hnat : (965397997 : ℕ)^4779*25000000000000^3755 ≤ 7447599617729^3755*2500000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      965397997 2500000000 7447599617729 25000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4576733351/10000000000 : ℝ)^4779 ≤ (7396360683841/20000000000000 : ℝ)^3755 := by
    have hnat : (4576733351 : ℕ)^4779*20000000000000^3755 ≤ 7396360683841^3755*10000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4576733351 10000000000 7396360683841 20000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4779/1024 : ℝ)) 4779 3755 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4207554891/10000000000 : ℝ), (965397997/2500000000 : ℝ), (4576733351/10000000000 : ℝ)] ![(33227798091789/100000000000000 : ℝ), (7447599617729/25000000000000 : ℝ), (7396360683841/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4207554891/10000000000 : ℝ)|^4779 ≤ (33227798091789/100000000000000 : ℝ)^3755
        have hw : |(4207554891/10000000000 : ℝ)|=(4207554891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(965397997/2500000000 : ℝ)|^4779 ≤ (7447599617729/25000000000000 : ℝ)^3755
        have hw : |(965397997/2500000000 : ℝ)|=(965397997/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4576733351/10000000000 : ℝ)|^4779 ≤ (7396360683841/20000000000000 : ℝ)^3755
        have hw : |(4576733351/10000000000 : ℝ)|=(4576733351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1615_s2_4 (p : ℝ) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-845263721/5000000000 : ℝ)*x 0 + (5056377/9765625 : ℝ)*x 1 + (5462324327/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (845263721/5000000000 : ℝ)^4779 ≤ (2082243510039/20000000000000 : ℝ)^3755 := by
    have hnat : (845263721 : ℕ)^4779*20000000000000^3755 ≤ 2082243510039^3755*5000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      845263721 5000000000 2082243510039 20000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5056377/9765625 : ℝ)^4779 ≤ (1352179556081/3125000000000 : ℝ)^3755 := by
    have hnat : (5056377 : ℕ)^4779*3125000000000^3755 ≤ 1352179556081^3755*9765625^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5056377 9765625 1352179556081 3125000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5462324327/10000000000 : ℝ)^4779 ≤ (46319036641311/100000000000000 : ℝ)^3755 := by
    have hnat : (5462324327 : ℕ)^4779*100000000000000^3755 ≤ 46319036641311^3755*10000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5462324327 10000000000 46319036641311 100000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4779/1024 : ℝ)) 4779 3755 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-845263721/5000000000 : ℝ), (5056377/9765625 : ℝ), (5462324327/10000000000 : ℝ)] ![(2082243510039/20000000000000 : ℝ), (1352179556081/3125000000000 : ℝ), (46319036641311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-845263721/5000000000 : ℝ)|^4779 ≤ (2082243510039/20000000000000 : ℝ)^3755
        have hw : |(-845263721/5000000000 : ℝ)|=(845263721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5056377/9765625 : ℝ)|^4779 ≤ (1352179556081/3125000000000 : ℝ)^3755
        have hw : |(5056377/9765625 : ℝ)|=(5056377/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5462324327/10000000000 : ℝ)|^4779 ≤ (46319036641311/100000000000000 : ℝ)^3755
        have hw : |(5462324327/10000000000 : ℝ)|=(5462324327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1615_s2_5 (p : ℝ) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638887001/5000000000 : ℝ)*x 0 + (-388214121/2500000000 : ℝ)*x 1 + (1092464831/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638887001/5000000000 : ℝ)^4779 ≤ (44336588162549/100000000000000 : ℝ)^3755 := by
    have hnat : (2638887001 : ℕ)^4779*100000000000000^3755 ≤ 44336588162549^3755*5000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638887001 5000000000 44336588162549 100000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (388214121/2500000000 : ℝ)^4779 ≤ (9344377036703/100000000000000 : ℝ)^3755 := by
    have hnat : (388214121 : ℕ)^4779*100000000000000^3755 ≤ 9344377036703^3755*2500000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      388214121 2500000000 9344377036703 100000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1092464831/2000000000 : ℝ)^4779 ≤ (1447469837033/3125000000000 : ℝ)^3755 := by
    have hnat : (1092464831 : ℕ)^4779*3125000000000^3755 ≤ 1447469837033^3755*2000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092464831 2000000000 1447469837033 3125000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4779/1024 : ℝ)) 4779 3755 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638887001/5000000000 : ℝ), (-388214121/2500000000 : ℝ), (1092464831/2000000000 : ℝ)] ![(44336588162549/100000000000000 : ℝ), (9344377036703/100000000000000 : ℝ), (1447469837033/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638887001/5000000000 : ℝ)|^4779 ≤ (44336588162549/100000000000000 : ℝ)^3755
        have hw : |(2638887001/5000000000 : ℝ)|=(2638887001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-388214121/2500000000 : ℝ)|^4779 ≤ (9344377036703/100000000000000 : ℝ)^3755
        have hw : |(-388214121/2500000000 : ℝ)|=(388214121/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1092464831/2000000000 : ℝ)|^4779 ≤ (1447469837033/3125000000000 : ℝ)^3755
        have hw : |(1092464831/2000000000 : ℝ)|=(1092464831/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1615_s2_6 (p : ℝ) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5277773947/10000000000 : ℝ)*x 0 + (5462324349/10000000000 : ℝ)*x 1 + (-1552856287/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5277773947/10000000000 : ℝ)^4779 ≤ (44336587574517/100000000000000 : ℝ)^3755 := by
    have hnat : (5277773947 : ℕ)^4779*100000000000000^3755 ≤ 44336587574517^3755*10000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5277773947 10000000000 44336587574517 100000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5462324349/10000000000 : ℝ)^4779 ≤ (46319036878739/100000000000000 : ℝ)^3755 := by
    have hnat : (5462324349 : ℕ)^4779*100000000000000^3755 ≤ 46319036878739^3755*10000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5462324349 10000000000 46319036878739 100000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1552856287/10000000000 : ℝ)^4779 ≤ (934437552797/10000000000000 : ℝ)^3755 := by
    have hnat : (1552856287 : ℕ)^4779*10000000000000^3755 ≤ 934437552797^3755*10000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1552856287 10000000000 934437552797 10000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4779/1024 : ℝ)) 4779 3755 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5277773947/10000000000 : ℝ), (5462324349/10000000000 : ℝ), (-1552856287/10000000000 : ℝ)] ![(44336587574517/100000000000000 : ℝ), (46319036878739/100000000000000 : ℝ), (934437552797/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5277773947/10000000000 : ℝ)|^4779 ≤ (44336587574517/100000000000000 : ℝ)^3755
        have hw : |(5277773947/10000000000 : ℝ)|=(5277773947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5462324349/10000000000 : ℝ)|^4779 ≤ (46319036878739/100000000000000 : ℝ)^3755
        have hw : |(5462324349/10000000000 : ℝ)|=(5462324349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1552856287/10000000000 : ℝ)|^4779 ≤ (934437552797/10000000000000 : ℝ)^3755
        have hw : |(-1552856287/10000000000 : ℝ)|=(1552856287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1615_s2_7 (p : ℝ) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4207750881/10000000000 : ℝ)*x 0 + (1142792237/2500000000 : ℝ)*x 1 + (3867217563/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4207750881/10000000000 : ℝ)^4779 ≤ (16614883976283/50000000000000 : ℝ)^3755 := by
    have hnat : (4207750881 : ℕ)^4779*50000000000000^3755 ≤ 16614883976283^3755*10000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4207750881 10000000000 16614883976283 50000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1142792237/2500000000 : ℝ)^4779 ≤ (36924588917803/100000000000000 : ℝ)^3755 := by
    have hnat : (1142792237 : ℕ)^4779*100000000000000^3755 ≤ 36924588917803^3755*2500000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1142792237 2500000000 36924588917803 100000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3867217563/10000000000 : ℝ)^4779 ≤ (7461410778237/25000000000000 : ℝ)^3755 := by
    have hnat : (3867217563 : ℕ)^4779*25000000000000^3755 ≤ 7461410778237^3755*10000000000^4779 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3867217563 10000000000 7461410778237 25000000000000 4779 3755 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4779/1024 : ℝ)) 4779 3755 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4207750881/10000000000 : ℝ), (1142792237/2500000000 : ℝ), (3867217563/10000000000 : ℝ)] ![(16614883976283/50000000000000 : ℝ), (36924588917803/100000000000000 : ℝ), (7461410778237/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4207750881/10000000000 : ℝ)|^4779 ≤ (16614883976283/50000000000000 : ℝ)^3755
        have hw : |(4207750881/10000000000 : ℝ)|=(4207750881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1142792237/2500000000 : ℝ)|^4779 ≤ (36924588917803/100000000000000 : ℝ)^3755
        have hw : |(1142792237/2500000000 : ℝ)|=(1142792237/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3867217563/10000000000 : ℝ)|^4779 ≤ (7461410778237/25000000000000 : ℝ)^3755
        have hw : |(3867217563/10000000000 : ℝ)|=(3867217563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1615_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (173676369/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2217/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9219/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5171/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16473/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2217/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9219/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2217/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9219/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2217/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9219/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2217/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9219/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2217/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9219/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2217/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9219/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9219/100000 : ℝ) ^ (4775/1024 : ℝ) ≤ (1486728465721783/100000000000000000000 : ℝ) := by
    have hpowers : (9219/100000 : ℝ)^4775 ≤ (1486728465721783/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9219 : ℕ)^4775*100000000000000000000^1024 ≤ 1486728465721783^1024*100000^4775 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9219 100000 1486728465721783 100000000000000000000 4775 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9219/100000 : ℝ)) (X := (1486728465721783/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4775 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2217/12500 : ℝ) ^ (4775/1024 : ℝ) ≤ (15715184684668721/50000000000000000000 : ℝ) := by
    have hpowers : (2217/12500 : ℝ)^4775 ≤ (15715184684668721/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2217 : ℕ)^4775*50000000000000000000^1024 ≤ 15715184684668721^1024*12500^4775 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2217 12500 15715184684668721 50000000000000000000 4775 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2217/12500 : ℝ)) (X := (15715184684668721/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4775 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001486728465721783/50000000000000000000 : ℝ) ≤ (10000063765117027/10000000000000000 : ℝ) ^ (4775/1024 : ℝ) := by
    have hpowers : (50001486728465721783/50000000000000000000 : ℝ)^1024 ≤ (10000063765117027/10000000000000000 : ℝ)^4775 := by
      have hnat : (50001486728465721783 : ℕ)^1024*10000000000000000^4775 ≤ 10000063765117027^4775*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001486728465721783 50000000000000000000 10000063765117027 10000000000000000 1024 4775 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000063765117027/10000000000000000 : ℝ)) (X := (50001486728465721783/50000000000000000000 : ℝ)) (by norm_num) 4775 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (4001316683913402369/4000000000000000000 : ℝ) ≤ (156261028387121/156250000000000 : ℝ) ^ (4775/1024 : ℝ) := by
    have hpowers : (4001316683913402369/4000000000000000000 : ℝ)^1024 ≤ (156261028387121/156250000000000 : ℝ)^4775 := by
      have hnat : (4001316683913402369 : ℕ)^1024*156250000000000^4775 ≤ 156261028387121^4775*4000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4001316683913402369 4000000000000000000 156261028387121 156250000000000 1024 4775 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156261028387121/156250000000000 : ℝ)) (X := (4001316683913402369/4000000000000000000 : ℝ)) (by norm_num) 4775 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015715184684668721/25000000000000000000 : ℝ) ≤ (10001347868434461/10000000000000000 : ℝ) ^ (4775/1024 : ℝ) := by
    have hpowers : (25015715184684668721/25000000000000000000 : ℝ)^1024 ≤ (10001347868434461/10000000000000000 : ℝ)^4775 := by
      have hnat : (25015715184684668721 : ℕ)^1024*10000000000000000^4775 ≤ 10001347868434461^4775*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015715184684668721 25000000000000000000 10001347868434461 10000000000000000 1024 4775 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001347868434461/10000000000000000 : ℝ)) (X := (25015715184684668721/25000000000000000000 : ℝ)) (by norm_num) 4775 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1486728465721783/100000000000000000000 : ℝ) ≤ ((28386234979672764971/28390000000000000000 : ℝ)+2*(642051658717/851700000000000 : ℝ)*(9219/100000 : ℝ))^(4775/1024 : ℝ) := by
    rw [show (28386234979672764971/28390000000000000000 : ℝ)+2*(642051658717/851700000000000 : ℝ)*(9219/100000 : ℝ)=(10000063765117027/10000000000000000 : ℝ) by norm_num, show 1+2*(1486728465721783/100000000000000000000 : ℝ)=(50001486728465721783/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15715184684668721/50000000000000000000 : ℝ)+(1486728465721783/100000000000000000000 : ℝ) ≤ ((28386234979672764971/28390000000000000000 : ℝ)+(642051658717/851700000000000 : ℝ)*((2217/12500 : ℝ)+(9219/100000 : ℝ)))^(4775/1024 : ℝ) := by
    rw [show (28386234979672764971/28390000000000000000 : ℝ)+(642051658717/851700000000000 : ℝ)*((2217/12500 : ℝ)+(9219/100000 : ℝ))=(156261028387121/156250000000000 : ℝ) by norm_num, show 1+(15715184684668721/50000000000000000000 : ℝ)+(1486728465721783/100000000000000000000 : ℝ)=(4001316683913402369/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15715184684668721/50000000000000000000 : ℝ) ≤ ((28386234979672764971/28390000000000000000 : ℝ)+2*(642051658717/851700000000000 : ℝ)*(2217/12500 : ℝ))^(4775/1024 : ℝ) := by
    rw [show (28386234979672764971/28390000000000000000 : ℝ)+2*(642051658717/851700000000000 : ℝ)*(2217/12500 : ℝ)=(10001347868434461/10000000000000000 : ℝ) by norm_num, show 1+2*(15715184684668721/50000000000000000000 : ℝ)=(25015715184684668721/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (28386234979672764971/28390000000000000000 : ℝ)*(X 1 0+X 2 0)+(642051658717/851700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4775/1024 : ℝ)) (lo := (9219/100000 : ℝ)) (hi := (2217/12500 : ℝ)) (c := (28386234979672764971/28390000000000000000 : ℝ)) (alpha := (642051658717/851700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (28386234979672764971/28390000000000000000 : ℝ)*(X 0 1+X 2 1)+(642051658717/851700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4775/1024 : ℝ)) (lo := (9219/100000 : ℝ)) (hi := (2217/12500 : ℝ)) (c := (28386234979672764971/28390000000000000000 : ℝ)) (alpha := (642051658717/851700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (28386234979672764971/28390000000000000000 : ℝ)*(X 0 2+X 1 2)+(642051658717/851700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4775/1024 : ℝ)) (lo := (9219/100000 : ℝ)) (hi := (2217/12500 : ℝ)) (c := (28386234979672764971/28390000000000000000 : ℝ)) (alpha := (642051658717/851700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-67617929/400000000 : ℝ)*X 0 0+(2732299259/5000000000 : ℝ)*X 0 1+(5175480543/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1615_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((535463427/1000000000 : ℝ)*X 1 0+(-459924999/2500000000 : ℝ)*X 1 1+(5175480527/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1615_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1070926847/2000000000 : ℝ)*X 2 0+(5175480491/10000000000 : ℝ)*X 2 1+(-183970009/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1615_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4207554891/10000000000 : ℝ)*X 0 0+(965397997/2500000000 : ℝ)*X 0 1+(4576733351/10000000000 : ℝ)*X 0 2+(4207554891/10000000000 : ℝ)*X 1 0+(965397997/2500000000 : ℝ)*X 1 1+(4576733351/10000000000 : ℝ)*X 1 2+(4207554891/10000000000 : ℝ)*X 2 0+(965397997/2500000000 : ℝ)*X 2 1+(4576733351/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1615_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-845263721/5000000000 : ℝ)*X 0 0+(5056377/9765625 : ℝ)*X 0 1+(5462324327/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1615_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2638887001/5000000000 : ℝ)*X 1 0+(-388214121/2500000000 : ℝ)*X 1 1+(1092464831/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1615_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5277773947/10000000000 : ℝ)*X 2 0+(5462324349/10000000000 : ℝ)*X 2 1+(-1552856287/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1615_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4207750881/10000000000 : ℝ)*X 0 0+(1142792237/2500000000 : ℝ)*X 0 1+(3867217563/10000000000 : ℝ)*X 0 2+(4207750881/10000000000 : ℝ)*X 1 0+(1142792237/2500000000 : ℝ)*X 1 1+(3867217563/10000000000 : ℝ)*X 1 2+(4207750881/10000000000 : ℝ)*X 2 0+(1142792237/2500000000 : ℝ)*X 2 1+(3867217563/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1615_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (333754347308307178963055757/70975000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (797113713/100000000000000 : ℝ)*(base19) + (768561301/100000000000000 : ℝ)*(base23) + (3182929/100000000000000 : ℝ)*(lower2) + (152676803/100000000000000 : ℝ)*(upper3) + (75244293/100000000000000 : ℝ)*(upper5) + (242857278379589/10000000000000 : ℝ)*(major0) + (242857278379589/10000000000000 : ℝ)*(major1) + (242857278379589/10000000000000 : ℝ)*(major2) + (864701302198669/25000000000000 : ℝ)*(sp0) + (864703075755033/25000000000000 : ℝ)*(sp1) + (54043942680821/1562500000000 : ℝ)*(sp2) + (174791039287489/12500000000000 : ℝ)*(sp3) + (7891339169/100000000000000 : ℝ)*(sp4) + (3996410643/100000000000000 : ℝ)*(sp7) + (279666462142111/20000000000000 : ℝ)*(f.failure) + (864703275033461/25000000000000 : ℝ)*(f.sum) + (2632461694583/8517000000000000000000000000 : ℝ)*base66 + (6390109630036969243/851700000000000000000000000000000 : ℝ)*base68 + (1289178299575369243/851700000000000000000000000000000 : ℝ)*base70 + (1541635503827530757/851700000000000000000000000000000 : ℝ)*base71 + (2799974038889/851700000000000000000000000 : ℝ)*base74 + (3757674235221469243/851700000000000000000000000000000 : ℝ)*base76 + (316194910512469243/851700000000000000000000000000000 : ℝ)*base78 + (9368248018437769243/851700000000000000000000000000000 : ℝ)*base80 + (32642491880389/8517000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (474959/2000000000000000000000 : ℝ)*base89 + (474959/2000000000000000000000 : ℝ)*base91 + (474959/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2981964804124334631880134141/354875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (151489083/12500000000000 : ℝ)*(base19) + (158336957/12500000000000 : ℝ)*(base23) + (81804849/50000000000000 : ℝ)*(upper3) + (3747873/12500000000000 : ℝ)*(lower4) + (202176279/100000000000000 : ℝ)*(upper5) + (1233581767054243/50000000000000 : ℝ)*(major0) + (1233581767054243/50000000000000 : ℝ)*(major1) + (1233581767054243/50000000000000 : ℝ)*(major2) + (11360895957/100000000000000 : ℝ)*(sp1) + (3434027757/25000000000000 : ℝ)*(sp2) + (1756887278687723/50000000000000 : ℝ)*(sp4) + (1756880992283413/50000000000000 : ℝ)*(sp5) + (3513759554568763/100000000000000 : ℝ)*(sp6) + (142055223074619/10000000000000 : ℝ)*(sp7) + (142055223074619/10000000000000 : ℝ)*(f.failure) + (1756887278687723/50000000000000 : ℝ)*(f.sum) + (6678574313617/10646250000000000000000000000 : ℝ)*base66 + (76671286674277065859/4258500000000000000000000000000000 : ℝ)*base67 + (59463964514863065859/4258500000000000000000000000000000 : ℝ)*base69 + (16988886535093065859/4258500000000000000000000000000000 : ℝ)*base71 + (136484819134261/21292500000000000000000000000 : ℝ)*base73 + (18413146514633565859/4258500000000000000000000000000000 : ℝ)*base75 + (18180597529001565859/4258500000000000000000000000000000 : ℝ)*base77 + (5015531281302434141/4258500000000000000000000000000000 : ℝ)*base80 + (160511710885097/42585000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (16021589/1000000000000000000000 : ℝ)*base90 + (16021589/1000000000000000000000 : ℝ)*base92 + (16021589/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1615_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (173676369/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2217/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9219/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5171/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16473/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1615_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1615_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (173676369/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5171/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16473/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1615_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1615_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1615_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4775/1024 : ℝ) ≤ p) (hpb : p ≤ (4779/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (173676369/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5171/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16473/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1615_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
