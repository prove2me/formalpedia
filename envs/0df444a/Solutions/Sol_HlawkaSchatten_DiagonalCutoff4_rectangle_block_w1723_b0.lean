-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1723_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:00:17.991634+00:00
-- url     : https://prove2.me/submissions/5991be92-5bda-449c-a2dc-ac3a4537fe63

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
theorem support_rectangle_w1723_s0_0 (p : ℝ) (hpa : (5399/1024 : ℝ) ≤ p) (hpb : p ≤ (5407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1299180213/10000000000 : ℝ)*x 0 + (5672595397/10000000000 : ℝ)*x 1 + (2486734593/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1299180213/10000000000 : ℝ)^5407 ≤ (806484523123/10000000000000 : ℝ)^4383 := by
    have hnat : (1299180213 : ℕ)^5407*10000000000000^4383 ≤ 806484523123^4383*10000000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299180213 10000000000 806484523123 10000000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5672595397/10000000000 : ℝ)^5407 ≤ (49688726757999/100000000000000 : ℝ)^4383 := by
    have hnat : (5672595397 : ℕ)^5407*100000000000000^4383 ≤ 49688726757999^4383*10000000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5672595397 10000000000 49688726757999 100000000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2486734593/5000000000 : ℝ)^5407 ≤ (42246428002231/100000000000000 : ℝ)^4383 := by
    have hnat : (2486734593 : ℕ)^5407*100000000000000^4383 ≤ 42246428002231^4383*5000000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2486734593 5000000000 42246428002231 100000000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5407/1024 : ℝ)) 5407 4383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1299180213/10000000000 : ℝ), (5672595397/10000000000 : ℝ), (2486734593/5000000000 : ℝ)] ![(806484523123/10000000000000 : ℝ), (49688726757999/100000000000000 : ℝ), (42246428002231/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1299180213/10000000000 : ℝ)|^5407 ≤ (806484523123/10000000000000 : ℝ)^4383
        have hw : |(-1299180213/10000000000 : ℝ)|=(1299180213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5672595397/10000000000 : ℝ)|^5407 ≤ (49688726757999/100000000000000 : ℝ)^4383
        have hw : |(5672595397/10000000000 : ℝ)|=(5672595397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2486734593/5000000000 : ℝ)|^5407 ≤ (42246428002231/100000000000000 : ℝ)^4383
        have hw : |(2486734593/5000000000 : ℝ)|=(2486734593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1723_s0_1 (p : ℝ) (hpa : (5399/1024 : ℝ) ≤ p) (hpb : p ≤ (5407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1348835741/2500000000 : ℝ)*x 0 + (-838101897/5000000000 : ℝ)*x 1 + (2486734297/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1348835741/2500000000 : ℝ)^5407 ≤ (46710088105621/100000000000000 : ℝ)^4383 := by
    have hnat : (1348835741 : ℕ)^5407*100000000000000^4383 ≤ 46710088105621^4383*2500000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348835741 2500000000 46710088105621 100000000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (838101897/5000000000 : ℝ)^5407 ≤ (11043490081133/100000000000000 : ℝ)^4383 := by
    have hnat : (838101897 : ℕ)^5407*100000000000000^4383 ≤ 11043490081133^4383*5000000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      838101897 5000000000 11043490081133 100000000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2486734297/5000000000 : ℝ)^5407 ≤ (1689856871949/4000000000000 : ℝ)^4383 := by
    have hnat : (2486734297 : ℕ)^5407*4000000000000^4383 ≤ 1689856871949^4383*5000000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2486734297 5000000000 1689856871949 4000000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5407/1024 : ℝ)) 5407 4383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1348835741/2500000000 : ℝ), (-838101897/5000000000 : ℝ), (2486734297/5000000000 : ℝ)] ![(46710088105621/100000000000000 : ℝ), (11043490081133/100000000000000 : ℝ), (1689856871949/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1348835741/2500000000 : ℝ)|^5407 ≤ (46710088105621/100000000000000 : ℝ)^4383
        have hw : |(1348835741/2500000000 : ℝ)|=(1348835741/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-838101897/5000000000 : ℝ)|^5407 ≤ (11043490081133/100000000000000 : ℝ)^4383
        have hw : |(-838101897/5000000000 : ℝ)|=(838101897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2486734297/5000000000 : ℝ)|^5407 ≤ (1689856871949/4000000000000 : ℝ)^4383
        have hw : |(2486734297/5000000000 : ℝ)|=(2486734297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1723_s0_2 (p : ℝ) (hpa : (5399/1024 : ℝ) ≤ p) (hpb : p ≤ (5407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2697670913/5000000000 : ℝ)*x 0 + (497346927/1000000000 : ℝ)*x 1 + (-838102209/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2697670913/5000000000 : ℝ)^5407 ≤ (46710075951633/100000000000000 : ℝ)^4383 := by
    have hnat : (2697670913 : ℕ)^5407*100000000000000^4383 ≤ 46710075951633^4383*5000000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697670913 5000000000 46710075951633 100000000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (497346927/1000000000 : ℝ)^5407 ≤ (21123214441229/50000000000000 : ℝ)^4383 := by
    have hnat : (497346927 : ℕ)^5407*50000000000000^4383 ≤ 21123214441229^4383*1000000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      497346927 1000000000 21123214441229 50000000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (838102209/5000000000 : ℝ)^5407 ≤ (552174757639/5000000000000 : ℝ)^4383 := by
    have hnat : (838102209 : ℕ)^5407*5000000000000^4383 ≤ 552174757639^4383*5000000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      838102209 5000000000 552174757639 5000000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5407/1024 : ℝ)) 5407 4383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2697670913/5000000000 : ℝ), (497346927/1000000000 : ℝ), (-838102209/5000000000 : ℝ)] ![(46710075951633/100000000000000 : ℝ), (21123214441229/50000000000000 : ℝ), (552174757639/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2697670913/5000000000 : ℝ)|^5407 ≤ (46710075951633/100000000000000 : ℝ)^4383
        have hw : |(2697670913/5000000000 : ℝ)|=(2697670913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(497346927/1000000000 : ℝ)|^5407 ≤ (21123214441229/50000000000000 : ℝ)^4383
        have hw : |(497346927/1000000000 : ℝ)|=(497346927/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-838102209/5000000000 : ℝ)|^5407 ≤ (552174757639/5000000000000 : ℝ)^4383
        have hw : |(-838102209/5000000000 : ℝ)|=(838102209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1723_s0_3 (p : ℝ) (hpa : (5399/1024 : ℝ) ≤ p) (hpb : p ≤ (5407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2014394809/5000000000 : ℝ)*x 0 + (1533598433/5000000000 : ℝ)*x 1 + (5154337853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2014394809/5000000000 : ℝ)^5407 ≤ (8144633820203/25000000000000 : ℝ)^4383 := by
    have hnat : (2014394809 : ℕ)^5407*25000000000000^4383 ≤ 8144633820203^4383*5000000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2014394809 5000000000 8144633820203 25000000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1533598433/5000000000 : ℝ)^5407 ≤ (11635877546653/50000000000000 : ℝ)^4383 := by
    have hnat : (1533598433 : ℕ)^5407*50000000000000^4383 ≤ 11635877546653^4383*5000000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1533598433 5000000000 11635877546653 50000000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5154337853/10000000000 : ℝ)^5407 ≤ (22074854807499/50000000000000 : ℝ)^4383 := by
    have hnat : (5154337853 : ℕ)^5407*50000000000000^4383 ≤ 22074854807499^4383*10000000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5154337853 10000000000 22074854807499 50000000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5407/1024 : ℝ)) 5407 4383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2014394809/5000000000 : ℝ), (1533598433/5000000000 : ℝ), (5154337853/10000000000 : ℝ)] ![(8144633820203/25000000000000 : ℝ), (11635877546653/50000000000000 : ℝ), (22074854807499/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2014394809/5000000000 : ℝ)|^5407 ≤ (8144633820203/25000000000000 : ℝ)^4383
        have hw : |(2014394809/5000000000 : ℝ)|=(2014394809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1533598433/5000000000 : ℝ)|^5407 ≤ (11635877546653/50000000000000 : ℝ)^4383
        have hw : |(1533598433/5000000000 : ℝ)|=(1533598433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5154337853/10000000000 : ℝ)|^5407 ≤ (22074854807499/50000000000000 : ℝ)^4383
        have hw : |(5154337853/10000000000 : ℝ)|=(5154337853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1723_s0_4 (p : ℝ) (hpa : (5399/1024 : ℝ) ≤ p) (hpb : p ≤ (5407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1300660489/10000000000 : ℝ)*x 0 + (2495201903/5000000000 : ℝ)*x 1 + (5655111239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1300660489/10000000000 : ℝ)^5407 ≤ (8076182593389/100000000000000 : ℝ)^4383 := by
    have hnat : (1300660489 : ℕ)^5407*100000000000000^4383 ≤ 8076182593389^4383*10000000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1300660489 10000000000 8076182593389 100000000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2495201903/5000000000 : ℝ)^5407 ≤ (10605988654681/25000000000000 : ℝ)^4383 := by
    have hnat : (2495201903 : ℕ)^5407*25000000000000^4383 ≤ 10605988654681^4383*5000000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2495201903 5000000000 10605988654681 25000000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5655111239/10000000000 : ℝ)^5407 ≤ (3093741422937/6250000000000 : ℝ)^4383 := by
    have hnat : (5655111239 : ℕ)^5407*6250000000000^4383 ≤ 3093741422937^4383*10000000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5655111239 10000000000 3093741422937 6250000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5407/1024 : ℝ)) 5407 4383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1300660489/10000000000 : ℝ), (2495201903/5000000000 : ℝ), (5655111239/10000000000 : ℝ)] ![(8076182593389/100000000000000 : ℝ), (10605988654681/25000000000000 : ℝ), (3093741422937/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1300660489/10000000000 : ℝ)|^5407 ≤ (8076182593389/100000000000000 : ℝ)^4383
        have hw : |(-1300660489/10000000000 : ℝ)|=(1300660489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2495201903/5000000000 : ℝ)|^5407 ≤ (10605988654681/25000000000000 : ℝ)^4383
        have hw : |(2495201903/5000000000 : ℝ)|=(2495201903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5655111239/10000000000 : ℝ)|^5407 ≤ (3093741422937/6250000000000 : ℝ)^4383
        have hw : |(5655111239/10000000000 : ℝ)|=(5655111239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1723_s0_5 (p : ℝ) (hpa : (5399/1024 : ℝ) ≤ p) (hpb : p ≤ (5407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5206341571/10000000000 : ℝ)*x 0 + (-1989123/20000000 : ℝ)*x 1 + (5655111323/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5206341571/10000000000 : ℝ)^5407 ≤ (558748298777/1250000000000 : ℝ)^4383 := by
    have hnat : (5206341571 : ℕ)^5407*1250000000000^4383 ≤ 558748298777^4383*10000000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5206341571 10000000000 558748298777 1250000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1989123/20000000 : ℝ)^5407 ≤ (2900136204579/50000000000000 : ℝ)^4383 := by
    have hnat : (1989123 : ℕ)^5407*50000000000000^4383 ≤ 2900136204579^4383*20000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1989123 20000000 2900136204579 50000000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5655111323/10000000000 : ℝ)^5407 ≤ (49499863674033/100000000000000 : ℝ)^4383 := by
    have hnat : (5655111323 : ℕ)^5407*100000000000000^4383 ≤ 49499863674033^4383*10000000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5655111323 10000000000 49499863674033 100000000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5407/1024 : ℝ)) 5407 4383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5206341571/10000000000 : ℝ), (-1989123/20000000 : ℝ), (5655111323/10000000000 : ℝ)] ![(558748298777/1250000000000 : ℝ), (2900136204579/50000000000000 : ℝ), (49499863674033/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5206341571/10000000000 : ℝ)|^5407 ≤ (558748298777/1250000000000 : ℝ)^4383
        have hw : |(5206341571/10000000000 : ℝ)|=(5206341571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1989123/20000000 : ℝ)|^5407 ≤ (2900136204579/50000000000000 : ℝ)^4383
        have hw : |(-1989123/20000000 : ℝ)|=(1989123/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5655111323/10000000000 : ℝ)|^5407 ≤ (49499863674033/100000000000000 : ℝ)^4383
        have hw : |(5655111323/10000000000 : ℝ)|=(5655111323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1723_s0_6 (p : ℝ) (hpa : (5399/1024 : ℝ) ≤ p) (hpb : p ≤ (5407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5206341259/10000000000 : ℝ)*x 0 + (2827555647/5000000000 : ℝ)*x 1 + (-994562003/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5206341259/10000000000 : ℝ)^5407 ≤ (8939972119521/20000000000000 : ℝ)^4383 := by
    have hnat : (5206341259 : ℕ)^5407*20000000000000^4383 ≤ 8939972119521^4383*10000000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5206341259 10000000000 8939972119521 20000000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2827555647/5000000000 : ℝ)^5407 ≤ (6187482920111/12500000000000 : ℝ)^4383 := by
    have hnat : (2827555647 : ℕ)^5407*12500000000000^4383 ≤ 6187482920111^4383*5000000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2827555647 5000000000 6187482920111 12500000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (994562003/10000000000 : ℝ)^5407 ≤ (5800276028001/100000000000000 : ℝ)^4383 := by
    have hnat : (994562003 : ℕ)^5407*100000000000000^4383 ≤ 5800276028001^4383*10000000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      994562003 10000000000 5800276028001 100000000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5407/1024 : ℝ)) 5407 4383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5206341259/10000000000 : ℝ), (2827555647/5000000000 : ℝ), (-994562003/10000000000 : ℝ)] ![(8939972119521/20000000000000 : ℝ), (6187482920111/12500000000000 : ℝ), (5800276028001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5206341259/10000000000 : ℝ)|^5407 ≤ (8939972119521/20000000000000 : ℝ)^4383
        have hw : |(5206341259/10000000000 : ℝ)|=(5206341259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2827555647/5000000000 : ℝ)|^5407 ≤ (6187482920111/12500000000000 : ℝ)^4383
        have hw : |(2827555647/5000000000 : ℝ)|=(2827555647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-994562003/10000000000 : ℝ)|^5407 ≤ (5800276028001/100000000000000 : ℝ)^4383
        have hw : |(-994562003/10000000000 : ℝ)|=(994562003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1723_s0_7 (p : ℝ) (hpa : (5399/1024 : ℝ) ≤ p) (hpb : p ≤ (5407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (806641313/2000000000 : ℝ)*x 0 + (5103783297/10000000000 : ℝ)*x 1 + (3119392499/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (806641313/2000000000 : ℝ)^5407 ≤ (16311301453319/50000000000000 : ℝ)^4383 := by
    have hnat : (806641313 : ℕ)^5407*50000000000000^4383 ≤ 16311301453319^4383*2000000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      806641313 2000000000 16311301453319 50000000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5103783297/10000000000 : ℝ)^5407 ≤ (10904031943341/25000000000000 : ℝ)^4383 := by
    have hnat : (5103783297 : ℕ)^5407*25000000000000^4383 ≤ 10904031943341^4383*10000000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5103783297 10000000000 10904031943341 25000000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3119392499/10000000000 : ℝ)^5407 ≤ (2970158663301/12500000000000 : ℝ)^4383 := by
    have hnat : (3119392499 : ℕ)^5407*12500000000000^4383 ≤ 2970158663301^4383*10000000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3119392499 10000000000 2970158663301 12500000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5407/1024 : ℝ)) 5407 4383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(806641313/2000000000 : ℝ), (5103783297/10000000000 : ℝ), (3119392499/10000000000 : ℝ)] ![(16311301453319/50000000000000 : ℝ), (10904031943341/25000000000000 : ℝ), (2970158663301/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(806641313/2000000000 : ℝ)|^5407 ≤ (16311301453319/50000000000000 : ℝ)^4383
        have hw : |(806641313/2000000000 : ℝ)|=(806641313/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5103783297/10000000000 : ℝ)|^5407 ≤ (10904031943341/25000000000000 : ℝ)^4383
        have hw : |(5103783297/10000000000 : ℝ)|=(5103783297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3119392499/10000000000 : ℝ)|^5407 ≤ (2970158663301/12500000000000 : ℝ)^4383
        have hw : |(3119392499/10000000000 : ℝ)|=(3119392499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1723_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5399/1024 : ℝ) ≤ p) (hpb : p ≤ (5407/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (199267911/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (3207/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2683/12500 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (5399/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5399 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5399*1^1024 ≤ 0^1024*1^5399 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5399 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5399 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5399/1024 : ℝ) ≤ (3191073740433249/400000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5399 ≤ (3191073740433249/400000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5399*400000000000000000^1024 ≤ 3191073740433249^1024*5^5399 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 3191073740433249 400000000000000000 5399 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (3191073740433249/400000000000000000 : ℝ)) (by norm_num) (by norm_num) 5399 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5399/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5399 := by
      have hnat : (1 : ℕ)^1024*1^5399 ≤ 1^5399*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5399 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5399 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (403191073740433249/400000000000000000 : ℝ) ≤ (2003016436395393/2000000000000000 : ℝ) ^ (5399/1024 : ℝ) := by
    have hpowers : (403191073740433249/400000000000000000 : ℝ)^1024 ≤ (2003016436395393/2000000000000000 : ℝ)^5399 := by
      have hnat : (403191073740433249 : ℕ)^1024*2000000000000000^5399 ≤ 2003016436395393^5399*400000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        403191073740433249 400000000000000000 2003016436395393 2000000000000000 1024 5399 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2003016436395393/2000000000000000 : ℝ)) (X := (403191073740433249/400000000000000000 : ℝ)) (by norm_num) 5399 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (203191073740433249/200000000000000000 : ℝ) ≤ (1003016436395393/1000000000000000 : ℝ) ^ (5399/1024 : ℝ) := by
    have hpowers : (203191073740433249/200000000000000000 : ℝ)^1024 ≤ (1003016436395393/1000000000000000 : ℝ)^5399 := by
      have hnat : (203191073740433249 : ℕ)^1024*1000000000000000^5399 ≤ 1003016436395393^5399*200000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        203191073740433249 200000000000000000 1003016436395393 1000000000000000 1024 5399 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1003016436395393/1000000000000000 : ℝ)) (X := (203191073740433249/200000000000000000 : ℝ)) (by norm_num) 5399 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(3016436395393/800000000000000 : ℝ)*(0 : ℝ))^(5399/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(3016436395393/800000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3191073740433249/400000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(3016436395393/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5399/1024 : ℝ) := by
    rw [show (1 : ℝ)+(3016436395393/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2003016436395393/2000000000000000 : ℝ) by norm_num, show 1+(3191073740433249/400000000000000000 : ℝ)+(0 : ℝ)=(403191073740433249/400000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3191073740433249/400000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(3016436395393/800000000000000 : ℝ)*(2/5 : ℝ))^(5399/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(3016436395393/800000000000000 : ℝ)*(2/5 : ℝ)=(1003016436395393/1000000000000000 : ℝ) by norm_num, show 1+2*(3191073740433249/400000000000000000 : ℝ)=(203191073740433249/200000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(3016436395393/800000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5399/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (3016436395393/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(3016436395393/800000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5399/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (3016436395393/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(3016436395393/800000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5399/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (3016436395393/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1299180213/10000000000 : ℝ)*X 0 0+(5672595397/10000000000 : ℝ)*X 0 1+(2486734593/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1723_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1348835741/2500000000 : ℝ)*X 1 0+(-838101897/5000000000 : ℝ)*X 1 1+(2486734297/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1723_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2697670913/5000000000 : ℝ)*X 2 0+(497346927/1000000000 : ℝ)*X 2 1+(-838102209/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1723_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2014394809/5000000000 : ℝ)*X 0 0+(1533598433/5000000000 : ℝ)*X 0 1+(5154337853/10000000000 : ℝ)*X 0 2+(2014394809/5000000000 : ℝ)*X 1 0+(1533598433/5000000000 : ℝ)*X 1 1+(5154337853/10000000000 : ℝ)*X 1 2+(2014394809/5000000000 : ℝ)*X 2 0+(1533598433/5000000000 : ℝ)*X 2 1+(5154337853/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1723_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1300660489/10000000000 : ℝ)*X 0 0+(2495201903/5000000000 : ℝ)*X 0 1+(5655111239/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1723_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5206341571/10000000000 : ℝ)*X 1 0+(-1989123/20000000 : ℝ)*X 1 1+(5655111323/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1723_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5206341259/10000000000 : ℝ)*X 2 0+(2827555647/5000000000 : ℝ)*X 2 1+(-994562003/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1723_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((806641313/2000000000 : ℝ)*X 0 0+(5103783297/10000000000 : ℝ)*X 0 1+(3119392499/10000000000 : ℝ)*X 0 2+(806641313/2000000000 : ℝ)*X 1 0+(5103783297/10000000000 : ℝ)*X 1 1+(3119392499/10000000000 : ℝ)*X 1 2+(806641313/2000000000 : ℝ)*X 2 0+(5103783297/10000000000 : ℝ)*X 2 1+(3119392499/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1723_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (47553649492134400908537/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (216977159/100000000000000 : ℝ)*(base1) + (1930537239/100000000000000 : ℝ)*(base19) + (1628840069/100000000000000 : ℝ)*(base23) + (86409193/20000000000000 : ℝ)*(upper3) + (107409787/100000000000000 : ℝ)*(upper5) + (477374858939997/50000000000000 : ℝ)*(major0) + (477374858939997/50000000000000 : ℝ)*(major1) + (477374858939997/50000000000000 : ℝ)*(major2) + (357591395053597/25000000000000 : ℝ)*(sp0) + (715184252532943/50000000000000 : ℝ)*(sp1) + (89398050422691/6250000000000 : ℝ)*(sp2) + (29945367833977/6250000000000 : ℝ)*(sp3) + (634045737/12500000000000 : ℝ)*(sp4) + (1290405867/50000000000000 : ℝ)*(sp7) + (239564341566263/50000000000000 : ℝ)*(f.failure) + (357592608900781/25000000000000 : ℝ)*(f.sum) + (52470384273821/20000000000000000000000000000 : ℝ)*base65 + (264022093353821/40000000000000000000000000000 : ℝ)*base67 + (67086007273821/40000000000000000000000000000 : ℝ)*base69 + (288456658633821/40000000000000000000000000000 : ℝ)*base71 + (51169697713821/20000000000000000000000000000 : ℝ)*base73 + (181484768393821/40000000000000000000000000000 : ℝ)*base75 + (235582492553821/40000000000000000000000000000 : ℝ)*base77 + (155129417033821/40000000000000000000000000000 : ℝ)*base79 + (32698524846179/20000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (3913407/5000000000000000000000 : ℝ)*base90 + (3913407/5000000000000000000000 : ℝ)*base92 + (3913407/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2755688029502740605573/1600000000000000000000000000 : ℝ) := by norm_num
    linear_combination (48083799/10000000000000 : ℝ)*(base19) + (411490613/100000000000000 : ℝ)*(base23) + (12948111/50000000000000 : ℝ)*(upper2) + (87932369/100000000000000 : ℝ)*(upper3) + (28323173/50000000000000 : ℝ)*(upper5) + (40167071377571/4000000000000 : ℝ)*(major0) + (40167071377571/4000000000000 : ℝ)*(major1) + (40167071377571/4000000000000 : ℝ)*(major2) + (1960316029/100000000000000 : ℝ)*(sp1) + (1163346649/100000000000000 : ℝ)*(sp2) + (60176820007089/4000000000000 : ℝ)*(sp4) + (752209029511603/50000000000000 : ℝ)*(sp5) + (752209462669981/50000000000000 : ℝ)*(sp6) + (503933011291153/100000000000000 : ℝ)*(sp7) + (503933011291153/100000000000000 : ℝ)*(f.failure) + (60176820007089/4000000000000 : ℝ)*(f.sum) + (248777658403/1600000000000000000000000000 : ℝ)*base65 + (2069179400797/3200000000000000000000000000 : ℝ)*base68 + (13409849940003/3200000000000000000000000000 : ℝ)*base69 + (3245072644003/3200000000000000000000000000 : ℝ)*base71 + (3257513533597/1600000000000000000000000000 : ℝ)*base74 + (5322416375203/3200000000000000000000000000 : ℝ)*base75 + (19514939364003/3200000000000000000000000000 : ℝ)*base77 + (17962216733603/3200000000000000000000000000 : ℝ)*base79 + (2104064444003/1600000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (28908617/10000000000000000000000 : ℝ)*base90 + (28908617/10000000000000000000000 : ℝ)*base92 + (28908617/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1723_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5399/1024 : ℝ) ≤ p) (hpb : p ≤ (5407/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (199267911/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3207/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2683/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1723_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1723_s1_0 (p : ℝ) (hpa : (5399/1024 : ℝ) ≤ p) (hpb : p ≤ (5407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1363731943/10000000000 : ℝ)*x 0 + (2736564439/5000000000 : ℝ)*x 1 + (5130290107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1363731943/10000000000 : ℝ)^5407 ≤ (8562011558799/100000000000000 : ℝ)^4383 := by
    have hnat : (1363731943 : ℕ)^5407*100000000000000^4383 ≤ 8562011558799^4383*10000000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1363731943 10000000000 8562011558799 100000000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2736564439/5000000000 : ℝ)^5407 ≤ (47542245768811/100000000000000 : ℝ)^4383 := by
    have hnat : (2736564439 : ℕ)^5407*100000000000000^4383 ≤ 47542245768811^4383*5000000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2736564439 5000000000 47542245768811 100000000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5130290107/10000000000 : ℝ)^5407 ≤ (85733872391/195312500000 : ℝ)^4383 := by
    have hnat : (5130290107 : ℕ)^5407*195312500000^4383 ≤ 85733872391^4383*10000000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5130290107 10000000000 85733872391 195312500000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5407/1024 : ℝ)) 5407 4383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1363731943/10000000000 : ℝ), (2736564439/5000000000 : ℝ), (5130290107/10000000000 : ℝ)] ![(8562011558799/100000000000000 : ℝ), (47542245768811/100000000000000 : ℝ), (85733872391/195312500000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1363731943/10000000000 : ℝ)|^5407 ≤ (8562011558799/100000000000000 : ℝ)^4383
        have hw : |(-1363731943/10000000000 : ℝ)|=(1363731943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2736564439/5000000000 : ℝ)|^5407 ≤ (47542245768811/100000000000000 : ℝ)^4383
        have hw : |(2736564439/5000000000 : ℝ)|=(2736564439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5130290107/10000000000 : ℝ)|^5407 ≤ (85733872391/195312500000 : ℝ)^4383
        have hw : |(5130290107/10000000000 : ℝ)|=(5130290107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1723_s1_1 (p : ℝ) (hpa : (5399/1024 : ℝ) ≤ p) (hpb : p ≤ (5407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5342221253/10000000000 : ℝ)*x 0 + (-770857229/5000000000 : ℝ)*x 1 + (2565144569/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5342221253/10000000000 : ℝ)^5407 ≤ (4614339551741/10000000000000 : ℝ)^4383 := by
    have hnat : (5342221253 : ℕ)^5407*10000000000000^4383 ≤ 4614339551741^4383*10000000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5342221253 10000000000 4614339551741 10000000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (770857229/5000000000 : ℝ)^5407 ≤ (79686976237/800000000000 : ℝ)^4383 := by
    have hnat : (770857229 : ℕ)^5407*800000000000^4383 ≤ 79686976237^4383*5000000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      770857229 5000000000 79686976237 800000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2565144569/5000000000 : ℝ)^5407 ≤ (43895732436229/100000000000000 : ℝ)^4383 := by
    have hnat : (2565144569 : ℕ)^5407*100000000000000^4383 ≤ 43895732436229^4383*5000000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2565144569 5000000000 43895732436229 100000000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5407/1024 : ℝ)) 5407 4383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5342221253/10000000000 : ℝ), (-770857229/5000000000 : ℝ), (2565144569/5000000000 : ℝ)] ![(4614339551741/10000000000000 : ℝ), (79686976237/800000000000 : ℝ), (43895732436229/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5342221253/10000000000 : ℝ)|^5407 ≤ (4614339551741/10000000000000 : ℝ)^4383
        have hw : |(5342221253/10000000000 : ℝ)|=(5342221253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-770857229/5000000000 : ℝ)|^5407 ≤ (79686976237/800000000000 : ℝ)^4383
        have hw : |(-770857229/5000000000 : ℝ)|=(770857229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2565144569/5000000000 : ℝ)|^5407 ≤ (43895732436229/100000000000000 : ℝ)^4383
        have hw : |(2565144569/5000000000 : ℝ)|=(2565144569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1723_s1_2 (p : ℝ) (hpa : (5399/1024 : ℝ) ≤ p) (hpb : p ≤ (5407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2671110029/5000000000 : ℝ)*x 0 + (160321561/312500000 : ℝ)*x 1 + (-770857489/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2671110029/5000000000 : ℝ)^5407 ≤ (369147062273/800000000000 : ℝ)^4383 := by
    have hnat : (2671110029 : ℕ)^5407*800000000000^4383 ≤ 369147062273^4383*5000000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2671110029 5000000000 369147062273 800000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (160321561/312500000 : ℝ)^5407 ≤ (2194787051407/5000000000000 : ℝ)^4383 := by
    have hnat : (160321561 : ℕ)^5407*5000000000000^4383 ≤ 2194787051407^4383*312500000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      160321561 312500000 2194787051407 5000000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (770857489/5000000000 : ℝ)^5407 ≤ (1245109521777/12500000000000 : ℝ)^4383 := by
    have hnat : (770857489 : ℕ)^5407*12500000000000^4383 ≤ 1245109521777^4383*5000000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      770857489 5000000000 1245109521777 12500000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5407/1024 : ℝ)) 5407 4383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2671110029/5000000000 : ℝ), (160321561/312500000 : ℝ), (-770857489/5000000000 : ℝ)] ![(369147062273/800000000000 : ℝ), (2194787051407/5000000000000 : ℝ), (1245109521777/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2671110029/5000000000 : ℝ)|^5407 ≤ (369147062273/800000000000 : ℝ)^4383
        have hw : |(2671110029/5000000000 : ℝ)|=(2671110029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(160321561/312500000 : ℝ)|^5407 ≤ (2194787051407/5000000000000 : ℝ)^4383
        have hw : |(160321561/312500000 : ℝ)|=(160321561/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-770857489/5000000000 : ℝ)|^5407 ≤ (1245109521777/12500000000000 : ℝ)^4383
        have hw : |(-770857489/5000000000 : ℝ)|=(770857489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1723_s1_3 (p : ℝ) (hpa : (5399/1024 : ℝ) ≤ p) (hpb : p ≤ (5407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (510781097/1250000000 : ℝ)*x 0 + (3594094017/10000000000 : ℝ)*x 1 + (4617585719/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (510781097/1250000000 : ℝ)^5407 ≤ (16576340051619/50000000000000 : ℝ)^4383 := by
    have hnat : (510781097 : ℕ)^5407*50000000000000^4383 ≤ 16576340051619^4383*1250000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      510781097 1250000000 16576340051619 50000000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3594094017/10000000000 : ℝ)^5407 ≤ (14149198084341/50000000000000 : ℝ)^4383 := by
    have hnat : (3594094017 : ℕ)^5407*50000000000000^4383 ≤ 14149198084341^4383*10000000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3594094017 10000000000 14149198084341 50000000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4617585719/10000000000 : ℝ)^5407 ≤ (38548923711433/100000000000000 : ℝ)^4383 := by
    have hnat : (4617585719 : ℕ)^5407*100000000000000^4383 ≤ 38548923711433^4383*10000000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4617585719 10000000000 38548923711433 100000000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5407/1024 : ℝ)) 5407 4383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(510781097/1250000000 : ℝ), (3594094017/10000000000 : ℝ), (4617585719/10000000000 : ℝ)] ![(16576340051619/50000000000000 : ℝ), (14149198084341/50000000000000 : ℝ), (38548923711433/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(510781097/1250000000 : ℝ)|^5407 ≤ (16576340051619/50000000000000 : ℝ)^4383
        have hw : |(510781097/1250000000 : ℝ)|=(510781097/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3594094017/10000000000 : ℝ)|^5407 ≤ (14149198084341/50000000000000 : ℝ)^4383
        have hw : |(3594094017/10000000000 : ℝ)|=(3594094017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4617585719/10000000000 : ℝ)|^5407 ≤ (38548923711433/100000000000000 : ℝ)^4383
        have hw : |(4617585719/10000000000 : ℝ)|=(4617585719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1723_s1_4 (p : ℝ) (hpa : (5399/1024 : ℝ) ≤ p) (hpb : p ≤ (5407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-340976439/2500000000 : ℝ)*x 0 + (1283593807/2500000000 : ℝ)*x 1 + (5468978659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (340976439/2500000000 : ℝ)^5407 ≤ (2140839448093/25000000000000 : ℝ)^4383 := by
    have hnat : (340976439 : ℕ)^5407*25000000000000^4383 ≤ 2140839448093^4383*2500000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340976439 2500000000 2140839448093 25000000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1283593807/2500000000 : ℝ)^5407 ≤ (8787773167011/20000000000000 : ℝ)^4383 := by
    have hnat : (1283593807 : ℕ)^5407*20000000000000^4383 ≤ 8787773167011^4383*2500000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1283593807 2500000000 8787773167011 20000000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5468978659/10000000000 : ℝ)^5407 ≤ (47497776350111/100000000000000 : ℝ)^4383 := by
    have hnat : (5468978659 : ℕ)^5407*100000000000000^4383 ≤ 47497776350111^4383*10000000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5468978659 10000000000 47497776350111 100000000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5407/1024 : ℝ)) 5407 4383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-340976439/2500000000 : ℝ), (1283593807/2500000000 : ℝ), (5468978659/10000000000 : ℝ)] ![(2140839448093/25000000000000 : ℝ), (8787773167011/20000000000000 : ℝ), (47497776350111/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-340976439/2500000000 : ℝ)|^5407 ≤ (2140839448093/25000000000000 : ℝ)^4383
        have hw : |(-340976439/2500000000 : ℝ)|=(340976439/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1283593807/2500000000 : ℝ)|^5407 ≤ (8787773167011/20000000000000 : ℝ)^4383
        have hw : |(1283593807/2500000000 : ℝ)|=(1283593807/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5468978659/10000000000 : ℝ)|^5407 ≤ (47497776350111/100000000000000 : ℝ)^4383
        have hw : |(5468978659/10000000000 : ℝ)|=(5468978659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1723_s1_5 (p : ℝ) (hpa : (5399/1024 : ℝ) ≤ p) (hpb : p ≤ (5407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1050084909/2000000000 : ℝ)*x 0 + (-48121027/400000000 : ℝ)*x 1 + (2734489429/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050084909/2000000000 : ℝ)^5407 ≤ (1806689223353/4000000000000 : ℝ)^4383 := by
    have hnat : (1050084909 : ℕ)^5407*4000000000000^4383 ≤ 1806689223353^4383*2000000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050084909 2000000000 1806689223353 4000000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (48121027/400000000 : ℝ)^5407 ≤ (1833747731853/25000000000000 : ℝ)^4383 := by
    have hnat : (48121027 : ℕ)^5407*25000000000000^4383 ≤ 1833747731853^4383*400000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48121027 400000000 1833747731853 25000000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2734489429/5000000000 : ℝ)^5407 ≤ (23748889241099/50000000000000 : ℝ)^4383 := by
    have hnat : (2734489429 : ℕ)^5407*50000000000000^4383 ≤ 23748889241099^4383*5000000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2734489429 5000000000 23748889241099 50000000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5407/1024 : ℝ)) 5407 4383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050084909/2000000000 : ℝ), (-48121027/400000000 : ℝ), (2734489429/5000000000 : ℝ)] ![(1806689223353/4000000000000 : ℝ), (1833747731853/25000000000000 : ℝ), (23748889241099/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050084909/2000000000 : ℝ)|^5407 ≤ (1806689223353/4000000000000 : ℝ)^4383
        have hw : |(1050084909/2000000000 : ℝ)|=(1050084909/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-48121027/400000000 : ℝ)|^5407 ≤ (1833747731853/25000000000000 : ℝ)^4383
        have hw : |(-48121027/400000000 : ℝ)|=(48121027/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2734489429/5000000000 : ℝ)|^5407 ≤ (23748889241099/50000000000000 : ℝ)^4383
        have hw : |(2734489429/5000000000 : ℝ)|=(2734489429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1723_s1_6 (p : ℝ) (hpa : (5399/1024 : ℝ) ≤ p) (hpb : p ≤ (5407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2625212131/5000000000 : ℝ)*x 0 + (2734489547/5000000000 : ℝ)*x 1 + (-1203025737/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2625212131/5000000000 : ℝ)^5407 ≤ (22583613790257/50000000000000 : ℝ)^4383 := by
    have hnat : (2625212131 : ℕ)^5407*50000000000000^4383 ≤ 22583613790257^4383*5000000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2625212131 5000000000 22583613790257 50000000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2734489547/5000000000 : ℝ)^5407 ≤ (2968611313169/6250000000000 : ℝ)^4383 := by
    have hnat : (2734489547 : ℕ)^5407*6250000000000^4383 ≤ 2968611313169^4383*5000000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2734489547 5000000000 2968611313169 6250000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1203025737/10000000000 : ℝ)^5407 ≤ (1173598623/16000000000 : ℝ)^4383 := by
    have hnat : (1203025737 : ℕ)^5407*16000000000^4383 ≤ 1173598623^4383*10000000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1203025737 10000000000 1173598623 16000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5407/1024 : ℝ)) 5407 4383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2625212131/5000000000 : ℝ), (2734489547/5000000000 : ℝ), (-1203025737/10000000000 : ℝ)] ![(22583613790257/50000000000000 : ℝ), (2968611313169/6250000000000 : ℝ), (1173598623/16000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2625212131/5000000000 : ℝ)|^5407 ≤ (22583613790257/50000000000000 : ℝ)^4383
        have hw : |(2625212131/5000000000 : ℝ)|=(2625212131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2734489547/5000000000 : ℝ)|^5407 ≤ (2968611313169/6250000000000 : ℝ)^4383
        have hw : |(2734489547/5000000000 : ℝ)|=(2734489547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1203025737/10000000000 : ℝ)|^5407 ≤ (1173598623/16000000000 : ℝ)^4383
        have hw : |(-1203025737/10000000000 : ℝ)|=(1203025737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1723_s1_7 (p : ℝ) (hpa : (5399/1024 : ℝ) ≤ p) (hpb : p ≤ (5407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4086766251/10000000000 : ℝ)*x 0 + (1151348171/2500000000 : ℝ)*x 1 + (901619993/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4086766251/10000000000 : ℝ)^5407 ≤ (16578929722303/50000000000000 : ℝ)^4383 := by
    have hnat : (4086766251 : ℕ)^5407*50000000000000^4383 ≤ 16578929722303^4383*10000000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4086766251 10000000000 16578929722303 50000000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1151348171/2500000000 : ℝ)^5407 ≤ (4802923765589/12500000000000 : ℝ)^4383 := by
    have hnat : (1151348171 : ℕ)^5407*12500000000000^4383 ≤ 4802923765589^4383*2500000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1151348171 2500000000 4802923765589 12500000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (901619993/2500000000 : ℝ)^5407 ≤ (3552343802287/12500000000000 : ℝ)^4383 := by
    have hnat : (901619993 : ℕ)^5407*12500000000000^4383 ≤ 3552343802287^4383*2500000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901619993 2500000000 3552343802287 12500000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5407/1024 : ℝ)) 5407 4383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4086766251/10000000000 : ℝ), (1151348171/2500000000 : ℝ), (901619993/2500000000 : ℝ)] ![(16578929722303/50000000000000 : ℝ), (4802923765589/12500000000000 : ℝ), (3552343802287/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4086766251/10000000000 : ℝ)|^5407 ≤ (16578929722303/50000000000000 : ℝ)^4383
        have hw : |(4086766251/10000000000 : ℝ)|=(4086766251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1151348171/2500000000 : ℝ)|^5407 ≤ (4802923765589/12500000000000 : ℝ)^4383
        have hw : |(1151348171/2500000000 : ℝ)|=(1151348171/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(901619993/2500000000 : ℝ)|^5407 ≤ (3552343802287/12500000000000 : ℝ)^4383
        have hw : |(901619993/2500000000 : ℝ)|=(901619993/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1723_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5399/1024 : ℝ) ≤ p) (hpb : p ≤ (5407/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (199267911/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2683/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3207/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (4951/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17237/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2683/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3207/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2683/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3207/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2683/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3207/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2683/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3207/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2683/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3207/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2683/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3207/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3207/50000 : ℝ) ^ (5399/1024 : ℝ) ≤ (12840266084329/25000000000000000000 : ℝ) := by
    have hpowers : (3207/50000 : ℝ)^5399 ≤ (12840266084329/25000000000000000000 : ℝ)^1024 := by
      have hnat : (3207 : ℕ)^5399*25000000000000000000^1024 ≤ 12840266084329^1024*50000^5399 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3207 50000 12840266084329 25000000000000000000 5399 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3207/50000 : ℝ)) (X := (12840266084329/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5399 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2683/12500 : ℝ) ^ (5399/1024 : ℝ) ≤ (2995508512801503/10000000000000000000 : ℝ) := by
    have hpowers : (2683/12500 : ℝ)^5399 ≤ (2995508512801503/10000000000000000000 : ℝ)^1024 := by
      have hnat : (2683 : ℕ)^5399*10000000000000000000^1024 ≤ 2995508512801503^1024*12500^5399 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2683 12500 2995508512801503 10000000000000000000 5399 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2683/12500 : ℝ)) (X := (2995508512801503/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5399 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500012840266084329/12500000000000000000 : ℝ) ≤ (10000001948275903/10000000000000000 : ℝ) ^ (5399/1024 : ℝ) := by
    have hpowers : (12500012840266084329/12500000000000000000 : ℝ)^1024 ≤ (10000001948275903/10000000000000000 : ℝ)^5399 := by
      have hnat : (12500012840266084329 : ℕ)^1024*10000000000000000^5399 ≤ 10000001948275903^5399*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500012840266084329 12500000000000000000 10000001948275903 10000000000000000 1024 5399 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001948275903/10000000000000000 : ℝ)) (X := (12500012840266084329/12500000000000000000 : ℝ)) (by norm_num) 5399 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50015003223096176173/50000000000000000000 : ℝ) ≤ (1000056904734113/1000000000000000 : ℝ) ^ (5399/1024 : ℝ) := by
    have hpowers : (50015003223096176173/50000000000000000000 : ℝ)^1024 ≤ (1000056904734113/1000000000000000 : ℝ)^5399 := by
      have hnat : (50015003223096176173 : ℕ)^1024*1000000000000000^5399 ≤ 1000056904734113^5399*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015003223096176173 50000000000000000000 1000056904734113 1000000000000000 1024 5399 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000056904734113/1000000000000000 : ℝ)) (X := (50015003223096176173/50000000000000000000 : ℝ)) (by norm_num) 5399 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5002995508512801503/5000000000000000000 : ℝ) ≤ (10001136146406357/10000000000000000 : ℝ) ^ (5399/1024 : ℝ) := by
    have hpowers : (5002995508512801503/5000000000000000000 : ℝ)^1024 ≤ (10001136146406357/10000000000000000 : ℝ)^5399 := by
      have hnat : (5002995508512801503 : ℕ)^1024*10000000000000000^5399 ≤ 10001136146406357^5399*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002995508512801503 5000000000000000000 10001136146406357 10000000000000000 1024 5399 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001136146406357/10000000000000000 : ℝ)) (X := (5002995508512801503/5000000000000000000 : ℝ)) (by norm_num) 5399 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(12840266084329/25000000000000000000 : ℝ) ≤ ((75246377287371804097/75250000000000000000 : ℝ)+2*(567099065227/1505000000000000 : ℝ)*(3207/50000 : ℝ))^(5399/1024 : ℝ) := by
    rw [show (75246377287371804097/75250000000000000000 : ℝ)+2*(567099065227/1505000000000000 : ℝ)*(3207/50000 : ℝ)=(10000001948275903/10000000000000000 : ℝ) by norm_num, show 1+2*(12840266084329/25000000000000000000 : ℝ)=(12500012840266084329/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2995508512801503/10000000000000000000 : ℝ)+(12840266084329/25000000000000000000 : ℝ) ≤ ((75246377287371804097/75250000000000000000 : ℝ)+(567099065227/1505000000000000 : ℝ)*((2683/12500 : ℝ)+(3207/50000 : ℝ)))^(5399/1024 : ℝ) := by
    rw [show (75246377287371804097/75250000000000000000 : ℝ)+(567099065227/1505000000000000 : ℝ)*((2683/12500 : ℝ)+(3207/50000 : ℝ))=(1000056904734113/1000000000000000 : ℝ) by norm_num, show 1+(2995508512801503/10000000000000000000 : ℝ)+(12840266084329/25000000000000000000 : ℝ)=(50015003223096176173/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2995508512801503/10000000000000000000 : ℝ) ≤ ((75246377287371804097/75250000000000000000 : ℝ)+2*(567099065227/1505000000000000 : ℝ)*(2683/12500 : ℝ))^(5399/1024 : ℝ) := by
    rw [show (75246377287371804097/75250000000000000000 : ℝ)+2*(567099065227/1505000000000000 : ℝ)*(2683/12500 : ℝ)=(10001136146406357/10000000000000000 : ℝ) by norm_num, show 1+2*(2995508512801503/10000000000000000000 : ℝ)=(5002995508512801503/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (75246377287371804097/75250000000000000000 : ℝ)*(X 1 0+X 2 0)+(567099065227/1505000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5399/1024 : ℝ)) (lo := (3207/50000 : ℝ)) (hi := (2683/12500 : ℝ)) (c := (75246377287371804097/75250000000000000000 : ℝ)) (alpha := (567099065227/1505000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (75246377287371804097/75250000000000000000 : ℝ)*(X 0 1+X 2 1)+(567099065227/1505000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5399/1024 : ℝ)) (lo := (3207/50000 : ℝ)) (hi := (2683/12500 : ℝ)) (c := (75246377287371804097/75250000000000000000 : ℝ)) (alpha := (567099065227/1505000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (75246377287371804097/75250000000000000000 : ℝ)*(X 0 2+X 1 2)+(567099065227/1505000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5399/1024 : ℝ)) (lo := (3207/50000 : ℝ)) (hi := (2683/12500 : ℝ)) (c := (75246377287371804097/75250000000000000000 : ℝ)) (alpha := (567099065227/1505000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1363731943/10000000000 : ℝ)*X 0 0+(2736564439/5000000000 : ℝ)*X 0 1+(5130290107/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1723_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5342221253/10000000000 : ℝ)*X 1 0+(-770857229/5000000000 : ℝ)*X 1 1+(2565144569/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1723_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2671110029/5000000000 : ℝ)*X 2 0+(160321561/312500000 : ℝ)*X 2 1+(-770857489/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1723_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((510781097/1250000000 : ℝ)*X 0 0+(3594094017/10000000000 : ℝ)*X 0 1+(4617585719/10000000000 : ℝ)*X 0 2+(510781097/1250000000 : ℝ)*X 1 0+(3594094017/10000000000 : ℝ)*X 1 1+(4617585719/10000000000 : ℝ)*X 1 2+(510781097/1250000000 : ℝ)*X 2 0+(3594094017/10000000000 : ℝ)*X 2 1+(4617585719/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1723_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-340976439/2500000000 : ℝ)*X 0 0+(1283593807/2500000000 : ℝ)*X 0 1+(5468978659/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1723_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1050084909/2000000000 : ℝ)*X 1 0+(-48121027/400000000 : ℝ)*X 1 1+(2734489429/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1723_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2625212131/5000000000 : ℝ)*X 2 0+(2734489547/5000000000 : ℝ)*X 2 1+(-1203025737/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1723_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4086766251/10000000000 : ℝ)*X 0 0+(1151348171/2500000000 : ℝ)*X 0 1+(901619993/2500000000 : ℝ)*X 0 2+(4086766251/10000000000 : ℝ)*X 1 0+(1151348171/2500000000 : ℝ)*X 1 1+(901619993/2500000000 : ℝ)*X 1 2+(4086766251/10000000000 : ℝ)*X 2 0+(1151348171/2500000000 : ℝ)*X 2 1+(901619993/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1723_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (46958140757142963742384491/8750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (231566843/50000000000000 : ℝ)*(base19) + (5526297/5000000000000 : ℝ)*(lower2) + (224623279/100000000000000 : ℝ)*(lower4) + (32836713/25000000000000 : ℝ)*(lower5) + (194694298130643/10000000000000 : ℝ)*(major0) + (194694298130643/10000000000000 : ℝ)*(major1) + (194694298130643/10000000000000 : ℝ)*(major2) + (364604142811693/12500000000000 : ℝ)*(sp0) + (2916830993205259/100000000000000 : ℝ)*(sp1) + (291683004537443/10000000000000 : ℝ)*(sp2) + (977047920829777/100000000000000 : ℝ)*(sp3) + (4720401377/100000000000000 : ℝ)*(sp4) + (6406555977/100000000000000 : ℝ)*(sp5) + (1954380123/25000000000000 : ℝ)*(sp6) + (977047920829777/100000000000000 : ℝ)*(f.failure) + (1458418931447461/50000000000000 : ℝ)*(f.sum) + (121841080182739/7525000000000000000000000000 : ℝ)*base66 + (2159413313685805629/752500000000000000000000000000000 : ℝ)*base68 + (1029425447271694371/752500000000000000000000000000000 : ℝ)*base69 + (5892589251803305629/752500000000000000000000000000000 : ℝ)*base72 + (40176763891839/7525000000000000000000000000 : ℝ)*base74 + (1001636858629194371/752500000000000000000000000000000 : ℝ)*base75 + (3008158062933305629/752500000000000000000000000000000 : ℝ)*base78 + (1474991251235805629/752500000000000000000000000000000 : ℝ)*base80 + (5721423964757/3762500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (49385847/10000000000000000000000 : ℝ)*base89 + (49385847/10000000000000000000000 : ℝ)*base91 + (49385847/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9054200929446401744385381129/940625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (586164587/100000000000000 : ℝ)*(base19) + (465832743/50000000000000 : ℝ)*(base23) + (173154697/100000000000000 : ℝ)*(upper3) + (110092279/50000000000000 : ℝ)*(lower4) + (21672993/50000000000000 : ℝ)*(upper5) + (498711940678619/25000000000000 : ℝ)*(major0) + (498711940678619/25000000000000 : ℝ)*(major1) + (498711940678619/25000000000000 : ℝ)*(major2) + (560656939/12500000000000 : ℝ)*(sp1) + (9474159377/100000000000000 : ℝ)*(sp2) + (2988606894514987/100000000000000 : ℝ)*(sp4) + (373575227886861/12500000000000 : ℝ)*(sp5) + (747149122172531/25000000000000 : ℝ)*(sp6) + (500544155028171/50000000000000 : ℝ)*(sp7) + (500544155028171/50000000000000 : ℝ)*(f.failure) + (2988606894514987/100000000000000 : ℝ)*(f.sum) + (35650426713569/9406250000000000000000000000 : ℝ)*base65 + (11287088283694847957/1881250000000000000000000000000000 : ℝ)*base68 + (1998794338651097957/1881250000000000000000000000000000 : ℝ)*base70 + (388339812717652043/1881250000000000000000000000000000 : ℝ)*base71 + (29876747820487/18812500000000000000000000000 : ℝ)*base74 + (11234686102569847957/1881250000000000000000000000000000 : ℝ)*base76 + (5230107107644847957/1881250000000000000000000000000000 : ℝ)*base78 + (2366261324280152043/1881250000000000000000000000000000 : ℝ)*base79 + (4899785830847/4703125000000000000000000000 : ℝ)*base81 + (18679219/5000000000000000000000 : ℝ)*base90 + (18679219/5000000000000000000000 : ℝ)*base92 + (18679219/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1723_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5399/1024 : ℝ) ≤ p) (hpb : p ≤ (5407/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (199267911/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2683/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3207/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4951/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17237/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1723_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1723_s2_0 (p : ℝ) (hpa : (5399/1024 : ℝ) ≤ p) (hpb : p ≤ (5407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-683186663/5000000000 : ℝ)*x 0 + (2731094699/5000000000 : ℝ)*x 1 + (5139453033/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (683186663/5000000000 : ℝ)^5407 ≤ (1716494836107/20000000000000 : ℝ)^4383 := by
    have hnat : (683186663 : ℕ)^5407*20000000000000^4383 ≤ 1716494836107^4383*5000000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683186663 5000000000 1716494836107 20000000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2731094699/5000000000 : ℝ)^5407 ≤ (47425046708243/100000000000000 : ℝ)^4383 := by
    have hnat : (2731094699 : ℕ)^5407*100000000000000^4383 ≤ 47425046708243^4383*5000000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2731094699 5000000000 47425046708243 100000000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5139453033/10000000000 : ℝ)^5407 ≤ (21996239553569/50000000000000 : ℝ)^4383 := by
    have hnat : (5139453033 : ℕ)^5407*50000000000000^4383 ≤ 21996239553569^4383*10000000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5139453033 10000000000 21996239553569 50000000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5407/1024 : ℝ)) 5407 4383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-683186663/5000000000 : ℝ), (2731094699/5000000000 : ℝ), (5139453033/10000000000 : ℝ)] ![(1716494836107/20000000000000 : ℝ), (47425046708243/100000000000000 : ℝ), (21996239553569/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-683186663/5000000000 : ℝ)|^5407 ≤ (1716494836107/20000000000000 : ℝ)^4383
        have hw : |(-683186663/5000000000 : ℝ)|=(683186663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2731094699/5000000000 : ℝ)|^5407 ≤ (47425046708243/100000000000000 : ℝ)^4383
        have hw : |(2731094699/5000000000 : ℝ)|=(2731094699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5139453033/10000000000 : ℝ)|^5407 ≤ (21996239553569/50000000000000 : ℝ)^4383
        have hw : |(5139453033/10000000000 : ℝ)|=(5139453033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1723_s2_1 (p : ℝ) (hpa : (5399/1024 : ℝ) ≤ p) (hpb : p ≤ (5407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5339239779/10000000000 : ℝ)*x 0 + (-61342281/400000000 : ℝ)*x 1 + (5139452821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5339239779/10000000000 : ℝ)^5407 ≤ (46111628584511/100000000000000 : ℝ)^4383 := by
    have hnat : (5339239779 : ℕ)^5407*100000000000000^4383 ≤ 46111628584511^4383*10000000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5339239779 10000000000 46111628584511 100000000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (61342281/400000000 : ℝ)^5407 ≤ (4947947268239/50000000000000 : ℝ)^4383 := by
    have hnat : (61342281 : ℕ)^5407*50000000000000^4383 ≤ 4947947268239^4383*400000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      61342281 400000000 4947947268239 50000000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5139452821/10000000000 : ℝ)^5407 ≤ (10998119217127/25000000000000 : ℝ)^4383 := by
    have hnat : (5139452821 : ℕ)^5407*25000000000000^4383 ≤ 10998119217127^4383*10000000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5139452821 10000000000 10998119217127 25000000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5407/1024 : ℝ)) 5407 4383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5339239779/10000000000 : ℝ), (-61342281/400000000 : ℝ), (5139452821/10000000000 : ℝ)] ![(46111628584511/100000000000000 : ℝ), (4947947268239/50000000000000 : ℝ), (10998119217127/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5339239779/10000000000 : ℝ)|^5407 ≤ (46111628584511/100000000000000 : ℝ)^4383
        have hw : |(5339239779/10000000000 : ℝ)|=(5339239779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-61342281/400000000 : ℝ)|^5407 ≤ (4947947268239/50000000000000 : ℝ)^4383
        have hw : |(-61342281/400000000 : ℝ)|=(61342281/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5139452821/10000000000 : ℝ)|^5407 ≤ (10998119217127/25000000000000 : ℝ)^4383
        have hw : |(5139452821/10000000000 : ℝ)|=(5139452821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1723_s2_2 (p : ℝ) (hpa : (5399/1024 : ℝ) ≤ p) (hpb : p ≤ (5407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5339239519/10000000000 : ℝ)*x 0 + (5139453097/10000000000 : ℝ)*x 1 + (-766778503/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5339239519/10000000000 : ℝ)^5407 ≤ (922232516289/2000000000000 : ℝ)^4383 := by
    have hnat : (5339239519 : ℕ)^5407*2000000000000^4383 ≤ 922232516289^4383*10000000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5339239519 10000000000 922232516289 2000000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5139453097/10000000000 : ℝ)^5407 ≤ (43992479782951/100000000000000 : ℝ)^4383 := by
    have hnat : (5139453097 : ℕ)^5407*100000000000000^4383 ≤ 43992479782951^4383*10000000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5139453097 10000000000 43992479782951 100000000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (766778503/5000000000 : ℝ)^5407 ≤ (9895894385229/100000000000000 : ℝ)^4383 := by
    have hnat : (766778503 : ℕ)^5407*100000000000000^4383 ≤ 9895894385229^4383*5000000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      766778503 5000000000 9895894385229 100000000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5407/1024 : ℝ)) 5407 4383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5339239519/10000000000 : ℝ), (5139453097/10000000000 : ℝ), (-766778503/5000000000 : ℝ)] ![(922232516289/2000000000000 : ℝ), (43992479782951/100000000000000 : ℝ), (9895894385229/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5339239519/10000000000 : ℝ)|^5407 ≤ (922232516289/2000000000000 : ℝ)^4383
        have hw : |(5339239519/10000000000 : ℝ)|=(5339239519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5139453097/10000000000 : ℝ)|^5407 ≤ (43992479782951/100000000000000 : ℝ)^4383
        have hw : |(5139453097/10000000000 : ℝ)|=(5139453097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-766778503/5000000000 : ℝ)|^5407 ≤ (9895894385229/100000000000000 : ℝ)^4383
        have hw : |(-766778503/5000000000 : ℝ)|=(766778503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1723_s2_3 (p : ℝ) (hpa : (5399/1024 : ℝ) ≤ p) (hpb : p ≤ (5407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2044151809/5000000000 : ℝ)*x 0 + (3623921839/10000000000 : ℝ)*x 1 + (2293703289/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2044151809/5000000000 : ℝ)^5407 ≤ (33173247658833/100000000000000 : ℝ)^4383 := by
    have hnat : (2044151809 : ℕ)^5407*100000000000000^4383 ≤ 33173247658833^4383*5000000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2044151809 5000000000 33173247658833 100000000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3623921839/10000000000 : ℝ)^5407 ≤ (14294198342051/50000000000000 : ℝ)^4383 := by
    have hnat : (3623921839 : ℕ)^5407*50000000000000^4383 ≤ 14294198342051^4383*10000000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3623921839 10000000000 14294198342051 50000000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2293703289/5000000000 : ℝ)^5407 ≤ (4779794454393/12500000000000 : ℝ)^4383 := by
    have hnat : (2293703289 : ℕ)^5407*12500000000000^4383 ≤ 4779794454393^4383*5000000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2293703289 5000000000 4779794454393 12500000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5407/1024 : ℝ)) 5407 4383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2044151809/5000000000 : ℝ), (3623921839/10000000000 : ℝ), (2293703289/5000000000 : ℝ)] ![(33173247658833/100000000000000 : ℝ), (14294198342051/50000000000000 : ℝ), (4779794454393/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2044151809/5000000000 : ℝ)|^5407 ≤ (33173247658833/100000000000000 : ℝ)^4383
        have hw : |(2044151809/5000000000 : ℝ)|=(2044151809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3623921839/10000000000 : ℝ)|^5407 ≤ (14294198342051/50000000000000 : ℝ)^4383
        have hw : |(3623921839/10000000000 : ℝ)|=(3623921839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2293703289/5000000000 : ℝ)|^5407 ≤ (4779794454393/12500000000000 : ℝ)^4383
        have hw : |(2293703289/5000000000 : ℝ)|=(2293703289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1723_s2_4 (p : ℝ) (hpa : (5399/1024 : ℝ) ≤ p) (hpb : p ≤ (5407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1366518027/10000000000 : ℝ)*x 0 + (5143074467/10000000000 : ℝ)*x 1 + (272925693/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1366518027/10000000000 : ℝ)^5407 ≤ (8583595436933/100000000000000 : ℝ)^4383 := by
    have hnat : (1366518027 : ℕ)^5407*100000000000000^4383 ≤ 8583595436933^4383*10000000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1366518027 10000000000 8583595436933 100000000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5143074467/10000000000 : ℝ)^5407 ≤ (440307230577/1000000000000 : ℝ)^4383 := by
    have hnat : (5143074467 : ℕ)^5407*1000000000000^4383 ≤ 440307230577^4383*10000000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5143074467 10000000000 440307230577 1000000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (272925693/500000000 : ℝ)^5407 ≤ (47385681488213/100000000000000 : ℝ)^4383 := by
    have hnat : (272925693 : ℕ)^5407*100000000000000^4383 ≤ 47385681488213^4383*500000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272925693 500000000 47385681488213 100000000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5407/1024 : ℝ)) 5407 4383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1366518027/10000000000 : ℝ), (5143074467/10000000000 : ℝ), (272925693/500000000 : ℝ)] ![(8583595436933/100000000000000 : ℝ), (440307230577/1000000000000 : ℝ), (47385681488213/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1366518027/10000000000 : ℝ)|^5407 ≤ (8583595436933/100000000000000 : ℝ)^4383
        have hw : |(-1366518027/10000000000 : ℝ)|=(1366518027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5143074467/10000000000 : ℝ)|^5407 ≤ (440307230577/1000000000000 : ℝ)^4383
        have hw : |(5143074467/10000000000 : ℝ)|=(5143074467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(272925693/500000000 : ℝ)|^5407 ≤ (47385681488213/100000000000000 : ℝ)^4383
        have hw : |(272925693/500000000 : ℝ)|=(272925693/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1723_s2_5 (p : ℝ) (hpa : (5399/1024 : ℝ) ≤ p) (hpb : p ≤ (5407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5252848653/10000000000 : ℝ)*x 0 + (-607247957/5000000000 : ℝ)*x 1 + (682314229/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5252848653/10000000000 : ℝ)^5407 ≤ (9038591518873/20000000000000 : ℝ)^4383 := by
    have hnat : (5252848653 : ℕ)^5407*20000000000000^4383 ≤ 9038591518873^4383*10000000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252848653 10000000000 9038591518873 20000000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (607247957/5000000000 : ℝ)^5407 ≤ (3710680602427/50000000000000 : ℝ)^4383 := by
    have hnat : (607247957 : ℕ)^5407*50000000000000^4383 ≤ 3710680602427^4383*5000000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      607247957 5000000000 3710680602427 50000000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (682314229/1250000000 : ℝ)^5407 ≤ (9477136237671/20000000000000 : ℝ)^4383 := by
    have hnat : (682314229 : ℕ)^5407*20000000000000^4383 ≤ 9477136237671^4383*1250000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      682314229 1250000000 9477136237671 20000000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5407/1024 : ℝ)) 5407 4383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5252848653/10000000000 : ℝ), (-607247957/5000000000 : ℝ), (682314229/1250000000 : ℝ)] ![(9038591518873/20000000000000 : ℝ), (3710680602427/50000000000000 : ℝ), (9477136237671/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5252848653/10000000000 : ℝ)|^5407 ≤ (9038591518873/20000000000000 : ℝ)^4383
        have hw : |(5252848653/10000000000 : ℝ)|=(5252848653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-607247957/5000000000 : ℝ)|^5407 ≤ (3710680602427/50000000000000 : ℝ)^4383
        have hw : |(-607247957/5000000000 : ℝ)|=(607247957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(682314229/1250000000 : ℝ)|^5407 ≤ (9477136237671/20000000000000 : ℝ)^4383
        have hw : |(682314229/1250000000 : ℝ)|=(682314229/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1723_s2_6 (p : ℝ) (hpa : (5399/1024 : ℝ) ≤ p) (hpb : p ≤ (5407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5252848643/10000000000 : ℝ)*x 0 + (2729256923/5000000000 : ℝ)*x 1 + (-1214495907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5252848643/10000000000 : ℝ)^5407 ≤ (4519295748823/10000000000000 : ℝ)^4383 := by
    have hnat : (5252848643 : ℕ)^5407*10000000000000^4383 ≤ 4519295748823^4383*10000000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252848643 10000000000 4519295748823 10000000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2729256923/5000000000 : ℝ)^5407 ≤ (11846420334571/25000000000000 : ℝ)^4383 := by
    have hnat : (2729256923 : ℕ)^5407*25000000000000^4383 ≤ 11846420334571^4383*5000000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2729256923 5000000000 11846420334571 25000000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1214495907/10000000000 : ℝ)^5407 ≤ (3710680576043/50000000000000 : ℝ)^4383 := by
    have hnat : (1214495907 : ℕ)^5407*50000000000000^4383 ≤ 3710680576043^4383*10000000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1214495907 10000000000 3710680576043 50000000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5407/1024 : ℝ)) 5407 4383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5252848643/10000000000 : ℝ), (2729256923/5000000000 : ℝ), (-1214495907/10000000000 : ℝ)] ![(4519295748823/10000000000000 : ℝ), (11846420334571/25000000000000 : ℝ), (3710680576043/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5252848643/10000000000 : ℝ)|^5407 ≤ (4519295748823/10000000000000 : ℝ)^4383
        have hw : |(5252848643/10000000000 : ℝ)|=(5252848643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2729256923/5000000000 : ℝ)|^5407 ≤ (11846420334571/25000000000000 : ℝ)^4383
        have hw : |(2729256923/5000000000 : ℝ)|=(2729256923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1214495907/10000000000 : ℝ)|^5407 ≤ (3710680576043/50000000000000 : ℝ)^4383
        have hw : |(-1214495907/10000000000 : ℝ)|=(1214495907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1723_s2_7 (p : ℝ) (hpa : (5399/1024 : ℝ) ≤ p) (hpb : p ≤ (5407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (408873541/1000000000 : ℝ)*x 0 + (2288297281/5000000000 : ℝ)*x 1 + (3634894931/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (408873541/1000000000 : ℝ)^5407 ≤ (8294392476749/25000000000000 : ℝ)^4383 := by
    have hnat : (408873541 : ℕ)^5407*25000000000000^4383 ≤ 8294392476749^4383*1000000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      408873541 1000000000 8294392476749 25000000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2288297281/5000000000 : ℝ)^5407 ≤ (38127207061169/100000000000000 : ℝ)^4383 := by
    have hnat : (2288297281 : ℕ)^5407*100000000000000^4383 ≤ 38127207061169^4383*5000000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2288297281 5000000000 38127207061169 100000000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3634894931/10000000000 : ℝ)^5407 ≤ (3586902878521/12500000000000 : ℝ)^4383 := by
    have hnat : (3634894931 : ℕ)^5407*12500000000000^4383 ≤ 3586902878521^4383*10000000000^5407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3634894931 10000000000 3586902878521 12500000000000 5407 4383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5407/1024 : ℝ)) 5407 4383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(408873541/1000000000 : ℝ), (2288297281/5000000000 : ℝ), (3634894931/10000000000 : ℝ)] ![(8294392476749/25000000000000 : ℝ), (38127207061169/100000000000000 : ℝ), (3586902878521/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(408873541/1000000000 : ℝ)|^5407 ≤ (8294392476749/25000000000000 : ℝ)^4383
        have hw : |(408873541/1000000000 : ℝ)|=(408873541/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2288297281/5000000000 : ℝ)|^5407 ≤ (38127207061169/100000000000000 : ℝ)^4383
        have hw : |(2288297281/5000000000 : ℝ)|=(2288297281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3634894931/10000000000 : ℝ)|^5407 ≤ (3586902878521/12500000000000 : ℝ)^4383
        have hw : |(3634894931/10000000000 : ℝ)|=(3634894931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1723_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5399/1024 : ℝ) ≤ p) (hpb : p ≤ (5407/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (199267911/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17237/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4951/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10101/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17007/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17237/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4951/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17237/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4951/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17237/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4951/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17237/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4951/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17237/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4951/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17237/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4951/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4951/50000 : ℝ) ^ (5399/1024 : ℝ) ≤ (20279083671577/4000000000000000000 : ℝ) := by
    have hpowers : (4951/50000 : ℝ)^5399 ≤ (20279083671577/4000000000000000000 : ℝ)^1024 := by
      have hnat : (4951 : ℕ)^5399*4000000000000000000^1024 ≤ 20279083671577^1024*50000^5399 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4951 50000 20279083671577 4000000000000000000 5399 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4951/50000 : ℝ)) (X := (20279083671577/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5399 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17237/100000 : ℝ) ^ (5399/1024 : ℝ) ≤ (9424841213463401/100000000000000000000 : ℝ) := by
    have hpowers : (17237/100000 : ℝ)^5399 ≤ (9424841213463401/100000000000000000000 : ℝ)^1024 := by
      have hnat : (17237 : ℕ)^5399*100000000000000000000^1024 ≤ 9424841213463401^1024*100000^5399 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17237 100000 9424841213463401 100000000000000000000 5399 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17237/100000 : ℝ)) (X := (9424841213463401/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5399 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000020279083671577/2000000000000000000 : ℝ) ≤ (5000009615528973/5000000000000000 : ℝ) ^ (5399/1024 : ℝ) := by
    have hpowers : (2000020279083671577/2000000000000000000 : ℝ)^1024 ≤ (5000009615528973/5000000000000000 : ℝ)^5399 := by
      have hnat : (2000020279083671577 : ℕ)^1024*5000000000000000^5399 ≤ 5000009615528973^5399*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000020279083671577 2000000000000000000 5000009615528973 5000000000000000 1024 5399 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000009615528973/5000000000000000 : ℝ)) (X := (2000020279083671577/2000000000000000000 : ℝ)) (by norm_num) 5399 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50004965909152626413/50000000000000000000 : ℝ) ≤ (1000018836400659/1000000000000000 : ℝ) ^ (5399/1024 : ℝ) := by
    have hpowers : (50004965909152626413/50000000000000000000 : ℝ)^1024 ≤ (1000018836400659/1000000000000000 : ℝ)^5399 := by
      have hnat : (50004965909152626413 : ℕ)^1024*1000000000000000^5399 ≤ 1000018836400659^5399*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004965909152626413 50000000000000000000 1000018836400659 1000000000000000 1024 5399 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000018836400659/1000000000000000 : ℝ)) (X := (50004965909152626413/50000000000000000000 : ℝ)) (by norm_num) 5399 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50009424841213463401/50000000000000000000 : ℝ) ≤ (5000178748477617/5000000000000000 : ℝ) ^ (5399/1024 : ℝ) := by
    have hpowers : (50009424841213463401/50000000000000000000 : ℝ)^1024 ≤ (5000178748477617/5000000000000000 : ℝ)^5399 := by
      have hnat : (50009424841213463401 : ℕ)^1024*5000000000000000^5399 ≤ 5000178748477617^5399*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009424841213463401 50000000000000000000 5000178748477617 5000000000000000 1024 5399 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000178748477617/5000000000000000 : ℝ)) (X := (50009424841213463401/50000000000000000000 : ℝ)) (by norm_num) 5399 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(20279083671577/4000000000000000000 : ℝ) ≤ ((12224465258482514689/12225000000000000000 : ℝ)+2*(14094412387/61125000000000 : ℝ)*(4951/50000 : ℝ))^(5399/1024 : ℝ) := by
    rw [show (12224465258482514689/12225000000000000000 : ℝ)+2*(14094412387/61125000000000 : ℝ)*(4951/50000 : ℝ)=(5000009615528973/5000000000000000 : ℝ) by norm_num, show 1+2*(20279083671577/4000000000000000000 : ℝ)=(2000020279083671577/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9424841213463401/100000000000000000000 : ℝ)+(20279083671577/4000000000000000000 : ℝ) ≤ ((12224465258482514689/12225000000000000000 : ℝ)+(14094412387/61125000000000 : ℝ)*((17237/100000 : ℝ)+(4951/50000 : ℝ)))^(5399/1024 : ℝ) := by
    rw [show (12224465258482514689/12225000000000000000 : ℝ)+(14094412387/61125000000000 : ℝ)*((17237/100000 : ℝ)+(4951/50000 : ℝ))=(1000018836400659/1000000000000000 : ℝ) by norm_num, show 1+(9424841213463401/100000000000000000000 : ℝ)+(20279083671577/4000000000000000000 : ℝ)=(50004965909152626413/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9424841213463401/100000000000000000000 : ℝ) ≤ ((12224465258482514689/12225000000000000000 : ℝ)+2*(14094412387/61125000000000 : ℝ)*(17237/100000 : ℝ))^(5399/1024 : ℝ) := by
    rw [show (12224465258482514689/12225000000000000000 : ℝ)+2*(14094412387/61125000000000 : ℝ)*(17237/100000 : ℝ)=(5000178748477617/5000000000000000 : ℝ) by norm_num, show 1+2*(9424841213463401/100000000000000000000 : ℝ)=(50009424841213463401/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (12224465258482514689/12225000000000000000 : ℝ)*(X 1 0+X 2 0)+(14094412387/61125000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5399/1024 : ℝ)) (lo := (4951/50000 : ℝ)) (hi := (17237/100000 : ℝ)) (c := (12224465258482514689/12225000000000000000 : ℝ)) (alpha := (14094412387/61125000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (12224465258482514689/12225000000000000000 : ℝ)*(X 0 1+X 2 1)+(14094412387/61125000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5399/1024 : ℝ)) (lo := (4951/50000 : ℝ)) (hi := (17237/100000 : ℝ)) (c := (12224465258482514689/12225000000000000000 : ℝ)) (alpha := (14094412387/61125000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (12224465258482514689/12225000000000000000 : ℝ)*(X 0 2+X 1 2)+(14094412387/61125000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5399/1024 : ℝ)) (lo := (4951/50000 : ℝ)) (hi := (17237/100000 : ℝ)) (c := (12224465258482514689/12225000000000000000 : ℝ)) (alpha := (14094412387/61125000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-683186663/5000000000 : ℝ)*X 0 0+(2731094699/5000000000 : ℝ)*X 0 1+(5139453033/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1723_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5339239779/10000000000 : ℝ)*X 1 0+(-61342281/400000000 : ℝ)*X 1 1+(5139452821/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1723_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5339239519/10000000000 : ℝ)*X 2 0+(5139453097/10000000000 : ℝ)*X 2 1+(-766778503/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1723_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2044151809/5000000000 : ℝ)*X 0 0+(3623921839/10000000000 : ℝ)*X 0 1+(2293703289/5000000000 : ℝ)*X 0 2+(2044151809/5000000000 : ℝ)*X 1 0+(3623921839/10000000000 : ℝ)*X 1 1+(2293703289/5000000000 : ℝ)*X 1 2+(2044151809/5000000000 : ℝ)*X 2 0+(3623921839/10000000000 : ℝ)*X 2 1+(2293703289/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1723_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1366518027/10000000000 : ℝ)*X 0 0+(5143074467/10000000000 : ℝ)*X 0 1+(272925693/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1723_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5252848653/10000000000 : ℝ)*X 1 0+(-607247957/5000000000 : ℝ)*X 1 1+(682314229/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1723_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5252848643/10000000000 : ℝ)*X 2 0+(2729256923/5000000000 : ℝ)*X 2 1+(-1214495907/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1723_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((408873541/1000000000 : ℝ)*X 0 0+(2288297281/5000000000 : ℝ)*X 0 1+(3634894931/10000000000 : ℝ)*X 0 2+(408873541/1000000000 : ℝ)*X 1 0+(2288297281/5000000000 : ℝ)*X 1 1+(3634894931/10000000000 : ℝ)*X 1 2+(408873541/1000000000 : ℝ)*X 2 0+(2288297281/5000000000 : ℝ)*X 2 1+(3634894931/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1723_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (289331069628795156636182157/20375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (77021917/4000000000000 : ℝ)*(base19) + (1614187561/100000000000000 : ℝ)*(base23) + (42840399/50000000000000 : ℝ)*(lower2) + (170231353/50000000000000 : ℝ)*(upper3) + (22060709/10000000000000 : ℝ)*(upper5) + (206822563645271/10000000000000 : ℝ)*(major0) + (206822563645271/10000000000000 : ℝ)*(major1) + (206822563645271/10000000000000 : ℝ)*(major2) + (309852215736361/10000000000000 : ℝ)*(sp0) + (1549268417928677/50000000000000 : ℝ)*(sp1) + (1549268573608859/50000000000000 : ℝ)*(sp2) + (129738139425011/12500000000000 : ℝ)*(sp3) + (16604041669/100000000000000 : ℝ)*(sp4) + (6922756779/100000000000000 : ℝ)*(sp7) + (518956019078433/50000000000000 : ℝ)*(f.failure) + (19365867258783/625000000000 : ℝ)*(f.sum) + (15011679565679/2445000000000000000000000000 : ℝ)*base66 + (859699793590929/250000000000000000000000000000 : ℝ)*base68 + (3219999231090929/250000000000000000000000000000 : ℝ)*base70 + (2020979220340929/250000000000000000000000000000 : ℝ)*base72 + (301262614271/611250000000000000000000000 : ℝ)*base74 + (974132772090929/250000000000000000000000000000 : ℝ)*base76 + (2720007439340929/250000000000000000000000000000 : ℝ)*base78 + (1034049904340929/250000000000000000000000000000 : ℝ)*base80 + (17485298178209/2445000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (10936537/5000000000000000000000 : ℝ)*base90 + (10936537/5000000000000000000000 : ℝ)*base92 + (10936537/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (691329482358296682999213171/50937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (965224749/50000000000000 : ℝ)*(base19) + (2066706707/100000000000000 : ℝ)*(base23) + (302095451/100000000000000 : ℝ)*(upper3) + (3926827/6250000000000 : ℝ)*(lower4) + (291045351/100000000000000 : ℝ)*(upper5) + (1058022516777261/50000000000000 : ℝ)*(major0) + (1058022516777261/50000000000000 : ℝ)*(major1) + (1058022516777261/50000000000000 : ℝ)*(major2) + (2216421757/12500000000000 : ℝ)*(sp1) + (1194412391/6250000000000 : ℝ)*(sp2) + (1585090018160687/50000000000000 : ℝ)*(sp4) + (158508018724891/5000000000000 : ℝ)*(sp5) + (317015885901641/10000000000000 : ℝ)*(sp6) + (265477394595977/25000000000000 : ℝ)*(sp7) + (265477394595977/25000000000000 : ℝ)*(f.failure) + (1585090018160687/50000000000000 : ℝ)*(f.sum) + (1822303415649/2037500000000000000000000000 : ℝ)*base66 + (8175375955813061/1250000000000000000000000000000 : ℝ)*base67 + (4020440913313061/1250000000000000000000000000000 : ℝ)*base69 + (5378092943313061/1250000000000000000000000000000 : ℝ)*base71 + (1160186557197/254687500000000000000000000 : ℝ)*base73 + (7787077306686939/1250000000000000000000000000000 : ℝ)*base76 + (15017217430813061/1250000000000000000000000000000 : ℝ)*base77 + (11897308413313061/1250000000000000000000000000000 : ℝ)*base79 + (3978903748351/2037500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (24205953/2500000000000000000000 : ℝ)*base90 + (24205953/2500000000000000000000 : ℝ)*base92 + (24205953/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1723_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5399/1024 : ℝ) ≤ p) (hpb : p ≤ (5407/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (199267911/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17237/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4951/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10101/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17007/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1723_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1723_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5399/1024 : ℝ) ≤ p) (hpb : p ≤ (5407/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (199267911/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10101/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17007/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1723_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1723_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1723_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5399/1024 : ℝ) ≤ p) (hpb : p ≤ (5407/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (199267911/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10101/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17007/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1723_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
