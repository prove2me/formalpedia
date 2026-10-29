-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1367_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:19:35.607843+00:00
-- url     : https://prove2.me/submissions/62d3863d-1fd2-4f76-b994-09cad813e6f5

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
theorem support_rectangle_w1367_s3_0 (p : ℝ) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-40420981/200000000 : ℝ)*x 0 + (5424076987/10000000000 : ℝ)*x 1 + (2616841703/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (40420981/200000000 : ℝ)^4327 ≤ (12310932827127/100000000000000 : ℝ)^3303 := by
    have hnat : (40420981 : ℕ)^4327*100000000000000^3303 ≤ 12310932827127^3303*200000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40420981 200000000 12310932827127 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5424076987/10000000000 : ℝ)^4327 ≤ (44870532823541/100000000000000 : ℝ)^3303 := by
    have hnat : (5424076987 : ℕ)^4327*100000000000000^3303 ≤ 44870532823541^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424076987 10000000000 44870532823541 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2616841703/5000000000 : ℝ)^4327 ≤ (42818534340337/100000000000000 : ℝ)^3303 := by
    have hnat : (2616841703 : ℕ)^4327*100000000000000^3303 ≤ 42818534340337^3303*5000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2616841703 5000000000 42818534340337 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4327/1024 : ℝ)) 4327 3303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-40420981/200000000 : ℝ), (5424076987/10000000000 : ℝ), (2616841703/5000000000 : ℝ)] ![(12310932827127/100000000000000 : ℝ), (44870532823541/100000000000000 : ℝ), (42818534340337/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-40420981/200000000 : ℝ)|^4327 ≤ (12310932827127/100000000000000 : ℝ)^3303
        have hw : |(-40420981/200000000 : ℝ)|=(40420981/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5424076987/10000000000 : ℝ)|^4327 ≤ (44870532823541/100000000000000 : ℝ)^3303
        have hw : |(5424076987/10000000000 : ℝ)|=(5424076987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2616841703/5000000000 : ℝ)|^4327 ≤ (42818534340337/100000000000000 : ℝ)^3303
        have hw : |(2616841703/5000000000 : ℝ)|=(2616841703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1367_s3_1 (p : ℝ) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337948163/2500000000 : ℝ)*x 0 + (-529573727/2500000000 : ℝ)*x 1 + (1308420901/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337948163/2500000000 : ℝ)^4327 ≤ (22044401171303/50000000000000 : ℝ)^3303 := by
    have hnat : (1337948163 : ℕ)^4327*50000000000000^3303 ≤ 22044401171303^3303*2500000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337948163 2500000000 22044401171303 50000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (529573727/2500000000 : ℝ)^4327 ≤ (13092661173789/100000000000000 : ℝ)^3303 := by
    have hnat : (529573727 : ℕ)^4327*100000000000000^3303 ≤ 13092661173789^3303*2500000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529573727 2500000000 13092661173789 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1308420901/2500000000 : ℝ)^4327 ≤ (21409268231223/50000000000000 : ℝ)^3303 := by
    have hnat : (1308420901 : ℕ)^4327*50000000000000^3303 ≤ 21409268231223^3303*2500000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1308420901 2500000000 21409268231223 50000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4327/1024 : ℝ)) 4327 3303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337948163/2500000000 : ℝ), (-529573727/2500000000 : ℝ), (1308420901/2500000000 : ℝ)] ![(22044401171303/50000000000000 : ℝ), (13092661173789/100000000000000 : ℝ), (21409268231223/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337948163/2500000000 : ℝ)|^4327 ≤ (22044401171303/50000000000000 : ℝ)^3303
        have hw : |(1337948163/2500000000 : ℝ)|=(1337948163/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-529573727/2500000000 : ℝ)|^4327 ≤ (13092661173789/100000000000000 : ℝ)^3303
        have hw : |(-529573727/2500000000 : ℝ)|=(529573727/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1308420901/2500000000 : ℝ)|^4327 ≤ (21409268231223/50000000000000 : ℝ)^3303
        have hw : |(1308420901/2500000000 : ℝ)|=(1308420901/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1367_s3_2 (p : ℝ) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1045272/1953125 : ℝ)*x 0 + (1308420851/2500000000 : ℝ)*x 1 + (-211829519/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1045272/1953125 : ℝ)^4327 ≤ (440888022131/1000000000000 : ℝ)^3303 := by
    have hnat : (1045272 : ℕ)^4327*1000000000000^3303 ≤ 440888022131^3303*1953125^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045272 1953125 440888022131 1000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1308420851/2500000000 : ℝ)^4327 ≤ (42818534318901/100000000000000 : ℝ)^3303 := by
    have hnat : (1308420851 : ℕ)^4327*100000000000000^3303 ≤ 42818534318901^3303*2500000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1308420851 2500000000 42818534318901 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (211829519/1000000000 : ℝ)^4327 ≤ (13092663457121/100000000000000 : ℝ)^3303 := by
    have hnat : (211829519 : ℕ)^4327*100000000000000^3303 ≤ 13092663457121^3303*1000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211829519 1000000000 13092663457121 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4327/1024 : ℝ)) 4327 3303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1045272/1953125 : ℝ), (1308420851/2500000000 : ℝ), (-211829519/1000000000 : ℝ)] ![(440888022131/1000000000000 : ℝ), (42818534318901/100000000000000 : ℝ), (13092663457121/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1045272/1953125 : ℝ)|^4327 ≤ (440888022131/1000000000000 : ℝ)^3303
        have hw : |(1045272/1953125 : ℝ)|=(1045272/1953125 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1308420851/2500000000 : ℝ)|^4327 ≤ (42818534318901/100000000000000 : ℝ)^3303
        have hw : |(1308420851/2500000000 : ℝ)|=(1308420851/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-211829519/1000000000 : ℝ)|^4327 ≤ (13092663457121/100000000000000 : ℝ)^3303
        have hw : |(-211829519/1000000000 : ℝ)|=(211829519/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1367_s3_3 (p : ℝ) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (539900323/1250000000 : ℝ)*x 0 + (2061130547/5000000000 : ℝ)*x 1 + (7239693/16000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (539900323/1250000000 : ℝ)^4327 ≤ (33294381801337/100000000000000 : ℝ)^3303 := by
    have hnat : (539900323 : ℕ)^4327*100000000000000^3303 ≤ 33294381801337^3303*1250000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539900323 1250000000 33294381801337 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2061130547/5000000000 : ℝ)^4327 ≤ (31319826148407/100000000000000 : ℝ)^3303 := by
    have hnat : (2061130547 : ℕ)^4327*100000000000000^3303 ≤ 31319826148407^3303*5000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2061130547 5000000000 31319826148407 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7239693/16000000 : ℝ)^4327 ≤ (35385792032827/100000000000000 : ℝ)^3303 := by
    have hnat : (7239693 : ℕ)^4327*100000000000000^3303 ≤ 35385792032827^3303*16000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7239693 16000000 35385792032827 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4327/1024 : ℝ)) 4327 3303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(539900323/1250000000 : ℝ), (2061130547/5000000000 : ℝ), (7239693/16000000 : ℝ)] ![(33294381801337/100000000000000 : ℝ), (31319826148407/100000000000000 : ℝ), (35385792032827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(539900323/1250000000 : ℝ)|^4327 ≤ (33294381801337/100000000000000 : ℝ)^3303
        have hw : |(539900323/1250000000 : ℝ)|=(539900323/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2061130547/5000000000 : ℝ)|^4327 ≤ (31319826148407/100000000000000 : ℝ)^3303
        have hw : |(2061130547/5000000000 : ℝ)|=(2061130547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7239693/16000000 : ℝ)|^4327 ≤ (35385792032827/100000000000000 : ℝ)^3303
        have hw : |(7239693/16000000 : ℝ)|=(7239693/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1367_s3_4 (p : ℝ) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1010533549/5000000000 : ℝ)*x 0 + (5234465757/10000000000 : ℝ)*x 1 + (5423289929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1010533549/5000000000 : ℝ)^4327 ≤ (12311076846897/100000000000000 : ℝ)^3303 := by
    have hnat : (1010533549 : ℕ)^4327*100000000000000^3303 ≤ 12311076846897^3303*5000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1010533549 5000000000 12311076846897 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5234465757/10000000000 : ℝ)^4327 ≤ (10706729889671/25000000000000 : ℝ)^3303 := by
    have hnat : (5234465757 : ℕ)^4327*25000000000000^3303 ≤ 10706729889671^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5234465757 10000000000 10706729889671 25000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5423289929/10000000000 : ℝ)^4327 ≤ (22431001788463/50000000000000 : ℝ)^3303 := by
    have hnat : (5423289929 : ℕ)^4327*50000000000000^3303 ≤ 22431001788463^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423289929 10000000000 22431001788463 50000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4327/1024 : ℝ)) 4327 3303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1010533549/5000000000 : ℝ), (5234465757/10000000000 : ℝ), (5423289929/10000000000 : ℝ)] ![(12311076846897/100000000000000 : ℝ), (10706729889671/25000000000000 : ℝ), (22431001788463/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1010533549/5000000000 : ℝ)|^4327 ≤ (12311076846897/100000000000000 : ℝ)^3303
        have hw : |(-1010533549/5000000000 : ℝ)|=(1010533549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5234465757/10000000000 : ℝ)|^4327 ≤ (10706729889671/25000000000000 : ℝ)^3303
        have hw : |(5234465757/10000000000 : ℝ)|=(5234465757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5423289929/10000000000 : ℝ)|^4327 ≤ (22431001788463/50000000000000 : ℝ)^3303
        have hw : |(5423289929/10000000000 : ℝ)|=(5423289929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1367_s3_5 (p : ℝ) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (662826631/1250000000 : ℝ)*x 0 + (-96434419/500000000 : ℝ)*x 1 + (216931597/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (662826631/1250000000 : ℝ)^4327 ≤ (21779403541381/50000000000000 : ℝ)^3303 := by
    have hnat : (662826631 : ℕ)^4327*50000000000000^3303 ≤ 21779403541381^3303*1250000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      662826631 1250000000 21779403541381 50000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (96434419/500000000 : ℝ)^4327 ≤ (5789594682861/50000000000000 : ℝ)^3303 := by
    have hnat : (96434419 : ℕ)^4327*50000000000000^3303 ≤ 5789594682861^3303*500000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      96434419 500000000 5789594682861 50000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216931597/400000000 : ℝ)^4327 ≤ (44862003533579/100000000000000 : ℝ)^3303 := by
    have hnat : (216931597 : ℕ)^4327*100000000000000^3303 ≤ 44862003533579^3303*400000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216931597 400000000 44862003533579 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4327/1024 : ℝ)) 4327 3303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(662826631/1250000000 : ℝ), (-96434419/500000000 : ℝ), (216931597/400000000 : ℝ)] ![(21779403541381/50000000000000 : ℝ), (5789594682861/50000000000000 : ℝ), (44862003533579/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(662826631/1250000000 : ℝ)|^4327 ≤ (21779403541381/50000000000000 : ℝ)^3303
        have hw : |(662826631/1250000000 : ℝ)|=(662826631/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-96434419/500000000 : ℝ)|^4327 ≤ (5789594682861/50000000000000 : ℝ)^3303
        have hw : |(-96434419/500000000 : ℝ)|=(96434419/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216931597/400000000 : ℝ)|^4327 ≤ (44862003533579/100000000000000 : ℝ)^3303
        have hw : |(216931597/400000000 : ℝ)|=(216931597/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1367_s3_6 (p : ℝ) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (662826619/1250000000 : ℝ)*x 0 + (5423289997/10000000000 : ℝ)*x 1 + (-1928688413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (662826619/1250000000 : ℝ)^4327 ≤ (21779403024839/50000000000000 : ℝ)^3303 := by
    have hnat : (662826619 : ℕ)^4327*50000000000000^3303 ≤ 21779403024839^3303*1250000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      662826619 1250000000 21779403024839 50000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5423289997/10000000000 : ℝ)^4327 ≤ (44862004313817/100000000000000 : ℝ)^3303 := by
    have hnat : (5423289997 : ℕ)^4327*100000000000000^3303 ≤ 44862004313817^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423289997 10000000000 44862004313817 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1928688413/10000000000 : ℝ)^4327 ≤ (723699351579/6250000000000 : ℝ)^3303 := by
    have hnat : (1928688413 : ℕ)^4327*6250000000000^3303 ≤ 723699351579^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1928688413 10000000000 723699351579 6250000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4327/1024 : ℝ)) 4327 3303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(662826619/1250000000 : ℝ), (5423289997/10000000000 : ℝ), (-1928688413/10000000000 : ℝ)] ![(21779403024839/50000000000000 : ℝ), (44862004313817/100000000000000 : ℝ), (723699351579/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(662826619/1250000000 : ℝ)|^4327 ≤ (21779403024839/50000000000000 : ℝ)^3303
        have hw : |(662826619/1250000000 : ℝ)|=(662826619/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5423289997/10000000000 : ℝ)|^4327 ≤ (44862004313817/100000000000000 : ℝ)^3303
        have hw : |(5423289997/10000000000 : ℝ)|=(5423289997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1928688413/10000000000 : ℝ)|^4327 ≤ (723699351579/6250000000000 : ℝ)^3303
        have hw : |(-1928688413/10000000000 : ℝ)|=(1928688413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1367_s3_7 (p : ℝ) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4319240359/10000000000 : ℝ)*x 0 + (4523154161/10000000000 : ℝ)*x 1 + (824785001/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4319240359/10000000000 : ℝ)^4327 ≤ (33294763262883/100000000000000 : ℝ)^3303 := by
    have hnat : (4319240359 : ℕ)^4327*100000000000000^3303 ≤ 33294763262883^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4319240359 10000000000 33294763262883 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4523154161/10000000000 : ℝ)^4327 ≤ (35368848322553/100000000000000 : ℝ)^3303 := by
    have hnat : (4523154161 : ℕ)^4327*100000000000000^3303 ≤ 35368848322553^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4523154161 10000000000 35368848322553 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (824785001/2000000000 : ℝ)^4327 ≤ (626727768041/2000000000000 : ℝ)^3303 := by
    have hnat : (824785001 : ℕ)^4327*2000000000000^3303 ≤ 626727768041^3303*2000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      824785001 2000000000 626727768041 2000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4327/1024 : ℝ)) 4327 3303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4319240359/10000000000 : ℝ), (4523154161/10000000000 : ℝ), (824785001/2000000000 : ℝ)] ![(33294763262883/100000000000000 : ℝ), (35368848322553/100000000000000 : ℝ), (626727768041/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4319240359/10000000000 : ℝ)|^4327 ≤ (33294763262883/100000000000000 : ℝ)^3303
        have hw : |(4319240359/10000000000 : ℝ)|=(4319240359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4523154161/10000000000 : ℝ)|^4327 ≤ (35368848322553/100000000000000 : ℝ)^3303
        have hw : |(4523154161/10000000000 : ℝ)|=(4523154161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(824785001/2000000000 : ℝ)|^4327 ≤ (626727768041/2000000000000 : ℝ)^3303
        have hw : |(824785001/2000000000 : ℝ)|=(824785001/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1367_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38928637/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2001/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10011/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10957/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14987/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2001/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10011/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2001/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10011/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2001/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10011/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2001/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10011/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2001/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10011/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2001/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10011/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10011/100000 : ℝ) ^ (2163/512 : ℝ) ≤ (5989736437062683/100000000000000000000 : ℝ) := by
    have hpowers : (10011/100000 : ℝ)^2163 ≤ (5989736437062683/100000000000000000000 : ℝ)^512 := by
      have hnat : (10011 : ℕ)^2163*100000000000000000000^512 ≤ 5989736437062683^512*100000^2163 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10011 100000 5989736437062683 100000000000000000000 2163 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10011/100000 : ℝ)) (X := (5989736437062683/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2163 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2001/12500 : ℝ) ^ (2163/512 : ℝ) ≤ (21757297728288173/50000000000000000000 : ℝ) := by
    have hpowers : (2001/12500 : ℝ)^2163 ≤ (21757297728288173/50000000000000000000 : ℝ)^512 := by
      have hnat : (2001 : ℕ)^2163*50000000000000000000^512 ≤ 21757297728288173^512*12500^2163 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2001 12500 21757297728288173 50000000000000000000 2163 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2001/12500 : ℝ)) (X := (21757297728288173/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2163 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005989736437062683/50000000000000000000 : ℝ) ≤ (5000141775536599/5000000000000000 : ℝ) ^ (2163/512 : ℝ) := by
    have hpowers : (50005989736437062683/50000000000000000000 : ℝ)^512 ≤ (5000141775536599/5000000000000000 : ℝ)^2163 := by
      have hnat : (50005989736437062683 : ℕ)^512*5000000000000000^2163 ≤ 5000141775536599^2163*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005989736437062683 50000000000000000000 5000141775536599 5000000000000000 512 2163 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000141775536599/5000000000000000 : ℝ)) (X := (50005989736437062683/50000000000000000000 : ℝ)) (by norm_num) 2163 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100049504331893639029/100000000000000000000 : ℝ) ≤ (1250146448397077/1250000000000000 : ℝ) ^ (2163/512 : ℝ) := by
    have hpowers : (100049504331893639029/100000000000000000000 : ℝ)^512 ≤ (1250146448397077/1250000000000000 : ℝ)^2163 := by
      have hnat : (100049504331893639029 : ℕ)^512*1250000000000000^2163 ≤ 1250146448397077^2163*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100049504331893639029 100000000000000000000 1250146448397077 1250000000000000 512 2163 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250146448397077/1250000000000000 : ℝ)) (X := (100049504331893639029/100000000000000000000 : ℝ)) (by norm_num) 2163 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25021757297728288173/25000000000000000000 : ℝ) ≤ (5001029811640017/5000000000000000 : ℝ) ^ (2163/512 : ℝ) := by
    have hpowers : (25021757297728288173/25000000000000000000 : ℝ)^512 ≤ (5001029811640017/5000000000000000 : ℝ)^2163 := by
      have hnat : (25021757297728288173 : ℕ)^512*5000000000000000^2163 ≤ 5001029811640017^2163*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25021757297728288173 25000000000000000000 5001029811640017 5000000000000000 512 2163 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001029811640017/5000000000000000 : ℝ)) (X := (25021757297728288173/25000000000000000000 : ℝ)) (by norm_num) 2163 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5989736437062683/100000000000000000000 : ℝ) ≤ ((1998464006564111107/1999000000000000000 : ℝ)+2*(444018051709/299850000000000 : ℝ)*(10011/100000 : ℝ))^(2163/512 : ℝ) := by
    rw [show (1998464006564111107/1999000000000000000 : ℝ)+2*(444018051709/299850000000000 : ℝ)*(10011/100000 : ℝ)=(5000141775536599/5000000000000000 : ℝ) by norm_num, show 1+2*(5989736437062683/100000000000000000000 : ℝ)=(50005989736437062683/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(21757297728288173/50000000000000000000 : ℝ)+(5989736437062683/100000000000000000000 : ℝ) ≤ ((1998464006564111107/1999000000000000000 : ℝ)+(444018051709/299850000000000 : ℝ)*((2001/12500 : ℝ)+(10011/100000 : ℝ)))^(2163/512 : ℝ) := by
    rw [show (1998464006564111107/1999000000000000000 : ℝ)+(444018051709/299850000000000 : ℝ)*((2001/12500 : ℝ)+(10011/100000 : ℝ))=(1250146448397077/1250000000000000 : ℝ) by norm_num, show 1+(21757297728288173/50000000000000000000 : ℝ)+(5989736437062683/100000000000000000000 : ℝ)=(100049504331893639029/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(21757297728288173/50000000000000000000 : ℝ) ≤ ((1998464006564111107/1999000000000000000 : ℝ)+2*(444018051709/299850000000000 : ℝ)*(2001/12500 : ℝ))^(2163/512 : ℝ) := by
    rw [show (1998464006564111107/1999000000000000000 : ℝ)+2*(444018051709/299850000000000 : ℝ)*(2001/12500 : ℝ)=(5001029811640017/5000000000000000 : ℝ) by norm_num, show 1+2*(21757297728288173/50000000000000000000 : ℝ)=(25021757297728288173/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1998464006564111107/1999000000000000000 : ℝ)*(X 1 0+X 2 0)+(444018051709/299850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2163/512 : ℝ)) (lo := (10011/100000 : ℝ)) (hi := (2001/12500 : ℝ)) (c := (1998464006564111107/1999000000000000000 : ℝ)) (alpha := (444018051709/299850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1998464006564111107/1999000000000000000 : ℝ)*(X 0 1+X 2 1)+(444018051709/299850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2163/512 : ℝ)) (lo := (10011/100000 : ℝ)) (hi := (2001/12500 : ℝ)) (c := (1998464006564111107/1999000000000000000 : ℝ)) (alpha := (444018051709/299850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1998464006564111107/1999000000000000000 : ℝ)*(X 0 2+X 1 2)+(444018051709/299850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2163/512 : ℝ)) (lo := (10011/100000 : ℝ)) (hi := (2001/12500 : ℝ)) (c := (1998464006564111107/1999000000000000000 : ℝ)) (alpha := (444018051709/299850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-40420981/200000000 : ℝ)*X 0 0+(5424076987/10000000000 : ℝ)*X 0 1+(2616841703/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1367_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337948163/2500000000 : ℝ)*X 1 0+(-529573727/2500000000 : ℝ)*X 1 1+(1308420901/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1367_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1045272/1953125 : ℝ)*X 2 0+(1308420851/2500000000 : ℝ)*X 2 1+(-211829519/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1367_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((539900323/1250000000 : ℝ)*X 0 0+(2061130547/5000000000 : ℝ)*X 0 1+(7239693/16000000 : ℝ)*X 0 2+(539900323/1250000000 : ℝ)*X 1 0+(2061130547/5000000000 : ℝ)*X 1 1+(7239693/16000000 : ℝ)*X 1 2+(539900323/1250000000 : ℝ)*X 2 0+(2061130547/5000000000 : ℝ)*X 2 1+(7239693/16000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1367_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1010533549/5000000000 : ℝ)*X 0 0+(5234465757/10000000000 : ℝ)*X 0 1+(5423289929/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1367_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((662826631/1250000000 : ℝ)*X 1 0+(-96434419/500000000 : ℝ)*X 1 1+(216931597/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1367_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((662826619/1250000000 : ℝ)*X 2 0+(5423289997/10000000000 : ℝ)*X 2 1+(-1928688413/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1367_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4319240359/10000000000 : ℝ)*X 0 0+(4523154161/10000000000 : ℝ)*X 0 1+(824785001/2000000000 : ℝ)*X 0 2+(4319240359/10000000000 : ℝ)*X 1 0+(4523154161/10000000000 : ℝ)*X 1 1+(824785001/2000000000 : ℝ)*X 1 2+(4319240359/10000000000 : ℝ)*X 2 0+(4523154161/10000000000 : ℝ)*X 2 1+(824785001/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1367_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (37415526943466543842062211/3123437500000000000000000000000 : ℝ) := by norm_num
    linear_combination (234798237/12500000000000 : ℝ)*(base19) + (1639015901/100000000000000 : ℝ)*(base23) + (30425247/20000000000000 : ℝ)*(lower2) + (483101049/100000000000000 : ℝ)*(upper3) + (30323191/100000000000000 : ℝ)*(lower4) + (15110465092991/390625000000 : ℝ)*(major0) + (15110465092991/390625000000 : ℝ)*(major1) + (15110465092991/390625000000 : ℝ)*(major2) + (2626159387865377/50000000000000 : ℝ)*(sp0) + (5252344121806467/100000000000000 : ℝ)*(sp1) + (2626172180588231/50000000000000 : ℝ)*(sp2) + (77631035827243/3125000000000 : ℝ)*(sp3) + (27224461609/100000000000000 : ℝ)*(sp4) + (14516913/78125000000 : ℝ)*(sp7) + (2484211728120417/100000000000000 : ℝ)*(f.failure) + (5252346000192363/100000000000000 : ℝ)*(f.sum) + (40812095146321/14992500000000000000000000000 : ℝ)*base66 + (113386991145568013/18740625000000000000000000000000 : ℝ)*base67 + (354607472632036763/18740625000000000000000000000000 : ℝ)*base69 + (53252774951000597/4685156250000000000000000000000 : ℝ)*base71 + (31047482397037/7496250000000000000000000000 : ℝ)*base73 + (60875623307656847/4685156250000000000000000000000 : ℝ)*base75 + (7847908296433111/2342578125000000000000000000000 : ℝ)*base77 + (8101426857596243/1171289062500000000000000000000 : ℝ)*base79 + (57058709237557/7496250000000000000000000000 : ℝ)*base81 + (5681629/2500000000000000000000 : ℝ)*base89 + (5681629/2500000000000000000000 : ℝ)*base91 + (5681629/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (213584533837068207701983953/49975000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12600103/1562500000000 : ℝ)*(base19) + (77181739/10000000000000 : ℝ)*(base23) + (78690459/100000000000000 : ℝ)*(upper3) + (17624313/50000000000000 : ℝ)*(lower4) + (48763327/50000000000000 : ℝ)*(upper5) + (3900378898461807/100000000000000 : ℝ)*(major0) + (3900378898461807/100000000000000 : ℝ)*(major1) + (3900378898461807/100000000000000 : ℝ)*(major2) + (15203084139/100000000000000 : ℝ)*(sp1) + (585763443/4000000000000 : ℝ)*(sp2) + (2647965694175271/50000000000000 : ℝ)*(sp4) + (529591537885981/10000000000000 : ℝ)*(sp5) + (1323978993111769/25000000000000 : ℝ)*(sp6) + (2504826266112147/100000000000000 : ℝ)*(sp7) + (2504826266112147/100000000000000 : ℝ)*(f.failure) + (2647965694175271/50000000000000 : ℝ)*(f.sum) + (6812598816273/9995000000000000000000000000 : ℝ)*base66 + (1665582647405489651/199900000000000000000000000000000 : ℝ)*base68 + (1088371028523710349/199900000000000000000000000000000 : ℝ)*base69 + (531437429026510349/199900000000000000000000000000000 : ℝ)*base71 + (25248856056283/9995000000000000000000000000 : ℝ)*base74 + (743167778892510349/199900000000000000000000000000000 : ℝ)*base75 + (264197347110910349/199900000000000000000000000000000 : ℝ)*base77 + (24310427772310349/199900000000000000000000000000000 : ℝ)*base79 + (20568241954073/9995000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (3146361/2500000000000000000000 : ℝ)*base90 + (3146361/2500000000000000000000 : ℝ)*base92 + (3146361/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1367_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38928637/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2001/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10011/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10957/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14987/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1367_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1367_s4_0 (p : ℝ) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-126395153/625000000 : ℝ)*x 0 + (2706779709/5000000000 : ℝ)*x 1 + (5243363969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (126395153/625000000 : ℝ)^4327 ≤ (12321095290677/100000000000000 : ℝ)^3303 := by
    have hnat : (126395153 : ℕ)^4327*100000000000000^3303 ≤ 12321095290677^3303*625000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126395153 625000000 12321095290677 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2706779709/5000000000 : ℝ)^4327 ≤ (22378293493969/50000000000000 : ℝ)^3303 := by
    have hnat : (2706779709 : ℕ)^4327*50000000000000^3303 ≤ 22378293493969^3303*5000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706779709 5000000000 22378293493969 50000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243363969/10000000000 : ℝ)^4327 ≤ (42922317702481/100000000000000 : ℝ)^3303 := by
    have hnat : (5243363969 : ℕ)^4327*100000000000000^3303 ≤ 42922317702481^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243363969 10000000000 42922317702481 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4327/1024 : ℝ)) 4327 3303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-126395153/625000000 : ℝ), (2706779709/5000000000 : ℝ), (5243363969/10000000000 : ℝ)] ![(12321095290677/100000000000000 : ℝ), (22378293493969/50000000000000 : ℝ), (42922317702481/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-126395153/625000000 : ℝ)|^4327 ≤ (12321095290677/100000000000000 : ℝ)^3303
        have hw : |(-126395153/625000000 : ℝ)|=(126395153/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2706779709/5000000000 : ℝ)|^4327 ≤ (22378293493969/50000000000000 : ℝ)^3303
        have hw : |(2706779709/5000000000 : ℝ)|=(2706779709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243363969/10000000000 : ℝ)|^4327 ≤ (42922317702481/100000000000000 : ℝ)^3303
        have hw : |(5243363969/10000000000 : ℝ)|=(5243363969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1367_s4_1 (p : ℝ) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349101533/10000000000 : ℝ)*x 0 + (-1054528959/5000000000 : ℝ)*x 1 + (40963781/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349101533/10000000000 : ℝ)^4327 ≤ (5507470211099/12500000000000 : ℝ)^3303 := by
    have hnat : (5349101533 : ℕ)^4327*12500000000000^3303 ≤ 5507470211099^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349101533 10000000000 5507470211099 12500000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1054528959/5000000000 : ℝ)^4327 ≤ (13017920613017/100000000000000 : ℝ)^3303 := by
    have hnat : (1054528959 : ℕ)^4327*100000000000000^3303 ≤ 13017920613017^3303*5000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054528959 5000000000 13017920613017 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (40963781/78125000 : ℝ)^4327 ≤ (42922317691757/100000000000000 : ℝ)^3303 := by
    have hnat : (40963781 : ℕ)^4327*100000000000000^3303 ≤ 42922317691757^3303*78125000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40963781 78125000 42922317691757 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4327/1024 : ℝ)) 4327 3303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349101533/10000000000 : ℝ), (-1054528959/5000000000 : ℝ), (40963781/78125000 : ℝ)] ![(5507470211099/12500000000000 : ℝ), (13017920613017/100000000000000 : ℝ), (42922317691757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349101533/10000000000 : ℝ)|^4327 ≤ (5507470211099/12500000000000 : ℝ)^3303
        have hw : |(5349101533/10000000000 : ℝ)|=(5349101533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1054528959/5000000000 : ℝ)|^4327 ≤ (13017920613017/100000000000000 : ℝ)^3303
        have hw : |(-1054528959/5000000000 : ℝ)|=(1054528959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(40963781/78125000 : ℝ)|^4327 ≤ (42922317691757/100000000000000 : ℝ)^3303
        have hw : |(40963781/78125000 : ℝ)|=(40963781/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1367_s4_2 (p : ℝ) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337275383/2500000000 : ℝ)*x 0 + (40963781/78125000 : ℝ)*x 1 + (-1054528959/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337275383/2500000000 : ℝ)^4327 ≤ (44059761678001/100000000000000 : ℝ)^3303 := by
    have hnat : (1337275383 : ℕ)^4327*100000000000000^3303 ≤ 44059761678001^3303*2500000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337275383 2500000000 44059761678001 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (40963781/78125000 : ℝ)^4327 ≤ (42922317691757/100000000000000 : ℝ)^3303 := by
    have hnat : (40963781 : ℕ)^4327*100000000000000^3303 ≤ 42922317691757^3303*78125000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40963781 78125000 42922317691757 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1054528959/5000000000 : ℝ)^4327 ≤ (13017920613017/100000000000000 : ℝ)^3303 := by
    have hnat : (1054528959 : ℕ)^4327*100000000000000^3303 ≤ 13017920613017^3303*5000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054528959 5000000000 13017920613017 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4327/1024 : ℝ)) 4327 3303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337275383/2500000000 : ℝ), (40963781/78125000 : ℝ), (-1054528959/5000000000 : ℝ)] ![(44059761678001/100000000000000 : ℝ), (42922317691757/100000000000000 : ℝ), (13017920613017/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337275383/2500000000 : ℝ)|^4327 ≤ (44059761678001/100000000000000 : ℝ)^3303
        have hw : |(1337275383/2500000000 : ℝ)|=(1337275383/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(40963781/78125000 : ℝ)|^4327 ≤ (42922317691757/100000000000000 : ℝ)^3303
        have hw : |(40963781/78125000 : ℝ)|=(40963781/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1054528959/5000000000 : ℝ)|^4327 ≤ (13017920613017/100000000000000 : ℝ)^3303
        have hw : |(-1054528959/5000000000 : ℝ)|=(1054528959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1367_s4_3 (p : ℝ) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1079994209/2500000000 : ℝ)*x 0 + (2071759077/5000000000 : ℝ)*x 1 + (4503360853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079994209/2500000000 : ℝ)^4327 ≤ (33302200601361/100000000000000 : ℝ)^3303 := by
    have hnat : (1079994209 : ℕ)^4327*100000000000000^3303 ≤ 33302200601361^3303*2500000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079994209 2500000000 33302200601361 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2071759077/5000000000 : ℝ)^4327 ≤ (31531570563791/100000000000000 : ℝ)^3303 := by
    have hnat : (2071759077 : ℕ)^4327*100000000000000^3303 ≤ 31531570563791^3303*5000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2071759077 5000000000 31531570563791 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4503360853/10000000000 : ℝ)^4327 ≤ (35166228821071/100000000000000 : ℝ)^3303 := by
    have hnat : (4503360853 : ℕ)^4327*100000000000000^3303 ≤ 35166228821071^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4503360853 10000000000 35166228821071 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4327/1024 : ℝ)) 4327 3303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1079994209/2500000000 : ℝ), (2071759077/5000000000 : ℝ), (4503360853/10000000000 : ℝ)] ![(33302200601361/100000000000000 : ℝ), (31531570563791/100000000000000 : ℝ), (35166228821071/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1079994209/2500000000 : ℝ)|^4327 ≤ (33302200601361/100000000000000 : ℝ)^3303
        have hw : |(1079994209/2500000000 : ℝ)|=(1079994209/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2071759077/5000000000 : ℝ)|^4327 ≤ (31531570563791/100000000000000 : ℝ)^3303
        have hw : |(2071759077/5000000000 : ℝ)|=(2071759077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4503360853/10000000000 : ℝ)|^4327 ≤ (35166228821071/100000000000000 : ℝ)^3303
        have hw : |(4503360853/10000000000 : ℝ)|=(4503360853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1367_s4_4 (p : ℝ) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-505583829/2500000000 : ℝ)*x 0 + (1048797909/2000000000 : ℝ)*x 1 + (5412930501/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (505583829/2500000000 : ℝ)^4327 ≤ (6160598997499/50000000000000 : ℝ)^3303 := by
    have hnat : (505583829 : ℕ)^4327*50000000000000^3303 ≤ 6160598997499^3303*2500000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      505583829 2500000000 6160598997499 50000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048797909/2000000000 : ℝ)^4327 ≤ (42929026421323/100000000000000 : ℝ)^3303 := by
    have hnat : (1048797909 : ℕ)^4327*100000000000000^3303 ≤ 42929026421323^3303*2000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048797909 2000000000 42929026421323 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5412930501/10000000000 : ℝ)^4327 ≤ (44749775564371/100000000000000 : ℝ)^3303 := by
    have hnat : (5412930501 : ℕ)^4327*100000000000000^3303 ≤ 44749775564371^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412930501 10000000000 44749775564371 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4327/1024 : ℝ)) 4327 3303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-505583829/2500000000 : ℝ), (1048797909/2000000000 : ℝ), (5412930501/10000000000 : ℝ)] ![(6160598997499/50000000000000 : ℝ), (42929026421323/100000000000000 : ℝ), (44749775564371/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-505583829/2500000000 : ℝ)|^4327 ≤ (6160598997499/50000000000000 : ℝ)^3303
        have hw : |(-505583829/2500000000 : ℝ)|=(505583829/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048797909/2000000000 : ℝ)|^4327 ≤ (42929026421323/100000000000000 : ℝ)^3303
        have hw : |(1048797909/2000000000 : ℝ)|=(1048797909/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5412930501/10000000000 : ℝ)|^4327 ≤ (44749775564371/100000000000000 : ℝ)^3303
        have hw : |(5412930501/10000000000 : ℝ)|=(5412930501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1367_s4_5 (p : ℝ) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305139597/10000000000 : ℝ)*x 0 + (-969745733/5000000000 : ℝ)*x 1 + (541293031/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305139597/10000000000 : ℝ)^4327 ≤ (8717199603779/20000000000000 : ℝ)^3303 := by
    have hnat : (5305139597 : ℕ)^4327*20000000000000^3303 ≤ 8717199603779^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305139597 10000000000 8717199603779 20000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (969745733/5000000000 : ℝ)^4327 ≤ (583211423507/5000000000000 : ℝ)^3303 := by
    have hnat : (969745733 : ℕ)^4327*5000000000000^3303 ≤ 583211423507^3303*5000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      969745733 5000000000 583211423507 5000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (541293031/1000000000 : ℝ)^4327 ≤ (22374886747901/50000000000000 : ℝ)^3303 := by
    have hnat : (541293031 : ℕ)^4327*50000000000000^3303 ≤ 22374886747901^3303*1000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541293031 1000000000 22374886747901 50000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4327/1024 : ℝ)) 4327 3303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305139597/10000000000 : ℝ), (-969745733/5000000000 : ℝ), (541293031/1000000000 : ℝ)] ![(8717199603779/20000000000000 : ℝ), (583211423507/5000000000000 : ℝ), (22374886747901/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305139597/10000000000 : ℝ)|^4327 ≤ (8717199603779/20000000000000 : ℝ)^3303
        have hw : |(5305139597/10000000000 : ℝ)|=(5305139597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-969745733/5000000000 : ℝ)|^4327 ≤ (583211423507/5000000000000 : ℝ)^3303
        have hw : |(-969745733/5000000000 : ℝ)|=(969745733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(541293031/1000000000 : ℝ)|^4327 ≤ (22374886747901/50000000000000 : ℝ)^3303
        have hw : |(541293031/1000000000 : ℝ)|=(541293031/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1367_s4_6 (p : ℝ) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (41446403/78125000 : ℝ)*x 0 + (5412930377/10000000000 : ℝ)*x 1 + (-30304553/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41446403/78125000 : ℝ)^4327 ≤ (43585997878977/100000000000000 : ℝ)^3303 := by
    have hnat : (41446403 : ℕ)^4327*100000000000000^3303 ≤ 43585997878977^3303*78125000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41446403 78125000 43585997878977 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5412930377/10000000000 : ℝ)^4327 ≤ (22374887110713/50000000000000 : ℝ)^3303 := by
    have hnat : (5412930377 : ℕ)^4327*50000000000000^3303 ≤ 22374887110713^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412930377 10000000000 22374887110713 50000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (30304553/156250000 : ℝ)^4327 ≤ (11664227887127/100000000000000 : ℝ)^3303 := by
    have hnat : (30304553 : ℕ)^4327*100000000000000^3303 ≤ 11664227887127^3303*156250000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30304553 156250000 11664227887127 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4327/1024 : ℝ)) 4327 3303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41446403/78125000 : ℝ), (5412930377/10000000000 : ℝ), (-30304553/156250000 : ℝ)] ![(43585997878977/100000000000000 : ℝ), (22374887110713/50000000000000 : ℝ), (11664227887127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41446403/78125000 : ℝ)|^4327 ≤ (43585997878977/100000000000000 : ℝ)^3303
        have hw : |(41446403/78125000 : ℝ)|=(41446403/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5412930377/10000000000 : ℝ)|^4327 ≤ (22374887110713/50000000000000 : ℝ)^3303
        have hw : |(5412930377/10000000000 : ℝ)|=(5412930377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-30304553/156250000 : ℝ)|^4327 ≤ (11664227887127/100000000000000 : ℝ)^3303
        have hw : |(-30304553/156250000 : ℝ)|=(30304553/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1367_s4_7 (p : ℝ) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (86400073/200000000 : ℝ)*x 0 + (2251019197/5000000000 : ℝ)*x 1 + (414484791/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (86400073/200000000 : ℝ)^4327 ≤ (6660494278177/20000000000000 : ℝ)^3303 := by
    have hnat : (86400073 : ℕ)^4327*20000000000000^3303 ≤ 6660494278177^3303*200000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86400073 200000000 6660494278177 20000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2251019197/5000000000 : ℝ)^4327 ≤ (35152700938759/100000000000000 : ℝ)^3303 := by
    have hnat : (2251019197 : ℕ)^4327*100000000000000^3303 ≤ 35152700938759^3303*5000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251019197 5000000000 35152700938759 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (414484791/1000000000 : ℝ)^4327 ≤ (15772413827433/50000000000000 : ℝ)^3303 := by
    have hnat : (414484791 : ℕ)^4327*50000000000000^3303 ≤ 15772413827433^3303*1000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      414484791 1000000000 15772413827433 50000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4327/1024 : ℝ)) 4327 3303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(86400073/200000000 : ℝ), (2251019197/5000000000 : ℝ), (414484791/1000000000 : ℝ)] ![(6660494278177/20000000000000 : ℝ), (35152700938759/100000000000000 : ℝ), (15772413827433/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(86400073/200000000 : ℝ)|^4327 ≤ (6660494278177/20000000000000 : ℝ)^3303
        have hw : |(86400073/200000000 : ℝ)|=(86400073/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2251019197/5000000000 : ℝ)|^4327 ≤ (35152700938759/100000000000000 : ℝ)^3303
        have hw : |(2251019197/5000000000 : ℝ)|=(2251019197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(414484791/1000000000 : ℝ)|^4327 ≤ (15772413827433/50000000000000 : ℝ)^3303
        have hw : |(414484791/1000000000 : ℝ)|=(414484791/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1367_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38928637/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14987/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10957/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2791/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14767/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14987/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10957/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14987/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10957/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14987/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10957/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14987/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10957/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14987/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10957/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14987/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10957/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10957/100000 : ℝ) ^ (2163/512 : ℝ) ≤ (1754294034584337/20000000000000000000 : ℝ) := by
    have hpowers : (10957/100000 : ℝ)^2163 ≤ (1754294034584337/20000000000000000000 : ℝ)^512 := by
      have hnat : (10957 : ℕ)^2163*20000000000000000000^512 ≤ 1754294034584337^512*100000^2163 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10957 100000 1754294034584337 20000000000000000000 2163 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10957/100000 : ℝ)) (X := (1754294034584337/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2163 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14987/100000 : ℝ) ^ (2163/512 : ℝ) ≤ (32939471348672761/100000000000000000000 : ℝ) := by
    have hpowers : (14987/100000 : ℝ)^2163 ≤ (32939471348672761/100000000000000000000 : ℝ)^512 := by
      have hnat : (14987 : ℕ)^2163*100000000000000000000^512 ≤ 32939471348672761^512*100000^2163 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14987 100000 32939471348672761 100000000000000000000 2163 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14987/100000 : ℝ)) (X := (32939471348672761/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2163 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001754294034584337/10000000000000000000 : ℝ) ≤ (5000207614058207/5000000000000000 : ℝ) ^ (2163/512 : ℝ) := by
    have hpowers : (10001754294034584337/10000000000000000000 : ℝ)^512 ≤ (5000207614058207/5000000000000000 : ℝ)^2163 := by
      have hnat : (10001754294034584337 : ℕ)^512*5000000000000000^2163 ≤ 5000207614058207^2163*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001754294034584337 10000000000000000000 5000207614058207 5000000000000000 512 2163 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000207614058207/5000000000000000 : ℝ)) (X := (10001754294034584337/10000000000000000000 : ℝ)) (by norm_num) 2163 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50020855470760797223/50000000000000000000 : ℝ) ≤ (250024679384271/250000000000000 : ℝ) ^ (2163/512 : ℝ) := by
    have hpowers : (50020855470760797223/50000000000000000000 : ℝ)^512 ≤ (250024679384271/250000000000000 : ℝ)^2163 := by
      have hnat : (50020855470760797223 : ℕ)^512*250000000000000^2163 ≤ 250024679384271^2163*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020855470760797223 50000000000000000000 250024679384271 250000000000000 512 2163 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250024679384271/250000000000000 : ℝ)) (X := (50020855470760797223/50000000000000000000 : ℝ)) (by norm_num) 2163 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032939471348672761/50000000000000000000 : ℝ) ≤ (5000779561312633/5000000000000000 : ℝ) ^ (2163/512 : ℝ) := by
    have hpowers : (50032939471348672761/50000000000000000000 : ℝ)^512 ≤ (5000779561312633/5000000000000000 : ℝ)^2163 := by
      have hnat : (50032939471348672761 : ℕ)^512*5000000000000000^2163 ≤ 5000779561312633^2163*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032939471348672761 50000000000000000000 5000779561312633 5000000000000000 512 2163 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000779561312633/5000000000000000 : ℝ)) (X := (50032939471348672761/50000000000000000000 : ℝ)) (by norm_num) 2163 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1754294034584337/20000000000000000000 : ℝ) ≤ ((1259035616161739283/1259375000000000000 : ℝ)+2*(285973627213/201500000000000 : ℝ)*(10957/100000 : ℝ))^(2163/512 : ℝ) := by
    rw [show (1259035616161739283/1259375000000000000 : ℝ)+2*(285973627213/201500000000000 : ℝ)*(10957/100000 : ℝ)=(5000207614058207/5000000000000000 : ℝ) by norm_num, show 1+2*(1754294034584337/20000000000000000000 : ℝ)=(10001754294034584337/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32939471348672761/100000000000000000000 : ℝ)+(1754294034584337/20000000000000000000 : ℝ) ≤ ((1259035616161739283/1259375000000000000 : ℝ)+(285973627213/201500000000000 : ℝ)*((14987/100000 : ℝ)+(10957/100000 : ℝ)))^(2163/512 : ℝ) := by
    rw [show (1259035616161739283/1259375000000000000 : ℝ)+(285973627213/201500000000000 : ℝ)*((14987/100000 : ℝ)+(10957/100000 : ℝ))=(250024679384271/250000000000000 : ℝ) by norm_num, show 1+(32939471348672761/100000000000000000000 : ℝ)+(1754294034584337/20000000000000000000 : ℝ)=(50020855470760797223/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32939471348672761/100000000000000000000 : ℝ) ≤ ((1259035616161739283/1259375000000000000 : ℝ)+2*(285973627213/201500000000000 : ℝ)*(14987/100000 : ℝ))^(2163/512 : ℝ) := by
    rw [show (1259035616161739283/1259375000000000000 : ℝ)+2*(285973627213/201500000000000 : ℝ)*(14987/100000 : ℝ)=(5000779561312633/5000000000000000 : ℝ) by norm_num, show 1+2*(32939471348672761/100000000000000000000 : ℝ)=(50032939471348672761/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1259035616161739283/1259375000000000000 : ℝ)*(X 1 0+X 2 0)+(285973627213/201500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2163/512 : ℝ)) (lo := (10957/100000 : ℝ)) (hi := (14987/100000 : ℝ)) (c := (1259035616161739283/1259375000000000000 : ℝ)) (alpha := (285973627213/201500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1259035616161739283/1259375000000000000 : ℝ)*(X 0 1+X 2 1)+(285973627213/201500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2163/512 : ℝ)) (lo := (10957/100000 : ℝ)) (hi := (14987/100000 : ℝ)) (c := (1259035616161739283/1259375000000000000 : ℝ)) (alpha := (285973627213/201500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1259035616161739283/1259375000000000000 : ℝ)*(X 0 2+X 1 2)+(285973627213/201500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2163/512 : ℝ)) (lo := (10957/100000 : ℝ)) (hi := (14987/100000 : ℝ)) (c := (1259035616161739283/1259375000000000000 : ℝ)) (alpha := (285973627213/201500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-126395153/625000000 : ℝ)*X 0 0+(2706779709/5000000000 : ℝ)*X 0 1+(5243363969/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1367_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349101533/10000000000 : ℝ)*X 1 0+(-1054528959/5000000000 : ℝ)*X 1 1+(40963781/78125000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1367_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337275383/2500000000 : ℝ)*X 2 0+(40963781/78125000 : ℝ)*X 2 1+(-1054528959/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1367_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1079994209/2500000000 : ℝ)*X 0 0+(2071759077/5000000000 : ℝ)*X 0 1+(4503360853/10000000000 : ℝ)*X 0 2+(1079994209/2500000000 : ℝ)*X 1 0+(2071759077/5000000000 : ℝ)*X 1 1+(4503360853/10000000000 : ℝ)*X 1 2+(1079994209/2500000000 : ℝ)*X 2 0+(2071759077/5000000000 : ℝ)*X 2 1+(4503360853/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1367_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-505583829/2500000000 : ℝ)*X 0 0+(1048797909/2000000000 : ℝ)*X 0 1+(5412930501/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1367_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305139597/10000000000 : ℝ)*X 1 0+(-969745733/5000000000 : ℝ)*X 1 1+(541293031/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1367_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((41446403/78125000 : ℝ)*X 2 0+(5412930377/10000000000 : ℝ)*X 2 1+(-30304553/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1367_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((86400073/200000000 : ℝ)*X 0 0+(2251019197/5000000000 : ℝ)*X 0 1+(414484791/1000000000 : ℝ)*X 0 2+(86400073/200000000 : ℝ)*X 1 0+(2251019197/5000000000 : ℝ)*X 1 1+(414484791/1000000000 : ℝ)*X 1 2+(86400073/200000000 : ℝ)*X 2 0+(2251019197/5000000000 : ℝ)*X 2 1+(414484791/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1367_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (264460557907525677223270653/31484375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (785117427/50000000000000 : ℝ)*(base19) + (730959127/50000000000000 : ℝ)*(base23) + (14338021/25000000000000 : ℝ)*(lower2) + (212165071/100000000000000 : ℝ)*(upper3) + (26415983/20000000000000 : ℝ)*(upper5) + (2163671289393599/50000000000000 : ℝ)*(major0) + (2163671289393599/50000000000000 : ℝ)*(major1) + (2163671289393599/50000000000000 : ℝ)*(major2) + (5875630713439279/100000000000000 : ℝ)*(sp0) + (2937830322084457/50000000000000 : ℝ)*(sp1) + (1175132150497103/20000000000000 : ℝ)*(sp2) + (2779006501993929/100000000000000 : ℝ)*(sp3) + (3150096449/10000000000000 : ℝ)*(sp4) + (4040296341/25000000000000 : ℝ)*(sp7) + (2779022663179293/100000000000000 : ℝ)*(f.failure) + (5875662214403769/100000000000000 : ℝ)*(f.sum) + (36234150721637/5037500000000000000000000000 : ℝ)*base65 + (730830177398969233/62968750000000000000000000000000 : ℝ)*base68 + (378803970163344233/62968750000000000000000000000000 : ℝ)*base70 + (509839035298344233/62968750000000000000000000000000 : ℝ)*base72 + (2494732459519/2518750000000000000000000000 : ℝ)*base74 + (665717484715375483/62968750000000000000000000000000 : ℝ)*base76 + (239448944463031733/62968750000000000000000000000000 : ℝ)*base78 + (404342677358969233/62968750000000000000000000000000 : ℝ)*base80 + (19014890281149/10075000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (13113641/2500000000000000000000 : ℝ)*base89 + (13113641/2500000000000000000000 : ℝ)*base91 + (13113641/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (17701107214465316942997/10075000000000000000000000000 : ℝ) := by norm_num
    linear_combination (365862309/100000000000000 : ℝ)*(base19) + (147637747/25000000000000 : ℝ)*(base23) + (97365569/100000000000000 : ℝ)*(upper2) + (14453547/100000000000000 : ℝ)*(upper3) + (2179712977041551/50000000000000 : ℝ)*(major0) + (2179712977041551/50000000000000 : ℝ)*(major1) + (2179712977041551/50000000000000 : ℝ)*(major2) + (2377408291/100000000000000 : ℝ)*(sp1) + (9094558621/100000000000000 : ℝ)*(sp2) + (156192431/100000000000000 : ℝ)*(sp3) + (5919225218644241/100000000000000 : ℝ)*(sp4) + (5919222475373641/100000000000000 : ℝ)*(sp5) + (739901941691829/12500000000000 : ℝ)*(sp6) + (279962647476507/10000000000000 : ℝ)*(sp7) + (1399813315478751/50000000000000 : ℝ)*(f.failure) + (5919225218644241/100000000000000 : ℝ)*(f.sum) + (10188815077613/5037500000000000000000000000 : ℝ)*base65 + (179108409549189567/62968750000000000000000000000000 : ℝ)*base68 + (370687795385908317/62968750000000000000000000000000 : ℝ)*base70 + (261675592374091683/62968750000000000000000000000000 : ℝ)*base71 + (6741605936619/2518750000000000000000000000 : ℝ)*base73 + (6786518943877067/62968750000000000000000000000000 : ℝ)*base76 + (14913171274091683/62968750000000000000000000000000 : ℝ)*base77 + (383138044991279183/62968750000000000000000000000000 : ℝ)*base79 + (185342694349/10075000000000000000000000000 : ℝ)*base82 + (3892387/1250000000000000000000 : ℝ)*base89 + (3892387/1250000000000000000000 : ℝ)*base91 + (3892387/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1367_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38928637/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14987/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10957/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2791/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14767/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1367_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1367_s5_0 (p : ℝ) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-404506643/2000000000 : ℝ)*x 0 + (2705863203/5000000000 : ℝ)*x 1 + (2622529087/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (404506643/2000000000 : ℝ)^4327 ≤ (6161388763227/50000000000000 : ℝ)^3303 := by
    have hnat : (404506643 : ℕ)^4327*50000000000000^3303 ≤ 6161388763227^3303*2000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      404506643 2000000000 6161388763227 50000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2705863203/5000000000 : ℝ)^4327 ≤ (11184183854181/25000000000000 : ℝ)^3303 := by
    have hnat : (2705863203 : ℕ)^4327*25000000000000^3303 ≤ 11184183854181^3303*5000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705863203 5000000000 11184183854181 25000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622529087/5000000000 : ℝ)^4327 ≤ (1717619481763/4000000000000 : ℝ)^3303 := by
    have hnat : (2622529087 : ℕ)^4327*4000000000000^3303 ≤ 1717619481763^3303*5000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622529087 5000000000 1717619481763 4000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4327/1024 : ℝ)) 4327 3303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-404506643/2000000000 : ℝ), (2705863203/5000000000 : ℝ), (2622529087/5000000000 : ℝ)] ![(6161388763227/50000000000000 : ℝ), (11184183854181/25000000000000 : ℝ), (1717619481763/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-404506643/2000000000 : ℝ)|^4327 ≤ (6161388763227/50000000000000 : ℝ)^3303
        have hw : |(-404506643/2000000000 : ℝ)|=(404506643/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2705863203/5000000000 : ℝ)|^4327 ≤ (11184183854181/25000000000000 : ℝ)^3303
        have hw : |(2705863203/5000000000 : ℝ)|=(2705863203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622529087/5000000000 : ℝ)|^4327 ≤ (1717619481763/4000000000000 : ℝ)^3303
        have hw : |(2622529087/5000000000 : ℝ)|=(2622529087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1367_s5_1 (p : ℝ) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674315817/5000000000 : ℝ)*x 0 + (-26342971/125000000 : ℝ)*x 1 + (5245058231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674315817/5000000000 : ℝ)^4327 ≤ (44054691335389/100000000000000 : ℝ)^3303 := by
    have hnat : (2674315817 : ℕ)^4327*100000000000000^3303 ≤ 44054691335389^3303*5000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674315817 5000000000 44054691335389 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (26342971/125000000 : ℝ)^4327 ≤ (6502410499217/50000000000000 : ℝ)^3303 := by
    have hnat : (26342971 : ℕ)^4327*50000000000000^3303 ≤ 6502410499217^3303*125000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26342971 125000000 6502410499217 50000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245058231/10000000000 : ℝ)^4327 ≤ (42940487655397/100000000000000 : ℝ)^3303 := by
    have hnat : (5245058231 : ℕ)^4327*100000000000000^3303 ≤ 42940487655397^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245058231 10000000000 42940487655397 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4327/1024 : ℝ)) 4327 3303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674315817/5000000000 : ℝ), (-26342971/125000000 : ℝ), (5245058231/10000000000 : ℝ)] ![(44054691335389/100000000000000 : ℝ), (6502410499217/50000000000000 : ℝ), (42940487655397/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674315817/5000000000 : ℝ)|^4327 ≤ (44054691335389/100000000000000 : ℝ)^3303
        have hw : |(2674315817/5000000000 : ℝ)|=(2674315817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-26342971/125000000 : ℝ)|^4327 ≤ (6502410499217/50000000000000 : ℝ)^3303
        have hw : |(-26342971/125000000 : ℝ)|=(26342971/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245058231/10000000000 : ℝ)|^4327 ≤ (42940487655397/100000000000000 : ℝ)^3303
        have hw : |(5245058231/10000000000 : ℝ)|=(5245058231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1367_s5_2 (p : ℝ) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668578937/1250000000 : ℝ)*x 0 + (2622529213/5000000000 : ℝ)*x 1 + (-526859401/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668578937/1250000000 : ℝ)^4327 ≤ (44054689846347/100000000000000 : ℝ)^3303 := by
    have hnat : (668578937 : ℕ)^4327*100000000000000^3303 ≤ 44054689846347^3303*1250000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668578937 1250000000 44054689846347 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622529213/5000000000 : ℝ)^4327 ≤ (42940489746761/100000000000000 : ℝ)^3303 := by
    have hnat : (2622529213 : ℕ)^4327*100000000000000^3303 ≤ 42940489746761^3303*5000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622529213 5000000000 42940489746761 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526859401/2500000000 : ℝ)^4327 ≤ (812801274003/6250000000000 : ℝ)^3303 := by
    have hnat : (526859401 : ℕ)^4327*6250000000000^3303 ≤ 812801274003^3303*2500000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526859401 2500000000 812801274003 6250000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4327/1024 : ℝ)) 4327 3303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668578937/1250000000 : ℝ), (2622529213/5000000000 : ℝ), (-526859401/2500000000 : ℝ)] ![(44054689846347/100000000000000 : ℝ), (42940489746761/100000000000000 : ℝ), (812801274003/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668578937/1250000000 : ℝ)|^4327 ≤ (44054689846347/100000000000000 : ℝ)^3303
        have hw : |(668578937/1250000000 : ℝ)|=(668578937/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622529213/5000000000 : ℝ)|^4327 ≤ (42940489746761/100000000000000 : ℝ)^3303
        have hw : |(2622529213/5000000000 : ℝ)|=(2622529213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-526859401/2500000000 : ℝ)|^4327 ≤ (812801274003/6250000000000 : ℝ)^3303
        have hw : |(-526859401/2500000000 : ℝ)|=(526859401/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1367_s5_3 (p : ℝ) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2160051603/5000000000 : ℝ)*x 0 + (2073615849/5000000000 : ℝ)*x 1 + (4499616221/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2160051603/5000000000 : ℝ)^4327 ≤ (33303476792693/100000000000000 : ℝ)^3303 := by
    have hnat : (2160051603 : ℕ)^4327*100000000000000^3303 ≤ 33303476792693^3303*5000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2160051603 5000000000 33303476792693 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2073615849/5000000000 : ℝ)^4327 ≤ (6313719257747/20000000000000 : ℝ)^3303 := by
    have hnat : (2073615849 : ℕ)^4327*20000000000000^3303 ≤ 6313719257747^3303*5000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2073615849 5000000000 6313719257747 20000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4499616221/10000000000 : ℝ)^4327 ≤ (35127926903017/100000000000000 : ℝ)^3303 := by
    have hnat : (4499616221 : ℕ)^4327*100000000000000^3303 ≤ 35127926903017^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4499616221 10000000000 35127926903017 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4327/1024 : ℝ)) 4327 3303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2160051603/5000000000 : ℝ), (2073615849/5000000000 : ℝ), (4499616221/10000000000 : ℝ)] ![(33303476792693/100000000000000 : ℝ), (6313719257747/20000000000000 : ℝ), (35127926903017/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2160051603/5000000000 : ℝ)|^4327 ≤ (33303476792693/100000000000000 : ℝ)^3303
        have hw : |(2160051603/5000000000 : ℝ)|=(2160051603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2073615849/5000000000 : ℝ)|^4327 ≤ (6313719257747/20000000000000 : ℝ)^3303
        have hw : |(2073615849/5000000000 : ℝ)|=(2073615849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4499616221/10000000000 : ℝ)|^4327 ≤ (35127926903017/100000000000000 : ℝ)^3303
        have hw : |(4499616221/10000000000 : ℝ)|=(4499616221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1367_s5_4 (p : ℝ) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-505636271/2500000000 : ℝ)*x 0 + (5245658391/10000000000 : ℝ)*x 1 + (5411123213/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (505636271/2500000000 : ℝ)^4327 ≤ (3080718065109/25000000000000 : ℝ)^3303 := by
    have hnat : (505636271 : ℕ)^4327*25000000000000^3303 ≤ 3080718065109^3303*2500000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      505636271 2500000000 3080718065109 25000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245658391/10000000000 : ℝ)^4327 ≤ (42946924451157/100000000000000 : ℝ)^3303 := by
    have hnat : (5245658391 : ℕ)^4327*100000000000000^3303 ≤ 42946924451157^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245658391 10000000000 42946924451157 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411123213/10000000000 : ℝ)^4327 ≤ (22365101637737/50000000000000 : ℝ)^3303 := by
    have hnat : (5411123213 : ℕ)^4327*50000000000000^3303 ≤ 22365101637737^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411123213 10000000000 22365101637737 50000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4327/1024 : ℝ)) 4327 3303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-505636271/2500000000 : ℝ), (5245658391/10000000000 : ℝ), (5411123213/10000000000 : ℝ)] ![(3080718065109/25000000000000 : ℝ), (42946924451157/100000000000000 : ℝ), (22365101637737/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-505636271/2500000000 : ℝ)|^4327 ≤ (3080718065109/25000000000000 : ℝ)^3303
        have hw : |(-505636271/2500000000 : ℝ)|=(505636271/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245658391/10000000000 : ℝ)|^4327 ≤ (42946924451157/100000000000000 : ℝ)^3303
        have hw : |(5245658391/10000000000 : ℝ)|=(5245658391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411123213/10000000000 : ℝ)|^4327 ≤ (22365101637737/50000000000000 : ℝ)^3303
        have hw : |(5411123213/10000000000 : ℝ)|=(5411123213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1367_s5_5 (p : ℝ) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652790259/5000000000 : ℝ)*x 0 + (-1941372801/10000000000 : ℝ)*x 1 + (5411123227/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652790259/5000000000 : ℝ)^4327 ≤ (8718148731973/20000000000000 : ℝ)^3303 := by
    have hnat : (2652790259 : ℕ)^4327*20000000000000^3303 ≤ 8718148731973^3303*5000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652790259 5000000000 8718148731973 20000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1941372801/10000000000 : ℝ)^4327 ≤ (2335810579207/20000000000000 : ℝ)^3303 := by
    have hnat : (1941372801 : ℕ)^4327*20000000000000^3303 ≤ 2335810579207^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1941372801 10000000000 2335810579207 20000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411123227/10000000000 : ℝ)^4327 ≤ (44730203427081/100000000000000 : ℝ)^3303 := by
    have hnat : (5411123227 : ℕ)^4327*100000000000000^3303 ≤ 44730203427081^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411123227 10000000000 44730203427081 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4327/1024 : ℝ)) 4327 3303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652790259/5000000000 : ℝ), (-1941372801/10000000000 : ℝ), (5411123227/10000000000 : ℝ)] ![(8718148731973/20000000000000 : ℝ), (2335810579207/20000000000000 : ℝ), (44730203427081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652790259/5000000000 : ℝ)|^4327 ≤ (8718148731973/20000000000000 : ℝ)^3303
        have hw : |(2652790259/5000000000 : ℝ)|=(2652790259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1941372801/10000000000 : ℝ)|^4327 ≤ (2335810579207/20000000000000 : ℝ)^3303
        have hw : |(-1941372801/10000000000 : ℝ)|=(1941372801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411123227/10000000000 : ℝ)|^4327 ≤ (44730203427081/100000000000000 : ℝ)^3303
        have hw : |(5411123227/10000000000 : ℝ)|=(5411123227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1367_s5_6 (p : ℝ) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (132639513/250000000 : ℝ)*x 0 + (5411123219/10000000000 : ℝ)*x 1 + (-1941372809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132639513/250000000 : ℝ)^4327 ≤ (2724421480087/6250000000000 : ℝ)^3303 := by
    have hnat : (132639513 : ℕ)^4327*6250000000000^3303 ≤ 2724421480087^3303*250000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132639513 250000000 2724421480087 6250000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5411123219/10000000000 : ℝ)^4327 ≤ (1397818854389/3125000000000 : ℝ)^3303 := by
    have hnat : (5411123219 : ℕ)^4327*3125000000000^3303 ≤ 1397818854389^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411123219 10000000000 1397818854389 3125000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1941372809/10000000000 : ℝ)^4327 ≤ (11679052959083/100000000000000 : ℝ)^3303 := by
    have hnat : (1941372809 : ℕ)^4327*100000000000000^3303 ≤ 11679052959083^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1941372809 10000000000 11679052959083 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4327/1024 : ℝ)) 4327 3303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132639513/250000000 : ℝ), (5411123219/10000000000 : ℝ), (-1941372809/10000000000 : ℝ)] ![(2724421480087/6250000000000 : ℝ), (1397818854389/3125000000000 : ℝ), (11679052959083/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132639513/250000000 : ℝ)|^4327 ≤ (2724421480087/6250000000000 : ℝ)^3303
        have hw : |(132639513/250000000 : ℝ)|=(132639513/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5411123219/10000000000 : ℝ)|^4327 ≤ (1397818854389/3125000000000 : ℝ)^3303
        have hw : |(5411123219/10000000000 : ℝ)|=(5411123219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1941372809/10000000000 : ℝ)|^4327 ≤ (11679052959083/100000000000000 : ℝ)^3303
        have hw : |(-1941372809/10000000000 : ℝ)|=(1941372809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1367_s5_7 (p : ℝ) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (216006433/500000000 : ℝ)*x 0 + (35143341/78125000 : ℝ)*x 1 + (4148506857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (216006433/500000000 : ℝ)^4327 ≤ (33303733850153/100000000000000 : ℝ)^3303 := by
    have hnat : (216006433 : ℕ)^4327*100000000000000^3303 ≤ 33303733850153^3303*500000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216006433 500000000 33303733850153 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (35143341/78125000 : ℝ)^4327 ≤ (35114953561503/100000000000000 : ℝ)^3303 := by
    have hnat : (35143341 : ℕ)^4327*100000000000000^3303 ≤ 35114953561503^3303*78125000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35143341 78125000 35114953561503 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4148506857/10000000000 : ℝ)^4327 ≤ (15790656288013/50000000000000 : ℝ)^3303 := by
    have hnat : (4148506857 : ℕ)^4327*50000000000000^3303 ≤ 15790656288013^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4148506857 10000000000 15790656288013 50000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4327/1024 : ℝ)) 4327 3303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(216006433/500000000 : ℝ), (35143341/78125000 : ℝ), (4148506857/10000000000 : ℝ)] ![(33303733850153/100000000000000 : ℝ), (35114953561503/100000000000000 : ℝ), (15790656288013/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(216006433/500000000 : ℝ)|^4327 ≤ (33303733850153/100000000000000 : ℝ)^3303
        have hw : |(216006433/500000000 : ℝ)|=(216006433/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(35143341/78125000 : ℝ)|^4327 ≤ (35114953561503/100000000000000 : ℝ)^3303
        have hw : |(35143341/78125000 : ℝ)|=(35143341/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4148506857/10000000000 : ℝ)|^4327 ≤ (15790656288013/50000000000000 : ℝ)^3303
        have hw : |(4148506857/10000000000 : ℝ)|=(4148506857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1367_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38928637/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14767/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2791/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (14/125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14729/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14767/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2791/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14767/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2791/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14767/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2791/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14767/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2791/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14767/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2791/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14767/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2791/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2791/25000 : ℝ) ^ (2163/512 : ℝ) ≤ (2373289547884363/25000000000000000000 : ℝ) := by
    have hpowers : (2791/25000 : ℝ)^2163 ≤ (2373289547884363/25000000000000000000 : ℝ)^512 := by
      have hnat : (2791 : ℕ)^2163*25000000000000000000^512 ≤ 2373289547884363^512*25000^2163 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2791 25000 2373289547884363 25000000000000000000 2163 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2791/25000 : ℝ)) (X := (2373289547884363/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2163 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14767/100000 : ℝ) ^ (2163/512 : ℝ) ≤ (6188912637332869/20000000000000000000 : ℝ) := by
    have hpowers : (14767/100000 : ℝ)^2163 ≤ (6188912637332869/20000000000000000000 : ℝ)^512 := by
      have hnat : (14767 : ℕ)^2163*20000000000000000000^512 ≤ 6188912637332869^512*100000^2163 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14767 100000 6188912637332869 20000000000000000000 2163 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14767/100000 : ℝ)) (X := (6188912637332869/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2163 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502373289547884363/12500000000000000000 : ℝ) ≤ (1250056173657413/1250000000000000 : ℝ) ^ (2163/512 : ℝ) := by
    have hpowers : (12502373289547884363/12500000000000000000 : ℝ)^512 ≤ (1250056173657413/1250000000000000 : ℝ)^2163 := by
      have hnat : (12502373289547884363 : ℕ)^512*1250000000000000^2163 ≤ 1250056173657413^2163*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502373289547884363 12500000000000000000 1250056173657413 1250000000000000 512 2163 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250056173657413/1250000000000000 : ℝ)) (X := (12502373289547884363/12500000000000000000 : ℝ)) (by norm_num) 2163 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100040437721378201797/100000000000000000000 : ℝ) ≤ (2500239261660449/2500000000000000 : ℝ) ^ (2163/512 : ℝ) := by
    have hpowers : (100040437721378201797/100000000000000000000 : ℝ)^512 ≤ (2500239261660449/2500000000000000 : ℝ)^2163 := by
      have hnat : (100040437721378201797 : ℕ)^512*2500000000000000^2163 ≤ 2500239261660449^2163*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100040437721378201797 100000000000000000000 2500239261660449 2500000000000000 512 2163 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500239261660449/2500000000000000 : ℝ)) (X := (100040437721378201797/100000000000000000000 : ℝ)) (by norm_num) 2163 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006188912637332869/10000000000000000000 : ℝ) ≤ (312545772000759/312500000000000 : ℝ) ^ (2163/512 : ℝ) := by
    have hpowers : (10006188912637332869/10000000000000000000 : ℝ)^512 ≤ (312545772000759/312500000000000 : ℝ)^2163 := by
      have hnat : (10006188912637332869 : ℕ)^512*312500000000000^2163 ≤ 312545772000759^2163*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006188912637332869 10000000000000000000 312545772000759 312500000000000 512 2163 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312545772000759/312500000000000 : ℝ)) (X := (10006188912637332869/10000000000000000000 : ℝ)) (by norm_num) 2163 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2373289547884363/25000000000000000000 : ℝ) ≤ ((4502535521933123867/4503750000000000000 : ℝ)+2*(126914345623/90075000000000 : ℝ)*(2791/25000 : ℝ))^(2163/512 : ℝ) := by
    rw [show (4502535521933123867/4503750000000000000 : ℝ)+2*(126914345623/90075000000000 : ℝ)*(2791/25000 : ℝ)=(1250056173657413/1250000000000000 : ℝ) by norm_num, show 1+2*(2373289547884363/25000000000000000000 : ℝ)=(12502373289547884363/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6188912637332869/20000000000000000000 : ℝ)+(2373289547884363/25000000000000000000 : ℝ) ≤ ((4502535521933123867/4503750000000000000 : ℝ)+(126914345623/90075000000000 : ℝ)*((14767/100000 : ℝ)+(2791/25000 : ℝ)))^(2163/512 : ℝ) := by
    rw [show (4502535521933123867/4503750000000000000 : ℝ)+(126914345623/90075000000000 : ℝ)*((14767/100000 : ℝ)+(2791/25000 : ℝ))=(2500239261660449/2500000000000000 : ℝ) by norm_num, show 1+(6188912637332869/20000000000000000000 : ℝ)+(2373289547884363/25000000000000000000 : ℝ)=(100040437721378201797/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6188912637332869/20000000000000000000 : ℝ) ≤ ((4502535521933123867/4503750000000000000 : ℝ)+2*(126914345623/90075000000000 : ℝ)*(14767/100000 : ℝ))^(2163/512 : ℝ) := by
    rw [show (4502535521933123867/4503750000000000000 : ℝ)+2*(126914345623/90075000000000 : ℝ)*(14767/100000 : ℝ)=(312545772000759/312500000000000 : ℝ) by norm_num, show 1+2*(6188912637332869/20000000000000000000 : ℝ)=(10006188912637332869/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4502535521933123867/4503750000000000000 : ℝ)*(X 1 0+X 2 0)+(126914345623/90075000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2163/512 : ℝ)) (lo := (2791/25000 : ℝ)) (hi := (14767/100000 : ℝ)) (c := (4502535521933123867/4503750000000000000 : ℝ)) (alpha := (126914345623/90075000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4502535521933123867/4503750000000000000 : ℝ)*(X 0 1+X 2 1)+(126914345623/90075000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2163/512 : ℝ)) (lo := (2791/25000 : ℝ)) (hi := (14767/100000 : ℝ)) (c := (4502535521933123867/4503750000000000000 : ℝ)) (alpha := (126914345623/90075000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4502535521933123867/4503750000000000000 : ℝ)*(X 0 2+X 1 2)+(126914345623/90075000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2163/512 : ℝ)) (lo := (2791/25000 : ℝ)) (hi := (14767/100000 : ℝ)) (c := (4502535521933123867/4503750000000000000 : ℝ)) (alpha := (126914345623/90075000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-404506643/2000000000 : ℝ)*X 0 0+(2705863203/5000000000 : ℝ)*X 0 1+(2622529087/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1367_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674315817/5000000000 : ℝ)*X 1 0+(-26342971/125000000 : ℝ)*X 1 1+(5245058231/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1367_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668578937/1250000000 : ℝ)*X 2 0+(2622529213/5000000000 : ℝ)*X 2 1+(-526859401/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1367_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2160051603/5000000000 : ℝ)*X 0 0+(2073615849/5000000000 : ℝ)*X 0 1+(4499616221/10000000000 : ℝ)*X 0 2+(2160051603/5000000000 : ℝ)*X 1 0+(2073615849/5000000000 : ℝ)*X 1 1+(4499616221/10000000000 : ℝ)*X 1 2+(2160051603/5000000000 : ℝ)*X 2 0+(2073615849/5000000000 : ℝ)*X 2 1+(4499616221/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1367_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-505636271/2500000000 : ℝ)*X 0 0+(5245658391/10000000000 : ℝ)*X 0 1+(5411123213/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1367_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652790259/5000000000 : ℝ)*X 1 0+(-1941372801/10000000000 : ℝ)*X 1 1+(5411123227/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1367_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((132639513/250000000 : ℝ)*X 2 0+(5411123219/10000000000 : ℝ)*X 2 1+(-1941372809/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1367_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((216006433/500000000 : ℝ)*X 0 0+(35143341/78125000 : ℝ)*X 0 1+(4148506857/10000000000 : ℝ)*X 0 2+(216006433/500000000 : ℝ)*X 1 0+(35143341/78125000 : ℝ)*X 1 1+(4148506857/10000000000 : ℝ)*X 1 2+(216006433/500000000 : ℝ)*X 2 0+(35143341/78125000 : ℝ)*X 2 1+(4148506857/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1367_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (27471095688882106605628577/3002500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1076761241/50000000000000 : ℝ)*(base19) + (1908816497/100000000000000 : ℝ)*(base23) + (61168151/25000000000000 : ℝ)*(upper3) + (12020919/25000000000000 : ℝ)*(upper4) + (61688797/25000000000000 : ℝ)*(upper5) + (176757838181131/4000000000000 : ℝ)*(major0) + (176757838181131/4000000000000 : ℝ)*(major1) + (176757838181131/4000000000000 : ℝ)*(major2) + (5999992196270139/100000000000000 : ℝ)*(sp0) + (6000039030483703/100000000000000 : ℝ)*(sp1) + (6000039275189689/100000000000000 : ℝ)*(sp2) + (1418914895613179/50000000000000 : ℝ)*(sp3) + (48987736047/100000000000000 : ℝ)*(sp4) + (10314421877/50000000000000 : ℝ)*(sp7) + (2837850420070111/100000000000000 : ℝ)*(f.failure) + (3000020592003093/50000000000000 : ℝ)*(f.sum) + (1702562828719/720600000000000000000000000 : ℝ)*base65 + (35367135060498577/18015000000000000000000000000000 : ℝ)*base67 + (9598439319408577/18015000000000000000000000000000 : ℝ)*base69 + (140613415745546423/18015000000000000000000000000000 : ℝ)*base72 + (344543134397/225187500000000000000000000 : ℝ)*base73 + (84419759471531423/18015000000000000000000000000000 : ℝ)*base76 + (100486517262176423/18015000000000000000000000000000 : ℝ)*base78 + (37836073474046423/18015000000000000000000000000000 : ℝ)*base80 + (126152190979/90075000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (9331293/2500000000000000000000 : ℝ)*base90 + (9331293/2500000000000000000000 : ℝ)*base92 + (9331293/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (204226237734171579608351367/37531250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (93244921/10000000000000 : ℝ)*(base19) + (249244663/25000000000000 : ℝ)*(base23) + (14385393/12500000000000 : ℝ)*(upper3) + (7220821/25000000000000 : ℝ)*(lower4) + (22375721/20000000000000 : ℝ)*(upper5) + (2225505774031667/50000000000000 : ℝ)*(major0) + (2225505774031667/50000000000000 : ℝ)*(major1) + (2225505774031667/50000000000000 : ℝ)*(major2) + (4836469581/25000000000000 : ℝ)*(sp1) + (10154331989/50000000000000 : ℝ)*(sp2) + (1510894986588817/25000000000000 : ℝ)*(sp4) + (3021779834013867/50000000000000 : ℝ)*(sp5) + (3021779320356319/50000000000000 : ℝ)*(sp6) + (1429221484194057/50000000000000 : ℝ)*(sp7) + (1429221484194057/50000000000000 : ℝ)*(f.failure) + (1510894986588817/25000000000000 : ℝ)*(f.sum) + (454162000831/562968750000000000000000000 : ℝ)*base66 + (4261149700092703711/225187500000000000000000000000000 : ℝ)*base68 + (1822487100815578711/225187500000000000000000000000000 : ℝ)*base70 + (1081642989119203711/225187500000000000000000000000000 : ℝ)*base72 + (24246629272471/9007500000000000000000000000 : ℝ)*base74 + (590402153311453711/225187500000000000000000000000000 : ℝ)*base76 + (1362378665222953711/225187500000000000000000000000000 : ℝ)*base78 + (61147589023078711/225187500000000000000000000000000 : ℝ)*base80 + (7457718894083/4503750000000000000000000000 : ℝ)*base82 + (7510309/1250000000000000000000 : ℝ)*base89 + (7510309/1250000000000000000000 : ℝ)*base91 + (7510309/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1367_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38928637/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14767/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2791/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (14/125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14729/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1367_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1367_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38928637/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2001/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10011/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (14/125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14729/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1367_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1367_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1367_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38928637/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2001/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10011/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (14/125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14729/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1367_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
