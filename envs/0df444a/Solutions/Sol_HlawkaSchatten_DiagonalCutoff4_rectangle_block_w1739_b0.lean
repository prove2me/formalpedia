-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1739_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:12:36.517172+00:00
-- url     : https://prove2.me/submissions/c247aff2-4c6c-4dcd-88d4-1af426cad223

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
theorem support_rectangle_w1739_s0_0 (p : ℝ) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-307958383/2500000000 : ℝ)*x 0 + (1416489839/2500000000 : ℝ)*x 1 + (4960103713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (307958383/2500000000 : ℝ)^5599 ≤ (3854470341779/50000000000000 : ℝ)^4575 := by
    have hnat : (307958383 : ℕ)^5599*50000000000000^4575 ≤ 3854470341779^4575*2500000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      307958383 2500000000 3854470341779 50000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1416489839/2500000000 : ℝ)^5599 ≤ (9978835142527/20000000000000 : ℝ)^4575 := by
    have hnat : (1416489839 : ℕ)^5599*20000000000000^4575 ≤ 9978835142527^4575*2500000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1416489839 2500000000 9978835142527 20000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4960103713/10000000000 : ℝ)^5599 ≤ (42396883585321/100000000000000 : ℝ)^4575 := by
    have hnat : (4960103713 : ℕ)^5599*100000000000000^4575 ≤ 42396883585321^4575*10000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4960103713 10000000000 42396883585321 100000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5599/1024 : ℝ)) 5599 4575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-307958383/2500000000 : ℝ), (1416489839/2500000000 : ℝ), (4960103713/10000000000 : ℝ)] ![(3854470341779/50000000000000 : ℝ), (9978835142527/20000000000000 : ℝ), (42396883585321/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-307958383/2500000000 : ℝ)|^5599 ≤ (3854470341779/50000000000000 : ℝ)^4575
        have hw : |(-307958383/2500000000 : ℝ)|=(307958383/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1416489839/2500000000 : ℝ)|^5599 ≤ (9978835142527/20000000000000 : ℝ)^4575
        have hw : |(1416489839/2500000000 : ℝ)|=(1416489839/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4960103713/10000000000 : ℝ)|^5599 ≤ (42396883585321/100000000000000 : ℝ)^4575
        have hw : |(4960103713/10000000000 : ℝ)|=(4960103713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1739_s0_1 (p : ℝ) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5385040297/10000000000 : ℝ)*x 0 + (-1612654657/10000000000 : ℝ)*x 1 + (2480052009/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5385040297/10000000000 : ℝ)^5599 ≤ (46883744359933/100000000000000 : ℝ)^4575 := by
    have hnat : (5385040297 : ℕ)^5599*100000000000000^4575 ≤ 46883744359933^4575*10000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385040297 10000000000 46883744359933 100000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1612654657/10000000000 : ℝ)^5599 ≤ (334980276539/3125000000000 : ℝ)^4575 := by
    have hnat : (1612654657 : ℕ)^5599*3125000000000^4575 ≤ 334980276539^4575*10000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1612654657 10000000000 334980276539 3125000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2480052009/5000000000 : ℝ)^5599 ≤ (42396886775847/100000000000000 : ℝ)^4575 := by
    have hnat : (2480052009 : ℕ)^5599*100000000000000^4575 ≤ 42396886775847^4575*5000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2480052009 5000000000 42396886775847 100000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5599/1024 : ℝ)) 5599 4575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5385040297/10000000000 : ℝ), (-1612654657/10000000000 : ℝ), (2480052009/5000000000 : ℝ)] ![(46883744359933/100000000000000 : ℝ), (334980276539/3125000000000 : ℝ), (42396886775847/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5385040297/10000000000 : ℝ)|^5599 ≤ (46883744359933/100000000000000 : ℝ)^4575
        have hw : |(5385040297/10000000000 : ℝ)|=(5385040297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1612654657/10000000000 : ℝ)|^5599 ≤ (334980276539/3125000000000 : ℝ)^4575
        have hw : |(-1612654657/10000000000 : ℝ)|=(1612654657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2480052009/5000000000 : ℝ)|^5599 ≤ (42396886775847/100000000000000 : ℝ)^4575
        have hw : |(2480052009/5000000000 : ℝ)|=(2480052009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1739_s0_2 (p : ℝ) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5385039469/10000000000 : ℝ)*x 0 + (4960104737/10000000000 : ℝ)*x 1 + (-1612654817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5385039469/10000000000 : ℝ)^5599 ≤ (46883735537609/100000000000000 : ℝ)^4575 := by
    have hnat : (5385039469 : ℕ)^5599*100000000000000^4575 ≤ 46883735537609^4575*10000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385039469 10000000000 46883735537609 100000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4960104737/10000000000 : ℝ)^5599 ≤ (21198447148561/50000000000000 : ℝ)^4575 := by
    have hnat : (4960104737 : ℕ)^5599*50000000000000^4575 ≤ 21198447148561^4575*10000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4960104737 10000000000 21198447148561 50000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1612654817/10000000000 : ℝ)^5599 ≤ (10719370150817/100000000000000 : ℝ)^4575 := by
    have hnat : (1612654817 : ℕ)^5599*100000000000000^4575 ≤ 10719370150817^4575*10000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1612654817 10000000000 10719370150817 100000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5599/1024 : ℝ)) 5599 4575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5385039469/10000000000 : ℝ), (4960104737/10000000000 : ℝ), (-1612654817/10000000000 : ℝ)] ![(46883735537609/100000000000000 : ℝ), (21198447148561/50000000000000 : ℝ), (10719370150817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5385039469/10000000000 : ℝ)|^5599 ≤ (46883735537609/100000000000000 : ℝ)^4575
        have hw : |(5385039469/10000000000 : ℝ)|=(5385039469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4960104737/10000000000 : ℝ)|^5599 ≤ (21198447148561/50000000000000 : ℝ)^4575
        have hw : |(4960104737/10000000000 : ℝ)|=(4960104737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1612654817/10000000000 : ℝ)|^5599 ≤ (10719370150817/100000000000000 : ℝ)^4575
        have hw : |(-1612654817/10000000000 : ℝ)|=(1612654817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1739_s0_3 (p : ℝ) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3994058911/10000000000 : ℝ)*x 0 + (743491911/2500000000 : ℝ)*x 1 + (1037846843/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3994058911/10000000000 : ℝ)^5599 ≤ (32523779253147/100000000000000 : ℝ)^4575 := by
    have hnat : (3994058911 : ℕ)^5599*100000000000000^4575 ≤ 32523779253147^4575*10000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3994058911 10000000000 32523779253147 100000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (743491911/2500000000 : ℝ)^5599 ≤ (22670215630471/100000000000000 : ℝ)^4575 := by
    have hnat : (743491911 : ℕ)^5599*100000000000000^4575 ≤ 22670215630471^4575*2500000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      743491911 2500000000 22670215630471 100000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1037846843/2000000000 : ℝ)^5599 ≤ (22403002554867/50000000000000 : ℝ)^4575 := by
    have hnat : (1037846843 : ℕ)^5599*50000000000000^4575 ≤ 22403002554867^4575*2000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037846843 2000000000 22403002554867 50000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5599/1024 : ℝ)) 5599 4575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3994058911/10000000000 : ℝ), (743491911/2500000000 : ℝ), (1037846843/2000000000 : ℝ)] ![(32523779253147/100000000000000 : ℝ), (22670215630471/100000000000000 : ℝ), (22403002554867/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3994058911/10000000000 : ℝ)|^5599 ≤ (32523779253147/100000000000000 : ℝ)^4575
        have hw : |(3994058911/10000000000 : ℝ)|=(3994058911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(743491911/2500000000 : ℝ)|^5599 ≤ (22670215630471/100000000000000 : ℝ)^4575
        have hw : |(743491911/2500000000 : ℝ)|=(743491911/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1037846843/2000000000 : ℝ)|^5599 ≤ (22403002554867/50000000000000 : ℝ)^4575
        have hw : |(1037846843/2000000000 : ℝ)|=(1037846843/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1739_s0_4 (p : ℝ) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-24669049/200000000 : ℝ)*x 0 + (2489202599/5000000000 : ℝ)*x 1 + (2823514879/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (24669049/200000000 : ℝ)^5599 ≤ (7721341513513/100000000000000 : ℝ)^4575 := by
    have hnat : (24669049 : ℕ)^5599*100000000000000^4575 ≤ 7721341513513^4575*200000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24669049 200000000 7721341513513 100000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2489202599/5000000000 : ℝ)^5599 ≤ (42588409701073/100000000000000 : ℝ)^4575 := by
    have hnat : (2489202599 : ℕ)^5599*100000000000000^4575 ≤ 42588409701073^4575*5000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2489202599 5000000000 42588409701073 100000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2823514879/5000000000 : ℝ)^5599 ≤ (12422562192623/25000000000000 : ℝ)^4575 := by
    have hnat : (2823514879 : ℕ)^5599*25000000000000^4575 ≤ 12422562192623^4575*5000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2823514879 5000000000 12422562192623 25000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5599/1024 : ℝ)) 5599 4575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-24669049/200000000 : ℝ), (2489202599/5000000000 : ℝ), (2823514879/5000000000 : ℝ)] ![(7721341513513/100000000000000 : ℝ), (42588409701073/100000000000000 : ℝ), (12422562192623/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-24669049/200000000 : ℝ)|^5599 ≤ (7721341513513/100000000000000 : ℝ)^4575
        have hw : |(-24669049/200000000 : ℝ)|=(24669049/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2489202599/5000000000 : ℝ)|^5599 ≤ (42588409701073/100000000000000 : ℝ)^4575
        have hw : |(2489202599/5000000000 : ℝ)|=(2489202599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2823514879/5000000000 : ℝ)|^5599 ≤ (12422562192623/25000000000000 : ℝ)^4575
        have hw : |(2823514879/5000000000 : ℝ)|=(2823514879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1739_s0_5 (p : ℝ) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5195788151/10000000000 : ℝ)*x 0 + (-185145997/2000000000 : ℝ)*x 1 + (352939397/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5195788151/10000000000 : ℝ)^5599 ≤ (11218817608709/25000000000000 : ℝ)^4575 := by
    have hnat : (5195788151 : ℕ)^5599*25000000000000^4575 ≤ 11218817608709^4575*10000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195788151 10000000000 11218817608709 25000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (185145997/2000000000 : ℝ)^5599 ≤ (5434474374543/100000000000000 : ℝ)^4575 := by
    have hnat : (185145997 : ℕ)^5599*100000000000000^4575 ≤ 5434474374543^4575*2000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      185145997 2000000000 5434474374543 100000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (352939397/625000000 : ℝ)^5599 ≤ (24845127583603/50000000000000 : ℝ)^4575 := by
    have hnat : (352939397 : ℕ)^5599*50000000000000^4575 ≤ 24845127583603^4575*625000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      352939397 625000000 24845127583603 50000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5599/1024 : ℝ)) 5599 4575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5195788151/10000000000 : ℝ), (-185145997/2000000000 : ℝ), (352939397/625000000 : ℝ)] ![(11218817608709/25000000000000 : ℝ), (5434474374543/100000000000000 : ℝ), (24845127583603/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5195788151/10000000000 : ℝ)|^5599 ≤ (11218817608709/25000000000000 : ℝ)^4575
        have hw : |(5195788151/10000000000 : ℝ)|=(5195788151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-185145997/2000000000 : ℝ)|^5599 ≤ (5434474374543/100000000000000 : ℝ)^4575
        have hw : |(-185145997/2000000000 : ℝ)|=(185145997/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(352939397/625000000 : ℝ)|^5599 ≤ (24845127583603/50000000000000 : ℝ)^4575
        have hw : |(352939397/625000000 : ℝ)|=(352939397/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1739_s0_6 (p : ℝ) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1039157853/2000000000 : ℝ)*x 0 + (1129405843/2000000000 : ℝ)*x 1 + (-231432513/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1039157853/2000000000 : ℝ)^5599 ≤ (44875282209817/100000000000000 : ℝ)^4575 := by
    have hnat : (1039157853 : ℕ)^5599*100000000000000^4575 ≤ 44875282209817^4575*2000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039157853 2000000000 44875282209817 100000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1129405843/2000000000 : ℝ)^5599 ≤ (49690242922991/100000000000000 : ℝ)^4575 := by
    have hnat : (1129405843 : ℕ)^5599*100000000000000^4575 ≤ 49690242922991^4575*2000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1129405843 2000000000 49690242922991 100000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (231432513/2500000000 : ℝ)^5599 ≤ (54344748559/1000000000000 : ℝ)^4575 := by
    have hnat : (231432513 : ℕ)^5599*1000000000000^4575 ≤ 54344748559^4575*2500000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      231432513 2500000000 54344748559 1000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5599/1024 : ℝ)) 5599 4575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1039157853/2000000000 : ℝ), (1129405843/2000000000 : ℝ), (-231432513/2500000000 : ℝ)] ![(44875282209817/100000000000000 : ℝ), (49690242922991/100000000000000 : ℝ), (54344748559/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1039157853/2000000000 : ℝ)|^5599 ≤ (44875282209817/100000000000000 : ℝ)^4575
        have hw : |(1039157853/2000000000 : ℝ)|=(1039157853/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1129405843/2000000000 : ℝ)|^5599 ≤ (49690242922991/100000000000000 : ℝ)^4575
        have hw : |(1129405843/2000000000 : ℝ)|=(1129405843/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-231432513/2500000000 : ℝ)|^5599 ≤ (54344748559/1000000000000 : ℝ)^4575
        have hw : |(-231432513/2500000000 : ℝ)|=(231432513/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1739_s0_7 (p : ℝ) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (999786087/2500000000 : ℝ)*x 0 + (1026359831/2000000000 : ℝ)*x 1 + (758344489/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (999786087/2500000000 : ℝ)^5599 ≤ (32574466189841/100000000000000 : ℝ)^4575 := by
    have hnat : (999786087 : ℕ)^5599*100000000000000^4575 ≤ 32574466189841^4575*2500000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      999786087 2500000000 32574466189841 100000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1026359831/2000000000 : ℝ)^5599 ≤ (22099920951331/50000000000000 : ℝ)^4575 := by
    have hnat : (1026359831 : ℕ)^5599*50000000000000^4575 ≤ 22099920951331^4575*2000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026359831 2000000000 22099920951331 50000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (758344489/2500000000 : ℝ)^5599 ≤ (5806422971427/25000000000000 : ℝ)^4575 := by
    have hnat : (758344489 : ℕ)^5599*25000000000000^4575 ≤ 5806422971427^4575*2500000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      758344489 2500000000 5806422971427 25000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5599/1024 : ℝ)) 5599 4575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(999786087/2500000000 : ℝ), (1026359831/2000000000 : ℝ), (758344489/2500000000 : ℝ)] ![(32574466189841/100000000000000 : ℝ), (22099920951331/50000000000000 : ℝ), (5806422971427/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(999786087/2500000000 : ℝ)|^5599 ≤ (32574466189841/100000000000000 : ℝ)^4575
        have hw : |(999786087/2500000000 : ℝ)|=(999786087/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1026359831/2000000000 : ℝ)|^5599 ≤ (22099920951331/50000000000000 : ℝ)^4575
        have hw : |(1026359831/2000000000 : ℝ)|=(1026359831/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(758344489/2500000000 : ℝ)|^5599 ≤ (5806422971427/25000000000000 : ℝ)^4575
        have hw : |(758344489/2500000000 : ℝ)|=(758344489/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1739_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (25865111/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (6249/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4293/20000 : ℝ)*pair X 0 0 := by
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
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
  have base37 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 1 2+(1 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 2).2]
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
  have hpowlo : (0 : ℝ) ^ (5583/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5583 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5583*1^1024 ≤ 0^1024*1^5583 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5583 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5583 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5583/1024 : ℝ) ≤ (135332467137690117/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5583 ≤ (135332467137690117/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5583*20000000000000000000^1024 ≤ 135332467137690117^1024*5^5583 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 135332467137690117 20000000000000000000 5583 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (135332467137690117/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5583 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5583/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5583 := by
      have hnat : (1 : ℕ)^1024*1^5583 ≤ 1^5583*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5583 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5583 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20135332467137690117/20000000000000000000 : ℝ) ≤ (10012376781517869/10000000000000000 : ℝ) ^ (5583/1024 : ℝ) := by
    have hpowers : (20135332467137690117/20000000000000000000 : ℝ)^1024 ≤ (10012376781517869/10000000000000000 : ℝ)^5583 := by
      have hnat : (20135332467137690117 : ℕ)^1024*10000000000000000^5583 ≤ 10012376781517869^5583*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20135332467137690117 20000000000000000000 10012376781517869 10000000000000000 1024 5583 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10012376781517869/10000000000000000 : ℝ)) (X := (20135332467137690117/20000000000000000000 : ℝ)) (by norm_num) 5583 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10135332467137690117/10000000000000000000 : ℝ) ≤ (5012376781517869/5000000000000000 : ℝ) ^ (5583/1024 : ℝ) := by
    have hpowers : (10135332467137690117/10000000000000000000 : ℝ)^1024 ≤ (5012376781517869/5000000000000000 : ℝ)^5583 := by
      have hnat : (10135332467137690117 : ℕ)^1024*5000000000000000^5583 ≤ 5012376781517869^5583*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10135332467137690117 10000000000000000000 5012376781517869 5000000000000000 1024 5583 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5012376781517869/5000000000000000 : ℝ)) (X := (10135332467137690117/10000000000000000000 : ℝ)) (by norm_num) 5583 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(12376781517869/4000000000000000 : ℝ)*(0 : ℝ))^(5583/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(12376781517869/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(135332467137690117/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(12376781517869/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5583/1024 : ℝ) := by
    rw [show (1 : ℝ)+(12376781517869/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10012376781517869/10000000000000000 : ℝ) by norm_num, show 1+(135332467137690117/20000000000000000000 : ℝ)+(0 : ℝ)=(20135332467137690117/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(135332467137690117/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(12376781517869/4000000000000000 : ℝ)*(2/5 : ℝ))^(5583/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(12376781517869/4000000000000000 : ℝ)*(2/5 : ℝ)=(5012376781517869/5000000000000000 : ℝ) by norm_num, show 1+2*(135332467137690117/20000000000000000000 : ℝ)=(10135332467137690117/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(12376781517869/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5583/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (12376781517869/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(12376781517869/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5583/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (12376781517869/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(12376781517869/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5583/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (12376781517869/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-307958383/2500000000 : ℝ)*X 0 0+(1416489839/2500000000 : ℝ)*X 0 1+(4960103713/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1739_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5385040297/10000000000 : ℝ)*X 1 0+(-1612654657/10000000000 : ℝ)*X 1 1+(2480052009/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1739_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5385039469/10000000000 : ℝ)*X 2 0+(4960104737/10000000000 : ℝ)*X 2 1+(-1612654817/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1739_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((3994058911/10000000000 : ℝ)*X 0 0+(743491911/2500000000 : ℝ)*X 0 1+(1037846843/2000000000 : ℝ)*X 0 2+(3994058911/10000000000 : ℝ)*X 1 0+(743491911/2500000000 : ℝ)*X 1 1+(1037846843/2000000000 : ℝ)*X 1 2+(3994058911/10000000000 : ℝ)*X 2 0+(743491911/2500000000 : ℝ)*X 2 1+(1037846843/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1739_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-24669049/200000000 : ℝ)*X 0 0+(2489202599/5000000000 : ℝ)*X 0 1+(2823514879/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1739_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5195788151/10000000000 : ℝ)*X 1 0+(-185145997/2000000000 : ℝ)*X 1 1+(352939397/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1739_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1039157853/2000000000 : ℝ)*X 2 0+(1129405843/2000000000 : ℝ)*X 2 1+(-231432513/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1739_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((999786087/2500000000 : ℝ)*X 0 0+(1026359831/2000000000 : ℝ)*X 0 1+(758344489/2500000000 : ℝ)*X 0 2+(999786087/2500000000 : ℝ)*X 1 0+(1026359831/2000000000 : ℝ)*X 1 1+(758344489/2500000000 : ℝ)*X 1 2+(999786087/2500000000 : ℝ)*X 2 0+(1026359831/2000000000 : ℝ)*X 2 1+(758344489/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1739_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (40902110619014832772119/6250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (46743653/100000000000000 : ℝ)*(base1) + (285751587/20000000000000 : ℝ)*(base19) + (605461021/50000000000000 : ℝ)*(base23) + (291662347/100000000000000 : ℝ)*(upper3) + (182127269/100000000000000 : ℝ)*(upper5) + (58379732105667/6250000000000 : ℝ)*(major0) + (58379732105667/6250000000000 : ℝ)*(major1) + (58379732105667/6250000000000 : ℝ)*(major2) + (177090987188883/12500000000000 : ℝ)*(sp0) + (1416732950250117/100000000000000 : ℝ)*(sp1) + (141673316808601/10000000000000 : ℝ)*(sp2) + (9028293814923/2000000000000 : ℝ)*(sp3) + (6528240641/100000000000000 : ℝ)*(sp4) + (2092738893/100000000000000 : ℝ)*(sp7) + (451416830228697/100000000000000 : ℝ)*(f.failure) + (1416734379008051/100000000000000 : ℝ)*(f.sum) + (5054370213623/12500000000000000000000000000 : ℝ)*base65 + (41800561261377/25000000000000000000000000000 : ℝ)*base68 + (43859755036377/25000000000000000000000000000 : ℝ)*base70 + (20275402588623/25000000000000000000000000000 : ℝ)*base71 + (44143257661377/12500000000000000000000000000 : ℝ)*base74 + (51852119936377/25000000000000000000000000000 : ℝ)*base76 + (51206304063623/25000000000000000000000000000 : ℝ)*base77 + (99072127961377/25000000000000000000000000000 : ℝ)*base80 + (17855678186377/12500000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (3290367/1250000000000000000000 : ℝ)*base89 + (3290367/1250000000000000000000 : ℝ)*base91 + (3290367/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (866857483321195596344709/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (252041103/100000000000000 : ℝ)*(base19) + (147714141/25000000000000 : ℝ)*(base23) + (500465319/100000000000000 : ℝ)*(base32) + (129855431/100000000000000 : ℝ)*(base37) + (116140481/100000000000000 : ℝ)*(upper3) + (986077573802929/100000000000000 : ℝ)*(major0) + (986077573802929/100000000000000 : ℝ)*(major1) + (986077573802929/100000000000000 : ℝ)*(major2) + (1199710703/100000000000000 : ℝ)*(sp1) + (1698047937/100000000000000 : ℝ)*(sp2) + (747803376055911/50000000000000 : ℝ)*(sp4) + (93475331272501/6250000000000 : ℝ)*(sp5) + (1495604463207321/100000000000000 : ℝ)*(sp6) + (95309495244157/20000000000000 : ℝ)*(sp7) + (238274053270767/50000000000000 : ℝ)*(f.failure) + (747803376055911/50000000000000 : ℝ)*(f.sum) + (246142557961699/200000000000000000000000000000 : ℝ)*base66 + (874935674361699/400000000000000000000000000000 : ℝ)*base68 + (3437786516361699/400000000000000000000000000000 : ℝ)*base70 + (522357656761699/400000000000000000000000000000 : ℝ)*base72 + (144433310761699/200000000000000000000000000000 : ℝ)*base74 + (2273591000361699/400000000000000000000000000000 : ℝ)*base76 + (264783781161699/400000000000000000000000000000 : ℝ)*base78 + (128379605561699/400000000000000000000000000000 : ℝ)*base80 + (1393929149761699/200000000000000000000000000000 : ℝ)*base82 + (4739863/625000000000000000000 : ℝ)*base90 + (4739863/625000000000000000000 : ℝ)*base92 + (4739863/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1739_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (25865111/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6249/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4293/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1739_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1739_s1_0 (p : ℝ) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1284678307/10000000000 : ℝ)*x 0 + (5517735299/10000000000 : ℝ)*x 1 + (2536598619/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1284678307/10000000000 : ℝ)^5599 ≤ (4057795701957/50000000000000 : ℝ)^4575 := by
    have hnat : (1284678307 : ℕ)^5599*50000000000000^4575 ≤ 4057795701957^4575*10000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1284678307 10000000000 4057795701957 50000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5517735299/10000000000 : ℝ)^5599 ≤ (48301481551439/100000000000000 : ℝ)^4575 := by
    have hnat : (5517735299 : ℕ)^5599*100000000000000^4575 ≤ 48301481551439^4575*10000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5517735299 10000000000 48301481551439 100000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2536598619/5000000000 : ℝ)^5599 ≤ (43582927036087/100000000000000 : ℝ)^4575 := by
    have hnat : (2536598619 : ℕ)^5599*100000000000000^4575 ≤ 43582927036087^4575*5000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2536598619 5000000000 43582927036087 100000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5599/1024 : ℝ)) 5599 4575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1284678307/10000000000 : ℝ), (5517735299/10000000000 : ℝ), (2536598619/5000000000 : ℝ)] ![(4057795701957/50000000000000 : ℝ), (48301481551439/100000000000000 : ℝ), (43582927036087/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1284678307/10000000000 : ℝ)|^5599 ≤ (4057795701957/50000000000000 : ℝ)^4575
        have hw : |(-1284678307/10000000000 : ℝ)|=(1284678307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5517735299/10000000000 : ℝ)|^5599 ≤ (48301481551439/100000000000000 : ℝ)^4575
        have hw : |(5517735299/10000000000 : ℝ)|=(5517735299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2536598619/5000000000 : ℝ)|^5599 ≤ (43582927036087/100000000000000 : ℝ)^4575
        have hw : |(2536598619/5000000000 : ℝ)|=(2536598619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1739_s1_1 (p : ℝ) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672764573/5000000000 : ℝ)*x 0 + (-1517933579/10000000000 : ℝ)*x 1 + (2536598503/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672764573/5000000000 : ℝ)^5599 ≤ (1858524004829/4000000000000 : ℝ)^4575 := by
    have hnat : (2672764573 : ℕ)^5599*4000000000000^4575 ≤ 1858524004829^4575*5000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672764573 5000000000 1858524004829 4000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1517933579/10000000000 : ℝ)^5599 ≤ (1990795053613/20000000000000 : ℝ)^4575 := by
    have hnat : (1517933579 : ℕ)^5599*20000000000000^4575 ≤ 1990795053613^4575*10000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1517933579 10000000000 1990795053613 20000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2536598503/5000000000 : ℝ)^5599 ≤ (21791462298459/50000000000000 : ℝ)^4575 := by
    have hnat : (2536598503 : ℕ)^5599*50000000000000^4575 ≤ 21791462298459^4575*5000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2536598503 5000000000 21791462298459 50000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5599/1024 : ℝ)) 5599 4575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672764573/5000000000 : ℝ), (-1517933579/10000000000 : ℝ), (2536598503/5000000000 : ℝ)] ![(1858524004829/4000000000000 : ℝ), (1990795053613/20000000000000 : ℝ), (21791462298459/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672764573/5000000000 : ℝ)|^5599 ≤ (1858524004829/4000000000000 : ℝ)^4575
        have hw : |(2672764573/5000000000 : ℝ)|=(2672764573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1517933579/10000000000 : ℝ)|^5599 ≤ (1990795053613/20000000000000 : ℝ)^4575
        have hw : |(-1517933579/10000000000 : ℝ)|=(1517933579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2536598503/5000000000 : ℝ)|^5599 ≤ (21791462298459/50000000000000 : ℝ)^4575
        have hw : |(2536598503/5000000000 : ℝ)|=(2536598503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1739_s1_2 (p : ℝ) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345528633/10000000000 : ℝ)*x 0 + (634149683/1250000000 : ℝ)*x 1 + (-1517933659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345528633/10000000000 : ℝ)^5599 ≤ (23231547331861/50000000000000 : ℝ)^4575 := by
    have hnat : (5345528633 : ℕ)^5599*50000000000000^4575 ≤ 23231547331861^4575*10000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345528633 10000000000 23231547331861 50000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (634149683/1250000000 : ℝ)^5599 ≤ (1743317176487/4000000000000 : ℝ)^4575 := by
    have hnat : (634149683 : ℕ)^5599*4000000000000^4575 ≤ 1743317176487^4575*1250000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      634149683 1250000000 1743317176487 4000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1517933659/10000000000 : ℝ)^5599 ≤ (2488493977523/25000000000000 : ℝ)^4575 := by
    have hnat : (1517933659 : ℕ)^5599*25000000000000^4575 ≤ 2488493977523^4575*10000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1517933659 10000000000 2488493977523 25000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5599/1024 : ℝ)) 5599 4575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345528633/10000000000 : ℝ), (634149683/1250000000 : ℝ), (-1517933659/10000000000 : ℝ)] ![(23231547331861/50000000000000 : ℝ), (1743317176487/4000000000000 : ℝ), (2488493977523/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345528633/10000000000 : ℝ)|^5599 ≤ (23231547331861/50000000000000 : ℝ)^4575
        have hw : |(5345528633/10000000000 : ℝ)|=(5345528633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(634149683/1250000000 : ℝ)|^5599 ≤ (1743317176487/4000000000000 : ℝ)^4575
        have hw : |(634149683/1250000000 : ℝ)|=(634149683/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1517933659/10000000000 : ℝ)|^5599 ≤ (2488493977523/25000000000000 : ℝ)^4575
        have hw : |(-1517933659/10000000000 : ℝ)|=(1517933659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1739_s1_3 (p : ℝ) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4043179423/10000000000 : ℝ)*x 0 + (3380086609/10000000000 : ℝ)*x 1 + (955046297/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4043179423/10000000000 : ℝ)^5599 ≤ (33013969009593/100000000000000 : ℝ)^4575 := by
    have hnat : (4043179423 : ℕ)^5599*100000000000000^4575 ≤ 33013969009593^4575*10000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4043179423 10000000000 33013969009593 100000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3380086609/10000000000 : ℝ)^5599 ≤ (6628725638089/25000000000000 : ℝ)^4575 := by
    have hnat : (3380086609 : ℕ)^5599*25000000000000^4575 ≤ 6628725638089^4575*10000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3380086609 10000000000 6628725638089 25000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (955046297/2000000000 : ℝ)^5599 ≤ (404711284263/1000000000000 : ℝ)^4575 := by
    have hnat : (955046297 : ℕ)^5599*1000000000000^4575 ≤ 404711284263^4575*2000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      955046297 2000000000 404711284263 1000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5599/1024 : ℝ)) 5599 4575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4043179423/10000000000 : ℝ), (3380086609/10000000000 : ℝ), (955046297/2000000000 : ℝ)] ![(33013969009593/100000000000000 : ℝ), (6628725638089/25000000000000 : ℝ), (404711284263/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4043179423/10000000000 : ℝ)|^5599 ≤ (33013969009593/100000000000000 : ℝ)^4575
        have hw : |(4043179423/10000000000 : ℝ)|=(4043179423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3380086609/10000000000 : ℝ)|^5599 ≤ (6628725638089/25000000000000 : ℝ)^4575
        have hw : |(3380086609/10000000000 : ℝ)|=(3380086609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(955046297/2000000000 : ℝ)|^5599 ≤ (404711284263/1000000000000 : ℝ)^4575
        have hw : |(955046297/2000000000 : ℝ)|=(955046297/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1739_s1_4 (p : ℝ) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1285081261/10000000000 : ℝ)*x 0 + (1270113361/2500000000 : ℝ)*x 1 + (2755160591/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1285081261/10000000000 : ℝ)^5599 ≤ (8118706818627/100000000000000 : ℝ)^4575 := by
    have hnat : (1285081261 : ℕ)^5599*100000000000000^4575 ≤ 8118706818627^4575*10000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1285081261 10000000000 8118706818627 100000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1270113361/2500000000 : ℝ)^5599 ≤ (43659228541273/100000000000000 : ℝ)^4575 := by
    have hnat : (1270113361 : ℕ)^5599*100000000000000^4575 ≤ 43659228541273^4575*2500000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1270113361 2500000000 43659228541273 100000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2755160591/5000000000 : ℝ)^5599 ≤ (1506939519623/3125000000000 : ℝ)^4575 := by
    have hnat : (2755160591 : ℕ)^5599*3125000000000^4575 ≤ 1506939519623^4575*5000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2755160591 5000000000 1506939519623 3125000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5599/1024 : ℝ)) 5599 4575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1285081261/10000000000 : ℝ), (1270113361/2500000000 : ℝ), (2755160591/5000000000 : ℝ)] ![(8118706818627/100000000000000 : ℝ), (43659228541273/100000000000000 : ℝ), (1506939519623/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1285081261/10000000000 : ℝ)|^5599 ≤ (8118706818627/100000000000000 : ℝ)^4575
        have hw : |(-1285081261/10000000000 : ℝ)|=(1285081261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1270113361/2500000000 : ℝ)|^5599 ≤ (43659228541273/100000000000000 : ℝ)^4575
        have hw : |(1270113361/2500000000 : ℝ)|=(1270113361/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2755160591/5000000000 : ℝ)|^5599 ≤ (1506939519623/3125000000000 : ℝ)^4575
        have hw : |(2755160591/5000000000 : ℝ)|=(2755160591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1739_s1_5 (p : ℝ) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (326710239/625000000 : ℝ)*x 0 + (-67550671/625000000 : ℝ)*x 1 + (1102064179/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (326710239/625000000 : ℝ)^5599 ≤ (22604625976267/50000000000000 : ℝ)^4575 := by
    have hnat : (326710239 : ℕ)^5599*50000000000000^4575 ≤ 22604625976267^4575*625000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326710239 625000000 22604625976267 50000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (67550671/625000000 : ℝ)^5599 ≤ (6568686475539/100000000000000 : ℝ)^4575 := by
    have hnat : (67550671 : ℕ)^5599*100000000000000^4575 ≤ 6568686475539^4575*625000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67550671 625000000 6568686475539 100000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1102064179/2000000000 : ℝ)^5599 ≤ (1928882462167/4000000000000 : ℝ)^4575 := by
    have hnat : (1102064179 : ℕ)^5599*4000000000000^4575 ≤ 1928882462167^4575*2000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102064179 2000000000 1928882462167 4000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5599/1024 : ℝ)) 5599 4575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(326710239/625000000 : ℝ), (-67550671/625000000 : ℝ), (1102064179/2000000000 : ℝ)] ![(22604625976267/50000000000000 : ℝ), (6568686475539/100000000000000 : ℝ), (1928882462167/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(326710239/625000000 : ℝ)|^5599 ≤ (22604625976267/50000000000000 : ℝ)^4575
        have hw : |(326710239/625000000 : ℝ)|=(326710239/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-67550671/625000000 : ℝ)|^5599 ≤ (6568686475539/100000000000000 : ℝ)^4575
        have hw : |(-67550671/625000000 : ℝ)|=(67550671/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1102064179/2000000000 : ℝ)|^5599 ≤ (1928882462167/4000000000000 : ℝ)^4575
        have hw : |(1102064179/2000000000 : ℝ)|=(1102064179/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1739_s1_6 (p : ℝ) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5227362971/10000000000 : ℝ)*x 0 + (1102064337/2000000000 : ℝ)*x 1 + (-1080810813/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5227362971/10000000000 : ℝ)^5599 ≤ (45209242924089/100000000000000 : ℝ)^4575 := by
    have hnat : (5227362971 : ℕ)^5599*100000000000000^4575 ≤ 45209242924089^4575*10000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227362971 10000000000 45209242924089 100000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1102064337/2000000000 : ℝ)^5599 ≤ (48222070015051/100000000000000 : ℝ)^4575 := by
    have hnat : (1102064337 : ℕ)^5599*100000000000000^4575 ≤ 48222070015051^4575*2000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102064337 2000000000 48222070015051 100000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1080810813/10000000000 : ℝ)^5599 ≤ (3284343524127/50000000000000 : ℝ)^4575 := by
    have hnat : (1080810813 : ℕ)^5599*50000000000000^4575 ≤ 3284343524127^4575*10000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080810813 10000000000 3284343524127 50000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5599/1024 : ℝ)) 5599 4575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5227362971/10000000000 : ℝ), (1102064337/2000000000 : ℝ), (-1080810813/10000000000 : ℝ)] ![(45209242924089/100000000000000 : ℝ), (48222070015051/100000000000000 : ℝ), (3284343524127/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5227362971/10000000000 : ℝ)|^5599 ≤ (45209242924089/100000000000000 : ℝ)^4575
        have hw : |(5227362971/10000000000 : ℝ)|=(5227362971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1102064337/2000000000 : ℝ)|^5599 ≤ (48222070015051/100000000000000 : ℝ)^4575
        have hw : |(1102064337/2000000000 : ℝ)|=(1102064337/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1080810813/10000000000 : ℝ)|^5599 ≤ (3284343524127/50000000000000 : ℝ)^4575
        have hw : |(-1080810813/10000000000 : ℝ)|=(1080810813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1739_s1_7 (p : ℝ) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (40444353/100000000 : ℝ)*x 0 + (4752453817/10000000000 : ℝ)*x 1 + (680671497/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (40444353/100000000 : ℝ)^5599 ≤ (16513259686427/50000000000000 : ℝ)^4575 := by
    have hnat : (40444353 : ℕ)^5599*50000000000000^4575 ≤ 16513259686427^4575*100000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40444353 100000000 16513259686427 50000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4752453817/10000000000 : ℝ)^5599 ≤ (8047000102657/20000000000000 : ℝ)^4575 := by
    have hnat : (4752453817 : ℕ)^5599*20000000000000^4575 ≤ 8047000102657^4575*10000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4752453817 10000000000 8047000102657 20000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (680671497/2000000000 : ℝ)^5599 ≤ (26738480107319/100000000000000 : ℝ)^4575 := by
    have hnat : (680671497 : ℕ)^5599*100000000000000^4575 ≤ 26738480107319^4575*2000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      680671497 2000000000 26738480107319 100000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5599/1024 : ℝ)) 5599 4575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(40444353/100000000 : ℝ), (4752453817/10000000000 : ℝ), (680671497/2000000000 : ℝ)] ![(16513259686427/50000000000000 : ℝ), (8047000102657/20000000000000 : ℝ), (26738480107319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(40444353/100000000 : ℝ)|^5599 ≤ (16513259686427/50000000000000 : ℝ)^4575
        have hw : |(40444353/100000000 : ℝ)|=(40444353/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4752453817/10000000000 : ℝ)|^5599 ≤ (8047000102657/20000000000000 : ℝ)^4575
        have hw : |(4752453817/10000000000 : ℝ)|=(4752453817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(680671497/2000000000 : ℝ)|^5599 ≤ (26738480107319/100000000000000 : ℝ)^4575
        have hw : |(680671497/2000000000 : ℝ)|=(680671497/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1739_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (25865111/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4293/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6249/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (879/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9153/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4293/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6249/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4293/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6249/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4293/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6249/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4293/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6249/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4293/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6249/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4293/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6249/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6249/100000 : ℝ) ^ (5583/1024 : ℝ) ≤ (6800177396061/25000000000000000000 : ℝ) := by
    have hpowers : (6249/100000 : ℝ)^5583 ≤ (6800177396061/25000000000000000000 : ℝ)^1024 := by
      have hnat : (6249 : ℕ)^5583*25000000000000000000^1024 ≤ 6800177396061^1024*100000^5583 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6249 100000 6800177396061 25000000000000000000 5583 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6249/100000 : ℝ)) (X := (6800177396061/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5583 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4293/20000 : ℝ) ^ (5583/1024 : ℝ) ≤ (22724672416003819/100000000000000000000 : ℝ) := by
    have hpowers : (4293/20000 : ℝ)^5583 ≤ (22724672416003819/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4293 : ℕ)^5583*100000000000000000000^1024 ≤ 22724672416003819^1024*20000^5583 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4293 20000 22724672416003819 100000000000000000000 5583 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4293/20000 : ℝ)) (X := (22724672416003819/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5583 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500006800177396061/12500000000000000000 : ℝ) ≤ (625000062362351/625000000000000 : ℝ) ^ (5583/1024 : ℝ) := by
    have hpowers : (12500006800177396061/12500000000000000000 : ℝ)^1024 ≤ (625000062362351/625000000000000 : ℝ)^5583 := by
      have hnat : (12500006800177396061 : ℕ)^1024*625000000000000^5583 ≤ 625000062362351^5583*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500006800177396061 12500000000000000000 625000062362351 625000000000000 1024 5583 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625000062362351/625000000000000 : ℝ)) (X := (12500006800177396061/12500000000000000000 : ℝ)) (by norm_num) 5583 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100022751873125588063/100000000000000000000 : ℝ) ≤ (2500104315574667/2500000000000000 : ℝ) ^ (5583/1024 : ℝ) := by
    have hpowers : (100022751873125588063/100000000000000000000 : ℝ)^1024 ≤ (2500104315574667/2500000000000000 : ℝ)^5583 := by
      have hnat : (100022751873125588063 : ℕ)^1024*2500000000000000^5583 ≤ 2500104315574667^5583*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100022751873125588063 100000000000000000000 2500104315574667 2500000000000000 1024 5583 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500104315574667/2500000000000000 : ℝ)) (X := (100022751873125588063/100000000000000000000 : ℝ)) (by norm_num) 5583 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50022724672416003819/50000000000000000000 : ℝ) ≤ (250020838169993/250000000000000 : ℝ) ^ (5583/1024 : ℝ) := by
    have hpowers : (50022724672416003819/50000000000000000000 : ℝ)^1024 ≤ (250020838169993/250000000000000 : ℝ)^5583 := by
      have hnat : (50022724672416003819 : ℕ)^1024*250000000000000^5583 ≤ 250020838169993^5583*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022724672416003819 50000000000000000000 250020838169993 250000000000000 1024 5583 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250020838169993/250000000000000 : ℝ)) (X := (50022724672416003819/50000000000000000000 : ℝ)) (by norm_num) 5583 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6800177396061/25000000000000000000 : ℝ) ≤ ((1267956772572953143/1268000000000000000 : ℝ)+2*(34688708421/126800000000000 : ℝ)*(6249/100000 : ℝ))^(5583/1024 : ℝ) := by
    rw [show (1267956772572953143/1268000000000000000 : ℝ)+2*(34688708421/126800000000000 : ℝ)*(6249/100000 : ℝ)=(625000062362351/625000000000000 : ℝ) by norm_num, show 1+2*(6800177396061/25000000000000000000 : ℝ)=(12500006800177396061/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(22724672416003819/100000000000000000000 : ℝ)+(6800177396061/25000000000000000000 : ℝ) ≤ ((1267956772572953143/1268000000000000000 : ℝ)+(34688708421/126800000000000 : ℝ)*((4293/20000 : ℝ)+(6249/100000 : ℝ)))^(5583/1024 : ℝ) := by
    rw [show (1267956772572953143/1268000000000000000 : ℝ)+(34688708421/126800000000000 : ℝ)*((4293/20000 : ℝ)+(6249/100000 : ℝ))=(2500104315574667/2500000000000000 : ℝ) by norm_num, show 1+(22724672416003819/100000000000000000000 : ℝ)+(6800177396061/25000000000000000000 : ℝ)=(100022751873125588063/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(22724672416003819/100000000000000000000 : ℝ) ≤ ((1267956772572953143/1268000000000000000 : ℝ)+2*(34688708421/126800000000000 : ℝ)*(4293/20000 : ℝ))^(5583/1024 : ℝ) := by
    rw [show (1267956772572953143/1268000000000000000 : ℝ)+2*(34688708421/126800000000000 : ℝ)*(4293/20000 : ℝ)=(250020838169993/250000000000000 : ℝ) by norm_num, show 1+2*(22724672416003819/100000000000000000000 : ℝ)=(50022724672416003819/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1267956772572953143/1268000000000000000 : ℝ)*(X 1 0+X 2 0)+(34688708421/126800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5583/1024 : ℝ)) (lo := (6249/100000 : ℝ)) (hi := (4293/20000 : ℝ)) (c := (1267956772572953143/1268000000000000000 : ℝ)) (alpha := (34688708421/126800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1267956772572953143/1268000000000000000 : ℝ)*(X 0 1+X 2 1)+(34688708421/126800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5583/1024 : ℝ)) (lo := (6249/100000 : ℝ)) (hi := (4293/20000 : ℝ)) (c := (1267956772572953143/1268000000000000000 : ℝ)) (alpha := (34688708421/126800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1267956772572953143/1268000000000000000 : ℝ)*(X 0 2+X 1 2)+(34688708421/126800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5583/1024 : ℝ)) (lo := (6249/100000 : ℝ)) (hi := (4293/20000 : ℝ)) (c := (1267956772572953143/1268000000000000000 : ℝ)) (alpha := (34688708421/126800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1284678307/10000000000 : ℝ)*X 0 0+(5517735299/10000000000 : ℝ)*X 0 1+(2536598619/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1739_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672764573/5000000000 : ℝ)*X 1 0+(-1517933579/10000000000 : ℝ)*X 1 1+(2536598503/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1739_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345528633/10000000000 : ℝ)*X 2 0+(634149683/1250000000 : ℝ)*X 2 1+(-1517933659/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1739_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4043179423/10000000000 : ℝ)*X 0 0+(3380086609/10000000000 : ℝ)*X 0 1+(955046297/2000000000 : ℝ)*X 0 2+(4043179423/10000000000 : ℝ)*X 1 0+(3380086609/10000000000 : ℝ)*X 1 1+(955046297/2000000000 : ℝ)*X 1 2+(4043179423/10000000000 : ℝ)*X 2 0+(3380086609/10000000000 : ℝ)*X 2 1+(955046297/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1739_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1285081261/10000000000 : ℝ)*X 0 0+(1270113361/2500000000 : ℝ)*X 0 1+(2755160591/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1739_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((326710239/625000000 : ℝ)*X 1 0+(-67550671/625000000 : ℝ)*X 1 1+(1102064179/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1739_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5227362971/10000000000 : ℝ)*X 2 0+(1102064337/2000000000 : ℝ)*X 2 1+(-1080810813/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1739_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((40444353/100000000 : ℝ)*X 0 0+(4752453817/10000000000 : ℝ)*X 0 1+(680671497/2000000000 : ℝ)*X 0 2+(40444353/100000000 : ℝ)*X 1 0+(4752453817/10000000000 : ℝ)*X 1 1+(680671497/2000000000 : ℝ)*X 1 2+(40444353/100000000 : ℝ)*X 2 0+(4752453817/10000000000 : ℝ)*X 2 1+(680671497/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1739_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (904657510614731012525067/247656250000000000000000000000 : ℝ) := by norm_num
    linear_combination (650582007/100000000000000 : ℝ)*(base19) + (390967177/100000000000000 : ℝ)*(base23) + (22810939/50000000000000 : ℝ)*(lower2) + (51455839/50000000000000 : ℝ)*(upper3) + (11122579/50000000000000 : ℝ)*(lower4) + (23174290965889/1562500000000 : ℝ)*(major0) + (23174290965889/1562500000000 : ℝ)*(major1) + (23174290965889/1562500000000 : ℝ)*(major2) + (562382895236621/25000000000000 : ℝ)*(sp0) + (1124767357414891/50000000000000 : ℝ)*(sp1) + (562383743611153/25000000000000 : ℝ)*(sp2) + (143354482463367/20000000000000 : ℝ)*(sp3) + (473058163/12500000000000 : ℝ)*(sp4) + (1344142637/100000000000000 : ℝ)*(sp7) + (44798359778717/6250000000000 : ℝ)*(f.failure) + (2249535365411789/100000000000000 : ℝ)*(f.sum) + (17078852655901/1585000000000000000000000000 : ℝ)*base66 + (2367620457795873/1981250000000000000000000000000 : ℝ)*base68 + (2573897913220873/1981250000000000000000000000000 : ℝ)*base70 + (16765552111527123/1981250000000000000000000000000 : ℝ)*base72 + (880886061403/792500000000000000000000000 : ℝ)*base74 + (3786724403995873/1981250000000000000000000000000 : ℝ)*base76 + (14009136511577123/1981250000000000000000000000000 : ℝ)*base78 + (7132166667120873/1981250000000000000000000000000 : ℝ)*base80 + (2167433054929/396250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (642587/78125000000000000000 : ℝ)*base89 + (642587/78125000000000000000 : ℝ)*base91 + (642587/78125000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (328013049616543471008587913/31700000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (594621633/50000000000000 : ℝ)*(base19) + (1852665091/100000000000000 : ℝ)*(base23) + (551079653/100000000000000 : ℝ)*(upper2) + (24571147/25000000000000 : ℝ)*(upper3) + (684558789/100000000000000 : ℝ)*(upper5) + (766883083392203/50000000000000 : ℝ)*(major0) + (766883083392203/50000000000000 : ℝ)*(major1) + (766883083392203/50000000000000 : ℝ)*(major2) + (527428707/6250000000000 : ℝ)*(sp1) + (7943615511/100000000000000 : ℝ)*(sp2) + (1163149431251363/50000000000000 : ℝ)*(sp4) + (581572308600037/25000000000000 : ℝ)*(sp5) + (581572266555531/25000000000000 : ℝ)*(sp6) + (148246625230451/20000000000000 : ℝ)*(sp7) + (148246625230451/20000000000000 : ℝ)*(f.failure) + (1163149431251363/50000000000000 : ℝ)*(f.sum) + (12825760517083/3170000000000000000000000000 : ℝ)*base65 + (116041102176574029/63400000000000000000000000000000 : ℝ)*base67 + (649097050938625971/63400000000000000000000000000000 : ℝ)*base70 + (158104259028425971/63400000000000000000000000000000 : ℝ)*base72 + (1333569835433/3170000000000000000000000000 : ℝ)*base73 + (149833598381374029/63400000000000000000000000000000 : ℝ)*base75 + (465305191757374029/63400000000000000000000000000000 : ℝ)*base77 + (145576962196574029/63400000000000000000000000000000 : ℝ)*base79 + (14977938909917/3170000000000000000000000000 : ℝ)*base82 + (695061/250000000000000000000 : ℝ)*base89 + (695061/250000000000000000000 : ℝ)*base91 + (695061/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1739_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (25865111/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4293/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6249/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (879/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9153/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1739_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1739_s2_0 (p : ℝ) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-643167913/5000000000 : ℝ)*x 0 + (2756223167/5000000000 : ℝ)*x 1 + (79333853/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (643167913/5000000000 : ℝ)^5599 ≤ (8128407812683/100000000000000 : ℝ)^4575 := by
    have hnat : (643167913 : ℕ)^5599*100000000000000^4575 ≤ 8128407812683^4575*5000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      643167913 5000000000 8128407812683 100000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2756223167/5000000000 : ℝ)^5599 ≤ (48244825924471/100000000000000 : ℝ)^4575 := by
    have hnat : (2756223167 : ℕ)^5599*100000000000000^4575 ≤ 48244825924471^4575*5000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2756223167 5000000000 48244825924471 100000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (79333853/156250000 : ℝ)^5599 ≤ (21813383123077/50000000000000 : ℝ)^4575 := by
    have hnat : (79333853 : ℕ)^5599*50000000000000^4575 ≤ 21813383123077^4575*156250000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79333853 156250000 21813383123077 50000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5599/1024 : ℝ)) 5599 4575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-643167913/5000000000 : ℝ), (2756223167/5000000000 : ℝ), (79333853/156250000 : ℝ)] ![(8128407812683/100000000000000 : ℝ), (48244825924471/100000000000000 : ℝ), (21813383123077/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-643167913/5000000000 : ℝ)|^5599 ≤ (8128407812683/100000000000000 : ℝ)^4575
        have hw : |(-643167913/5000000000 : ℝ)|=(643167913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2756223167/5000000000 : ℝ)|^5599 ≤ (48244825924471/100000000000000 : ℝ)^4575
        have hw : |(2756223167/5000000000 : ℝ)|=(2756223167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(79333853/156250000 : ℝ)|^5599 ≤ (21813383123077/50000000000000 : ℝ)^4575
        have hw : |(79333853/156250000 : ℝ)|=(79333853/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1739_s2_1 (p : ℝ) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672037479/5000000000 : ℝ)*x 0 + (-1514396629/10000000000 : ℝ)*x 1 + (5077367021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672037479/5000000000 : ℝ)^5599 ≤ (23223815881907/50000000000000 : ℝ)^4575 := by
    have hnat : (2672037479 : ℕ)^5599*50000000000000^4575 ≤ 23223815881907^4575*5000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672037479 5000000000 23223815881907 50000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1514396629/10000000000 : ℝ)^5599 ≤ (1985119493331/20000000000000 : ℝ)^4575 := by
    have hnat : (1514396629 : ℕ)^5599*20000000000000^4575 ≤ 1985119493331^4575*10000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1514396629 10000000000 1985119493331 20000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5077367021/10000000000 : ℝ)^5599 ≤ (1363336586167/3125000000000 : ℝ)^4575 := by
    have hnat : (5077367021 : ℕ)^5599*3125000000000^4575 ≤ 1363336586167^4575*10000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5077367021 10000000000 1363336586167 3125000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5599/1024 : ℝ)) 5599 4575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672037479/5000000000 : ℝ), (-1514396629/10000000000 : ℝ), (5077367021/10000000000 : ℝ)] ![(23223815881907/50000000000000 : ℝ), (1985119493331/20000000000000 : ℝ), (1363336586167/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672037479/5000000000 : ℝ)|^5599 ≤ (23223815881907/50000000000000 : ℝ)^4575
        have hw : |(2672037479/5000000000 : ℝ)|=(2672037479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1514396629/10000000000 : ℝ)|^5599 ≤ (1985119493331/20000000000000 : ℝ)^4575
        have hw : |(-1514396629/10000000000 : ℝ)|=(1514396629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5077367021/10000000000 : ℝ)|^5599 ≤ (1363336586167/3125000000000 : ℝ)^4575
        have hw : |(5077367021/10000000000 : ℝ)|=(5077367021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1739_s2_2 (p : ℝ) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336018733/2500000000 : ℝ)*x 0 + (5077364683/10000000000 : ℝ)*x 1 + (-94649983/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336018733/2500000000 : ℝ)^5599 ≤ (46447631487257/100000000000000 : ℝ)^4575 := by
    have hnat : (1336018733 : ℕ)^5599*100000000000000^4575 ≤ 46447631487257^4575*2500000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336018733 2500000000 46447631487257 100000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5077364683/10000000000 : ℝ)^5599 ≤ (43626746171883/100000000000000 : ℝ)^4575 := by
    have hnat : (5077364683 : ℕ)^5599*100000000000000^4575 ≤ 43626746171883^4575*10000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5077364683 10000000000 43626746171883 100000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (94649983/625000000 : ℝ)^5599 ≤ (992562232419/10000000000000 : ℝ)^4575 := by
    have hnat : (94649983 : ℕ)^5599*10000000000000^4575 ≤ 992562232419^4575*625000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94649983 625000000 992562232419 10000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5599/1024 : ℝ)) 5599 4575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336018733/2500000000 : ℝ), (5077364683/10000000000 : ℝ), (-94649983/625000000 : ℝ)] ![(46447631487257/100000000000000 : ℝ), (43626746171883/100000000000000 : ℝ), (992562232419/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336018733/2500000000 : ℝ)|^5599 ≤ (46447631487257/100000000000000 : ℝ)^4575
        have hw : |(1336018733/2500000000 : ℝ)|=(1336018733/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5077364683/10000000000 : ℝ)|^5599 ≤ (43626746171883/100000000000000 : ℝ)^4575
        have hw : |(5077364683/10000000000 : ℝ)|=(5077364683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-94649983/625000000 : ℝ)|^5599 ≤ (992562232419/10000000000000 : ℝ)^4575
        have hw : |(-94649983/625000000 : ℝ)|=(94649983/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1739_s2_3 (p : ℝ) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (808905859/2000000000 : ℝ)*x 0 + (1697409869/5000000000 : ℝ)*x 1 + (190411297/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (808905859/2000000000 : ℝ)^5599 ≤ (33027458728749/100000000000000 : ℝ)^4575 := by
    have hnat : (808905859 : ℕ)^5599*100000000000000^4575 ≤ 33027458728749^4575*2000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      808905859 2000000000 33027458728749 100000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1697409869/5000000000 : ℝ)^5599 ≤ (5331282575467/20000000000000 : ℝ)^4575 := by
    have hnat : (1697409869 : ℕ)^5599*20000000000000^4575 ≤ 5331282575467^4575*5000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1697409869 5000000000 5331282575467 20000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (190411297/400000000 : ℝ)^5599 ≤ (1259879011801/3125000000000 : ℝ)^4575 := by
    have hnat : (190411297 : ℕ)^5599*3125000000000^4575 ≤ 1259879011801^4575*400000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      190411297 400000000 1259879011801 3125000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5599/1024 : ℝ)) 5599 4575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(808905859/2000000000 : ℝ), (1697409869/5000000000 : ℝ), (190411297/400000000 : ℝ)] ![(33027458728749/100000000000000 : ℝ), (5331282575467/20000000000000 : ℝ), (1259879011801/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(808905859/2000000000 : ℝ)|^5599 ≤ (33027458728749/100000000000000 : ℝ)^4575
        have hw : |(808905859/2000000000 : ℝ)|=(808905859/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1697409869/5000000000 : ℝ)|^5599 ≤ (5331282575467/20000000000000 : ℝ)^4575
        have hw : |(1697409869/5000000000 : ℝ)|=(1697409869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(190411297/400000000 : ℝ)|^5599 ≤ (1259879011801/3125000000000 : ℝ)^4575
        have hw : |(190411297/400000000 : ℝ)|=(190411297/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1739_s2_4 (p : ℝ) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-643355669/5000000000 : ℝ)*x 0 + (5084319227/10000000000 : ℝ)*x 1 + (5505347269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (643355669/5000000000 : ℝ)^5599 ≤ (508206993259/6250000000000 : ℝ)^4575 := by
    have hnat : (643355669 : ℕ)^5599*6250000000000^4575 ≤ 508206993259^4575*5000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      643355669 5000000000 508206993259 6250000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5084319227/10000000000 : ℝ)^5599 ≤ (43699888543333/100000000000000 : ℝ)^4575 := by
    have hnat : (5084319227 : ℕ)^5599*100000000000000^4575 ≤ 43699888543333^4575*10000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5084319227 10000000000 43699888543333 100000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5505347269/10000000000 : ℝ)^5599 ≤ (48168799551219/100000000000000 : ℝ)^4575 := by
    have hnat : (5505347269 : ℕ)^5599*100000000000000^4575 ≤ 48168799551219^4575*10000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5505347269 10000000000 48168799551219 100000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5599/1024 : ℝ)) 5599 4575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-643355669/5000000000 : ℝ), (5084319227/10000000000 : ℝ), (5505347269/10000000000 : ℝ)] ![(508206993259/6250000000000 : ℝ), (43699888543333/100000000000000 : ℝ), (48168799551219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-643355669/5000000000 : ℝ)|^5599 ≤ (508206993259/6250000000000 : ℝ)^4575
        have hw : |(-643355669/5000000000 : ℝ)|=(643355669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5084319227/10000000000 : ℝ)|^5599 ≤ (43699888543333/100000000000000 : ℝ)^4575
        have hw : |(5084319227/10000000000 : ℝ)|=(5084319227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5505347269/10000000000 : ℝ)|^5599 ≤ (48168799551219/100000000000000 : ℝ)^4575
        have hw : |(5505347269/10000000000 : ℝ)|=(5505347269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1739_s2_5 (p : ℝ) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1307113471/2500000000 : ℝ)*x 0 + (-1086417149/10000000000 : ℝ)*x 1 + (5505347293/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1307113471/2500000000 : ℝ)^5599 ≤ (9044157958443/20000000000000 : ℝ)^4575 := by
    have hnat : (1307113471 : ℕ)^5599*20000000000000^4575 ≤ 9044157958443^4575*2500000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307113471 2500000000 9044157958443 20000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1086417149/10000000000 : ℝ)^5599 ≤ (3305205194891/50000000000000 : ℝ)^4575 := by
    have hnat : (1086417149 : ℕ)^5599*50000000000000^4575 ≤ 3305205194891^4575*10000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086417149 10000000000 3305205194891 50000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5505347293/10000000000 : ℝ)^5599 ≤ (24084399904103/50000000000000 : ℝ)^4575 := by
    have hnat : (5505347293 : ℕ)^5599*50000000000000^4575 ≤ 24084399904103^4575*10000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5505347293 10000000000 24084399904103 50000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5599/1024 : ℝ)) 5599 4575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1307113471/2500000000 : ℝ), (-1086417149/10000000000 : ℝ), (5505347293/10000000000 : ℝ)] ![(9044157958443/20000000000000 : ℝ), (3305205194891/50000000000000 : ℝ), (24084399904103/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1307113471/2500000000 : ℝ)|^5599 ≤ (9044157958443/20000000000000 : ℝ)^4575
        have hw : |(1307113471/2500000000 : ℝ)|=(1307113471/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1086417149/10000000000 : ℝ)|^5599 ≤ (3305205194891/50000000000000 : ℝ)^4575
        have hw : |(-1086417149/10000000000 : ℝ)|=(1086417149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5505347293/10000000000 : ℝ)|^5599 ≤ (24084399904103/50000000000000 : ℝ)^4575
        have hw : |(5505347293/10000000000 : ℝ)|=(5505347293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1739_s2_6 (p : ℝ) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5228453913/10000000000 : ℝ)*x 0 + (5505347273/10000000000 : ℝ)*x 1 + (-217283427/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5228453913/10000000000 : ℝ)^5599 ≤ (1808831603967/4000000000000 : ℝ)^4575 := by
    have hnat : (5228453913 : ℕ)^5599*4000000000000^4575 ≤ 1808831603967^4575*10000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5228453913 10000000000 1808831603967 4000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5505347273/10000000000 : ℝ)^5599 ≤ (963375991881/2000000000000 : ℝ)^4575 := by
    have hnat : (5505347273 : ℕ)^5599*2000000000000^4575 ≤ 963375991881^4575*10000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5505347273 10000000000 963375991881 2000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (217283427/2000000000 : ℝ)^5599 ≤ (6610410285531/100000000000000 : ℝ)^4575 := by
    have hnat : (217283427 : ℕ)^5599*100000000000000^4575 ≤ 6610410285531^4575*2000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217283427 2000000000 6610410285531 100000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5599/1024 : ℝ)) 5599 4575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5228453913/10000000000 : ℝ), (5505347273/10000000000 : ℝ), (-217283427/2000000000 : ℝ)] ![(1808831603967/4000000000000 : ℝ), (963375991881/2000000000000 : ℝ), (6610410285531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5228453913/10000000000 : ℝ)|^5599 ≤ (1808831603967/4000000000000 : ℝ)^4575
        have hw : |(5228453913/10000000000 : ℝ)|=(5228453913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5505347273/10000000000 : ℝ)|^5599 ≤ (963375991881/2000000000000 : ℝ)^4575
        have hw : |(5505347273/10000000000 : ℝ)|=(5505347273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-217283427/2000000000 : ℝ)|^5599 ≤ (6610410285531/100000000000000 : ℝ)^4575
        have hw : |(-217283427/2000000000 : ℝ)|=(217283427/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1739_s2_7 (p : ℝ) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4045707623/10000000000 : ℝ)*x 0 + (473846263/1000000000 : ℝ)*x 1 + (3417100713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4045707623/10000000000 : ℝ)^5599 ≤ (33039234975543/100000000000000 : ℝ)^4575 := by
    have hnat : (4045707623 : ℕ)^5599*100000000000000^4575 ≤ 33039234975543^4575*10000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4045707623 10000000000 33039234975543 100000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (473846263/1000000000 : ℝ)^5599 ≤ (1603603374143/4000000000000 : ℝ)^4575 := by
    have hnat : (473846263 : ℕ)^5599*4000000000000^4575 ≤ 1603603374143^4575*1000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      473846263 1000000000 1603603374143 4000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3417100713/10000000000 : ℝ)^5599 ≤ (13435340332179/50000000000000 : ℝ)^4575 := by
    have hnat : (3417100713 : ℕ)^5599*50000000000000^4575 ≤ 13435340332179^4575*10000000000^5599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3417100713 10000000000 13435340332179 50000000000000 5599 4575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5599/1024 : ℝ)) 5599 4575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4045707623/10000000000 : ℝ), (473846263/1000000000 : ℝ), (3417100713/10000000000 : ℝ)] ![(33039234975543/100000000000000 : ℝ), (1603603374143/4000000000000 : ℝ), (13435340332179/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4045707623/10000000000 : ℝ)|^5599 ≤ (33039234975543/100000000000000 : ℝ)^4575
        have hw : |(4045707623/10000000000 : ℝ)|=(4045707623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(473846263/1000000000 : ℝ)|^5599 ≤ (1603603374143/4000000000000 : ℝ)^4575
        have hw : |(473846263/1000000000 : ℝ)|=(473846263/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3417100713/10000000000 : ℝ)|^5599 ≤ (13435340332179/50000000000000 : ℝ)^4575
        have hw : |(3417100713/10000000000 : ℝ)|=(3417100713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1739_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (25865111/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9153/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (879/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (4441/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9097/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9153/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (879/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9153/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (879/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9153/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (879/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9153/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (879/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9153/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (879/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9153/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (879/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (879/10000 : ℝ) ^ (5583/1024 : ℝ) ≤ (10923218287423/6250000000000000000 : ℝ) := by
    have hpowers : (879/10000 : ℝ)^5583 ≤ (10923218287423/6250000000000000000 : ℝ)^1024 := by
      have hnat : (879 : ℕ)^5583*6250000000000000000^1024 ≤ 10923218287423^1024*10000^5583 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        879 10000 10923218287423 6250000000000000000 5583 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (879/10000 : ℝ)) (X := (10923218287423/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 5583 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (9153/50000 : ℝ) ^ (5583/1024 : ℝ) ≤ (9540037336156983/100000000000000000000 : ℝ) := by
    have hpowers : (9153/50000 : ℝ)^5583 ≤ (9540037336156983/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9153 : ℕ)^5583*100000000000000000000^1024 ≤ 9540037336156983^1024*50000^5583 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9153 50000 9540037336156983 100000000000000000000 5583 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9153/50000 : ℝ)) (X := (9540037336156983/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5583 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125010923218287423/3125000000000000000 : ℝ) ≤ (10000006411096293/10000000000000000 : ℝ) ^ (5583/1024 : ℝ) := by
    have hpowers : (3125010923218287423/3125000000000000000 : ℝ)^1024 ≤ (10000006411096293/10000000000000000 : ℝ)^5583 := by
      have hnat : (3125010923218287423 : ℕ)^1024*10000000000000000^5583 ≤ 10000006411096293^5583*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125010923218287423 3125000000000000000 10000006411096293 10000000000000000 1024 5583 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000006411096293/10000000000000000 : ℝ)) (X := (3125010923218287423/3125000000000000000 : ℝ)) (by norm_num) 5583 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100009714808828755751/100000000000000000000 : ℝ) ≤ (625011136004029/625000000000000 : ℝ) ^ (5583/1024 : ℝ) := by
    have hpowers : (100009714808828755751/100000000000000000000 : ℝ)^1024 ≤ (625011136004029/625000000000000 : ℝ)^5583 := by
      have hnat : (100009714808828755751 : ℕ)^1024*625000000000000^5583 ≤ 625011136004029^5583*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100009714808828755751 100000000000000000000 625011136004029 625000000000000 1024 5583 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625011136004029/625000000000000 : ℝ)) (X := (100009714808828755751/100000000000000000000 : ℝ)) (by norm_num) 5583 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50009540037336156983/50000000000000000000 : ℝ) ≤ (2000069988206527/2000000000000000 : ℝ) ^ (5583/1024 : ℝ) := by
    have hpowers : (50009540037336156983/50000000000000000000 : ℝ)^1024 ≤ (2000069988206527/2000000000000000 : ℝ)^5583 := by
      have hnat : (50009540037336156983 : ℕ)^1024*2000000000000000^5583 ≤ 2000069988206527^5583*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009540037336156983 50000000000000000000 2000069988206527 2000000000000000 1024 5583 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000069988206527/2000000000000000 : ℝ)) (X := (50009540037336156983/50000000000000000000 : ℝ)) (by norm_num) 5583 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10923218287423/6250000000000000000 : ℝ) ≤ ((3964876724160494917/3965000000000000000 : ℝ)+2*(171764968171/951600000000000 : ℝ)*(879/10000 : ℝ))^(5583/1024 : ℝ) := by
    rw [show (3964876724160494917/3965000000000000000 : ℝ)+2*(171764968171/951600000000000 : ℝ)*(879/10000 : ℝ)=(10000006411096293/10000000000000000 : ℝ) by norm_num, show 1+2*(10923218287423/6250000000000000000 : ℝ)=(3125010923218287423/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9540037336156983/100000000000000000000 : ℝ)+(10923218287423/6250000000000000000 : ℝ) ≤ ((3964876724160494917/3965000000000000000 : ℝ)+(171764968171/951600000000000 : ℝ)*((9153/50000 : ℝ)+(879/10000 : ℝ)))^(5583/1024 : ℝ) := by
    rw [show (3964876724160494917/3965000000000000000 : ℝ)+(171764968171/951600000000000 : ℝ)*((9153/50000 : ℝ)+(879/10000 : ℝ))=(625011136004029/625000000000000 : ℝ) by norm_num, show 1+(9540037336156983/100000000000000000000 : ℝ)+(10923218287423/6250000000000000000 : ℝ)=(100009714808828755751/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9540037336156983/100000000000000000000 : ℝ) ≤ ((3964876724160494917/3965000000000000000 : ℝ)+2*(171764968171/951600000000000 : ℝ)*(9153/50000 : ℝ))^(5583/1024 : ℝ) := by
    rw [show (3964876724160494917/3965000000000000000 : ℝ)+2*(171764968171/951600000000000 : ℝ)*(9153/50000 : ℝ)=(2000069988206527/2000000000000000 : ℝ) by norm_num, show 1+2*(9540037336156983/100000000000000000000 : ℝ)=(50009540037336156983/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3964876724160494917/3965000000000000000 : ℝ)*(X 1 0+X 2 0)+(171764968171/951600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5583/1024 : ℝ)) (lo := (879/10000 : ℝ)) (hi := (9153/50000 : ℝ)) (c := (3964876724160494917/3965000000000000000 : ℝ)) (alpha := (171764968171/951600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3964876724160494917/3965000000000000000 : ℝ)*(X 0 1+X 2 1)+(171764968171/951600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5583/1024 : ℝ)) (lo := (879/10000 : ℝ)) (hi := (9153/50000 : ℝ)) (c := (3964876724160494917/3965000000000000000 : ℝ)) (alpha := (171764968171/951600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3964876724160494917/3965000000000000000 : ℝ)*(X 0 2+X 1 2)+(171764968171/951600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5583/1024 : ℝ)) (lo := (879/10000 : ℝ)) (hi := (9153/50000 : ℝ)) (c := (3964876724160494917/3965000000000000000 : ℝ)) (alpha := (171764968171/951600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-643167913/5000000000 : ℝ)*X 0 0+(2756223167/5000000000 : ℝ)*X 0 1+(79333853/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1739_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672037479/5000000000 : ℝ)*X 1 0+(-1514396629/10000000000 : ℝ)*X 1 1+(5077367021/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1739_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336018733/2500000000 : ℝ)*X 2 0+(5077364683/10000000000 : ℝ)*X 2 1+(-94649983/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1739_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((808905859/2000000000 : ℝ)*X 0 0+(1697409869/5000000000 : ℝ)*X 0 1+(190411297/400000000 : ℝ)*X 0 2+(808905859/2000000000 : ℝ)*X 1 0+(1697409869/5000000000 : ℝ)*X 1 1+(190411297/400000000 : ℝ)*X 1 2+(808905859/2000000000 : ℝ)*X 2 0+(1697409869/5000000000 : ℝ)*X 2 1+(190411297/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1739_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-643355669/5000000000 : ℝ)*X 0 0+(5084319227/10000000000 : ℝ)*X 0 1+(5505347269/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1739_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1307113471/2500000000 : ℝ)*X 1 0+(-1086417149/10000000000 : ℝ)*X 1 1+(5505347293/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1739_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5228453913/10000000000 : ℝ)*X 2 0+(5505347273/10000000000 : ℝ)*X 2 1+(-217283427/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1739_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4045707623/10000000000 : ℝ)*X 0 0+(473846263/1000000000 : ℝ)*X 0 1+(3417100713/10000000000 : ℝ)*X 0 2+(4045707623/10000000000 : ℝ)*X 1 0+(473846263/1000000000 : ℝ)*X 1 1+(3417100713/10000000000 : ℝ)*X 1 2+(4045707623/10000000000 : ℝ)*X 2 0+(473846263/1000000000 : ℝ)*X 2 1+(3417100713/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1739_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (343890650583777294956524123/99125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (281025243/25000000000000 : ℝ)*(base19) + (174493549/20000000000000 : ℝ)*(base23) + (149251871/50000000000000 : ℝ)*(upper3) + (1183729/4000000000000 : ℝ)*(lower4) + (1515405213131377/100000000000000 : ℝ)*(major0) + (1515405213131377/100000000000000 : ℝ)*(major1) + (1515405213131377/100000000000000 : ℝ)*(major2) + (143652646439453/6250000000000 : ℝ)*(sp0) + (574612369390269/25000000000000 : ℝ)*(sp1) + (114921802795361/5000000000000 : ℝ)*(sp2) + (183088886136783/25000000000000 : ℝ)*(sp3) + (8258630799/100000000000000 : ℝ)*(sp4) + (6836643541/50000000000000 : ℝ)*(sp6) + (104110287/2500000000000 : ℝ)*(sp7) + (732359708958613/100000000000000 : ℝ)*(f.failure) + (71826581301939/3125000000000 : ℝ)*(f.sum) + (107765707750867/47580000000000000000000000000 : ℝ)*base65 + (514155520963382279/91500000000000000000000000000000 : ℝ)*base67 + (735993238924382279/91500000000000000000000000000000 : ℝ)*base69 + (271106105282882279/91500000000000000000000000000000 : ℝ)*base71 + (126126023650507/47580000000000000000000000000 : ℝ)*base73 + (108960752259117721/91500000000000000000000000000000 : ℝ)*base76 + (892580867315882279/91500000000000000000000000000000 : ℝ)*base77 + (637458959111882279/91500000000000000000000000000000 : ℝ)*base79 + (179173769847667/47580000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (7151043/1250000000000000000000 : ℝ)*base89 + (7151043/1250000000000000000000 : ℝ)*base91 + (7151043/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (154456443247924305870624519/19825000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (258736523/25000000000000 : ℝ)*(base19) + (9024241/800000000000 : ℝ)*(base23) + (174215831/100000000000000 : ℝ)*(upper3) + (34397277/100000000000000 : ℝ)*(lower4) + (10340527/6250000000000 : ℝ)*(upper5) + (156596671001769/10000000000000 : ℝ)*(major0) + (156596671001769/10000000000000 : ℝ)*(major1) + (156596671001769/10000000000000 : ℝ)*(major2) + (3465776877/50000000000000 : ℝ)*(sp1) + (1514028377/20000000000000 : ℝ)*(sp2) + (23751382687451/1000000000000 : ℝ)*(sp4) + (2375130302245253/100000000000000 : ℝ)*(sp5) + (2375129570573089/100000000000000 : ℝ)*(sp6) + (151358978318099/20000000000000 : ℝ)*(sp7) + (151358978318099/20000000000000 : ℝ)*(f.failure) + (23751382687451/1000000000000 : ℝ)*(f.sum) + (3783611823023/1586000000000000000000000000 : ℝ)*base65 + (23756981913429179/3050000000000000000000000000000 : ℝ)*base68 + (1462443532679179/3050000000000000000000000000000 : ℝ)*base70 + (2831671188620821/3050000000000000000000000000000 : ℝ)*base71 + (2487215373949/1586000000000000000000000000 : ℝ)*base74 + (10945368025170821/3050000000000000000000000000000 : ℝ)*base75 + (4474814545029179/3050000000000000000000000000000 : ℝ)*base78 + (4478987372029179/3050000000000000000000000000000 : ℝ)*base80 + (7067050439793/1586000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (1056011/250000000000000000000 : ℝ)*base90 + (1056011/250000000000000000000 : ℝ)*base92 + (1056011/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1739_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (25865111/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9153/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (879/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4441/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9097/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1739_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1739_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (25865111/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4441/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9097/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1739_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1739_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1739_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5583/1024 : ℝ) ≤ p) (hpb : p ≤ (5599/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (25865111/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4441/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9097/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1739_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
