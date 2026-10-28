-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1075_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:12:58.356981+00:00
-- url     : https://prove2.me/submissions/2cd3febf-5cd7-431e-b015-9886483567c3

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
theorem support_rectangle_w1075_s0_0 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1913199387/10000000000 : ℝ)*x 0 + (6069945243/10000000000 : ℝ)*x 1 + (2385970171/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1913199387/10000000000 : ℝ)^2067 ≤ (2774676096147/25000000000000 : ℝ)^1555 := by
    have hnat : (1913199387 : ℕ)^2067*25000000000000^1555 ≤ 2774676096147^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1913199387 10000000000 2774676096147 25000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6069945243/10000000000 : ℝ)^2067 ≤ (51498679610513/100000000000000 : ℝ)^1555 := by
    have hnat : (6069945243 : ℕ)^2067*100000000000000^1555 ≤ 51498679610513^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6069945243 10000000000 51498679610513 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2385970171/5000000000 : ℝ)^2067 ≤ (37402615992933/100000000000000 : ℝ)^1555 := by
    have hnat : (2385970171 : ℕ)^2067*100000000000000^1555 ≤ 37402615992933^1555*5000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2385970171 5000000000 37402615992933 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1913199387/10000000000 : ℝ), (6069945243/10000000000 : ℝ), (2385970171/5000000000 : ℝ)] ![(2774676096147/25000000000000 : ℝ), (51498679610513/100000000000000 : ℝ), (37402615992933/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1913199387/10000000000 : ℝ)|^2067 ≤ (2774676096147/25000000000000 : ℝ)^1555
        have hw : |(-1913199387/10000000000 : ℝ)|=(1913199387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6069945243/10000000000 : ℝ)|^2067 ≤ (51498679610513/100000000000000 : ℝ)^1555
        have hw : |(6069945243/10000000000 : ℝ)|=(6069945243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2385970171/5000000000 : ℝ)|^2067 ≤ (37402615992933/100000000000000 : ℝ)^1555
        have hw : |(2385970171/5000000000 : ℝ)|=(2385970171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_s0_1 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (345035393/625000000 : ℝ)*x 0 + (-1330034847/5000000000 : ℝ)*x 1 + (2385970413/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (345035393/625000000 : ℝ)^2067 ≤ (9079439481867/20000000000000 : ℝ)^1555 := by
    have hnat : (345035393 : ℕ)^2067*20000000000000^1555 ≤ 9079439481867^1555*625000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      345035393 625000000 9079439481867 20000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1330034847/5000000000 : ℝ)^2067 ≤ (17200181537973/100000000000000 : ℝ)^1555 := by
    have hnat : (1330034847 : ℕ)^2067*100000000000000^1555 ≤ 17200181537973^1555*5000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1330034847 5000000000 17200181537973 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2385970413/5000000000 : ℝ)^2067 ≤ (4675327629453/12500000000000 : ℝ)^1555 := by
    have hnat : (2385970413 : ℕ)^2067*12500000000000^1555 ≤ 4675327629453^1555*5000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2385970413 5000000000 4675327629453 12500000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(345035393/625000000 : ℝ), (-1330034847/5000000000 : ℝ), (2385970413/5000000000 : ℝ)] ![(9079439481867/20000000000000 : ℝ), (17200181537973/100000000000000 : ℝ), (4675327629453/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(345035393/625000000 : ℝ)|^2067 ≤ (9079439481867/20000000000000 : ℝ)^1555
        have hw : |(345035393/625000000 : ℝ)|=(345035393/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1330034847/5000000000 : ℝ)|^2067 ≤ (17200181537973/100000000000000 : ℝ)^1555
        have hw : |(-1330034847/5000000000 : ℝ)|=(1330034847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2385970413/5000000000 : ℝ)|^2067 ≤ (4675327629453/12500000000000 : ℝ)^1555
        have hw : |(2385970413/5000000000 : ℝ)|=(2385970413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_s0_2 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5520565687/10000000000 : ℝ)*x 0 + (2385970749/5000000000 : ℝ)*x 1 + (-665017411/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5520565687/10000000000 : ℝ)^2067 ≤ (4539719083987/10000000000000 : ℝ)^1555 := by
    have hnat : (5520565687 : ℕ)^2067*10000000000000^1555 ≤ 4539719083987^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5520565687 10000000000 4539719083987 10000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2385970749/5000000000 : ℝ)^2067 ≤ (4675328504631/12500000000000 : ℝ)^1555 := by
    have hnat : (2385970749 : ℕ)^2067*12500000000000^1555 ≤ 4675328504631^1555*5000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2385970749 5000000000 4675328504631 12500000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (665017411/2500000000 : ℝ)^2067 ≤ (17200181108219/100000000000000 : ℝ)^1555 := by
    have hnat : (665017411 : ℕ)^2067*100000000000000^1555 ≤ 17200181108219^1555*2500000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      665017411 2500000000 17200181108219 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5520565687/10000000000 : ℝ), (2385970749/5000000000 : ℝ), (-665017411/2500000000 : ℝ)] ![(4539719083987/10000000000000 : ℝ), (4675328504631/12500000000000 : ℝ), (17200181108219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5520565687/10000000000 : ℝ)|^2067 ≤ (4539719083987/10000000000000 : ℝ)^1555
        have hw : |(5520565687/10000000000 : ℝ)|=(5520565687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2385970749/5000000000 : ℝ)|^2067 ≤ (4675328504631/12500000000000 : ℝ)^1555
        have hw : |(2385970749/5000000000 : ℝ)|=(2385970749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-665017411/2500000000 : ℝ)|^2067 ≤ (17200181108219/100000000000000 : ℝ)^1555
        have hw : |(-665017411/2500000000 : ℝ)|=(665017411/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_s0_3 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (525808289/1250000000 : ℝ)*x 0 + (781097229/2500000000 : ℝ)*x 1 + (5672844211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (525808289/1250000000 : ℝ)^2067 ≤ (31629206305289/100000000000000 : ℝ)^1555 := by
    have hnat : (525808289 : ℕ)^2067*100000000000000^1555 ≤ 31629206305289^1555*1250000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525808289 1250000000 31629206305289 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (781097229/2500000000 : ℝ)^2067 ≤ (21301550399799/100000000000000 : ℝ)^1555 := by
    have hnat : (781097229 : ℕ)^2067*100000000000000^1555 ≤ 21301550399799^1555*2500000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      781097229 2500000000 21301550399799 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5672844211/10000000000 : ℝ)^2067 ≤ (11767310821713/25000000000000 : ℝ)^1555 := by
    have hnat : (5672844211 : ℕ)^2067*25000000000000^1555 ≤ 11767310821713^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5672844211 10000000000 11767310821713 25000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(525808289/1250000000 : ℝ), (781097229/2500000000 : ℝ), (5672844211/10000000000 : ℝ)] ![(31629206305289/100000000000000 : ℝ), (21301550399799/100000000000000 : ℝ), (11767310821713/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(525808289/1250000000 : ℝ)|^2067 ≤ (31629206305289/100000000000000 : ℝ)^1555
        have hw : |(525808289/1250000000 : ℝ)|=(525808289/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(781097229/2500000000 : ℝ)|^2067 ≤ (21301550399799/100000000000000 : ℝ)^1555
        have hw : |(781097229/2500000000 : ℝ)|=(781097229/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5672844211/10000000000 : ℝ)|^2067 ≤ (11767310821713/25000000000000 : ℝ)^1555
        have hw : |(5672844211/10000000000 : ℝ)|=(5672844211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_s0_4 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1918544603/10000000000 : ℝ)*x 0 + (4805452731/10000000000 : ℝ)*x 1 + (6035260327/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1918544603/10000000000 : ℝ)^2067 ≤ (11139941376643/100000000000000 : ℝ)^1555 := by
    have hnat : (1918544603 : ℕ)^2067*100000000000000^1555 ≤ 11139941376643^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1918544603 10000000000 11139941376643 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4805452731/10000000000 : ℝ)^2067 ≤ (1510087096221/4000000000000 : ℝ)^1555 := by
    have hnat : (4805452731 : ℕ)^2067*4000000000000^1555 ≤ 1510087096221^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4805452731 10000000000 1510087096221 4000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6035260327/10000000000 : ℝ)^2067 ≤ (51107881206957/100000000000000 : ℝ)^1555 := by
    have hnat : (6035260327 : ℕ)^2067*100000000000000^1555 ≤ 51107881206957^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6035260327 10000000000 51107881206957 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1918544603/10000000000 : ℝ), (4805452731/10000000000 : ℝ), (6035260327/10000000000 : ℝ)] ![(11139941376643/100000000000000 : ℝ), (1510087096221/4000000000000 : ℝ), (51107881206957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1918544603/10000000000 : ℝ)|^2067 ≤ (11139941376643/100000000000000 : ℝ)^1555
        have hw : |(-1918544603/10000000000 : ℝ)|=(1918544603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4805452731/10000000000 : ℝ)|^2067 ≤ (1510087096221/4000000000000 : ℝ)^1555
        have hw : |(4805452731/10000000000 : ℝ)|=(4805452731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6035260327/10000000000 : ℝ)|^2067 ≤ (51107881206957/100000000000000 : ℝ)^1555
        have hw : |(6035260327/10000000000 : ℝ)|=(6035260327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_s0_5 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2584109211/5000000000 : ℝ)*x 0 + (-69837671/500000000 : ℝ)*x 1 + (1508814561/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2584109211/5000000000 : ℝ)^2067 ≤ (41586784527793/100000000000000 : ℝ)^1555 := by
    have hnat : (2584109211 : ℕ)^2067*100000000000000^1555 ≤ 41586784527793^1555*5000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2584109211 5000000000 41586784527793 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (69837671/500000000 : ℝ)^2067 ≤ (3652678847391/50000000000000 : ℝ)^1555 := by
    have hnat : (69837671 : ℕ)^2067*50000000000000^1555 ≤ 3652678847391^1555*500000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69837671 500000000 3652678847391 50000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1508814561/2500000000 : ℝ)^2067 ≤ (25553928879873/50000000000000 : ℝ)^1555 := by
    have hnat : (1508814561 : ℕ)^2067*50000000000000^1555 ≤ 25553928879873^1555*2500000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1508814561 2500000000 25553928879873 50000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2584109211/5000000000 : ℝ), (-69837671/500000000 : ℝ), (1508814561/2500000000 : ℝ)] ![(41586784527793/100000000000000 : ℝ), (3652678847391/50000000000000 : ℝ), (25553928879873/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2584109211/5000000000 : ℝ)|^2067 ≤ (41586784527793/100000000000000 : ℝ)^1555
        have hw : |(2584109211/5000000000 : ℝ)|=(2584109211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-69837671/500000000 : ℝ)|^2067 ≤ (3652678847391/50000000000000 : ℝ)^1555
        have hw : |(-69837671/500000000 : ℝ)|=(69837671/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1508814561/2500000000 : ℝ)|^2067 ≤ (25553928879873/50000000000000 : ℝ)^1555
        have hw : |(1508814561/2500000000 : ℝ)|=(1508814561/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_s0_6 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5168218317/10000000000 : ℝ)*x 0 + (6035259781/10000000000 : ℝ)*x 1 + (-698375547/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5168218317/10000000000 : ℝ)^2067 ≤ (8317356680941/20000000000000 : ℝ)^1555 := by
    have hnat : (5168218317 : ℕ)^2067*20000000000000^1555 ≤ 8317356680941^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5168218317 10000000000 8317356680941 20000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6035259781/10000000000 : ℝ)^2067 ≤ (798560547827/1562500000000 : ℝ)^1555 := by
    have hnat : (6035259781 : ℕ)^2067*1562500000000^1555 ≤ 798560547827^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6035259781 10000000000 798560547827 1562500000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (698375547/5000000000 : ℝ)^2067 ≤ (7305341523613/100000000000000 : ℝ)^1555 := by
    have hnat : (698375547 : ℕ)^2067*100000000000000^1555 ≤ 7305341523613^1555*5000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      698375547 5000000000 7305341523613 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5168218317/10000000000 : ℝ), (6035259781/10000000000 : ℝ), (-698375547/5000000000 : ℝ)] ![(8317356680941/20000000000000 : ℝ), (798560547827/1562500000000 : ℝ), (7305341523613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5168218317/10000000000 : ℝ)|^2067 ≤ (8317356680941/20000000000000 : ℝ)^1555
        have hw : |(5168218317/10000000000 : ℝ)|=(5168218317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6035259781/10000000000 : ℝ)|^2067 ≤ (798560547827/1562500000000 : ℝ)^1555
        have hw : |(6035259781/10000000000 : ℝ)|=(6035259781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-698375547/5000000000 : ℝ)|^2067 ≤ (7305341523613/100000000000000 : ℝ)^1555
        have hw : |(-698375547/5000000000 : ℝ)|=(698375547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_s0_7 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4216960131/10000000000 : ℝ)*x 0 + (5607045367/10000000000 : ℝ)*x 1 + (1596245727/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4216960131/10000000000 : ℝ)^2067 ≤ (1586706731759/5000000000000 : ℝ)^1555 := by
    have hnat : (4216960131 : ℕ)^2067*5000000000000^1555 ≤ 1586706731759^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4216960131 10000000000 1586706731759 5000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5607045367/10000000000 : ℝ)^2067 ≤ (1853796799927/4000000000000 : ℝ)^1555 := by
    have hnat : (5607045367 : ℕ)^2067*4000000000000^1555 ≤ 1853796799927^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5607045367 10000000000 1853796799927 4000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1596245727/5000000000 : ℝ)^2067 ≤ (1370059084703/6250000000000 : ℝ)^1555 := by
    have hnat : (1596245727 : ℕ)^2067*6250000000000^1555 ≤ 1370059084703^1555*5000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1596245727 5000000000 1370059084703 6250000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4216960131/10000000000 : ℝ), (5607045367/10000000000 : ℝ), (1596245727/5000000000 : ℝ)] ![(1586706731759/5000000000000 : ℝ), (1853796799927/4000000000000 : ℝ), (1370059084703/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4216960131/10000000000 : ℝ)|^2067 ≤ (1586706731759/5000000000000 : ℝ)^1555
        have hw : |(4216960131/10000000000 : ℝ)|=(4216960131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5607045367/10000000000 : ℝ)|^2067 ≤ (1853796799927/4000000000000 : ℝ)^1555
        have hw : |(5607045367/10000000000 : ℝ)|=(5607045367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1596245727/5000000000 : ℝ)|^2067 ≤ (1370059084703/6250000000000 : ℝ)^1555
        have hw : |(1596245727/5000000000 : ℝ)|=(1596245727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1075_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148168151/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (67/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14037/50000 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
  have base45 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [sign1]
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
  have hpowlo : (0 : ℝ) ^ (8267/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8267 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8267*1^2048 ≤ 0^2048*1^8267 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8267 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8267 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8267/2048 : ℝ) ≤ (2475523007101680791/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8267 ≤ (2475523007101680791/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8267*100000000000000000000^2048 ≤ 2475523007101680791^2048*5^8267 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2475523007101680791 100000000000000000000 8267 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2475523007101680791/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8267 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8267/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8267 := by
      have hnat : (1 : ℕ)^2048*1^8267 ≤ 1^8267*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8267 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8267 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (102475523007101680791/100000000000000000000 : ℝ) ≤ (10060763702321091/10000000000000000 : ℝ) ^ (8267/2048 : ℝ) := by
    have hpowers : (102475523007101680791/100000000000000000000 : ℝ)^2048 ≤ (10060763702321091/10000000000000000 : ℝ)^8267 := by
      have hnat : (102475523007101680791 : ℕ)^2048*10000000000000000^8267 ≤ 10060763702321091^8267*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102475523007101680791 100000000000000000000 10060763702321091 10000000000000000 2048 8267 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10060763702321091/10000000000000000 : ℝ)) (X := (102475523007101680791/100000000000000000000 : ℝ)) (by norm_num) 8267 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (52475523007101680791/50000000000000000000 : ℝ) ≤ (5060763702321091/5000000000000000 : ℝ) ^ (8267/2048 : ℝ) := by
    have hpowers : (52475523007101680791/50000000000000000000 : ℝ)^2048 ≤ (5060763702321091/5000000000000000 : ℝ)^8267 := by
      have hnat : (52475523007101680791 : ℕ)^2048*5000000000000000^8267 ≤ 5060763702321091^8267*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52475523007101680791 50000000000000000000 5060763702321091 5000000000000000 2048 8267 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5060763702321091/5000000000000000 : ℝ)) (X := (52475523007101680791/50000000000000000000 : ℝ)) (by norm_num) 8267 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(60763702321091/4000000000000000 : ℝ)*(0 : ℝ))^(8267/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(60763702321091/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2475523007101680791/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(60763702321091/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8267/2048 : ℝ) := by
    rw [show (1 : ℝ)+(60763702321091/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10060763702321091/10000000000000000 : ℝ) by norm_num, show 1+(2475523007101680791/100000000000000000000 : ℝ)+(0 : ℝ)=(102475523007101680791/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2475523007101680791/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(60763702321091/4000000000000000 : ℝ)*(2/5 : ℝ))^(8267/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(60763702321091/4000000000000000 : ℝ)*(2/5 : ℝ)=(5060763702321091/5000000000000000 : ℝ) by norm_num, show 1+2*(2475523007101680791/100000000000000000000 : ℝ)=(52475523007101680791/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(60763702321091/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8267/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (60763702321091/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(60763702321091/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8267/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (60763702321091/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(60763702321091/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8267/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (60763702321091/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1913199387/10000000000 : ℝ)*X 0 0+(6069945243/10000000000 : ℝ)*X 0 1+(2385970171/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((345035393/625000000 : ℝ)*X 1 0+(-1330034847/5000000000 : ℝ)*X 1 1+(2385970413/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5520565687/10000000000 : ℝ)*X 2 0+(2385970749/5000000000 : ℝ)*X 2 1+(-665017411/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((525808289/1250000000 : ℝ)*X 0 0+(781097229/2500000000 : ℝ)*X 0 1+(5672844211/10000000000 : ℝ)*X 0 2+(525808289/1250000000 : ℝ)*X 1 0+(781097229/2500000000 : ℝ)*X 1 1+(5672844211/10000000000 : ℝ)*X 1 2+(525808289/1250000000 : ℝ)*X 2 0+(781097229/2500000000 : ℝ)*X 2 1+(5672844211/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1918544603/10000000000 : ℝ)*X 0 0+(4805452731/10000000000 : ℝ)*X 0 1+(6035260327/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2584109211/5000000000 : ℝ)*X 1 0+(-69837671/500000000 : ℝ)*X 1 1+(1508814561/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5168218317/10000000000 : ℝ)*X 2 0+(6035259781/10000000000 : ℝ)*X 2 1+(-698375547/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4216960131/10000000000 : ℝ)*X 0 0+(5607045367/10000000000 : ℝ)*X 0 1+(1596245727/5000000000 : ℝ)*X 0 2+(4216960131/10000000000 : ℝ)*X 1 0+(5607045367/10000000000 : ℝ)*X 1 1+(1596245727/5000000000 : ℝ)*X 1 2+(4216960131/10000000000 : ℝ)*X 2 0+(5607045367/10000000000 : ℝ)*X 2 1+(1596245727/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (134771921812331747279859/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8099863/50000000000000 : ℝ)*(base1) + (196614313/10000000000000 : ℝ)*(base19) + (863015821/50000000000000 : ℝ)*(base23) + (156238977/100000000000000 : ℝ)*(base24) + (53835531/10000000000000 : ℝ)*(upper3) + (116282467896517/20000000000000 : ℝ)*(major0) + (116282467896517/20000000000000 : ℝ)*(major1) + (116282467896517/20000000000000 : ℝ)*(major2) + (385210006934583/50000000000000 : ℝ)*(sp0) + (770422140652049/100000000000000 : ℝ)*(sp1) + (9630277806557/1250000000000 : ℝ)*(sp2) + (98099159065013/25000000000000 : ℝ)*(sp3) + (4109125739/100000000000000 : ℝ)*(sp4) + (3695090341/100000000000000 : ℝ)*(sp7) + (392400347550119/100000000000000 : ℝ)*(f.failure) + (770424106795179/100000000000000 : ℝ)*(f.sum) + (34407706899953/40000000000000000000000000000 : ℝ)*base66 + (179812948460047/80000000000000000000000000000 : ℝ)*base67 + (334464797660047/80000000000000000000000000000 : ℝ)*base69 + (107958333980047/80000000000000000000000000000 : ℝ)*base71 + (75033936379953/40000000000000000000000000000 : ℝ)*base74 + (102696713740047/80000000000000000000000000000 : ℝ)*base75 + (125778445340047/80000000000000000000000000000 : ℝ)*base77 + (299959321820047/80000000000000000000000000000 : ℝ)*base79 + (192095368700047/40000000000000000000000000000 : ℝ)*base81 + (12059969/10000000000000000000000 : ℝ)*base89 + (12059969/10000000000000000000000 : ℝ)*base91 + (12059969/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8390306041955423209563/1600000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2487359/250000000000 : ℝ)*(base19) + (239018169/20000000000000 : ℝ)*(base23) + (5351131/3125000000000 : ℝ)*(base39) + (3900287/2500000000000 : ℝ)*(base45) + (69082103/100000000000000 : ℝ)*(upper3) + (151198839/50000000000000 : ℝ)*(upper5) + (613644272573717/100000000000000 : ℝ)*(major0) + (613644272573717/100000000000000 : ℝ)*(major1) + (306822050668763/50000000000000 : ℝ)*(major2) + (46262937/6250000000000 : ℝ)*(sp2) + (101641779235463/12500000000000 : ℝ)*(sp4) + (101641654867513/12500000000000 : ℝ)*(sp5) + (406566234911029/50000000000000 : ℝ)*(sp6) + (414153965229489/100000000000000 : ℝ)*(sp7) + (414153965229489/100000000000000 : ℝ)*(f.failure) + (101641800639987/12500000000000 : ℝ)*(f.sum) + (459507702126113/400000000000000000000000000000 : ℝ)*base65 + (887772707619567/200000000000000000000000000000 : ℝ)*base68 + (2700226015765247/400000000000000000000000000000 : ℝ)*base69 + (310467879619567/200000000000000000000000000000 : ℝ)*base72 + (585459592273887/400000000000000000000000000000 : ℝ)*base74 + (4058143548565247/400000000000000000000000000000 : ℝ)*base75 + (1134976121765247/400000000000000000000000000000 : ℝ)*base77 + (366812990565247/400000000000000000000000000000 : ℝ)*base79 + (648204360165247/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (24195161/10000000000000000000000 : ℝ)*base90 + (24195161/10000000000000000000000 : ℝ)*base92 + (124195161/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1075_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148168151/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (67/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14037/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1075_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1075_s1_0 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1061343839/5000000000 : ℝ)*x 0 + (5719805311/10000000000 : ℝ)*x 1 + (4987928967/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061343839/5000000000 : ℝ)^2067 ≤ (12742549014379/100000000000000 : ℝ)^1555 := by
    have hnat : (1061343839 : ℕ)^2067*100000000000000^1555 ≤ 12742549014379^1555*5000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061343839 5000000000 12742549014379 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5719805311/10000000000 : ℝ)^2067 ≤ (5948486766113/12500000000000 : ℝ)^1555 := by
    have hnat : (5719805311 : ℕ)^2067*12500000000000^1555 ≤ 5948486766113^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5719805311 10000000000 5948486766113 12500000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4987928967/10000000000 : ℝ)^2067 ≤ (7933911368819/20000000000000 : ℝ)^1555 := by
    have hnat : (4987928967 : ℕ)^2067*20000000000000^1555 ≤ 7933911368819^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4987928967 10000000000 7933911368819 20000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1061343839/5000000000 : ℝ), (5719805311/10000000000 : ℝ), (4987928967/10000000000 : ℝ)] ![(12742549014379/100000000000000 : ℝ), (5948486766113/12500000000000 : ℝ), (7933911368819/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1061343839/5000000000 : ℝ)|^2067 ≤ (12742549014379/100000000000000 : ℝ)^1555
        have hw : |(-1061343839/5000000000 : ℝ)|=(1061343839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5719805311/10000000000 : ℝ)|^2067 ≤ (5948486766113/12500000000000 : ℝ)^1555
        have hw : |(5719805311/10000000000 : ℝ)|=(5719805311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4987928967/10000000000 : ℝ)|^2067 ≤ (7933911368819/20000000000000 : ℝ)^1555
        have hw : |(4987928967/10000000000 : ℝ)|=(4987928967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_s1_1 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2711407271/5000000000 : ℝ)*x 0 + (-629757069/2500000000 : ℝ)*x 1 + (311745579/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2711407271/5000000000 : ℝ)^2067 ≤ (44331811118743/100000000000000 : ℝ)^1555 := by
    have hnat : (2711407271 : ℕ)^2067*100000000000000^1555 ≤ 44331811118743^1555*5000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711407271 5000000000 44331811118743 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (629757069/2500000000 : ℝ)^2067 ≤ (15998628890691/100000000000000 : ℝ)^1555 := by
    have hnat : (629757069 : ℕ)^2067*100000000000000^1555 ≤ 15998628890691^1555*2500000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      629757069 2500000000 15998628890691 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (311745579/625000000 : ℝ)^2067 ≤ (39669559983907/100000000000000 : ℝ)^1555 := by
    have hnat : (311745579 : ℕ)^2067*100000000000000^1555 ≤ 39669559983907^1555*625000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      311745579 625000000 39669559983907 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2711407271/5000000000 : ℝ), (-629757069/2500000000 : ℝ), (311745579/625000000 : ℝ)] ![(44331811118743/100000000000000 : ℝ), (15998628890691/100000000000000 : ℝ), (39669559983907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2711407271/5000000000 : ℝ)|^2067 ≤ (44331811118743/100000000000000 : ℝ)^1555
        have hw : |(2711407271/5000000000 : ℝ)|=(2711407271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-629757069/2500000000 : ℝ)|^2067 ≤ (15998628890691/100000000000000 : ℝ)^1555
        have hw : |(-629757069/2500000000 : ℝ)|=(629757069/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(311745579/625000000 : ℝ)|^2067 ≤ (39669559983907/100000000000000 : ℝ)^1555
        have hw : |(311745579/625000000 : ℝ)|=(311745579/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_s1_2 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (271140761/500000000 : ℝ)*x 0 + (4987928523/10000000000 : ℝ)*x 1 + (-2519028331/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (271140761/500000000 : ℝ)^2067 ≤ (44331818486419/100000000000000 : ℝ)^1555 := by
    have hnat : (271140761 : ℕ)^2067*100000000000000^1555 ≤ 44331818486419^1555*500000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271140761 500000000 44331818486419 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4987928523/10000000000 : ℝ)^2067 ≤ (7933910430047/20000000000000 : ℝ)^1555 := by
    have hnat : (4987928523 : ℕ)^2067*20000000000000^1555 ≤ 7933910430047^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4987928523 10000000000 7933910430047 20000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2519028331/10000000000 : ℝ)^2067 ≤ (15998629355017/100000000000000 : ℝ)^1555 := by
    have hnat : (2519028331 : ℕ)^2067*100000000000000^1555 ≤ 15998629355017^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2519028331 10000000000 15998629355017 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(271140761/500000000 : ℝ), (4987928523/10000000000 : ℝ), (-2519028331/10000000000 : ℝ)] ![(44331818486419/100000000000000 : ℝ), (7933910430047/20000000000000 : ℝ), (15998629355017/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(271140761/500000000 : ℝ)|^2067 ≤ (44331818486419/100000000000000 : ℝ)^1555
        have hw : |(271140761/500000000 : ℝ)|=(271140761/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4987928523/10000000000 : ℝ)|^2067 ≤ (7933910430047/20000000000000 : ℝ)^1555
        have hw : |(4987928523/10000000000 : ℝ)|=(4987928523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2519028331/10000000000 : ℝ)|^2067 ≤ (15998629355017/100000000000000 : ℝ)^1555
        have hw : |(-2519028331/10000000000 : ℝ)|=(2519028331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_s1_3 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (108076399/250000000 : ℝ)*x 0 + (3664277689/10000000000 : ℝ)*x 1 + (318825951/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (108076399/250000000 : ℝ)^2067 ≤ (16399899829153/50000000000000 : ℝ)^1555 := by
    have hnat : (108076399 : ℕ)^2067*50000000000000^1555 ≤ 16399899829153^1555*250000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108076399 250000000 16399899829153 50000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3664277689/10000000000 : ℝ)^2067 ≤ (411383644603/1562500000000 : ℝ)^1555 := by
    have hnat : (3664277689 : ℕ)^2067*1562500000000^1555 ≤ 411383644603^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3664277689 10000000000 411383644603 1562500000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (318825951/625000000 : ℝ)^2067 ≤ (40871647083987/100000000000000 : ℝ)^1555 := by
    have hnat : (318825951 : ℕ)^2067*100000000000000^1555 ≤ 40871647083987^1555*625000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      318825951 625000000 40871647083987 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(108076399/250000000 : ℝ), (3664277689/10000000000 : ℝ), (318825951/625000000 : ℝ)] ![(16399899829153/50000000000000 : ℝ), (411383644603/1562500000000 : ℝ), (40871647083987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(108076399/250000000 : ℝ)|^2067 ≤ (16399899829153/50000000000000 : ℝ)^1555
        have hw : |(108076399/250000000 : ℝ)|=(108076399/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3664277689/10000000000 : ℝ)|^2067 ≤ (411383644603/1562500000000 : ℝ)^1555
        have hw : |(3664277689/10000000000 : ℝ)|=(3664277689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(318825951/625000000 : ℝ)|^2067 ≤ (40871647083987/100000000000000 : ℝ)^1555
        have hw : |(318825951/625000000 : ℝ)|=(318825951/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_s1_4 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-66362371/312500000 : ℝ)*x 0 + (4998179611/10000000000 : ℝ)*x 1 + (5709344707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66362371/312500000 : ℝ)^2067 ≤ (12749796535873/100000000000000 : ℝ)^1555 := by
    have hnat : (66362371 : ℕ)^2067*100000000000000^1555 ≤ 12749796535873^1555*312500000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66362371 312500000 12749796535873 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4998179611/10000000000 : ℝ)^2067 ≤ (9944490202167/25000000000000 : ℝ)^1555 := by
    have hnat : (4998179611 : ℕ)^2067*25000000000000^1555 ≤ 9944490202167^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4998179611 10000000000 9944490202167 25000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5709344707/10000000000 : ℝ)^2067 ≤ (47472242633313/100000000000000 : ℝ)^1555 := by
    have hnat : (5709344707 : ℕ)^2067*100000000000000^1555 ≤ 47472242633313^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5709344707 10000000000 47472242633313 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-66362371/312500000 : ℝ), (4998179611/10000000000 : ℝ), (5709344707/10000000000 : ℝ)] ![(12749796535873/100000000000000 : ℝ), (9944490202167/25000000000000 : ℝ), (47472242633313/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-66362371/312500000 : ℝ)|^2067 ≤ (12749796535873/100000000000000 : ℝ)^1555
        have hw : |(-66362371/312500000 : ℝ)|=(66362371/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4998179611/10000000000 : ℝ)|^2067 ≤ (9944490202167/25000000000000 : ℝ)^1555
        have hw : |(4998179611/10000000000 : ℝ)|=(4998179611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5709344707/10000000000 : ℝ)|^2067 ≤ (47472242633313/100000000000000 : ℝ)^1555
        have hw : |(5709344707/10000000000 : ℝ)|=(5709344707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_s1_5 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2617908351/5000000000 : ℝ)*x 0 + (-1797610341/10000000000 : ℝ)*x 1 + (1427336669/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2617908351/5000000000 : ℝ)^2067 ≤ (2115568669811/5000000000000 : ℝ)^1555 := by
    have hnat : (2617908351 : ℕ)^2067*5000000000000^1555 ≤ 2115568669811^1555*5000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2617908351 5000000000 2115568669811 5000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1797610341/10000000000 : ℝ)^2067 ≤ (319261318791/3125000000000 : ℝ)^1555 := by
    have hnat : (1797610341 : ℕ)^2067*3125000000000^1555 ≤ 319261318791^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1797610341 10000000000 319261318791 3125000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1427336669/2500000000 : ℝ)^2067 ≤ (47472264395839/100000000000000 : ℝ)^1555 := by
    have hnat : (1427336669 : ℕ)^2067*100000000000000^1555 ≤ 47472264395839^1555*2500000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1427336669 2500000000 47472264395839 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2617908351/5000000000 : ℝ), (-1797610341/10000000000 : ℝ), (1427336669/2500000000 : ℝ)] ![(2115568669811/5000000000000 : ℝ), (319261318791/3125000000000 : ℝ), (47472264395839/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2617908351/5000000000 : ℝ)|^2067 ≤ (2115568669811/5000000000000 : ℝ)^1555
        have hw : |(2617908351/5000000000 : ℝ)|=(2617908351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1797610341/10000000000 : ℝ)|^2067 ≤ (319261318791/3125000000000 : ℝ)^1555
        have hw : |(-1797610341/10000000000 : ℝ)|=(1797610341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1427336669/2500000000 : ℝ)|^2067 ≤ (47472264395839/100000000000000 : ℝ)^1555
        have hw : |(1427336669/2500000000 : ℝ)|=(1427336669/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_s1_6 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (654476829/1250000000 : ℝ)*x 0 + (2854674487/5000000000 : ℝ)*x 1 + (-1797609921/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (654476829/1250000000 : ℝ)^2067 ≤ (42311351160403/100000000000000 : ℝ)^1555 := by
    have hnat : (654476829 : ℕ)^2067*100000000000000^1555 ≤ 42311351160403^1555*1250000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654476829 1250000000 42311351160403 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2854674487/5000000000 : ℝ)^2067 ≤ (47472289794667/100000000000000 : ℝ)^1555 := by
    have hnat : (2854674487 : ℕ)^2067*100000000000000^1555 ≤ 47472289794667^1555*5000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2854674487 5000000000 47472289794667 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1797609921/10000000000 : ℝ)^2067 ≤ (2043271805677/20000000000000 : ℝ)^1555 := by
    have hnat : (1797609921 : ℕ)^2067*20000000000000^1555 ≤ 2043271805677^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1797609921 10000000000 2043271805677 20000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(654476829/1250000000 : ℝ), (2854674487/5000000000 : ℝ), (-1797609921/10000000000 : ℝ)] ![(42311351160403/100000000000000 : ℝ), (47472289794667/100000000000000 : ℝ), (2043271805677/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(654476829/1250000000 : ℝ)|^2067 ≤ (42311351160403/100000000000000 : ℝ)^1555
        have hw : |(654476829/1250000000 : ℝ)|=(654476829/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2854674487/5000000000 : ℝ)|^2067 ≤ (47472289794667/100000000000000 : ℝ)^1555
        have hw : |(2854674487/5000000000 : ℝ)|=(2854674487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1797609921/10000000000 : ℝ)|^2067 ≤ (2043271805677/20000000000000 : ℝ)^1555
        have hw : |(-1797609921/10000000000 : ℝ)|=(1797609921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_s1_7 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2162417309/5000000000 : ℝ)*x 0 + (508108607/1000000000 : ℝ)*x 1 + (1842405843/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2162417309/5000000000 : ℝ)^2067 ≤ (32817739238677/100000000000000 : ℝ)^1555 := by
    have hnat : (2162417309 : ℕ)^2067*100000000000000^1555 ≤ 32817739238677^1555*5000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2162417309 5000000000 32817739238677 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (508108607/1000000000 : ℝ)^2067 ≤ (40657406641023/100000000000000 : ℝ)^1555 := by
    have hnat : (508108607 : ℕ)^2067*100000000000000^1555 ≤ 40657406641023^1555*1000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508108607 1000000000 40657406641023 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1842405843/5000000000 : ℝ)^2067 ≤ (26524854101081/100000000000000 : ℝ)^1555 := by
    have hnat : (1842405843 : ℕ)^2067*100000000000000^1555 ≤ 26524854101081^1555*5000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1842405843 5000000000 26524854101081 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2162417309/5000000000 : ℝ), (508108607/1000000000 : ℝ), (1842405843/5000000000 : ℝ)] ![(32817739238677/100000000000000 : ℝ), (40657406641023/100000000000000 : ℝ), (26524854101081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2162417309/5000000000 : ℝ)|^2067 ≤ (32817739238677/100000000000000 : ℝ)^1555
        have hw : |(2162417309/5000000000 : ℝ)|=(2162417309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(508108607/1000000000 : ℝ)|^2067 ≤ (40657406641023/100000000000000 : ℝ)^1555
        have hw : |(508108607/1000000000 : ℝ)|=(508108607/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1842405843/5000000000 : ℝ)|^2067 ≤ (26524854101081/100000000000000 : ℝ)^1555
        have hw : |(1842405843/5000000000 : ℝ)|=(1842405843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1075_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148168151/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14037/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (67/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2633/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5187/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14037/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (67/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14037/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (67/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14037/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (67/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14037/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (67/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14037/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (67/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14037/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (67/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (67/50000 : ℝ) ^ (8267/2048 : ℝ) ≤ (253052499/100000000000000000000 : ℝ) := by
    have hpowers : (67/50000 : ℝ)^8267 ≤ (253052499/100000000000000000000 : ℝ)^2048 := by
      have hnat : (67 : ℕ)^8267*100000000000000000000^2048 ≤ 253052499^2048*50000^8267 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        67 50000 253052499 100000000000000000000 8267 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (67/50000 : ℝ)) (X := (253052499/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8267 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14037/50000 : ℝ) ^ (8267/2048 : ℝ) ≤ (592943731574240083/100000000000000000000 : ℝ) := by
    have hpowers : (14037/50000 : ℝ)^8267 ≤ (592943731574240083/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14037 : ℕ)^8267*100000000000000000000^2048 ≤ 592943731574240083^2048*50000^8267 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14037 50000 592943731574240083 100000000000000000000 8267 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14037/50000 : ℝ)) (X := (592943731574240083/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8267 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000000253052499/50000000000000000000 : ℝ) ≤ (5000000000006269/5000000000000000 : ℝ) ^ (8267/2048 : ℝ) := by
    have hpowers : (50000000000253052499/50000000000000000000 : ℝ)^2048 ≤ (5000000000006269/5000000000000000 : ℝ)^8267 := by
      have hnat : (50000000000253052499 : ℕ)^2048*5000000000000000^8267 ≤ 5000000000006269^8267*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000000253052499 50000000000000000000 5000000000006269 5000000000000000 2048 8267 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000000006269/5000000000000000 : ℝ)) (X := (50000000000253052499/50000000000000000000 : ℝ)) (by norm_num) 8267 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50296471865913646291/50000000000000000000 : ℝ) ≤ (625916028930671/625000000000000 : ℝ) ^ (8267/2048 : ℝ) := by
    have hpowers : (50296471865913646291/50000000000000000000 : ℝ)^2048 ≤ (625916028930671/625000000000000 : ℝ)^8267 := by
      have hnat : (50296471865913646291 : ℕ)^2048*625000000000000^8267 ≤ 625916028930671^8267*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50296471865913646291 50000000000000000000 625916028930671 625000000000000 2048 8267 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625916028930671/625000000000000 : ℝ)) (X := (50296471865913646291/50000000000000000000 : ℝ)) (by norm_num) 8267 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50592943731574240083/50000000000000000000 : ℝ) ≤ (5014656462884467/5000000000000000 : ℝ) ^ (8267/2048 : ℝ) := by
    have hpowers : (50592943731574240083/50000000000000000000 : ℝ)^2048 ≤ (5014656462884467/5000000000000000 : ℝ)^8267 := by
      have hnat : (50592943731574240083 : ℕ)^2048*5000000000000000^8267 ≤ 5014656462884467^8267*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50592943731574240083 50000000000000000000 5014656462884467 5000000000000000 2048 8267 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5014656462884467/5000000000000000 : ℝ)) (X := (50592943731574240083/50000000000000000000 : ℝ)) (by norm_num) 8267 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(253052499/100000000000000000000 : ℝ) ≤ ((8731127252134342333/8731250000000000000 : ℝ)+2*(7328231439099/1397000000000000 : ℝ)*(67/50000 : ℝ))^(8267/2048 : ℝ) := by
    rw [show (8731127252134342333/8731250000000000000 : ℝ)+2*(7328231439099/1397000000000000 : ℝ)*(67/50000 : ℝ)=(5000000000006269/5000000000000000 : ℝ) by norm_num, show 1+2*(253052499/100000000000000000000 : ℝ)=(50000000000253052499/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(592943731574240083/100000000000000000000 : ℝ)+(253052499/100000000000000000000 : ℝ) ≤ ((8731127252134342333/8731250000000000000 : ℝ)+(7328231439099/1397000000000000 : ℝ)*((14037/50000 : ℝ)+(67/50000 : ℝ)))^(8267/2048 : ℝ) := by
    rw [show (8731127252134342333/8731250000000000000 : ℝ)+(7328231439099/1397000000000000 : ℝ)*((14037/50000 : ℝ)+(67/50000 : ℝ))=(625916028930671/625000000000000 : ℝ) by norm_num, show 1+(592943731574240083/100000000000000000000 : ℝ)+(253052499/100000000000000000000 : ℝ)=(50296471865913646291/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(592943731574240083/100000000000000000000 : ℝ) ≤ ((8731127252134342333/8731250000000000000 : ℝ)+2*(7328231439099/1397000000000000 : ℝ)*(14037/50000 : ℝ))^(8267/2048 : ℝ) := by
    rw [show (8731127252134342333/8731250000000000000 : ℝ)+2*(7328231439099/1397000000000000 : ℝ)*(14037/50000 : ℝ)=(5014656462884467/5000000000000000 : ℝ) by norm_num, show 1+2*(592943731574240083/100000000000000000000 : ℝ)=(50592943731574240083/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8731127252134342333/8731250000000000000 : ℝ)*(X 1 0+X 2 0)+(7328231439099/1397000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8267/2048 : ℝ)) (lo := (67/50000 : ℝ)) (hi := (14037/50000 : ℝ)) (c := (8731127252134342333/8731250000000000000 : ℝ)) (alpha := (7328231439099/1397000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8731127252134342333/8731250000000000000 : ℝ)*(X 0 1+X 2 1)+(7328231439099/1397000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8267/2048 : ℝ)) (lo := (67/50000 : ℝ)) (hi := (14037/50000 : ℝ)) (c := (8731127252134342333/8731250000000000000 : ℝ)) (alpha := (7328231439099/1397000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8731127252134342333/8731250000000000000 : ℝ)*(X 0 2+X 1 2)+(7328231439099/1397000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8267/2048 : ℝ)) (lo := (67/50000 : ℝ)) (hi := (14037/50000 : ℝ)) (c := (8731127252134342333/8731250000000000000 : ℝ)) (alpha := (7328231439099/1397000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1061343839/5000000000 : ℝ)*X 0 0+(5719805311/10000000000 : ℝ)*X 0 1+(4987928967/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2711407271/5000000000 : ℝ)*X 1 0+(-629757069/2500000000 : ℝ)*X 1 1+(311745579/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((271140761/500000000 : ℝ)*X 2 0+(4987928523/10000000000 : ℝ)*X 2 1+(-2519028331/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((108076399/250000000 : ℝ)*X 0 0+(3664277689/10000000000 : ℝ)*X 0 1+(318825951/625000000 : ℝ)*X 0 2+(108076399/250000000 : ℝ)*X 1 0+(3664277689/10000000000 : ℝ)*X 1 1+(318825951/625000000 : ℝ)*X 1 2+(108076399/250000000 : ℝ)*X 2 0+(3664277689/10000000000 : ℝ)*X 2 1+(318825951/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-66362371/312500000 : ℝ)*X 0 0+(4998179611/10000000000 : ℝ)*X 0 1+(5709344707/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2617908351/5000000000 : ℝ)*X 1 0+(-1797610341/10000000000 : ℝ)*X 1 1+(1427336669/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((654476829/1250000000 : ℝ)*X 2 0+(2854674487/5000000000 : ℝ)*X 2 1+(-1797609921/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2162417309/5000000000 : ℝ)*X 0 0+(508108607/1000000000 : ℝ)*X 0 1+(1842405843/5000000000 : ℝ)*X 0 2+(2162417309/5000000000 : ℝ)*X 1 0+(508108607/1000000000 : ℝ)*X 1 1+(1842405843/5000000000 : ℝ)*X 1 2+(2162417309/5000000000 : ℝ)*X 2 0+(508108607/1000000000 : ℝ)*X 2 1+(1842405843/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (411964912961230659701428833/87312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (28545009/25000000000000 : ℝ)*(base1) + (196897233/20000000000000 : ℝ)*(base19) + (577659233/50000000000000 : ℝ)*(base23) + (91392709/100000000000000 : ℝ)*(upper3) + (119050669/100000000000000 : ℝ)*(upper5) + (206228990705167/20000000000000 : ℝ)*(major0) + (206228990705167/20000000000000 : ℝ)*(major1) + (206228990705167/20000000000000 : ℝ)*(major2) + (1366355638140641/100000000000000 : ℝ)*(sp0) + (170794985681867/12500000000000 : ℝ)*(sp1) + (273271942924527/20000000000000 : ℝ)*(sp2) + (173981640970351/25000000000000 : ℝ)*(sp3) + (1069196099/20000000000000 : ℝ)*(sp4) + (2201773091/100000000000000 : ℝ)*(sp7) + (69592887983453/10000000000000 : ℝ)*(f.failure) + (1366360869941101/100000000000000 : ℝ)*(f.sum) + (41632584820267/13970000000000000000000000000 : ℝ)*base66 + (674551255699015861/174625000000000000000000000000000 : ℝ)*base67 + (397743916566515861/174625000000000000000000000000000 : ℝ)*base69 + (82717368000484139/174625000000000000000000000000000 : ℝ)*base72 + (11235852686233/13970000000000000000000000000 : ℝ)*base73 + (843893843548984139/174625000000000000000000000000000 : ℝ)*base76 + (153968801379984139/174625000000000000000000000000000 : ℝ)*base78 + (692498166010109139/174625000000000000000000000000000 : ℝ)*base80 + (36240125429683/13970000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (394597/1000000000000000000000 : ℝ)*base90 + (394597/1000000000000000000000 : ℝ)*base92 + (394597/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2466588801164870339803869/21828125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (197703977/10000000000000 : ℝ)*(base19) + (62845479/3125000000000 : ℝ)*(base23) + (69222819/25000000000000 : ℝ)*(upper2) + (7465699/2000000000000 : ℝ)*(upper3) + (482231127/100000000000000 : ℝ)*(upper5) + (53058304656877/5000000000000 : ℝ)*(major0) + (53058304656877/5000000000000 : ℝ)*(major1) + (53058304656877/5000000000000 : ℝ)*(major2) + (2605508191/25000000000000 : ℝ)*(sp1) + (3033136693/25000000000000 : ℝ)*(sp2) + (43941930285407/3125000000000 : ℝ)*(sp4) + (140612937006049/10000000000000 : ℝ)*(sp5) + (351531906382731/25000000000000 : ℝ)*(sp6) + (716190413375369/100000000000000 : ℝ)*(sp7) + (716190413375369/100000000000000 : ℝ)*(f.failure) + (43941930285407/3125000000000 : ℝ)*(f.sum) + (3012630244089/1746250000000000000000000000 : ℝ)*base65 + (286387208077869709/43656250000000000000000000000000 : ℝ)*base68 + (245834158183369709/43656250000000000000000000000000 : ℝ)*base70 + (122829007032619709/43656250000000000000000000000000 : ℝ)*base72 + (1559747326893/3492500000000000000000000000 : ℝ)*base73 + (240138456817619709/43656250000000000000000000000000 : ℝ)*base76 + (83503096431994709/43656250000000000000000000000000 : ℝ)*base78 + (204814460171494709/43656250000000000000000000000000 : ℝ)*base80 + (180171595381/109140625000000000000000000 : ℝ)*base82 + (93672719/10000000000000000000000 : ℝ)*base89 + (93672719/10000000000000000000000 : ℝ)*base91 + (93672719/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1075_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148168151/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14037/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (67/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2633/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5187/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1075_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1075_s2_0 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-435920233/2000000000 : ℝ)*x 0 + (5524049749/10000000000 : ℝ)*x 1 + (1286891581/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (435920233/2000000000 : ℝ)^2067 ≤ (13198687758453/100000000000000 : ℝ)^1555 := by
    have hnat : (435920233 : ℕ)^2067*100000000000000^1555 ≤ 13198687758453^1555*2000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435920233 2000000000 13198687758453 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5524049749/10000000000 : ℝ)^2067 ≤ (2839704918183/6250000000000 : ℝ)^1555 := by
    have hnat : (5524049749 : ℕ)^2067*6250000000000^1555 ≤ 2839704918183^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5524049749 10000000000 2839704918183 6250000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1286891581/2500000000 : ℝ)^2067 ≤ (41366033523277/100000000000000 : ℝ)^1555 := by
    have hnat : (1286891581 : ℕ)^2067*100000000000000^1555 ≤ 41366033523277^1555*2500000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1286891581 2500000000 41366033523277 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-435920233/2000000000 : ℝ), (5524049749/10000000000 : ℝ), (1286891581/2500000000 : ℝ)] ![(13198687758453/100000000000000 : ℝ), (2839704918183/6250000000000 : ℝ), (41366033523277/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-435920233/2000000000 : ℝ)|^2067 ≤ (13198687758453/100000000000000 : ℝ)^1555
        have hw : |(-435920233/2000000000 : ℝ)|=(435920233/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5524049749/10000000000 : ℝ)|^2067 ≤ (2839704918183/6250000000000 : ℝ)^1555
        have hw : |(5524049749/10000000000 : ℝ)|=(5524049749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1286891581/2500000000 : ℝ)|^2067 ≤ (41366033523277/100000000000000 : ℝ)^1555
        have hw : |(1286891581/2500000000 : ℝ)|=(1286891581/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_s2_1 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (336050129/625000000 : ℝ)*x 0 + (-2375864247/10000000000 : ℝ)*x 1 + (5147567199/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (336050129/625000000 : ℝ)^2067 ≤ (43832503505083/100000000000000 : ℝ)^1555 := by
    have hnat : (336050129 : ℕ)^2067*100000000000000^1555 ≤ 43832503505083^1555*625000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336050129 625000000 43832503505083 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2375864247/10000000000 : ℝ)^2067 ≤ (592058144553/4000000000000 : ℝ)^1555 := by
    have hnat : (2375864247 : ℕ)^2067*4000000000000^1555 ≤ 592058144553^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2375864247 10000000000 592058144553 4000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5147567199/10000000000 : ℝ)^2067 ≤ (8273208574003/20000000000000 : ℝ)^1555 := by
    have hnat : (5147567199 : ℕ)^2067*20000000000000^1555 ≤ 8273208574003^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5147567199 10000000000 8273208574003 20000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(336050129/625000000 : ℝ), (-2375864247/10000000000 : ℝ), (5147567199/10000000000 : ℝ)] ![(43832503505083/100000000000000 : ℝ), (592058144553/4000000000000 : ℝ), (8273208574003/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(336050129/625000000 : ℝ)|^2067 ≤ (43832503505083/100000000000000 : ℝ)^1555
        have hw : |(336050129/625000000 : ℝ)|=(336050129/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2375864247/10000000000 : ℝ)|^2067 ≤ (592058144553/4000000000000 : ℝ)^1555
        have hw : |(-2375864247/10000000000 : ℝ)|=(2375864247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5147567199/10000000000 : ℝ)|^2067 ≤ (8273208574003/20000000000000 : ℝ)^1555
        have hw : |(5147567199/10000000000 : ℝ)|=(5147567199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_s2_2 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2100313/3906250 : ℝ)*x 0 + (5147568003/10000000000 : ℝ)*x 1 + (-475172847/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2100313/3906250 : ℝ)^2067 ≤ (43832495009399/100000000000000 : ℝ)^1555 := by
    have hnat : (2100313 : ℕ)^2067*100000000000000^1555 ≤ 43832495009399^1555*3906250^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2100313 3906250 43832495009399 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5147568003/10000000000 : ℝ)^2067 ≤ (10341512864583/25000000000000 : ℝ)^1555 := by
    have hnat : (5147568003 : ℕ)^2067*25000000000000^1555 ≤ 10341512864583^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5147568003 10000000000 10341512864583 25000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (475172847/2000000000 : ℝ)^2067 ≤ (14801453514451/100000000000000 : ℝ)^1555 := by
    have hnat : (475172847 : ℕ)^2067*100000000000000^1555 ≤ 14801453514451^1555*2000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      475172847 2000000000 14801453514451 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2100313/3906250 : ℝ), (5147568003/10000000000 : ℝ), (-475172847/2000000000 : ℝ)] ![(43832495009399/100000000000000 : ℝ), (10341512864583/25000000000000 : ℝ), (14801453514451/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2100313/3906250 : ℝ)|^2067 ≤ (43832495009399/100000000000000 : ℝ)^1555
        have hw : |(2100313/3906250 : ℝ)|=(2100313/3906250 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5147568003/10000000000 : ℝ)|^2067 ≤ (10341512864583/25000000000000 : ℝ)^1555
        have hw : |(5147568003/10000000000 : ℝ)|=(5147568003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-475172847/2000000000 : ℝ)|^2067 ≤ (14801453514451/100000000000000 : ℝ)^1555
        have hw : |(-475172847/2000000000 : ℝ)|=(475172847/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_s2_3 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (872384437/2000000000 : ℝ)*x 0 + (250505771/625000000 : ℝ)*x 1 + (1186813083/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (872384437/2000000000 : ℝ)^2067 ≤ (829808941093/2500000000000 : ℝ)^1555 := by
    have hnat : (872384437 : ℕ)^2067*2500000000000^1555 ≤ 829808941093^1555*2000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      872384437 2000000000 829808941093 2500000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (250505771/625000000 : ℝ)^2067 ≤ (1483101303507/5000000000000 : ℝ)^1555 := by
    have hnat : (250505771 : ℕ)^2067*5000000000000^1555 ≤ 1483101303507^1555*625000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      250505771 625000000 1483101303507 5000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1186813083/2500000000 : ℝ)^2067 ≤ (18572808135489/50000000000000 : ℝ)^1555 := by
    have hnat : (1186813083 : ℕ)^2067*50000000000000^1555 ≤ 18572808135489^1555*2500000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1186813083 2500000000 18572808135489 50000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(872384437/2000000000 : ℝ), (250505771/625000000 : ℝ), (1186813083/2500000000 : ℝ)] ![(829808941093/2500000000000 : ℝ), (1483101303507/5000000000000 : ℝ), (18572808135489/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(872384437/2000000000 : ℝ)|^2067 ≤ (829808941093/2500000000000 : ℝ)^1555
        have hw : |(872384437/2000000000 : ℝ)|=(872384437/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(250505771/625000000 : ℝ)|^2067 ≤ (1483101303507/5000000000000 : ℝ)^1555
        have hw : |(250505771/625000000 : ℝ)|=(250505771/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1186813083/2500000000 : ℝ)|^2067 ≤ (18572808135489/50000000000000 : ℝ)^1555
        have hw : |(1186813083/2500000000 : ℝ)|=(1186813083/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_s2_4 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-87188947/400000000 : ℝ)*x 0 + (2575144963/5000000000 : ℝ)*x 1 + (345081129/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (87188947/400000000 : ℝ)^2067 ≤ (13199673900247/100000000000000 : ℝ)^1555 := by
    have hnat : (87188947 : ℕ)^2067*100000000000000^1555 ≤ 13199673900247^1555*400000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87188947 400000000 13199673900247 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2575144963/5000000000 : ℝ)^2067 ≤ (41395129536141/100000000000000 : ℝ)^1555 := by
    have hnat : (2575144963 : ℕ)^2067*100000000000000^1555 ≤ 41395129536141^1555*5000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2575144963 5000000000 41395129536141 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (345081129/625000000 : ℝ)^2067 ≤ (11351299136587/25000000000000 : ℝ)^1555 := by
    have hnat : (345081129 : ℕ)^2067*25000000000000^1555 ≤ 11351299136587^1555*625000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      345081129 625000000 11351299136587 25000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-87188947/400000000 : ℝ), (2575144963/5000000000 : ℝ), (345081129/625000000 : ℝ)] ![(13199673900247/100000000000000 : ℝ), (41395129536141/100000000000000 : ℝ), (11351299136587/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-87188947/400000000 : ℝ)|^2067 ≤ (13199673900247/100000000000000 : ℝ)^1555
        have hw : |(-87188947/400000000 : ℝ)|=(87188947/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2575144963/5000000000 : ℝ)|^2067 ≤ (41395129536141/100000000000000 : ℝ)^1555
        have hw : |(2575144963/5000000000 : ℝ)|=(2575144963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(345081129/625000000 : ℝ)|^2067 ≤ (11351299136587/25000000000000 : ℝ)^1555
        have hw : |(345081129/625000000 : ℝ)|=(345081129/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_s2_5 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (264085627/500000000 : ℝ)*x 0 + (-1001068061/5000000000 : ℝ)*x 1 + (1380324539/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264085627/500000000 : ℝ)^2067 ≤ (21402546933771/50000000000000 : ℝ)^1555 := by
    have hnat : (264085627 : ℕ)^2067*50000000000000^1555 ≤ 21402546933771^1555*500000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264085627 500000000 21402546933771 50000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1001068061/5000000000 : ℝ)^2067 ≤ (5894854283627/50000000000000 : ℝ)^1555 := by
    have hnat : (1001068061 : ℕ)^2067*50000000000000^1555 ≤ 5894854283627^1555*5000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1001068061 5000000000 5894854283627 50000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1380324539/2500000000 : ℝ)^2067 ≤ (22702598776017/50000000000000 : ℝ)^1555 := by
    have hnat : (1380324539 : ℕ)^2067*50000000000000^1555 ≤ 22702598776017^1555*2500000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1380324539 2500000000 22702598776017 50000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(264085627/500000000 : ℝ), (-1001068061/5000000000 : ℝ), (1380324539/2500000000 : ℝ)] ![(21402546933771/50000000000000 : ℝ), (5894854283627/50000000000000 : ℝ), (22702598776017/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(264085627/500000000 : ℝ)|^2067 ≤ (21402546933771/50000000000000 : ℝ)^1555
        have hw : |(264085627/500000000 : ℝ)|=(264085627/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1001068061/5000000000 : ℝ)|^2067 ≤ (5894854283627/50000000000000 : ℝ)^1555
        have hw : |(-1001068061/5000000000 : ℝ)|=(1001068061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1380324539/2500000000 : ℝ)|^2067 ≤ (22702598776017/50000000000000 : ℝ)^1555
        have hw : |(1380324539/2500000000 : ℝ)|=(1380324539/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_s2_6 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2640856391/5000000000 : ℝ)*x 0 + (1380324499/2500000000 : ℝ)*x 1 + (-500534003/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2640856391/5000000000 : ℝ)^2067 ≤ (10701274118643/25000000000000 : ℝ)^1555 := by
    have hnat : (2640856391 : ℕ)^2067*25000000000000^1555 ≤ 10701274118643^1555*5000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640856391 5000000000 10701274118643 25000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1380324499/2500000000 : ℝ)^2067 ≤ (9081039160603/20000000000000 : ℝ)^1555 := by
    have hnat : (1380324499 : ℕ)^2067*20000000000000^1555 ≤ 9081039160603^1555*2500000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1380324499 2500000000 9081039160603 20000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (500534003/2500000000 : ℝ)^2067 ≤ (2947426926559/25000000000000 : ℝ)^1555 := by
    have hnat : (500534003 : ℕ)^2067*25000000000000^1555 ≤ 2947426926559^1555*2500000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      500534003 2500000000 2947426926559 25000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2640856391/5000000000 : ℝ), (1380324499/2500000000 : ℝ), (-500534003/2500000000 : ℝ)] ![(10701274118643/25000000000000 : ℝ), (9081039160603/20000000000000 : ℝ), (2947426926559/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2640856391/5000000000 : ℝ)|^2067 ≤ (10701274118643/25000000000000 : ℝ)^1555
        have hw : |(2640856391/5000000000 : ℝ)|=(2640856391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1380324499/2500000000 : ℝ)|^2067 ≤ (9081039160603/20000000000000 : ℝ)^1555
        have hw : |(1380324499/2500000000 : ℝ)|=(1380324499/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-500534003/2500000000 : ℝ)|^2067 ≤ (2947426926559/25000000000000 : ℝ)^1555
        have hw : |(-500534003/2500000000 : ℝ)|=(500534003/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_s2_7 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2181079677/5000000000 : ℝ)*x 0 + (296369641/625000000 : ℝ)*x 1 + (4013490223/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2181079677/5000000000 : ℝ)^2067 ≤ (8298689163461/25000000000000 : ℝ)^1555 := by
    have hnat : (2181079677 : ℕ)^2067*25000000000000^1555 ≤ 8298689163461^1555*5000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181079677 5000000000 8298689163461 25000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (296369641/625000000 : ℝ)^2067 ≤ (4636263149087/12500000000000 : ℝ)^1555 := by
    have hnat : (296369641 : ℕ)^2067*12500000000000^1555 ≤ 4636263149087^1555*625000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      296369641 625000000 4636263149087 12500000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4013490223/10000000000 : ℝ)^2067 ≤ (7428784534679/25000000000000 : ℝ)^1555 := by
    have hnat : (4013490223 : ℕ)^2067*25000000000000^1555 ≤ 7428784534679^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4013490223 10000000000 7428784534679 25000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2181079677/5000000000 : ℝ), (296369641/625000000 : ℝ), (4013490223/10000000000 : ℝ)] ![(8298689163461/25000000000000 : ℝ), (4636263149087/12500000000000 : ℝ), (7428784534679/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2181079677/5000000000 : ℝ)|^2067 ≤ (8298689163461/25000000000000 : ℝ)^1555
        have hw : |(2181079677/5000000000 : ℝ)|=(2181079677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(296369641/625000000 : ℝ)|^2067 ≤ (4636263149087/12500000000000 : ℝ)^1555
        have hw : |(296369641/625000000 : ℝ)|=(296369641/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4013490223/10000000000 : ℝ)|^2067 ≤ (7428784534679/25000000000000 : ℝ)^1555
        have hw : |(4013490223/10000000000 : ℝ)|=(4013490223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_s2_8 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-50292723/5000000000 : ℝ)*x 0 + (5926783349/10000000000 : ℝ)*x 1 + (5926594207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (50292723/5000000000 : ℝ)^2067 ≤ (221232521331/100000000000000 : ℝ)^1555 := by
    have hnat : (50292723 : ℕ)^2067*100000000000000^1555 ≤ 221232521331^1555*5000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50292723 5000000000 221232521331 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5926783349/10000000000 : ℝ)^2067 ≤ (9978088385133/20000000000000 : ℝ)^1555 := by
    have hnat : (5926783349 : ℕ)^2067*20000000000000^1555 ≤ 9978088385133^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5926783349 10000000000 9978088385133 20000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5926594207/10000000000 : ℝ)^2067 ≤ (6236040692947/12500000000000 : ℝ)^1555 := by
    have hnat : (5926594207 : ℕ)^2067*12500000000000^1555 ≤ 6236040692947^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5926594207 10000000000 6236040692947 12500000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-50292723/5000000000 : ℝ), (5926783349/10000000000 : ℝ), (5926594207/10000000000 : ℝ)] ![(221232521331/100000000000000 : ℝ), (9978088385133/20000000000000 : ℝ), (6236040692947/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-50292723/5000000000 : ℝ)|^2067 ≤ (221232521331/100000000000000 : ℝ)^1555
        have hw : |(-50292723/5000000000 : ℝ)|=(50292723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5926783349/10000000000 : ℝ)|^2067 ≤ (9978088385133/20000000000000 : ℝ)^1555
        have hw : |(5926783349/10000000000 : ℝ)|=(5926783349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5926594207/10000000000 : ℝ)|^2067 ≤ (6236040692947/12500000000000 : ℝ)^1555
        have hw : |(5926594207/10000000000 : ℝ)|=(5926594207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_s2_9 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (796576981/10000000000 : ℝ)*x 0 + (-4963729799/10000000000 : ℝ)*x 1 + (6562209653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (796576981/10000000000 : ℝ)^2067 ≤ (865736077399/25000000000000 : ℝ)^1555 := by
    have hnat : (796576981 : ℕ)^2067*25000000000000^1555 ≤ 865736077399^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      796576981 10000000000 865736077399 25000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4963729799/10000000000 : ℝ)^2067 ≤ (19706966837433/50000000000000 : ℝ)^1555 := by
    have hnat : (4963729799 : ℕ)^2067*50000000000000^1555 ≤ 19706966837433^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4963729799 10000000000 19706966837433 50000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6562209653/10000000000 : ℝ)^2067 ≤ (28561561004199/50000000000000 : ℝ)^1555 := by
    have hnat : (6562209653 : ℕ)^2067*50000000000000^1555 ≤ 28561561004199^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6562209653 10000000000 28561561004199 50000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(796576981/10000000000 : ℝ), (-4963729799/10000000000 : ℝ), (6562209653/10000000000 : ℝ)] ![(865736077399/25000000000000 : ℝ), (19706966837433/50000000000000 : ℝ), (28561561004199/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(796576981/10000000000 : ℝ)|^2067 ≤ (865736077399/25000000000000 : ℝ)^1555
        have hw : |(796576981/10000000000 : ℝ)|=(796576981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4963729799/10000000000 : ℝ)|^2067 ≤ (19706966837433/50000000000000 : ℝ)^1555
        have hw : |(-4963729799/10000000000 : ℝ)|=(4963729799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6562209653/10000000000 : ℝ)|^2067 ≤ (28561561004199/50000000000000 : ℝ)^1555
        have hw : |(6562209653/10000000000 : ℝ)|=(6562209653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_s2_10 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (397607193/5000000000 : ℝ)*x 0 + (262348179/400000000 : ℝ)*x 1 + (-1242079301/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (397607193/5000000000 : ℝ)^2067 ≤ (3455072542003/100000000000000 : ℝ)^1555 := by
    have hnat : (397607193 : ℕ)^2067*100000000000000^1555 ≤ 3455072542003^1555*5000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397607193 5000000000 3455072542003 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (262348179/400000000 : ℝ)^2067 ≤ (57082567065161/100000000000000 : ℝ)^1555 := by
    have hnat : (262348179 : ℕ)^2067*100000000000000^1555 ≤ 57082567065161^1555*400000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262348179 400000000 57082567065161 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1242079301/2500000000 : ℝ)^2067 ≤ (19731180187377/50000000000000 : ℝ)^1555 := by
    have hnat : (1242079301 : ℕ)^2067*50000000000000^1555 ≤ 19731180187377^1555*2500000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1242079301 2500000000 19731180187377 50000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(397607193/5000000000 : ℝ), (262348179/400000000 : ℝ), (-1242079301/2500000000 : ℝ)] ![(3455072542003/100000000000000 : ℝ), (57082567065161/100000000000000 : ℝ), (19731180187377/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(397607193/5000000000 : ℝ)|^2067 ≤ (3455072542003/100000000000000 : ℝ)^1555
        have hw : |(397607193/5000000000 : ℝ)|=(397607193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(262348179/400000000 : ℝ)|^2067 ≤ (57082567065161/100000000000000 : ℝ)^1555
        have hw : |(262348179/400000000 : ℝ)|=(262348179/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1242079301/2500000000 : ℝ)|^2067 ≤ (19731180187377/50000000000000 : ℝ)^1555
        have hw : |(-1242079301/2500000000 : ℝ)|=(1242079301/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1075_s2_11 (p : ℝ) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ)) (x : Fin 3 → ℝ) :
    (419397231/10000000000 : ℝ)*x 0 + (2934296251/5000000000 : ℝ)*x 1 + (23489851/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (419397231/10000000000 : ℝ)^2067 ≤ (738041248009/50000000000000 : ℝ)^1555 := by
    have hnat : (419397231 : ℕ)^2067*50000000000000^1555 ≤ 738041248009^1555*10000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419397231 10000000000 738041248009 50000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2934296251/5000000000 : ℝ)^2067 ≤ (49240373675601/100000000000000 : ℝ)^1555 := by
    have hnat : (2934296251 : ℕ)^2067*100000000000000^1555 ≤ 49240373675601^1555*5000000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2934296251 5000000000 49240373675601 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (23489851/40000000 : ℝ)^2067 ≤ (49283543810537/100000000000000 : ℝ)^1555 := by
    have hnat : (23489851 : ℕ)^2067*100000000000000^1555 ≤ 49283543810537^1555*40000000^2067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23489851 40000000 49283543810537 100000000000000 2067 1555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2067/512 : ℝ)) 2067 1555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(419397231/10000000000 : ℝ), (2934296251/5000000000 : ℝ), (23489851/40000000 : ℝ)] ![(738041248009/50000000000000 : ℝ), (49240373675601/100000000000000 : ℝ), (49283543810537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(419397231/10000000000 : ℝ)|^2067 ≤ (738041248009/50000000000000 : ℝ)^1555
        have hw : |(419397231/10000000000 : ℝ)|=(419397231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2934296251/5000000000 : ℝ)|^2067 ≤ (49240373675601/100000000000000 : ℝ)^1555
        have hw : |(2934296251/5000000000 : ℝ)|=(2934296251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(23489851/40000000 : ℝ)|^2067 ≤ (49283543810537/100000000000000 : ℝ)^1555
        have hw : |(23489851/40000000 : ℝ)|=(23489851/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1075_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148168151/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5187/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2633/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2189/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16711/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5187/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2633/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5187/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2633/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5187/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2633/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5187/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2633/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5187/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2633/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5187/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2633/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2633/50000 : ℝ) ^ (8267/2048 : ℝ) ≤ (138080593563457/20000000000000000000 : ℝ) := by
    have hpowers : (2633/50000 : ℝ)^8267 ≤ (138080593563457/20000000000000000000 : ℝ)^2048 := by
      have hnat : (2633 : ℕ)^8267*20000000000000000000^2048 ≤ 138080593563457^2048*50000^8267 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2633 50000 138080593563457 20000000000000000000 8267 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2633/50000 : ℝ)) (X := (138080593563457/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8267 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (5187/25000 : ℝ) ^ (8267/2048 : ℝ) ≤ (174941110934396279/100000000000000000000 : ℝ) := by
    have hpowers : (5187/25000 : ℝ)^8267 ≤ (174941110934396279/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5187 : ℕ)^8267*100000000000000000000^2048 ≤ 174941110934396279^2048*25000^8267 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5187 25000 174941110934396279 100000000000000000000 8267 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5187/25000 : ℝ)) (X := (174941110934396279/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8267 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000138080593563457/10000000000000000000 : ℝ) ≤ (10000034206796531/10000000000000000 : ℝ) ^ (8267/2048 : ℝ) := by
    have hpowers : (10000138080593563457/10000000000000000000 : ℝ)^2048 ≤ (10000034206796531/10000000000000000 : ℝ)^8267 := by
      have hnat : (10000138080593563457 : ℕ)^2048*10000000000000000^8267 ≤ 10000034206796531^8267*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000138080593563457 10000000000000000000 10000034206796531 10000000000000000 2048 8267 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000034206796531/10000000000000000 : ℝ)) (X := (10000138080593563457/10000000000000000000 : ℝ)) (by norm_num) 8267 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25043907878475553391/25000000000000000000 : ℝ) ≤ (10004348082338929/10000000000000000 : ℝ) ^ (8267/2048 : ℝ) := by
    have hpowers : (25043907878475553391/25000000000000000000 : ℝ)^2048 ≤ (10004348082338929/10000000000000000 : ℝ)^8267 := by
      have hnat : (25043907878475553391 : ℕ)^2048*10000000000000000^8267 ≤ 10004348082338929^8267*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25043907878475553391 25000000000000000000 10004348082338929 10000000000000000 2048 8267 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004348082338929/10000000000000000 : ℝ)) (X := (25043907878475553391/25000000000000000000 : ℝ)) (by norm_num) 8267 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50174941110934396279/50000000000000000000 : ℝ) ≤ (10008661957881327/10000000000000000 : ℝ) ^ (8267/2048 : ℝ) := by
    have hpowers : (50174941110934396279/50000000000000000000 : ℝ)^2048 ≤ (10008661957881327/10000000000000000 : ℝ)^8267 := by
      have hnat : (50174941110934396279 : ℕ)^2048*10000000000000000^8267 ≤ 10008661957881327^8267*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50174941110934396279 50000000000000000000 10008661957881327 10000000000000000 2048 8267 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10008661957881327/10000000000000000 : ℝ)) (X := (50174941110934396279/50000000000000000000 : ℝ)) (by norm_num) 8267 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(138080593563457/20000000000000000000 : ℝ) ≤ ((77387547926205678603/77410000000000000000 : ℝ)+2*(2156937771199/774100000000000 : ℝ)*(2633/50000 : ℝ))^(8267/2048 : ℝ) := by
    rw [show (77387547926205678603/77410000000000000000 : ℝ)+2*(2156937771199/774100000000000 : ℝ)*(2633/50000 : ℝ)=(10000034206796531/10000000000000000 : ℝ) by norm_num, show 1+2*(138080593563457/20000000000000000000 : ℝ)=(10000138080593563457/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(174941110934396279/100000000000000000000 : ℝ)+(138080593563457/20000000000000000000 : ℝ) ≤ ((77387547926205678603/77410000000000000000 : ℝ)+(2156937771199/774100000000000 : ℝ)*((5187/25000 : ℝ)+(2633/50000 : ℝ)))^(8267/2048 : ℝ) := by
    rw [show (77387547926205678603/77410000000000000000 : ℝ)+(2156937771199/774100000000000 : ℝ)*((5187/25000 : ℝ)+(2633/50000 : ℝ))=(10004348082338929/10000000000000000 : ℝ) by norm_num, show 1+(174941110934396279/100000000000000000000 : ℝ)+(138080593563457/20000000000000000000 : ℝ)=(25043907878475553391/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(174941110934396279/100000000000000000000 : ℝ) ≤ ((77387547926205678603/77410000000000000000 : ℝ)+2*(2156937771199/774100000000000 : ℝ)*(5187/25000 : ℝ))^(8267/2048 : ℝ) := by
    rw [show (77387547926205678603/77410000000000000000 : ℝ)+2*(2156937771199/774100000000000 : ℝ)*(5187/25000 : ℝ)=(10008661957881327/10000000000000000 : ℝ) by norm_num, show 1+2*(174941110934396279/100000000000000000000 : ℝ)=(50174941110934396279/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (77387547926205678603/77410000000000000000 : ℝ)*(X 1 0+X 2 0)+(2156937771199/774100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8267/2048 : ℝ)) (lo := (2633/50000 : ℝ)) (hi := (5187/25000 : ℝ)) (c := (77387547926205678603/77410000000000000000 : ℝ)) (alpha := (2156937771199/774100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (77387547926205678603/77410000000000000000 : ℝ)*(X 0 1+X 2 1)+(2156937771199/774100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8267/2048 : ℝ)) (lo := (2633/50000 : ℝ)) (hi := (5187/25000 : ℝ)) (c := (77387547926205678603/77410000000000000000 : ℝ)) (alpha := (2156937771199/774100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (77387547926205678603/77410000000000000000 : ℝ)*(X 0 2+X 1 2)+(2156937771199/774100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8267/2048 : ℝ)) (lo := (2633/50000 : ℝ)) (hi := (5187/25000 : ℝ)) (c := (77387547926205678603/77410000000000000000 : ℝ)) (alpha := (2156937771199/774100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-435920233/2000000000 : ℝ)*X 0 0+(5524049749/10000000000 : ℝ)*X 0 1+(1286891581/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((336050129/625000000 : ℝ)*X 1 0+(-2375864247/10000000000 : ℝ)*X 1 1+(5147567199/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2100313/3906250 : ℝ)*X 2 0+(5147568003/10000000000 : ℝ)*X 2 1+(-475172847/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((872384437/2000000000 : ℝ)*X 0 0+(250505771/625000000 : ℝ)*X 0 1+(1186813083/2500000000 : ℝ)*X 0 2+(872384437/2000000000 : ℝ)*X 1 0+(250505771/625000000 : ℝ)*X 1 1+(1186813083/2500000000 : ℝ)*X 1 2+(872384437/2000000000 : ℝ)*X 2 0+(250505771/625000000 : ℝ)*X 2 1+(1186813083/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-87188947/400000000 : ℝ)*X 0 0+(2575144963/5000000000 : ℝ)*X 0 1+(345081129/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((264085627/500000000 : ℝ)*X 1 0+(-1001068061/5000000000 : ℝ)*X 1 1+(1380324539/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2640856391/5000000000 : ℝ)*X 2 0+(1380324499/2500000000 : ℝ)*X 2 1+(-500534003/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2181079677/5000000000 : ℝ)*X 0 0+(296369641/625000000 : ℝ)*X 0 1+(4013490223/10000000000 : ℝ)*X 0 2+(2181079677/5000000000 : ℝ)*X 1 0+(296369641/625000000 : ℝ)*X 1 1+(4013490223/10000000000 : ℝ)*X 1 2+(2181079677/5000000000 : ℝ)*X 2 0+(296369641/625000000 : ℝ)*X 2 1+(4013490223/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-50292723/5000000000 : ℝ)*X 0 0+(5926783349/10000000000 : ℝ)*X 0 1+(5926594207/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_s2_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((796576981/10000000000 : ℝ)*X 1 0+(-4963729799/10000000000 : ℝ)*X 1 1+(6562209653/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_s2_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((397607193/5000000000 : ℝ)*X 2 0+(262348179/400000000 : ℝ)*X 2 1+(-1242079301/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_s2_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((419397231/10000000000 : ℝ)*X 0 0+(2934296251/5000000000 : ℝ)*X 0 1+(23489851/40000000 : ℝ)*X 0 2+(419397231/10000000000 : ℝ)*X 1 0+(2934296251/5000000000 : ℝ)*X 1 1+(23489851/40000000 : ℝ)*X 1 2+(419397231/10000000000 : ℝ)*X 2 0+(2934296251/5000000000 : ℝ)*X 2 1+(23489851/40000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1075_s2_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6917969498321477753371284849/3870500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2004551066751813/100000000000000 : ℝ)*(major0) + (2004551066751813/100000000000000 : ℝ)*(major1) + (2004551066751813/100000000000000 : ℝ)*(major2) + (664046406286787/25000000000000 : ℝ)*(sp0) + (1328097717728137/50000000000000 : ℝ)*(sp1) + (132809965162673/5000000000000 : ℝ)*(sp2) + (1352887446418351/100000000000000 : ℝ)*(sp3) + (12904261059/50000000000000 : ℝ)*(sp4) + (15524704789/100000000000000 : ℝ)*(sp5) + (481585673/4000000000000 : ℝ)*(sp6) + (334074357/25000000000000 : ℝ)*(sp8) + (1809805631/100000000000000 : ℝ)*(sp9) + (142707141/10000000000000 : ℝ)*(sp10) + (1857539969/100000000000000 : ℝ)*(sp11) + (16911116299479/1250000000000 : ℝ)*(f.failure) + (531242553993339/20000000000000 : ℝ)*(f.sum) + (49894276939493/38705000000000000000000000000 : ℝ)*base66 + (50151233205318257239/7741000000000000000000000000000000 : ℝ)*base67 + (49808488694962257239/7741000000000000000000000000000000 : ℝ)*base69 + (30667287038703257239/7741000000000000000000000000000000 : ℝ)*base71 + (50215880658929/19352500000000000000000000000 : ℝ)*base74 + (77866838136189257239/7741000000000000000000000000000000 : ℝ)*base75 + (12437567974880257239/7741000000000000000000000000000000 : ℝ)*base77 + (31000716501860257239/7741000000000000000000000000000000 : ℝ)*base79 + (13887002605177/38705000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (556671/125000000000000000000 : ℝ)*base90 + (556671/125000000000000000000 : ℝ)*base92 + (556671/125000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (115510589024356189691606727/24190625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6356543261039/312500000000 : ℝ)*(major0) + (6356543261039/312500000000 : ℝ)*(major1) + (6356543261039/312500000000 : ℝ)*(major2) + (581717461/100000000000000 : ℝ)*(sp1) + (13261261/25000000000000 : ℝ)*(sp2) + (357359309/100000000000000 : ℝ)*(sp3) + (336919865420799/12500000000000 : ℝ)*(sp4) + (134767937430061/5000000000000 : ℝ)*(sp5) + (673839785789051/25000000000000 : ℝ)*(sp6) + (686413624206211/50000000000000 : ℝ)*(sp7) + (77294007/12500000000000 : ℝ)*(sp8) + (211399767/100000000000000 : ℝ)*(sp9) + (863793/250000000000 : ℝ)*(sp10) + (380407621/100000000000000 : ℝ)*(sp11) + (1372827986179351/100000000000000 : ℝ)*(f.failure) + (168459971357403/6250000000000 : ℝ)*(f.sum) + (7737234914861/1935250000000000000000000000 : ℝ)*base66 + (125081611049595233/24190625000000000000000000000000 : ℝ)*base68 + (159140728704563983/24190625000000000000000000000000 : ℝ)*base70 + (31765371143419571/12095312500000000000000000000000 : ℝ)*base71 + (18472960229637/3870500000000000000000000000 : ℝ)*base74 + (136291672949657733/24190625000000000000000000000000 : ℝ)*base76 + (190947763952786017/24190625000000000000000000000000 : ℝ)*base77 + (107095440608907733/24190625000000000000000000000000 : ℝ)*base80 + (335474837331/241906250000000000000000000 : ℝ)*base82 + (7949999/10000000000000000000000 : ℝ)*base90 + (7949999/10000000000000000000000 : ℝ)*base92 + (7949999/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1075_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148168151/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5187/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2633/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2189/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16711/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1075_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1075_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148168151/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2189/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16711/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1075_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1075_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1075_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8267/2048 : ℝ) ≤ p) (hpb : p ≤ (2067/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148168151/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2189/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16711/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1075_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
