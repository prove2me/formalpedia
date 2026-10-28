-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1255_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:25:26.761471+00:00
-- url     : https://prove2.me/submissions/92110687-b88f-4bf2-9545-72a3ca72052e

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
theorem support_rectangle_w1255_s0_0 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-29008679/156250000 : ℝ)*x 0 + (3014290053/5000000000 : ℝ)*x 1 + (4794595219/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (29008679/156250000 : ℝ)^33 ≤ (10831646118521/100000000000000 : ℝ)^25 := by
    have hnat : (29008679 : ℕ)^33*100000000000000^25 ≤ 10831646118521^25*156250000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      29008679 156250000 10831646118521 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3014290053/5000000000 : ℝ)^33 ≤ (51272423715701/100000000000000 : ℝ)^25 := by
    have hnat : (3014290053 : ℕ)^33*100000000000000^25 ≤ 51272423715701^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3014290053 5000000000 51272423715701 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4794595219/10000000000 : ℝ)^33 ≤ (37895930160193/100000000000000 : ℝ)^25 := by
    have hnat : (4794595219 : ℕ)^33*100000000000000^25 ≤ 37895930160193^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4794595219 10000000000 37895930160193 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-29008679/156250000 : ℝ), (3014290053/5000000000 : ℝ), (4794595219/10000000000 : ℝ)] ![(10831646118521/100000000000000 : ℝ), (51272423715701/100000000000000 : ℝ), (37895930160193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-29008679/156250000 : ℝ)|^33 ≤ (10831646118521/100000000000000 : ℝ)^25
        have hw : |(-29008679/156250000 : ℝ)|=(29008679/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3014290053/5000000000 : ℝ)|^33 ≤ (51272423715701/100000000000000 : ℝ)^25
        have hw : |(3014290053/5000000000 : ℝ)|=(3014290053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4794595219/10000000000 : ℝ)|^33 ≤ (37895930160193/100000000000000 : ℝ)^25
        have hw : |(4794595219/10000000000 : ℝ)|=(4794595219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1255_s0_1 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5510427131/10000000000 : ℝ)*x 0 + (-2561646559/10000000000 : ℝ)*x 1 + (119864879/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5510427131/10000000000 : ℝ)^33 ≤ (45537013885537/100000000000000 : ℝ)^25 := by
    have hnat : (5510427131 : ℕ)^33*100000000000000^25 ≤ 45537013885537^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5510427131 10000000000 45537013885537 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2561646559/10000000000 : ℝ)^33 ≤ (3313411310491/20000000000000 : ℝ)^25 := by
    have hnat : (2561646559 : ℕ)^33*20000000000000^25 ≤ 3313411310491^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2561646559 10000000000 3313411310491 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (119864879/250000000 : ℝ)^33 ≤ (37895929544639/100000000000000 : ℝ)^25 := by
    have hnat : (119864879 : ℕ)^33*100000000000000^25 ≤ 37895929544639^25*250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      119864879 250000000 37895929544639 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5510427131/10000000000 : ℝ), (-2561646559/10000000000 : ℝ), (119864879/250000000 : ℝ)] ![(45537013885537/100000000000000 : ℝ), (3313411310491/20000000000000 : ℝ), (37895929544639/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5510427131/10000000000 : ℝ)|^33 ≤ (45537013885537/100000000000000 : ℝ)^25
        have hw : |(5510427131/10000000000 : ℝ)|=(5510427131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2561646559/10000000000 : ℝ)|^33 ≤ (3313411310491/20000000000000 : ℝ)^25
        have hw : |(-2561646559/10000000000 : ℝ)|=(2561646559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(119864879/250000000 : ℝ)|^33 ≤ (37895929544639/100000000000000 : ℝ)^25
        have hw : |(119864879/250000000 : ℝ)|=(119864879/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1255_s0_2 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (172200847/312500000 : ℝ)*x 0 + (4794595219/10000000000 : ℝ)*x 1 + (-1280823261/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (172200847/312500000 : ℝ)^33 ≤ (5692126698877/12500000000000 : ℝ)^25 := by
    have hnat : (172200847 : ℕ)^33*12500000000000^25 ≤ 5692126698877^25*312500000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172200847 312500000 5692126698877 12500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4794595219/10000000000 : ℝ)^33 ≤ (37895930160193/100000000000000 : ℝ)^25 := by
    have hnat : (4794595219 : ℕ)^33*100000000000000^25 ≤ 37895930160193^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4794595219 10000000000 37895930160193 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1280823261/5000000000 : ℝ)^33 ≤ (16567056236589/100000000000000 : ℝ)^25 := by
    have hnat : (1280823261 : ℕ)^33*100000000000000^25 ≤ 16567056236589^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1280823261 5000000000 16567056236589 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(172200847/312500000 : ℝ), (4794595219/10000000000 : ℝ), (-1280823261/5000000000 : ℝ)] ![(5692126698877/12500000000000 : ℝ), (37895930160193/100000000000000 : ℝ), (16567056236589/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(172200847/312500000 : ℝ)|^33 ≤ (5692126698877/12500000000000 : ℝ)^25
        have hw : |(172200847/312500000 : ℝ)|=(172200847/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4794595219/10000000000 : ℝ)|^33 ≤ (37895930160193/100000000000000 : ℝ)^25
        have hw : |(4794595219/10000000000 : ℝ)|=(4794595219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1280823261/5000000000 : ℝ)|^33 ≤ (16567056236589/100000000000000 : ℝ)^25
        have hw : |(-1280823261/5000000000 : ℝ)|=(1280823261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1255_s0_3 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4192002401/10000000000 : ℝ)*x 0 + (97387821/312500000 : ℝ)*x 1 + (1406480161/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4192002401/10000000000 : ℝ)^33 ≤ (31739231718549/100000000000000 : ℝ)^25 := by
    have hnat : (4192002401 : ℕ)^33*100000000000000^25 ≤ 31739231718549^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4192002401 10000000000 31739231718549 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (97387821/312500000 : ℝ)^33 ≤ (429194456059/2000000000000 : ℝ)^25 := by
    have hnat : (97387821 : ℕ)^33*2000000000000^25 ≤ 429194456059^25*312500000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      97387821 312500000 429194456059 2000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1406480161/2500000000 : ℝ)^33 ≤ (9360209091373/20000000000000 : ℝ)^25 := by
    have hnat : (1406480161 : ℕ)^33*20000000000000^25 ≤ 9360209091373^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1406480161 2500000000 9360209091373 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4192002401/10000000000 : ℝ), (97387821/312500000 : ℝ), (1406480161/2500000000 : ℝ)] ![(31739231718549/100000000000000 : ℝ), (429194456059/2000000000000 : ℝ), (9360209091373/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4192002401/10000000000 : ℝ)|^33 ≤ (31739231718549/100000000000000 : ℝ)^25
        have hw : |(4192002401/10000000000 : ℝ)|=(4192002401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(97387821/312500000 : ℝ)|^33 ≤ (429194456059/2000000000000 : ℝ)^25
        have hw : |(97387821/312500000 : ℝ)|=(97387821/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1406480161/2500000000 : ℝ)|^33 ≤ (9360209091373/20000000000000 : ℝ)^25
        have hw : |(1406480161/2500000000 : ℝ)|=(1406480161/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1255_s0_4 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1861376091/10000000000 : ℝ)*x 0 + (4826364397/10000000000 : ℝ)*x 1 + (1199137529/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1861376091/10000000000 : ℝ)^33 ≤ (10868786383709/100000000000000 : ℝ)^25 := by
    have hnat : (1861376091 : ℕ)^33*100000000000000^25 ≤ 10868786383709^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1861376091 10000000000 10868786383709 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4826364397/10000000000 : ℝ)^33 ≤ (19113866471529/50000000000000 : ℝ)^25 := by
    have hnat : (4826364397 : ℕ)^33*50000000000000^25 ≤ 19113866471529^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4826364397 10000000000 19113866471529 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1199137529/2000000000 : ℝ)^33 ≤ (50903480654027/100000000000000 : ℝ)^25 := by
    have hnat : (1199137529 : ℕ)^33*100000000000000^25 ≤ 50903480654027^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1199137529 2000000000 50903480654027 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1861376091/10000000000 : ℝ), (4826364397/10000000000 : ℝ), (1199137529/2000000000 : ℝ)] ![(10868786383709/100000000000000 : ℝ), (19113866471529/50000000000000 : ℝ), (50903480654027/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1861376091/10000000000 : ℝ)|^33 ≤ (10868786383709/100000000000000 : ℝ)^25
        have hw : |(-1861376091/10000000000 : ℝ)|=(1861376091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4826364397/10000000000 : ℝ)|^33 ≤ (19113866471529/50000000000000 : ℝ)^25
        have hw : |(4826364397/10000000000 : ℝ)|=(4826364397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1199137529/2000000000 : ℝ)|^33 ≤ (50903480654027/100000000000000 : ℝ)^25
        have hw : |(1199137529/2000000000 : ℝ)|=(1199137529/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1255_s0_5 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1293655749/2500000000 : ℝ)*x 0 + (-680275909/5000000000 : ℝ)*x 1 + (5995690021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1293655749/2500000000 : ℝ)^33 ≤ (41910216345711/100000000000000 : ℝ)^25 := by
    have hnat : (1293655749 : ℕ)^33*100000000000000^25 ≤ 41910216345711^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1293655749 2500000000 41910216345711 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (680275909/5000000000 : ℝ)^33 ≤ (3593138180969/50000000000000 : ℝ)^25 := by
    have hnat : (680275909 : ℕ)^33*50000000000000^25 ≤ 3593138180969^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      680275909 5000000000 3593138180969 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5995690021/10000000000 : ℝ)^33 ≤ (25451753640717/50000000000000 : ℝ)^25 := by
    have hnat : (5995690021 : ℕ)^33*50000000000000^25 ≤ 25451753640717^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5995690021 10000000000 25451753640717 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1293655749/2500000000 : ℝ), (-680275909/5000000000 : ℝ), (5995690021/10000000000 : ℝ)] ![(41910216345711/100000000000000 : ℝ), (3593138180969/50000000000000 : ℝ), (25451753640717/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1293655749/2500000000 : ℝ)|^33 ≤ (41910216345711/100000000000000 : ℝ)^25
        have hw : |(1293655749/2500000000 : ℝ)|=(1293655749/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-680275909/5000000000 : ℝ)|^33 ≤ (3593138180969/50000000000000 : ℝ)^25
        have hw : |(-680275909/5000000000 : ℝ)|=(680275909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5995690021/10000000000 : ℝ)|^33 ≤ (25451753640717/50000000000000 : ℝ)^25
        have hw : |(5995690021/10000000000 : ℝ)|=(5995690021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1255_s0_6 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2587312003/5000000000 : ℝ)*x 0 + (599568807/1000000000 : ℝ)*x 1 + (-272110681/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2587312003/5000000000 : ℝ)^33 ≤ (41910227143541/100000000000000 : ℝ)^25 := by
    have hnat : (2587312003 : ℕ)^33*100000000000000^25 ≤ 41910227143541^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587312003 5000000000 41910227143541 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (599568807/1000000000 : ℝ)^33 ≤ (25451742708463/50000000000000 : ℝ)^25 := by
    have hnat : (599568807 : ℕ)^33*50000000000000^25 ≤ 25451742708463^25*1000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      599568807 1000000000 25451742708463 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (272110681/2000000000 : ℝ)^33 ≤ (7186287426641/100000000000000 : ℝ)^25 := by
    have hnat : (272110681 : ℕ)^33*100000000000000^25 ≤ 7186287426641^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272110681 2000000000 7186287426641 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2587312003/5000000000 : ℝ), (599568807/1000000000 : ℝ), (-272110681/2000000000 : ℝ)] ![(41910227143541/100000000000000 : ℝ), (25451742708463/50000000000000 : ℝ), (7186287426641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2587312003/5000000000 : ℝ)|^33 ≤ (41910227143541/100000000000000 : ℝ)^25
        have hw : |(2587312003/5000000000 : ℝ)|=(2587312003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(599568807/1000000000 : ℝ)|^33 ≤ (25451742708463/50000000000000 : ℝ)^25
        have hw : |(599568807/1000000000 : ℝ)|=(599568807/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-272110681/2000000000 : ℝ)|^33 ≤ (7186287426641/100000000000000 : ℝ)^25
        have hw : |(-272110681/2000000000 : ℝ)|=(272110681/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1255_s0_7 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (840361589/2000000000 : ℝ)*x 0 + (2780659193/5000000000 : ℝ)*x 1 + (3183296563/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (840361589/2000000000 : ℝ)^33 ≤ (397965839003/1250000000000 : ℝ)^25 := by
    have hnat : (840361589 : ℕ)^33*1250000000000^25 ≤ 397965839003^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      840361589 2000000000 397965839003 1250000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2780659193/5000000000 : ℝ)^33 ≤ (46092964623591/100000000000000 : ℝ)^25 := by
    have hnat : (2780659193 : ℕ)^33*100000000000000^25 ≤ 46092964623591^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2780659193 5000000000 46092964623591 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3183296563/10000000000 : ℝ)^33 ≤ (551744205879/2500000000000 : ℝ)^25 := by
    have hnat : (3183296563 : ℕ)^33*2500000000000^25 ≤ 551744205879^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3183296563 10000000000 551744205879 2500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(840361589/2000000000 : ℝ), (2780659193/5000000000 : ℝ), (3183296563/10000000000 : ℝ)] ![(397965839003/1250000000000 : ℝ), (46092964623591/100000000000000 : ℝ), (551744205879/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(840361589/2000000000 : ℝ)|^33 ≤ (397965839003/1250000000000 : ℝ)^25
        have hw : |(840361589/2000000000 : ℝ)|=(840361589/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2780659193/5000000000 : ℝ)|^33 ≤ (46092964623591/100000000000000 : ℝ)^25
        have hw : |(2780659193/5000000000 : ℝ)|=(2780659193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3183296563/10000000000 : ℝ)|^33 ≤ (551744205879/2500000000000 : ℝ)^25
        have hw : |(3183296563/10000000000 : ℝ)|=(3183296563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1255_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37920797/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (87/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6847/25000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (8447/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8447 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8447*1^2048 ≤ 0^2048*1^8447 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8447 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8447 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8447/2048 : ℝ) ≤ (2283977235022623983/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8447 ≤ (2283977235022623983/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8447*100000000000000000000^2048 ≤ 2283977235022623983^2048*5^8447 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2283977235022623983 100000000000000000000 8447 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2283977235022623983/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8447 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8447/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8447 := by
      have hnat : (1 : ℕ)^2048*1^8447 ≤ 1^8447*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8447 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8447 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (102283977235022623983/100000000000000000000 : ℝ) ≤ (628431434382287/625000000000000 : ℝ) ^ (8447/2048 : ℝ) := by
    have hpowers : (102283977235022623983/100000000000000000000 : ℝ)^2048 ≤ (628431434382287/625000000000000 : ℝ)^8447 := by
      have hnat : (102283977235022623983 : ℕ)^2048*625000000000000^8447 ≤ 628431434382287^8447*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102283977235022623983 100000000000000000000 628431434382287 625000000000000 2048 8447 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (628431434382287/625000000000000 : ℝ)) (X := (102283977235022623983/100000000000000000000 : ℝ)) (by norm_num) 8447 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (52283977235022623983/50000000000000000000 : ℝ) ≤ (315931434382287/312500000000000 : ℝ) ^ (8447/2048 : ℝ) := by
    have hpowers : (52283977235022623983/50000000000000000000 : ℝ)^2048 ≤ (315931434382287/312500000000000 : ℝ)^8447 := by
      have hnat : (52283977235022623983 : ℕ)^2048*312500000000000^8447 ≤ 315931434382287^8447*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52283977235022623983 50000000000000000000 315931434382287 312500000000000 2048 8447 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (315931434382287/312500000000000 : ℝ)) (X := (52283977235022623983/50000000000000000000 : ℝ)) (by norm_num) 8447 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(3431434382287/250000000000000 : ℝ)*(0 : ℝ))^(8447/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(3431434382287/250000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2283977235022623983/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(3431434382287/250000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8447/2048 : ℝ) := by
    rw [show (1 : ℝ)+(3431434382287/250000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(628431434382287/625000000000000 : ℝ) by norm_num, show 1+(2283977235022623983/100000000000000000000 : ℝ)+(0 : ℝ)=(102283977235022623983/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2283977235022623983/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(3431434382287/250000000000000 : ℝ)*(2/5 : ℝ))^(8447/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(3431434382287/250000000000000 : ℝ)*(2/5 : ℝ)=(315931434382287/312500000000000 : ℝ) by norm_num, show 1+2*(2283977235022623983/100000000000000000000 : ℝ)=(52283977235022623983/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(3431434382287/250000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8447/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (3431434382287/250000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(3431434382287/250000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8447/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (3431434382287/250000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(3431434382287/250000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8447/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (3431434382287/250000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-29008679/156250000 : ℝ)*X 0 0+(3014290053/5000000000 : ℝ)*X 0 1+(4794595219/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5510427131/10000000000 : ℝ)*X 1 0+(-2561646559/10000000000 : ℝ)*X 1 1+(119864879/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((172200847/312500000 : ℝ)*X 2 0+(4794595219/10000000000 : ℝ)*X 2 1+(-1280823261/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4192002401/10000000000 : ℝ)*X 0 0+(97387821/312500000 : ℝ)*X 0 1+(1406480161/2500000000 : ℝ)*X 0 2+(4192002401/10000000000 : ℝ)*X 1 0+(97387821/312500000 : ℝ)*X 1 1+(1406480161/2500000000 : ℝ)*X 1 2+(4192002401/10000000000 : ℝ)*X 2 0+(97387821/312500000 : ℝ)*X 2 1+(1406480161/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1861376091/10000000000 : ℝ)*X 0 0+(4826364397/10000000000 : ℝ)*X 0 1+(1199137529/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1293655749/2500000000 : ℝ)*X 1 0+(-680275909/5000000000 : ℝ)*X 1 1+(5995690021/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2587312003/5000000000 : ℝ)*X 2 0+(599568807/1000000000 : ℝ)*X 2 1+(-272110681/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((840361589/2000000000 : ℝ)*X 0 0+(2780659193/5000000000 : ℝ)*X 0 1+(3183296563/10000000000 : ℝ)*X 0 2+(840361589/2000000000 : ℝ)*X 1 0+(2780659193/5000000000 : ℝ)*X 1 1+(3183296563/10000000000 : ℝ)*X 1 2+(840361589/2000000000 : ℝ)*X 2 0+(2780659193/5000000000 : ℝ)*X 2 1+(3183296563/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2024022842581124089293/781250000000000000000000000 : ℝ) := by norm_num
    linear_combination (4436921/12500000000000 : ℝ)*(base1) + (652039021/100000000000000 : ℝ)*(base19) + (15076801/2500000000000 : ℝ)*(base23) + (11249063/25000000000000 : ℝ)*(base24) + (142161477/100000000000000 : ℝ)*(upper3) + (302218083753891/50000000000000 : ℝ)*(major0) + (302218083753891/50000000000000 : ℝ)*(major1) + (302218083753891/50000000000000 : ℝ)*(major2) + (810384889991/100000000000 : ℝ)*(sp0) + (405192831610729/50000000000000 : ℝ)*(sp1) + (810385667192187/100000000000000 : ℝ)*(sp2) + (24905298474233/6250000000000 : ℝ)*(sp3) + (730382423/50000000000000 : ℝ)*(sp4) + (1122313677/100000000000000 : ℝ)*(sp7) + (398485933396773/100000000000000 : ℝ)*(f.failure) + (405193157630239/50000000000000 : ℝ)*(f.sum) + (12516807059967/6250000000000000000000000000 : ℝ)*base65 + (51564452728717/12500000000000000000000000000 : ℝ)*base67 + (46846147066217/12500000000000000000000000000 : ℝ)*base69 + (21450271591217/12500000000000000000000000000 : ℝ)*base71 + (16324690753717/6250000000000000000000000000 : ℝ)*base73 + (2228814441217/12500000000000000000000000000 : ℝ)*base75 + (23984528466217/12500000000000000000000000000 : ℝ)*base77 + (67792951591217/12500000000000000000000000000 : ℝ)*base79 + (47192934172467/6250000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (611919/2500000000000000000000 : ℝ)*base90 + (611919/2500000000000000000000 : ℝ)*base92 + (611919/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5312137139540062483773/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (29249577/12500000000000 : ℝ)*(base1) + (1967587211/100000000000000 : ℝ)*(base19) + (1062993991/50000000000000 : ℝ)*(base23) + (381589677/100000000000000 : ℝ)*(upper3) + (8936993/12500000000000 : ℝ)*(upper5) + (79732023502209/12500000000000 : ℝ)*(major0) + (79732023502209/12500000000000 : ℝ)*(major1) + (79732023502209/12500000000000 : ℝ)*(major2) + (976588391/25000000000000 : ℝ)*(sp1) + (47188769/1250000000000 : ℝ)*(sp2) + (213798403758683/25000000000000 : ℝ)*(sp4) + (855187507097341/100000000000000 : ℝ)*(sp5) + (427593739974307/50000000000000 : ℝ)*(sp6) + (105129619421657/25000000000000 : ℝ)*(sp7) + (105129677920811/25000000000000 : ℝ)*(f.failure) + (213798345259529/25000000000000 : ℝ)*(f.sum) + (2505059478017/1562500000000000000000000000 : ℝ)*base66 + (22037389440517/3125000000000000000000000000 : ℝ)*base68 + (11149160353017/3125000000000000000000000000 : ℝ)*base70 + (1905761215517/3125000000000000000000000000 : ℝ)*base72 + (4309540165571/781250000000000000000000000 : ℝ)*base74 + (28235040679/1562500000000000000000000000 : ℝ)*base75 + (6647096353017/3125000000000000000000000000 : ℝ)*base78 + (2541237115517/3125000000000000000000000000 : ℝ)*base80 + (518666668723/390625000000000000000000000 : ℝ)*base82 + (6006367/625000000000000000000 : ℝ)*base89 + (6006367/625000000000000000000 : ℝ)*base91 + (6006367/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1255_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37920797/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (87/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6847/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1255_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1255_s1_0 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-513253867/2500000000 : ℝ)*x 0 + (141809121/250000000 : ℝ)*x 1 + (1005010729/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (513253867/2500000000 : ℝ)^33 ≤ (12369659141077/100000000000000 : ℝ)^25 := by
    have hnat : (513253867 : ℕ)^33*100000000000000^25 ≤ 12369659141077^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513253867 2500000000 12369659141077 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (141809121/250000000 : ℝ)^33 ≤ (2956982156113/6250000000000 : ℝ)^25 := by
    have hnat : (141809121 : ℕ)^33*6250000000000^25 ≤ 2956982156113^25*250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141809121 250000000 2956982156113 6250000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1005010729/2000000000 : ℝ)^33 ≤ (40318626338181/100000000000000 : ℝ)^25 := by
    have hnat : (1005010729 : ℕ)^33*100000000000000^25 ≤ 40318626338181^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005010729 2000000000 40318626338181 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-513253867/2500000000 : ℝ), (141809121/250000000 : ℝ), (1005010729/2000000000 : ℝ)] ![(12369659141077/100000000000000 : ℝ), (2956982156113/6250000000000 : ℝ), (40318626338181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-513253867/2500000000 : ℝ)|^33 ≤ (12369659141077/100000000000000 : ℝ)^25
        have hw : |(-513253867/2500000000 : ℝ)|=(513253867/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(141809121/250000000 : ℝ)|^33 ≤ (2956982156113/6250000000000 : ℝ)^25
        have hw : |(141809121/250000000 : ℝ)|=(141809121/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1005010729/2000000000 : ℝ)|^33 ≤ (40318626338181/100000000000000 : ℝ)^25
        have hw : |(1005010729/2000000000 : ℝ)|=(1005010729/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1255_s1_1 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1353238923/2500000000 : ℝ)*x 0 + (-2400399603/10000000000 : ℝ)*x 1 + (5025053821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1353238923/2500000000 : ℝ)^33 ≤ (22238398464799/50000000000000 : ℝ)^25 := by
    have hnat : (1353238923 : ℕ)^33*50000000000000^25 ≤ 22238398464799^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353238923 2500000000 22238398464799 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2400399603/10000000000 : ℝ)^33 ≤ (608182994217/4000000000000 : ℝ)^25 := by
    have hnat : (2400399603 : ℕ)^33*4000000000000^25 ≤ 608182994217^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2400399603 10000000000 608182994217 4000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5025053821/10000000000 : ℝ)^33 ≤ (20159314101103/50000000000000 : ℝ)^25 := by
    have hnat : (5025053821 : ℕ)^33*50000000000000^25 ≤ 20159314101103^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5025053821 10000000000 20159314101103 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1353238923/2500000000 : ℝ), (-2400399603/10000000000 : ℝ), (5025053821/10000000000 : ℝ)] ![(22238398464799/50000000000000 : ℝ), (608182994217/4000000000000 : ℝ), (20159314101103/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1353238923/2500000000 : ℝ)|^33 ≤ (22238398464799/50000000000000 : ℝ)^25
        have hw : |(1353238923/2500000000 : ℝ)|=(1353238923/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2400399603/10000000000 : ℝ)|^33 ≤ (608182994217/4000000000000 : ℝ)^25
        have hw : |(-2400399603/10000000000 : ℝ)|=(2400399603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5025053821/10000000000 : ℝ)|^33 ≤ (20159314101103/50000000000000 : ℝ)^25
        have hw : |(5025053821/10000000000 : ℝ)|=(5025053821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1255_s1_2 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5412955851/10000000000 : ℝ)*x 0 + (2512526859/5000000000 : ℝ)*x 1 + (-300049941/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5412955851/10000000000 : ℝ)^33 ≤ (22238399327063/50000000000000 : ℝ)^25 := by
    have hnat : (5412955851 : ℕ)^33*50000000000000^25 ≤ 22238399327063^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412955851 10000000000 22238399327063 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2512526859/5000000000 : ℝ)^33 ≤ (1259957097229/3125000000000 : ℝ)^25 := by
    have hnat : (2512526859 : ℕ)^33*3125000000000^25 ≤ 1259957097229^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2512526859 5000000000 1259957097229 3125000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (300049941/1250000000 : ℝ)^33 ≤ (760228711417/5000000000000 : ℝ)^25 := by
    have hnat : (300049941 : ℕ)^33*5000000000000^25 ≤ 760228711417^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      300049941 1250000000 760228711417 5000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5412955851/10000000000 : ℝ), (2512526859/5000000000 : ℝ), (-300049941/1250000000 : ℝ)] ![(22238399327063/50000000000000 : ℝ), (1259957097229/3125000000000 : ℝ), (760228711417/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5412955851/10000000000 : ℝ)|^33 ≤ (22238399327063/50000000000000 : ℝ)^25
        have hw : |(5412955851/10000000000 : ℝ)|=(5412955851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2512526859/5000000000 : ℝ)|^33 ≤ (1259957097229/3125000000000 : ℝ)^25
        have hw : |(2512526859/5000000000 : ℝ)|=(2512526859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-300049941/1250000000 : ℝ)|^33 ≤ (760228711417/5000000000000 : ℝ)^25
        have hw : |(-300049941/1250000000 : ℝ)|=(300049941/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1255_s1_3 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (269232703/625000000 : ℝ)*x 0 + (3697772243/10000000000 : ℝ)*x 1 + (2507092999/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (269232703/625000000 : ℝ)^33 ≤ (16450423861853/50000000000000 : ℝ)^25 := by
    have hnat : (269232703 : ℕ)^33*50000000000000^25 ≤ 16450423861853^25*625000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269232703 625000000 16450423861853 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3697772243/10000000000 : ℝ)^33 ≤ (5379117170567/20000000000000 : ℝ)^25 := by
    have hnat : (3697772243 : ℕ)^33*20000000000000^25 ≤ 5379117170567^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3697772243 10000000000 5379117170567 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2507092999/5000000000 : ℝ)^33 ≤ (40203566409559/100000000000000 : ℝ)^25 := by
    have hnat : (2507092999 : ℕ)^33*100000000000000^25 ≤ 40203566409559^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2507092999 5000000000 40203566409559 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(269232703/625000000 : ℝ), (3697772243/10000000000 : ℝ), (2507092999/5000000000 : ℝ)] ![(16450423861853/50000000000000 : ℝ), (5379117170567/20000000000000 : ℝ), (40203566409559/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(269232703/625000000 : ℝ)|^33 ≤ (16450423861853/50000000000000 : ℝ)^25
        have hw : |(269232703/625000000 : ℝ)|=(269232703/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3697772243/10000000000 : ℝ)|^33 ≤ (5379117170567/20000000000000 : ℝ)^25
        have hw : |(3697772243/10000000000 : ℝ)|=(3697772243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2507092999/5000000000 : ℝ)|^33 ≤ (40203566409559/100000000000000 : ℝ)^25
        have hw : |(2507092999/5000000000 : ℝ)|=(2507092999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1255_s1_4 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2053676493/10000000000 : ℝ)*x 0 + (2516756801/5000000000 : ℝ)*x 1 + (353984051/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2053676493/10000000000 : ℝ)^33 ≤ (12374916646121/100000000000000 : ℝ)^25 := by
    have hnat : (2053676493 : ℕ)^33*100000000000000^25 ≤ 12374916646121^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2053676493 10000000000 12374916646121 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2516756801/5000000000 : ℝ)^33 ≤ (20204125139551/50000000000000 : ℝ)^25 := by
    have hnat : (2516756801 : ℕ)^33*50000000000000^25 ≤ 20204125139551^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2516756801 5000000000 20204125139551 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (353984051/625000000 : ℝ)^33 ≤ (47216833052687/100000000000000 : ℝ)^25 := by
    have hnat : (353984051 : ℕ)^33*100000000000000^25 ≤ 47216833052687^25*625000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      353984051 625000000 47216833052687 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2053676493/10000000000 : ℝ), (2516756801/5000000000 : ℝ), (353984051/625000000 : ℝ)] ![(12374916646121/100000000000000 : ℝ), (20204125139551/50000000000000 : ℝ), (47216833052687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2053676493/10000000000 : ℝ)|^33 ≤ (12374916646121/100000000000000 : ℝ)^25
        have hw : |(-2053676493/10000000000 : ℝ)|=(2053676493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2516756801/5000000000 : ℝ)|^33 ≤ (20204125139551/50000000000000 : ℝ)^25
        have hw : |(2516756801/5000000000 : ℝ)|=(2516756801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(353984051/625000000 : ℝ)|^33 ≤ (47216833052687/100000000000000 : ℝ)^25
        have hw : |(353984051/625000000 : ℝ)|=(353984051/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1255_s1_5 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5246087061/10000000000 : ℝ)*x 0 + (-220213541/1250000000 : ℝ)*x 1 + (5663745151/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5246087061/10000000000 : ℝ)^33 ≤ (42675915994311/100000000000000 : ℝ)^25 := by
    have hnat : (5246087061 : ℕ)^33*100000000000000^25 ≤ 42675915994311^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246087061 10000000000 42675915994311 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (220213541/1250000000 : ℝ)^33 ≤ (5053623623649/50000000000000 : ℝ)^25 := by
    have hnat : (220213541 : ℕ)^33*50000000000000^25 ≤ 5053623623649^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220213541 1250000000 5053623623649 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5663745151/10000000000 : ℝ)^33 ≤ (47216836739167/100000000000000 : ℝ)^25 := by
    have hnat : (5663745151 : ℕ)^33*100000000000000^25 ≤ 47216836739167^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5663745151 10000000000 47216836739167 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5246087061/10000000000 : ℝ), (-220213541/1250000000 : ℝ), (5663745151/10000000000 : ℝ)] ![(42675915994311/100000000000000 : ℝ), (5053623623649/50000000000000 : ℝ), (47216836739167/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5246087061/10000000000 : ℝ)|^33 ≤ (42675915994311/100000000000000 : ℝ)^25
        have hw : |(5246087061/10000000000 : ℝ)|=(5246087061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-220213541/1250000000 : ℝ)|^33 ≤ (5053623623649/50000000000000 : ℝ)^25
        have hw : |(-220213541/1250000000 : ℝ)|=(220213541/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5663745151/10000000000 : ℝ)|^33 ≤ (47216836739167/100000000000000 : ℝ)^25
        have hw : |(5663745151/10000000000 : ℝ)|=(5663745151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1255_s1_6 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5246086983/10000000000 : ℝ)*x 0 + (5663744917/10000000000 : ℝ)*x 1 + (-88085439/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5246086983/10000000000 : ℝ)^33 ≤ (2667244697297/6250000000000 : ℝ)^25 := by
    have hnat : (5246086983 : ℕ)^33*6250000000000^25 ≤ 2667244697297^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246086983 10000000000 2667244697297 6250000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5663744917/10000000000 : ℝ)^33 ≤ (47216834164133/100000000000000 : ℝ)^25 := by
    have hnat : (5663744917 : ℕ)^33*100000000000000^25 ≤ 47216834164133^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5663744917 10000000000 47216834164133 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (88085439/500000000 : ℝ)^33 ≤ (2526812667583/25000000000000 : ℝ)^25 := by
    have hnat : (88085439 : ℕ)^33*25000000000000^25 ≤ 2526812667583^25*500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88085439 500000000 2526812667583 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5246086983/10000000000 : ℝ), (5663744917/10000000000 : ℝ), (-88085439/500000000 : ℝ)] ![(2667244697297/6250000000000 : ℝ), (47216834164133/100000000000000 : ℝ), (2526812667583/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5246086983/10000000000 : ℝ)|^33 ≤ (2667244697297/6250000000000 : ℝ)^25
        have hw : |(5246086983/10000000000 : ℝ)|=(5246086983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5663744917/10000000000 : ℝ)|^33 ≤ (47216834164133/100000000000000 : ℝ)^25
        have hw : |(5663744917/10000000000 : ℝ)|=(5663744917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-88085439/500000000 : ℝ)|^33 ≤ (2526812667583/25000000000000 : ℝ)^25
        have hw : |(-88085439/500000000 : ℝ)|=(88085439/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1255_s1_7 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (215453367/500000000 : ℝ)*x 0 + (2498490723/5000000000 : ℝ)*x 1 + (3715302681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215453367/500000000 : ℝ)^33 ≤ (32914399115471/100000000000000 : ℝ)^25 := by
    have hnat : (215453367 : ℕ)^33*100000000000000^25 ≤ 32914399115471^25*500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215453367 500000000 32914399115471 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2498490723/5000000000 : ℝ)^33 ≤ (40021578403617/100000000000000 : ℝ)^25 := by
    have hnat : (2498490723 : ℕ)^33*100000000000000^25 ≤ 40021578403617^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2498490723 5000000000 40021578403617 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3715302681/10000000000 : ℝ)^33 ≤ (1353201123223/5000000000000 : ℝ)^25 := by
    have hnat : (3715302681 : ℕ)^33*5000000000000^25 ≤ 1353201123223^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3715302681 10000000000 1353201123223 5000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(215453367/500000000 : ℝ), (2498490723/5000000000 : ℝ), (3715302681/10000000000 : ℝ)] ![(32914399115471/100000000000000 : ℝ), (40021578403617/100000000000000 : ℝ), (1353201123223/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(215453367/500000000 : ℝ)|^33 ≤ (32914399115471/100000000000000 : ℝ)^25
        have hw : |(215453367/500000000 : ℝ)|=(215453367/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2498490723/5000000000 : ℝ)|^33 ≤ (40021578403617/100000000000000 : ℝ)^25
        have hw : |(2498490723/5000000000 : ℝ)|=(2498490723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3715302681/10000000000 : ℝ)|^33 ≤ (1353201123223/5000000000000 : ℝ)^25
        have hw : |(3715302681/10000000000 : ℝ)|=(3715302681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1255_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37920797/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6847/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (87/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (6259/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2493/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6847/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (87/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6847/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (87/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6847/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (87/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6847/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (87/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6847/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (87/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6847/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (87/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (87/10000 : ℝ) ^ (8447/2048 : ℝ) ≤ (158669340091/50000000000000000000 : ℝ) := by
    have hpowers : (87/10000 : ℝ)^8447 ≤ (158669340091/50000000000000000000 : ℝ)^2048 := by
      have hnat : (87 : ℕ)^8447*50000000000000000000^2048 ≤ 158669340091^2048*10000^8447 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        87 10000 158669340091 50000000000000000000 8447 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (87/10000 : ℝ)) (X := (158669340091/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8447 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (6847/25000 : ℝ) ^ (8447/2048 : ℝ) ≤ (239431314453420079/50000000000000000000 : ℝ) := by
    have hpowers : (6847/25000 : ℝ)^8447 ≤ (239431314453420079/50000000000000000000 : ℝ)^2048 := by
      have hnat : (6847 : ℕ)^8447*50000000000000000000^2048 ≤ 239431314453420079^2048*25000^8447 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6847 25000 239431314453420079 50000000000000000000 8447 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6847/25000 : ℝ)) (X := (239431314453420079/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8447 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000158669340091/25000000000000000000 : ℝ) ≤ (500000000769397/500000000000000 : ℝ) ^ (8447/2048 : ℝ) := by
    have hpowers : (25000000158669340091/25000000000000000000 : ℝ)^2048 ≤ (500000000769397/500000000000000 : ℝ)^8447 := by
      have hnat : (25000000158669340091 : ℕ)^2048*500000000000000^8447 ≤ 500000000769397^8447*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000158669340091 25000000000000000000 500000000769397 500000000000000 2048 8447 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500000000769397/500000000000000 : ℝ)) (X := (25000000158669340091/25000000000000000000 : ℝ)) (by norm_num) 8447 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (5023943147312276017/5000000000000000000 : ℝ) ≤ (5005794586644239/5000000000000000 : ℝ) ^ (8447/2048 : ℝ) := by
    have hpowers : (5023943147312276017/5000000000000000000 : ℝ)^2048 ≤ (5005794586644239/5000000000000000 : ℝ)^8447 := by
      have hnat : (5023943147312276017 : ℕ)^2048*5000000000000000^8447 ≤ 5005794586644239^8447*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5023943147312276017 5000000000000000000 5005794586644239 5000000000000000 2048 8447 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5005794586644239/5000000000000000 : ℝ)) (X := (5023943147312276017/5000000000000000000 : ℝ)) (by norm_num) 8447 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25239431314453420079/25000000000000000000 : ℝ) ≤ (1252897291398627/1250000000000000 : ℝ) ^ (8447/2048 : ℝ) := by
    have hpowers : (25239431314453420079/25000000000000000000 : ℝ)^2048 ≤ (1252897291398627/1250000000000000 : ℝ)^8447 := by
      have hnat : (25239431314453420079 : ℕ)^2048*1250000000000000^8447 ≤ 1252897291398627^8447*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25239431314453420079 25000000000000000000 1252897291398627 1250000000000000 2048 8447 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1252897291398627/1250000000000000 : ℝ)) (X := (25239431314453420079/25000000000000000000 : ℝ)) (by norm_num) 8447 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(158669340091/50000000000000000000 : ℝ) ≤ ((331449794091638071/331475000000000000 : ℝ)+2*(5794578950269/1325900000000000 : ℝ)*(87/10000 : ℝ))^(8447/2048 : ℝ) := by
    rw [show (331449794091638071/331475000000000000 : ℝ)+2*(5794578950269/1325900000000000 : ℝ)*(87/10000 : ℝ)=(500000000769397/500000000000000 : ℝ) by norm_num, show 1+2*(158669340091/50000000000000000000 : ℝ)=(25000000158669340091/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(239431314453420079/50000000000000000000 : ℝ)+(158669340091/50000000000000000000 : ℝ) ≤ ((331449794091638071/331475000000000000 : ℝ)+(5794578950269/1325900000000000 : ℝ)*((6847/25000 : ℝ)+(87/10000 : ℝ)))^(8447/2048 : ℝ) := by
    rw [show (331449794091638071/331475000000000000 : ℝ)+(5794578950269/1325900000000000 : ℝ)*((6847/25000 : ℝ)+(87/10000 : ℝ))=(5005794586644239/5000000000000000 : ℝ) by norm_num, show 1+(239431314453420079/50000000000000000000 : ℝ)+(158669340091/50000000000000000000 : ℝ)=(5023943147312276017/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(239431314453420079/50000000000000000000 : ℝ) ≤ ((331449794091638071/331475000000000000 : ℝ)+2*(5794578950269/1325900000000000 : ℝ)*(6847/25000 : ℝ))^(8447/2048 : ℝ) := by
    rw [show (331449794091638071/331475000000000000 : ℝ)+2*(5794578950269/1325900000000000 : ℝ)*(6847/25000 : ℝ)=(1252897291398627/1250000000000000 : ℝ) by norm_num, show 1+2*(239431314453420079/50000000000000000000 : ℝ)=(25239431314453420079/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (331449794091638071/331475000000000000 : ℝ)*(X 1 0+X 2 0)+(5794578950269/1325900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8447/2048 : ℝ)) (lo := (87/10000 : ℝ)) (hi := (6847/25000 : ℝ)) (c := (331449794091638071/331475000000000000 : ℝ)) (alpha := (5794578950269/1325900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (331449794091638071/331475000000000000 : ℝ)*(X 0 1+X 2 1)+(5794578950269/1325900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8447/2048 : ℝ)) (lo := (87/10000 : ℝ)) (hi := (6847/25000 : ℝ)) (c := (331449794091638071/331475000000000000 : ℝ)) (alpha := (5794578950269/1325900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (331449794091638071/331475000000000000 : ℝ)*(X 0 2+X 1 2)+(5794578950269/1325900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8447/2048 : ℝ)) (lo := (87/10000 : ℝ)) (hi := (6847/25000 : ℝ)) (c := (331449794091638071/331475000000000000 : ℝ)) (alpha := (5794578950269/1325900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-513253867/2500000000 : ℝ)*X 0 0+(141809121/250000000 : ℝ)*X 0 1+(1005010729/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1353238923/2500000000 : ℝ)*X 1 0+(-2400399603/10000000000 : ℝ)*X 1 1+(5025053821/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5412955851/10000000000 : ℝ)*X 2 0+(2512526859/5000000000 : ℝ)*X 2 1+(-300049941/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((269232703/625000000 : ℝ)*X 0 0+(3697772243/10000000000 : ℝ)*X 0 1+(2507092999/5000000000 : ℝ)*X 0 2+(269232703/625000000 : ℝ)*X 1 0+(3697772243/10000000000 : ℝ)*X 1 1+(2507092999/5000000000 : ℝ)*X 1 2+(269232703/625000000 : ℝ)*X 2 0+(3697772243/10000000000 : ℝ)*X 2 1+(2507092999/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2053676493/10000000000 : ℝ)*X 0 0+(2516756801/5000000000 : ℝ)*X 0 1+(353984051/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5246087061/10000000000 : ℝ)*X 1 0+(-220213541/1250000000 : ℝ)*X 1 1+(5663745151/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5246086983/10000000000 : ℝ)*X 2 0+(5663744917/10000000000 : ℝ)*X 2 1+(-88085439/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((215453367/500000000 : ℝ)*X 0 0+(2498490723/5000000000 : ℝ)*X 0 1+(3715302681/10000000000 : ℝ)*X 0 2+(215453367/500000000 : ℝ)*X 1 0+(2498490723/5000000000 : ℝ)*X 1 1+(3715302681/10000000000 : ℝ)*X 1 2+(215453367/500000000 : ℝ)*X 2 0+(2498490723/5000000000 : ℝ)*X 2 1+(3715302681/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (24675594062398364923993137/8286875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (23226109/100000000000000 : ℝ)*(base1) + (690973403/100000000000000 : ℝ)*(base19) + (147270413/20000000000000 : ℝ)*(base23) + (34821351/50000000000000 : ℝ)*(upper3) + (109777563/100000000000000 : ℝ)*(upper5) + (144031533725081/12500000000000 : ℝ)*(major0) + (144031533725081/12500000000000 : ℝ)*(major1) + (144031533725081/12500000000000 : ℝ)*(major2) + (1544855906956509/100000000000000 : ℝ)*(sp0) + (772429863758723/50000000000000 : ℝ)*(sp1) + (48276865066837/3125000000000 : ℝ)*(sp2) + (759641830830253/100000000000000 : ℝ)*(sp3) + (4428477/97656250000 : ℝ)*(sp4) + (2167798353/100000000000000 : ℝ)*(sp7) + (151928804370943/20000000000000 : ℝ)*(f.failure) + (1544860418490849/100000000000000 : ℝ)*(f.sum) + (4892095853331/8286875000000000000000000000 : ℝ)*base66 + (18896057425957627/8286875000000000000000000000000 : ℝ)*base67 + (6718076906093501/4143437500000000000000000000000 : ℝ)*base69 + (21717798644757749/4143437500000000000000000000000 : ℝ)*base72 + (434171792026507/66295000000000000000000000000 : ℝ)*base73 + (30465209729617373/8286875000000000000000000000000 : ℝ)*base76 + (32871197150060249/4143437500000000000000000000000 : ℝ)*base78 + (21302261022107373/8286875000000000000000000000000 : ℝ)*base80 + (388618113823487/66295000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (2201571/500000000000000000000 : ℝ)*base89 + (2201571/500000000000000000000 : ℝ)*base91 + (2201571/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (44481885047839751787644499/8286875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2289547/10000000000000 : ℝ)*(base1) + (1010462883/100000000000000 : ℝ)*(base19) + (47843397/5000000000000 : ℝ)*(base23) + (28786087/20000000000000 : ℝ)*(upper3) + (359233/312500000000 : ℝ)*(upper5) + (1183472870259973/100000000000000 : ℝ)*(major0) + (1183472870259973/100000000000000 : ℝ)*(major1) + (1183472870259973/100000000000000 : ℝ)*(major2) + (2618007133/50000000000000 : ℝ)*(sp1) + (2146376333/50000000000000 : ℝ)*(sp2) + (317343758692657/20000000000000 : ℝ)*(sp4) + (793356262045333/50000000000000 : ℝ)*(sp5) + (1586713520947209/100000000000000 : ℝ)*(sp6) + (78022676813161/10000000000000 : ℝ)*(sp7) + (19505669775677/2500000000000 : ℝ)*(f.failure) + (317343754113563/20000000000000 : ℝ)*(f.sum) + (6203551727107/4143437500000000000000000000 : ℝ)*base65 + (239983013093008667/33147500000000000000000000000000 : ℝ)*base68 + (59584915473158667/33147500000000000000000000000000 : ℝ)*base70 + (44107191803538667/33147500000000000000000000000000 : ℝ)*base72 + (160523266879393/66295000000000000000000000000 : ℝ)*base74 + (36732710491978667/33147500000000000000000000000000 : ℝ)*base76 + (186126906660498833/33147500000000000000000000000000 : ℝ)*base77 + (206891740235981167/33147500000000000000000000000000 : ℝ)*base80 + (252706426936847/66295000000000000000000000000 : ℝ)*base81 + (70431/62500000000000000000 : ℝ)*base90 + (70431/62500000000000000000 : ℝ)*base92 + (70431/62500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1255_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37920797/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6847/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (87/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6259/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2493/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1255_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1255_s2_0 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2100416151/10000000000 : ℝ)*x 0 + (68632401/125000000 : ℝ)*x 1 + (1035317063/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2100416151/10000000000 : ℝ)^33 ≤ (12748029529977/100000000000000 : ℝ)^25 := by
    have hnat : (2100416151 : ℕ)^33*100000000000000^25 ≤ 12748029529977^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2100416151 10000000000 12748029529977 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (68632401/125000000 : ℝ)^33 ≤ (22660386916489/50000000000000 : ℝ)^25 := by
    have hnat : (68632401 : ℕ)^33*50000000000000^25 ≤ 22660386916489^25*125000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68632401 125000000 22660386916489 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1035317063/2000000000 : ℝ)^33 ≤ (41931196615881/100000000000000 : ℝ)^25 := by
    have hnat : (1035317063 : ℕ)^33*100000000000000^25 ≤ 41931196615881^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035317063 2000000000 41931196615881 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2100416151/10000000000 : ℝ), (68632401/125000000 : ℝ), (1035317063/2000000000 : ℝ)] ![(12748029529977/100000000000000 : ℝ), (22660386916489/50000000000000 : ℝ), (41931196615881/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2100416151/10000000000 : ℝ)|^33 ≤ (12748029529977/100000000000000 : ℝ)^25
        have hw : |(-2100416151/10000000000 : ℝ)|=(2100416151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(68632401/125000000 : ℝ)|^33 ≤ (22660386916489/50000000000000 : ℝ)^25
        have hw : |(68632401/125000000 : ℝ)|=(68632401/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1035317063/2000000000 : ℝ)|^33 ≤ (41931196615881/100000000000000 : ℝ)^25
        have hw : |(1035317063/2000000000 : ℝ)|=(1035317063/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1255_s2_1 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5369160857/10000000000 : ℝ)*x 0 + (-226299641/1000000000 : ℝ)*x 1 + (5176585439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369160857/10000000000 : ℝ)^33 ≤ (22001205251519/50000000000000 : ℝ)^25 := by
    have hnat : (5369160857 : ℕ)^33*50000000000000^25 ≤ 22001205251519^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369160857 10000000000 22001205251519 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (226299641/1000000000 : ℝ)^33 ≤ (14066391536693/100000000000000 : ℝ)^25 := by
    have hnat : (226299641 : ℕ)^33*100000000000000^25 ≤ 14066391536693^25*1000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226299641 1000000000 14066391536693 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5176585439/10000000000 : ℝ)^33 ≤ (10482799485429/25000000000000 : ℝ)^25 := by
    have hnat : (5176585439 : ℕ)^33*25000000000000^25 ≤ 10482799485429^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176585439 10000000000 10482799485429 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369160857/10000000000 : ℝ), (-226299641/1000000000 : ℝ), (5176585439/10000000000 : ℝ)] ![(22001205251519/50000000000000 : ℝ), (14066391536693/100000000000000 : ℝ), (10482799485429/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369160857/10000000000 : ℝ)|^33 ≤ (22001205251519/50000000000000 : ℝ)^25
        have hw : |(5369160857/10000000000 : ℝ)|=(5369160857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-226299641/1000000000 : ℝ)|^33 ≤ (14066391536693/100000000000000 : ℝ)^25
        have hw : |(-226299641/1000000000 : ℝ)|=(226299641/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5176585439/10000000000 : ℝ)|^33 ≤ (10482799485429/25000000000000 : ℝ)^25
        have hw : |(5176585439/10000000000 : ℝ)|=(5176585439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1255_s2_2 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2684580379/5000000000 : ℝ)*x 0 + (2588292747/5000000000 : ℝ)*x 1 + (-2262996469/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684580379/5000000000 : ℝ)^33 ≤ (42971102961/97656250000 : ℝ)^25 := by
    have hnat : (2684580379 : ℕ)^33*97656250000^25 ≤ 42971102961^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684580379 5000000000 42971102961 97656250000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2588292747/5000000000 : ℝ)^33 ≤ (10482799632447/25000000000000 : ℝ)^25 := by
    have hnat : (2588292747 : ℕ)^33*25000000000000^25 ≤ 10482799632447^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588292747 5000000000 10482799632447 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2262996469/10000000000 : ℝ)^33 ≤ (14066392020781/100000000000000 : ℝ)^25 := by
    have hnat : (2262996469 : ℕ)^33*100000000000000^25 ≤ 14066392020781^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2262996469 10000000000 14066392020781 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684580379/5000000000 : ℝ), (2588292747/5000000000 : ℝ), (-2262996469/10000000000 : ℝ)] ![(42971102961/97656250000 : ℝ), (10482799632447/25000000000000 : ℝ), (14066392020781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684580379/5000000000 : ℝ)|^33 ≤ (42971102961/97656250000 : ℝ)^25
        have hw : |(2684580379/5000000000 : ℝ)|=(2684580379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2588292747/5000000000 : ℝ)|^33 ≤ (10482799632447/25000000000000 : ℝ)^25
        have hw : |(2588292747/5000000000 : ℝ)|=(2588292747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2262996469/10000000000 : ℝ)|^33 ≤ (14066392020781/100000000000000 : ℝ)^25
        have hw : |(-2262996469/10000000000 : ℝ)|=(2262996469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1255_s2_3 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4340490643/10000000000 : ℝ)*x 0 + (2016270241/5000000000 : ℝ)*x 1 + (1167781067/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4340490643/10000000000 : ℝ)^33 ≤ (33231599722997/100000000000000 : ℝ)^25 := by
    have hnat : (4340490643 : ℕ)^33*100000000000000^25 ≤ 33231599722997^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4340490643 10000000000 33231599722997 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2016270241/5000000000 : ℝ)^33 ≤ (15077659650487/50000000000000 : ℝ)^25 := by
    have hnat : (2016270241 : ℕ)^33*50000000000000^25 ≤ 15077659650487^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2016270241 5000000000 15077659650487 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1167781067/2500000000 : ℝ)^33 ≤ (3661308096091/10000000000000 : ℝ)^25 := by
    have hnat : (1167781067 : ℕ)^33*10000000000000^25 ≤ 3661308096091^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1167781067 2500000000 3661308096091 10000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4340490643/10000000000 : ℝ), (2016270241/5000000000 : ℝ), (1167781067/2500000000 : ℝ)] ![(33231599722997/100000000000000 : ℝ), (15077659650487/50000000000000 : ℝ), (3661308096091/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4340490643/10000000000 : ℝ)|^33 ≤ (33231599722997/100000000000000 : ℝ)^25
        have hw : |(4340490643/10000000000 : ℝ)|=(4340490643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2016270241/5000000000 : ℝ)|^33 ≤ (15077659650487/50000000000000 : ℝ)^25
        have hw : |(2016270241/5000000000 : ℝ)|=(2016270241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1167781067/2500000000 : ℝ)|^33 ≤ (3661308096091/10000000000000 : ℝ)^25
        have hw : |(1167781067/2500000000 : ℝ)|=(1167781067/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1255_s2_4 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2100491911/10000000000 : ℝ)*x 0 + (2589292953/5000000000 : ℝ)*x 1 + (5488572891/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2100491911/10000000000 : ℝ)^33 ≤ (6374318240827/50000000000000 : ℝ)^25 := by
    have hnat : (2100491911 : ℕ)^33*50000000000000^25 ≤ 6374318240827^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2100491911 10000000000 6374318240827 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2589292953/5000000000 : ℝ)^33 ≤ (41952588693893/100000000000000 : ℝ)^25 := by
    have hnat : (2589292953 : ℕ)^33*100000000000000^25 ≤ 41952588693893^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2589292953 5000000000 41952588693893 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5488572891/10000000000 : ℝ)^33 ≤ (905975496109/2000000000000 : ℝ)^25 := by
    have hnat : (5488572891 : ℕ)^33*2000000000000^25 ≤ 905975496109^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5488572891 10000000000 905975496109 2000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2100491911/10000000000 : ℝ), (2589292953/5000000000 : ℝ), (5488572891/10000000000 : ℝ)] ![(6374318240827/50000000000000 : ℝ), (41952588693893/100000000000000 : ℝ), (905975496109/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2100491911/10000000000 : ℝ)|^33 ≤ (6374318240827/50000000000000 : ℝ)^25
        have hw : |(-2100491911/10000000000 : ℝ)|=(2100491911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2589292953/5000000000 : ℝ)|^33 ≤ (41952588693893/100000000000000 : ℝ)^25
        have hw : |(2589292953/5000000000 : ℝ)|=(2589292953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5488572891/10000000000 : ℝ)|^33 ≤ (905975496109/2000000000000 : ℝ)^25
        have hw : |(5488572891/10000000000 : ℝ)|=(5488572891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1255_s2_5 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1322226839/2500000000 : ℝ)*x 0 + (-30484511/156250000 : ℝ)*x 1 + (686071617/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322226839/2500000000 : ℝ)^33 ≤ (862726349389/2000000000000 : ℝ)^25 := by
    have hnat : (1322226839 : ℕ)^33*2000000000000^25 ≤ 862726349389^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322226839 2500000000 862726349389 2000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (30484511/156250000 : ℝ)^33 ≤ (11564907223907/100000000000000 : ℝ)^25 := by
    have hnat : (30484511 : ℕ)^33*100000000000000^25 ≤ 11564907223907^25*156250000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30484511 156250000 11564907223907 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (686071617/1250000000 : ℝ)^33 ≤ (2831173455981/6250000000000 : ℝ)^25 := by
    have hnat : (686071617 : ℕ)^33*6250000000000^25 ≤ 2831173455981^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      686071617 1250000000 2831173455981 6250000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322226839/2500000000 : ℝ), (-30484511/156250000 : ℝ), (686071617/1250000000 : ℝ)] ![(862726349389/2000000000000 : ℝ), (11564907223907/100000000000000 : ℝ), (2831173455981/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322226839/2500000000 : ℝ)|^33 ≤ (862726349389/2000000000000 : ℝ)^25
        have hw : |(1322226839/2500000000 : ℝ)|=(1322226839/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-30484511/156250000 : ℝ)|^33 ≤ (11564907223907/100000000000000 : ℝ)^25
        have hw : |(-30484511/156250000 : ℝ)|=(30484511/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(686071617/1250000000 : ℝ)|^33 ≤ (2831173455981/6250000000000 : ℝ)^25
        have hw : |(686071617/1250000000 : ℝ)|=(686071617/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1255_s2_6 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5288907497/10000000000 : ℝ)*x 0 + (5488573039/10000000000 : ℝ)*x 1 + (-975504183/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288907497/10000000000 : ℝ)^33 ≤ (10784079746861/25000000000000 : ℝ)^25 := by
    have hnat : (5288907497 : ℕ)^33*25000000000000^25 ≤ 10784079746861^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288907497 10000000000 10784079746861 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5488573039/10000000000 : ℝ)^33 ≤ (45298776417813/100000000000000 : ℝ)^25 := by
    have hnat : (5488573039 : ℕ)^33*100000000000000^25 ≤ 45298776417813^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5488573039 10000000000 45298776417813 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (975504183/5000000000 : ℝ)^33 ≤ (462596183169/4000000000000 : ℝ)^25 := by
    have hnat : (975504183 : ℕ)^33*4000000000000^25 ≤ 462596183169^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      975504183 5000000000 462596183169 4000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288907497/10000000000 : ℝ), (5488573039/10000000000 : ℝ), (-975504183/5000000000 : ℝ)] ![(10784079746861/25000000000000 : ℝ), (45298776417813/100000000000000 : ℝ), (462596183169/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288907497/10000000000 : ℝ)|^33 ≤ (10784079746861/25000000000000 : ℝ)^25
        have hw : |(5288907497/10000000000 : ℝ)|=(5288907497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5488573039/10000000000 : ℝ)|^33 ≤ (45298776417813/100000000000000 : ℝ)^25
        have hw : |(5488573039/10000000000 : ℝ)|=(5488573039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-975504183/5000000000 : ℝ)|^33 ≤ (462596183169/4000000000000 : ℝ)^25
        have hw : |(-975504183/5000000000 : ℝ)|=(975504183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1255_s2_7 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2170322117/5000000000 : ℝ)*x 0 + (4667056153/10000000000 : ℝ)*x 1 + (4036646023/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2170322117/5000000000 : ℝ)^33 ≤ (8308287986917/25000000000000 : ℝ)^25 := by
    have hnat : (2170322117 : ℕ)^33*25000000000000^25 ≤ 8308287986917^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2170322117 5000000000 8308287986917 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4667056153/10000000000 : ℝ)^33 ≤ (36570996528493/100000000000000 : ℝ)^25 := by
    have hnat : (4667056153 : ℕ)^33*100000000000000^25 ≤ 36570996528493^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4667056153 10000000000 36570996528493 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4036646023/10000000000 : ℝ)^33 ≤ (30195851507159/100000000000000 : ℝ)^25 := by
    have hnat : (4036646023 : ℕ)^33*100000000000000^25 ≤ 30195851507159^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4036646023 10000000000 30195851507159 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2170322117/5000000000 : ℝ), (4667056153/10000000000 : ℝ), (4036646023/10000000000 : ℝ)] ![(8308287986917/25000000000000 : ℝ), (36570996528493/100000000000000 : ℝ), (30195851507159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2170322117/5000000000 : ℝ)|^33 ≤ (8308287986917/25000000000000 : ℝ)^25
        have hw : |(2170322117/5000000000 : ℝ)|=(2170322117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4667056153/10000000000 : ℝ)|^33 ≤ (36570996528493/100000000000000 : ℝ)^25
        have hw : |(4667056153/10000000000 : ℝ)|=(4667056153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4036646023/10000000000 : ℝ)|^33 ≤ (30195851507159/100000000000000 : ℝ)^25
        have hw : |(4036646023/10000000000 : ℝ)|=(4036646023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1255_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37920797/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2493/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6259/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (597/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16189/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2493/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6259/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2493/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6259/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2493/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6259/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2493/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6259/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2493/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6259/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2493/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6259/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6259/100000 : ℝ) ^ (8447/2048 : ℝ) ≤ (13585655015617/1250000000000000000 : ℝ) := by
    have hpowers : (6259/100000 : ℝ)^8447 ≤ (13585655015617/1250000000000000000 : ℝ)^2048 := by
      have hnat : (6259 : ℕ)^8447*1250000000000000000^2048 ≤ 13585655015617^2048*100000^8447 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6259 100000 13585655015617 1250000000000000000 8447 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6259/100000 : ℝ)) (X := (13585655015617/1250000000000000000 : ℝ)) (by norm_num) (by norm_num) 8447 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2493/12500 : ℝ) ^ (8447/2048 : ℝ) ≤ (129439695827059199/100000000000000000000 : ℝ) := by
    have hpowers : (2493/12500 : ℝ)^8447 ≤ (129439695827059199/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2493 : ℕ)^8447*100000000000000000000^2048 ≤ 129439695827059199^2048*12500^8447 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2493 12500 129439695827059199 100000000000000000000 8447 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2493/12500 : ℝ)) (X := (129439695827059199/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8447 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (625013585655015617/625000000000000000 : ℝ) ≤ (20000105403357/20000000000000 : ℝ) ^ (8447/2048 : ℝ) := by
    have hpowers : (625013585655015617/625000000000000000 : ℝ)^2048 ≤ (20000105403357/20000000000000 : ℝ)^8447 := by
      have hnat : (625013585655015617 : ℕ)^2048*20000000000000^8447 ≤ 20000105403357^8447*625000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        625013585655015617 625000000000000000 20000105403357 20000000000000 2048 8447 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (20000105403357/20000000000000 : ℝ)) (X := (625013585655015617/625000000000000000 : ℝ)) (by norm_num) 8447 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100130526548228308559/100000000000000000000 : ℝ) ≤ (200063261823023/200000000000000 : ℝ) ^ (8447/2048 : ℝ) := by
    have hpowers : (100130526548228308559/100000000000000000000 : ℝ)^2048 ≤ (200063261823023/200000000000000 : ℝ)^8447 := by
      have hnat : (100130526548228308559 : ℕ)^2048*200000000000000^8447 ≤ 200063261823023^8447*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100130526548228308559 100000000000000000000 200063261823023 200000000000000 2048 8447 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200063261823023/200000000000000 : ℝ)) (X := (100130526548228308559/100000000000000000000 : ℝ)) (by norm_num) 8447 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50129439695827059199/50000000000000000000 : ℝ) ≤ (50031367403119/50000000000000 : ℝ) ^ (8447/2048 : ℝ) := by
    have hpowers : (50129439695827059199/50000000000000000000 : ℝ)^2048 ≤ (50031367403119/50000000000000 : ℝ)^8447 := by
      have hnat : (50129439695827059199 : ℕ)^2048*50000000000000^8447 ≤ 50031367403119^8447*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50129439695827059199 50000000000000000000 50031367403119 50000000000000 2048 8447 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (50031367403119/50000000000000 : ℝ)) (X := (50129439695827059199/50000000000000000000 : ℝ)) (by norm_num) 8447 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13585655015617/1250000000000000000 : ℝ) ≤ ((684058926835258199/684250000000000000 : ℝ)+2*(62207789453/27370000000000 : ℝ)*(6259/100000 : ℝ))^(8447/2048 : ℝ) := by
    rw [show (684058926835258199/684250000000000000 : ℝ)+2*(62207789453/27370000000000 : ℝ)*(6259/100000 : ℝ)=(20000105403357/20000000000000 : ℝ) by norm_num, show 1+2*(13585655015617/1250000000000000000 : ℝ)=(625013585655015617/625000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(129439695827059199/100000000000000000000 : ℝ)+(13585655015617/1250000000000000000 : ℝ) ≤ ((684058926835258199/684250000000000000 : ℝ)+(62207789453/27370000000000 : ℝ)*((2493/12500 : ℝ)+(6259/100000 : ℝ)))^(8447/2048 : ℝ) := by
    rw [show (684058926835258199/684250000000000000 : ℝ)+(62207789453/27370000000000 : ℝ)*((2493/12500 : ℝ)+(6259/100000 : ℝ))=(200063261823023/200000000000000 : ℝ) by norm_num, show 1+(129439695827059199/100000000000000000000 : ℝ)+(13585655015617/1250000000000000000 : ℝ)=(100130526548228308559/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(129439695827059199/100000000000000000000 : ℝ) ≤ ((684058926835258199/684250000000000000 : ℝ)+2*(62207789453/27370000000000 : ℝ)*(2493/12500 : ℝ))^(8447/2048 : ℝ) := by
    rw [show (684058926835258199/684250000000000000 : ℝ)+2*(62207789453/27370000000000 : ℝ)*(2493/12500 : ℝ)=(50031367403119/50000000000000 : ℝ) by norm_num, show 1+2*(129439695827059199/100000000000000000000 : ℝ)=(50129439695827059199/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (684058926835258199/684250000000000000 : ℝ)*(X 1 0+X 2 0)+(62207789453/27370000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8447/2048 : ℝ)) (lo := (6259/100000 : ℝ)) (hi := (2493/12500 : ℝ)) (c := (684058926835258199/684250000000000000 : ℝ)) (alpha := (62207789453/27370000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (684058926835258199/684250000000000000 : ℝ)*(X 0 1+X 2 1)+(62207789453/27370000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8447/2048 : ℝ)) (lo := (6259/100000 : ℝ)) (hi := (2493/12500 : ℝ)) (c := (684058926835258199/684250000000000000 : ℝ)) (alpha := (62207789453/27370000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (684058926835258199/684250000000000000 : ℝ)*(X 0 2+X 1 2)+(62207789453/27370000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8447/2048 : ℝ)) (lo := (6259/100000 : ℝ)) (hi := (2493/12500 : ℝ)) (c := (684058926835258199/684250000000000000 : ℝ)) (alpha := (62207789453/27370000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2100416151/10000000000 : ℝ)*X 0 0+(68632401/125000000 : ℝ)*X 0 1+(1035317063/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5369160857/10000000000 : ℝ)*X 1 0+(-226299641/1000000000 : ℝ)*X 1 1+(5176585439/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2684580379/5000000000 : ℝ)*X 2 0+(2588292747/5000000000 : ℝ)*X 2 1+(-2262996469/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4340490643/10000000000 : ℝ)*X 0 0+(2016270241/5000000000 : ℝ)*X 0 1+(1167781067/2500000000 : ℝ)*X 0 2+(4340490643/10000000000 : ℝ)*X 1 0+(2016270241/5000000000 : ℝ)*X 1 1+(1167781067/2500000000 : ℝ)*X 1 2+(4340490643/10000000000 : ℝ)*X 2 0+(2016270241/5000000000 : ℝ)*X 2 1+(1167781067/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2100491911/10000000000 : ℝ)*X 0 0+(2589292953/5000000000 : ℝ)*X 0 1+(5488572891/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1322226839/2500000000 : ℝ)*X 1 0+(-30484511/156250000 : ℝ)*X 1 1+(686071617/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5288907497/10000000000 : ℝ)*X 2 0+(5488573039/10000000000 : ℝ)*X 2 1+(-975504183/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2170322117/5000000000 : ℝ)*X 0 0+(4667056153/10000000000 : ℝ)*X 0 1+(4036646023/10000000000 : ℝ)*X 0 2+(2170322117/5000000000 : ℝ)*X 1 0+(4667056153/10000000000 : ℝ)*X 1 1+(4036646023/10000000000 : ℝ)*X 1 2+(2170322117/5000000000 : ℝ)*X 2 0+(4667056153/10000000000 : ℝ)*X 2 1+(4036646023/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (144364484790533001752523579/34212500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7076063/1000000000000 : ℝ)*(base19) + (612360683/100000000000000 : ℝ)*(base23) + (19610749/100000000000000 : ℝ)*(lower2) + (126833861/100000000000000 : ℝ)*(upper3) + (42466187/100000000000000 : ℝ)*(upper5) + (2375318010606293/100000000000000 : ℝ)*(major0) + (2375318010606293/100000000000000 : ℝ)*(major1) + (2375318010606293/100000000000000 : ℝ)*(major2) + (796163645373193/25000000000000 : ℝ)*(sp0) + (796165503519077/25000000000000 : ℝ)*(sp1) + (127386484372877/4000000000000 : ℝ)*(sp2) + (782984408895257/50000000000000 : ℝ)*(sp3) + (2035047459/25000000000000 : ℝ)*(sp4) + (2170542371/50000000000000 : ℝ)*(sp7) + (195746644859407/12500000000000 : ℝ)*(f.failure) + (199041420105163/6250000000000 : ℝ)*(f.sum) + (198306131327/85531250000000000000000000 : ℝ)*base65 + (6857117278895371/4025000000000000000000000000000 : ℝ)*base67 + (15879912202704629/4025000000000000000000000000000 : ℝ)*base70 + (37518715443995371/4025000000000000000000000000000 : ℝ)*base71 + (152576373939/34212500000000000000000000 : ℝ)*base74 + (28963175330604629/4025000000000000000000000000000 : ℝ)*base76 + (38426984088145371/4025000000000000000000000000000 : ℝ)*base77 + (32067065713545371/4025000000000000000000000000000 : ℝ)*base79 + (12891840629383/2737000000000000000000000000 : ℝ)*base82 + (762379/312500000000000000000 : ℝ)*base89 + (762379/312500000000000000000 : ℝ)*base91 + (762379/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (24758601874685382925431603/17106250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (681654153/100000000000000 : ℝ)*(base19) + (1013597841/100000000000000 : ℝ)*(base23) + (75973091/100000000000000 : ℝ)*(upper2) + (121806013/100000000000000 : ℝ)*(upper3) + (11544227/50000000000000 : ℝ)*(upper5) + (2406104773859599/100000000000000 : ℝ)*(major0) + (2406104773859599/100000000000000 : ℝ)*(major1) + (2406104773859599/100000000000000 : ℝ)*(major2) + (6418014063/100000000000000 : ℝ)*(sp1) + (1315958063/10000000000000 : ℝ)*(sp2) + (32259395867801/1000000000000 : ℝ)*(sp4) + (806483121777971/25000000000000 : ℝ)*(sp5) + (322592541360163/10000000000000 : ℝ)*(sp6) + (317253982538869/20000000000000 : ℝ)*(sp7) + (317253982538869/20000000000000 : ℝ)*(f.failure) + (32259395867801/1000000000000 : ℝ)*(f.sum) + (751296506173/342125000000000000000000000 : ℝ)*base65 + (11211164811491047/4025000000000000000000000000000 : ℝ)*base68 + (14170681502741047/4025000000000000000000000000000 : ℝ)*base70 + (1499052477508953/4025000000000000000000000000000 : ℝ)*base71 + (9313063450491/2737000000000000000000000000 : ℝ)*base73 + (23472983701266047/4025000000000000000000000000000 : ℝ)*base76 + (5720135016366047/4025000000000000000000000000000 : ℝ)*base78 + (39002035676241047/4025000000000000000000000000000 : ℝ)*base80 + (10367623162551/2737000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (958593/500000000000000000000 : ℝ)*base89 + (958593/500000000000000000000 : ℝ)*base91 + (958593/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1255_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37920797/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2493/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6259/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (597/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16189/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1255_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1255_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37920797/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (597/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16189/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1255_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1255_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1255_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37920797/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (597/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16189/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1255_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
