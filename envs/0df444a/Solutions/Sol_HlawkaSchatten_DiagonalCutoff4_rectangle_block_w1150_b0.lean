-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1150_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:35:21.529829+00:00
-- url     : https://prove2.me/submissions/ce259d52-c63d-4ccb-82ee-8cac46ae3030

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
theorem support_rectangle_w1150_s0_0 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-944640699/5000000000 : ℝ)*x 0 + (302624149/500000000 : ℝ)*x 1 + (1195370811/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (944640699/5000000000 : ℝ)^8343 ≤ (10986231826821/100000000000000 : ℝ)^6295 := by
    have hnat : (944640699 : ℕ)^8343*100000000000000^6295 ≤ 10986231826821^6295*5000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      944640699 5000000000 10986231826821 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (302624149/500000000 : ℝ)^8343 ≤ (51402989415039/100000000000000 : ℝ)^6295 := by
    have hnat : (302624149 : ℕ)^8343*100000000000000^6295 ≤ 51402989415039^6295*500000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      302624149 500000000 51402989415039 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1195370811/2500000000 : ℝ)^8343 ≤ (18805389371853/50000000000000 : ℝ)^6295 := by
    have hnat : (1195370811 : ℕ)^8343*50000000000000^6295 ≤ 18805389371853^6295*2500000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1195370811 2500000000 18805389371853 50000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-944640699/5000000000 : ℝ), (302624149/500000000 : ℝ), (1195370811/2500000000 : ℝ)] ![(10986231826821/100000000000000 : ℝ), (51402989415039/100000000000000 : ℝ), (18805389371853/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-944640699/5000000000 : ℝ)|^8343 ≤ (10986231826821/100000000000000 : ℝ)^6295
        have hw : |(-944640699/5000000000 : ℝ)|=(944640699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(302624149/500000000 : ℝ)|^8343 ≤ (51402989415039/100000000000000 : ℝ)^6295
        have hw : |(302624149/500000000 : ℝ)|=(302624149/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1195370811/2500000000 : ℝ)|^8343 ≤ (18805389371853/50000000000000 : ℝ)^6295
        have hw : |(1195370811/2500000000 : ℝ)|=(1195370811/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s0_1 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2758171437/5000000000 : ℝ)*x 0 + (-1309229289/5000000000 : ℝ)*x 1 + (149421353/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2758171437/5000000000 : ℝ)^8343 ≤ (45456992493219/100000000000000 : ℝ)^6295 := by
    have hnat : (2758171437 : ℕ)^8343*100000000000000^6295 ≤ 45456992493219^6295*5000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2758171437 5000000000 45456992493219 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1309229289/5000000000 : ℝ)^8343 ≤ (16932228210003/100000000000000 : ℝ)^6295 := by
    have hnat : (1309229289 : ℕ)^8343*100000000000000^6295 ≤ 16932228210003^6295*5000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309229289 5000000000 16932228210003 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (149421353/312500000 : ℝ)^8343 ≤ (18805389642903/50000000000000 : ℝ)^6295 := by
    have hnat : (149421353 : ℕ)^8343*50000000000000^6295 ≤ 18805389642903^6295*312500000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      149421353 312500000 18805389642903 50000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2758171437/5000000000 : ℝ), (-1309229289/5000000000 : ℝ), (149421353/312500000 : ℝ)] ![(45456992493219/100000000000000 : ℝ), (16932228210003/100000000000000 : ℝ), (18805389642903/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2758171437/5000000000 : ℝ)|^8343 ≤ (45456992493219/100000000000000 : ℝ)^6295
        have hw : |(2758171437/5000000000 : ℝ)|=(2758171437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1309229289/5000000000 : ℝ)|^8343 ≤ (16932228210003/100000000000000 : ℝ)^6295
        have hw : |(-1309229289/5000000000 : ℝ)|=(1309229289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(149421353/312500000 : ℝ)|^8343 ≤ (18805389642903/50000000000000 : ℝ)^6295
        have hw : |(149421353/312500000 : ℝ)|=(149421353/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s0_2 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5516343157/10000000000 : ℝ)*x 0 + (4781483177/10000000000 : ℝ)*x 1 + (-1309229181/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5516343157/10000000000 : ℝ)^8343 ≤ (45456995583959/100000000000000 : ℝ)^6295 := by
    have hnat : (5516343157 : ℕ)^8343*100000000000000^6295 ≤ 45456995583959^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5516343157 10000000000 45456995583959 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4781483177/10000000000 : ℝ)^8343 ≤ (3761077804523/10000000000000 : ℝ)^6295 := by
    have hnat : (4781483177 : ℕ)^8343*10000000000000^6295 ≤ 3761077804523^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4781483177 10000000000 3761077804523 10000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1309229181/5000000000 : ℝ)^8343 ≤ (16932226358823/100000000000000 : ℝ)^6295 := by
    have hnat : (1309229181 : ℕ)^8343*100000000000000^6295 ≤ 16932226358823^6295*5000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309229181 5000000000 16932226358823 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5516343157/10000000000 : ℝ), (4781483177/10000000000 : ℝ), (-1309229181/5000000000 : ℝ)] ![(45456995583959/100000000000000 : ℝ), (3761077804523/10000000000000 : ℝ), (16932226358823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5516343157/10000000000 : ℝ)|^8343 ≤ (45456995583959/100000000000000 : ℝ)^6295
        have hw : |(5516343157/10000000000 : ℝ)|=(5516343157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4781483177/10000000000 : ℝ)|^8343 ≤ (3761077804523/10000000000000 : ℝ)^6295
        have hw : |(4781483177/10000000000 : ℝ)|=(4781483177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1309229181/5000000000 : ℝ)|^8343 ≤ (16932226358823/100000000000000 : ℝ)^6295
        have hw : |(-1309229181/5000000000 : ℝ)|=(1309229181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s0_3 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4200344613/10000000000 : ℝ)*x 0 + (3120710683/10000000000 : ℝ)*x 1 + (1130660069/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4200344613/10000000000 : ℝ)^8343 ≤ (31675636872593/100000000000000 : ℝ)^6295 := by
    have hnat : (4200344613 : ℕ)^8343*100000000000000^6295 ≤ 31675636872593^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4200344613 10000000000 31675636872593 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3120710683/10000000000 : ℝ)^8343 ≤ (10682801959177/50000000000000 : ℝ)^6295 := by
    have hnat : (3120710683 : ℕ)^8343*50000000000000^6295 ≤ 10682801959177^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3120710683 10000000000 10682801959177 50000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1130660069/2000000000 : ℝ)^8343 ≤ (2934922449697/6250000000000 : ℝ)^6295 := by
    have hnat : (1130660069 : ℕ)^8343*6250000000000^6295 ≤ 2934922449697^6295*2000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1130660069 2000000000 2934922449697 6250000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4200344613/10000000000 : ℝ), (3120710683/10000000000 : ℝ), (1130660069/2000000000 : ℝ)] ![(31675636872593/100000000000000 : ℝ), (10682801959177/50000000000000 : ℝ), (2934922449697/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4200344613/10000000000 : ℝ)|^8343 ≤ (31675636872593/100000000000000 : ℝ)^6295
        have hw : |(4200344613/10000000000 : ℝ)|=(4200344613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3120710683/10000000000 : ℝ)|^8343 ≤ (10682801959177/50000000000000 : ℝ)^6295
        have hw : |(3120710683/10000000000 : ℝ)|=(3120710683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1130660069/2000000000 : ℝ)|^8343 ≤ (2934922449697/6250000000000 : ℝ)^6295
        have hw : |(1130660069/2000000000 : ℝ)|=(1130660069/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s0_4 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-94720171/500000000 : ℝ)*x 0 + (4814267447/10000000000 : ℝ)*x 1 + (1203709113/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (94720171/500000000 : ℝ)^8343 ≤ (5512862018009/50000000000000 : ℝ)^6295 := by
    have hnat : (94720171 : ℕ)^8343*50000000000000^6295 ≤ 5512862018009^6295*500000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94720171 500000000 5512862018009 50000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4814267447/10000000000 : ℝ)^8343 ≤ (7590586954687/20000000000000 : ℝ)^6295 := by
    have hnat : (4814267447 : ℕ)^8343*20000000000000^6295 ≤ 7590586954687^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4814267447 10000000000 7590586954687 20000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1203709113/2000000000 : ℝ)^8343 ≤ (51021341178507/100000000000000 : ℝ)^6295 := by
    have hnat : (1203709113 : ℕ)^8343*100000000000000^6295 ≤ 51021341178507^6295*2000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1203709113 2000000000 51021341178507 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-94720171/500000000 : ℝ), (4814267447/10000000000 : ℝ), (1203709113/2000000000 : ℝ)] ![(5512862018009/50000000000000 : ℝ), (7590586954687/20000000000000 : ℝ), (51021341178507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-94720171/500000000 : ℝ)|^8343 ≤ (5512862018009/50000000000000 : ℝ)^6295
        have hw : |(-94720171/500000000 : ℝ)|=(94720171/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4814267447/10000000000 : ℝ)|^8343 ≤ (7590586954687/20000000000000 : ℝ)^6295
        have hw : |(4814267447/10000000000 : ℝ)|=(4814267447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1203709113/2000000000 : ℝ)|^8343 ≤ (51021341178507/100000000000000 : ℝ)^6295
        have hw : |(1203709113/2000000000 : ℝ)|=(1203709113/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s0_5 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (258547239/500000000 : ℝ)*x 0 + (-345349077/2500000000 : ℝ)*x 1 + (3009272701/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (258547239/500000000 : ℝ)^8343 ≤ (41723758926143/100000000000000 : ℝ)^6295 := by
    have hnat : (258547239 : ℕ)^8343*100000000000000^6295 ≤ 41723758926143^6295*500000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258547239 500000000 41723758926143 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (345349077/2500000000 : ℝ)^8343 ≤ (7254901713829/100000000000000 : ℝ)^6295 := by
    have hnat : (345349077 : ℕ)^8343*100000000000000^6295 ≤ 7254901713829^6295*2500000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      345349077 2500000000 7254901713829 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3009272701/5000000000 : ℝ)^8343 ≤ (6377667418393/12500000000000 : ℝ)^6295 := by
    have hnat : (3009272701 : ℕ)^8343*12500000000000^6295 ≤ 6377667418393^6295*5000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3009272701 5000000000 6377667418393 12500000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(258547239/500000000 : ℝ), (-345349077/2500000000 : ℝ), (3009272701/5000000000 : ℝ)] ![(41723758926143/100000000000000 : ℝ), (7254901713829/100000000000000 : ℝ), (6377667418393/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(258547239/500000000 : ℝ)|^8343 ≤ (41723758926143/100000000000000 : ℝ)^6295
        have hw : |(258547239/500000000 : ℝ)|=(258547239/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-345349077/2500000000 : ℝ)|^8343 ≤ (7254901713829/100000000000000 : ℝ)^6295
        have hw : |(-345349077/2500000000 : ℝ)|=(345349077/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3009272701/5000000000 : ℝ)|^8343 ≤ (6377667418393/12500000000000 : ℝ)^6295
        have hw : |(3009272701/5000000000 : ℝ)|=(3009272701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s0_6 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (517094477/1000000000 : ℝ)*x 0 + (6018545447/10000000000 : ℝ)*x 1 + (-1105117/8000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (517094477/1000000000 : ℝ)^8343 ≤ (41723758819203/100000000000000 : ℝ)^6295 := by
    have hnat : (517094477 : ℕ)^8343*100000000000000^6295 ≤ 41723758819203^6295*1000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517094477 1000000000 41723758819203 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6018545447/10000000000 : ℝ)^8343 ≤ (10204267970547/20000000000000 : ℝ)^6295 := by
    have hnat : (6018545447 : ℕ)^8343*20000000000000^6295 ≤ 10204267970547^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6018545447 10000000000 10204267970547 20000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1105117/8000000 : ℝ)^8343 ≤ (7254901310121/100000000000000 : ℝ)^6295 := by
    have hnat : (1105117 : ℕ)^8343*100000000000000^6295 ≤ 7254901310121^6295*8000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1105117 8000000 7254901310121 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(517094477/1000000000 : ℝ), (6018545447/10000000000 : ℝ), (-1105117/8000000 : ℝ)] ![(41723758819203/100000000000000 : ℝ), (10204267970547/20000000000000 : ℝ), (7254901310121/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(517094477/1000000000 : ℝ)|^8343 ≤ (41723758819203/100000000000000 : ℝ)^6295
        have hw : |(517094477/1000000000 : ℝ)|=(517094477/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6018545447/10000000000 : ℝ)|^8343 ≤ (10204267970547/20000000000000 : ℝ)^6295
        have hw : |(6018545447/10000000000 : ℝ)|=(6018545447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1105117/8000000 : ℝ)|^8343 ≤ (7254901310121/100000000000000 : ℝ)^6295
        have hw : |(-1105117/8000000 : ℝ)|=(1105117/8000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s0_7 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2105275497/5000000000 : ℝ)*x 0 + (1396993611/2500000000 : ℝ)*x 1 + (797083649/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2105275497/5000000000 : ℝ)^8343 ≤ (31777686224947/100000000000000 : ℝ)^6295 := by
    have hnat : (2105275497 : ℕ)^8343*100000000000000^6295 ≤ 31777686224947^6295*5000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2105275497 5000000000 31777686224947 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1396993611/2500000000 : ℝ)^8343 ≤ (4624095296079/10000000000000 : ℝ)^6295 := by
    have hnat : (1396993611 : ℕ)^8343*10000000000000^6295 ≤ 4624095296079^6295*2500000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1396993611 2500000000 4624095296079 10000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (797083649/2500000000 : ℝ)^8343 ≤ (2198136079711/10000000000000 : ℝ)^6295 := by
    have hnat : (797083649 : ℕ)^8343*10000000000000^6295 ≤ 2198136079711^6295*2500000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      797083649 2500000000 2198136079711 10000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2105275497/5000000000 : ℝ), (1396993611/2500000000 : ℝ), (797083649/2500000000 : ℝ)] ![(31777686224947/100000000000000 : ℝ), (4624095296079/10000000000000 : ℝ), (2198136079711/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2105275497/5000000000 : ℝ)|^8343 ≤ (31777686224947/100000000000000 : ℝ)^6295
        have hw : |(2105275497/5000000000 : ℝ)|=(2105275497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1396993611/2500000000 : ℝ)|^8343 ≤ (4624095296079/10000000000000 : ℝ)^6295
        have hw : |(1396993611/2500000000 : ℝ)|=(1396993611/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(797083649/2500000000 : ℝ)|^8343 ≤ (2198136079711/10000000000000 : ℝ)^6295
        have hw : |(797083649/2500000000 : ℝ)|=(797083649/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1150_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74814911/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (223/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3473/12500 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4171/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4171 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4171*1^1024 ≤ 0^1024*1^4171 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4171 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4171 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4171/1024 : ℝ) ≤ (2393833655738182939/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4171 ≤ (2393833655738182939/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4171*100000000000000000000^1024 ≤ 2393833655738182939^1024*5^4171 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2393833655738182939 100000000000000000000 4171 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2393833655738182939/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4171 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4171/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4171 := by
      have hnat : (1 : ℕ)^1024*1^4171 ≤ 1^4171*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4171 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4171 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (102393833655738182939/100000000000000000000 : ℝ) ≤ (5029123157245637/5000000000000000 : ℝ) ^ (4171/1024 : ℝ) := by
    have hpowers : (102393833655738182939/100000000000000000000 : ℝ)^1024 ≤ (5029123157245637/5000000000000000 : ℝ)^4171 := by
      have hnat : (102393833655738182939 : ℕ)^1024*5000000000000000^4171 ≤ 5029123157245637^4171*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102393833655738182939 100000000000000000000 5029123157245637 5000000000000000 1024 4171 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5029123157245637/5000000000000000 : ℝ)) (X := (102393833655738182939/100000000000000000000 : ℝ)) (by norm_num) 4171 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (52393833655738182939/50000000000000000000 : ℝ) ≤ (2529123157245637/2500000000000000 : ℝ) ^ (4171/1024 : ℝ) := by
    have hpowers : (52393833655738182939/50000000000000000000 : ℝ)^1024 ≤ (2529123157245637/2500000000000000 : ℝ)^4171 := by
      have hnat : (52393833655738182939 : ℕ)^1024*2500000000000000^4171 ≤ 2529123157245637^4171*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52393833655738182939 50000000000000000000 2529123157245637 2500000000000000 1024 4171 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2529123157245637/2500000000000000 : ℝ)) (X := (52393833655738182939/50000000000000000000 : ℝ)) (by norm_num) 4171 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(29123157245637/2000000000000000 : ℝ)*(0 : ℝ))^(4171/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(29123157245637/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2393833655738182939/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(29123157245637/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4171/1024 : ℝ) := by
    rw [show (1 : ℝ)+(29123157245637/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5029123157245637/5000000000000000 : ℝ) by norm_num, show 1+(2393833655738182939/100000000000000000000 : ℝ)+(0 : ℝ)=(102393833655738182939/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2393833655738182939/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(29123157245637/2000000000000000 : ℝ)*(2/5 : ℝ))^(4171/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(29123157245637/2000000000000000 : ℝ)*(2/5 : ℝ)=(2529123157245637/2500000000000000 : ℝ) by norm_num, show 1+2*(2393833655738182939/100000000000000000000 : ℝ)=(52393833655738182939/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(29123157245637/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4171/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (29123157245637/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(29123157245637/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4171/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (29123157245637/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(29123157245637/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4171/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (29123157245637/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-944640699/5000000000 : ℝ)*X 0 0+(302624149/500000000 : ℝ)*X 0 1+(1195370811/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2758171437/5000000000 : ℝ)*X 1 0+(-1309229289/5000000000 : ℝ)*X 1 1+(149421353/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5516343157/10000000000 : ℝ)*X 2 0+(4781483177/10000000000 : ℝ)*X 2 1+(-1309229181/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4200344613/10000000000 : ℝ)*X 0 0+(3120710683/10000000000 : ℝ)*X 0 1+(1130660069/2000000000 : ℝ)*X 0 2+(4200344613/10000000000 : ℝ)*X 1 0+(3120710683/10000000000 : ℝ)*X 1 1+(1130660069/2000000000 : ℝ)*X 1 2+(4200344613/10000000000 : ℝ)*X 2 0+(3120710683/10000000000 : ℝ)*X 2 1+(1130660069/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-94720171/500000000 : ℝ)*X 0 0+(4814267447/10000000000 : ℝ)*X 0 1+(1203709113/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((258547239/500000000 : ℝ)*X 1 0+(-345349077/2500000000 : ℝ)*X 1 1+(3009272701/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((517094477/1000000000 : ℝ)*X 2 0+(6018545447/10000000000 : ℝ)*X 2 1+(-1105117/8000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2105275497/5000000000 : ℝ)*X 0 0+(1396993611/2500000000 : ℝ)*X 0 1+(797083649/2500000000 : ℝ)*X 0 2+(2105275497/5000000000 : ℝ)*X 1 0+(1396993611/2500000000 : ℝ)*X 1 1+(797083649/2500000000 : ℝ)*X 1 2+(2105275497/5000000000 : ℝ)*X 2 0+(1396993611/2500000000 : ℝ)*X 2 1+(797083649/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (34318303729678796713263/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (17278999/25000000000000 : ℝ)*(base1) + (1709274507/100000000000000 : ℝ)*(base19) + (1610825067/100000000000000 : ℝ)*(base23) + (138813417/100000000000000 : ℝ)*(base24) + (79453941/20000000000000 : ℝ)*(upper3) + (147706179961767/25000000000000 : ℝ)*(major0) + (147706179961767/25000000000000 : ℝ)*(major1) + (147706179961767/25000000000000 : ℝ)*(major2) + (39339395887849/5000000000000 : ℝ)*(sp0) + (196697476107193/25000000000000 : ℝ)*(sp1) + (196697466016199/25000000000000 : ℝ)*(sp2) + (394854496233173/100000000000000 : ℝ)*(sp3) + (753012459/20000000000000 : ℝ)*(sp4) + (303185299/10000000000000 : ℝ)*(sp7) + (394857597202159/100000000000000 : ℝ)*(f.failure) + (786791613703279/100000000000000 : ℝ)*(f.sum) + (63537883335579/25000000000000000000000000000 : ℝ)*base65 + (82421388360579/50000000000000000000000000000 : ℝ)*base67 + (218295611560579/50000000000000000000000000000 : ℝ)*base69 + (138686195710579/50000000000000000000000000000 : ℝ)*base71 + (44973974985579/25000000000000000000000000000 : ℝ)*base73 + (104056725710579/50000000000000000000000000000 : ℝ)*base75 + (130864683510579/50000000000000000000000000000 : ℝ)*base77 + (164584892989421/50000000000000000000000000000 : ℝ)*base80 + (204056623235579/25000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (25407151/5000000000000000000000 : ℝ)*base90 + (25407151/5000000000000000000000 : ℝ)*base92 + (25407151/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (23988651159356453656503/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (33496203/100000000000000 : ℝ)*(base1) + (473538713/100000000000000 : ℝ)*(base19) + (471274143/100000000000000 : ℝ)*(base23) + (43878571/100000000000000 : ℝ)*(upper3) + (3008803/5000000000000 : ℝ)*(upper5) + (155887787004573/25000000000000 : ℝ)*(major0) + (155887787004573/25000000000000 : ℝ)*(major1) + (155887787004573/25000000000000 : ℝ)*(major2) + (896994537/100000000000000 : ℝ)*(sp1) + (443566007/50000000000000 : ℝ)*(sp2) + (830373073692263/100000000000000 : ℝ)*(sp4) + (83037166966281/10000000000000 : ℝ)*(sp5) + (830371681789903/100000000000000 : ℝ)*(sp6) + (416729158374581/100000000000000 : ℝ)*(sp7) + (6511393622981/1562500000000 : ℝ)*(f.failure) + (41518652009803/5000000000000 : ℝ)*(f.sum) + (37554801948001/25000000000000000000000000000 : ℝ)*base65 + (305660122951999/50000000000000000000000000000 : ℝ)*base68 + (321604990251999/50000000000000000000000000000 : ℝ)*base70 + (78513670698001/50000000000000000000000000000 : ℝ)*base71 + (103504449151999/25000000000000000000000000000 : ℝ)*base74 + (103164489101999/50000000000000000000000000000 : ℝ)*base76 + (122220047801999/50000000000000000000000000000 : ℝ)*base78 + (175655499148001/50000000000000000000000000000 : ℝ)*base79 + (56992583151999/25000000000000000000000000000 : ℝ)*base82 + (444691/78125000000000000000 : ℝ)*base89 + (444691/78125000000000000000 : ℝ)*base91 + (444691/78125000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1150_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74814911/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (223/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3473/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1150_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1150_s1_0 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-5233431/25000000 : ℝ)*x 0 + (5699367243/10000000000 : ℝ)*x 1 + (5003942951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5233431/25000000 : ℝ)^8343 ≤ (12586133760439/100000000000000 : ℝ)^6295 := by
    have hnat : (5233431 : ℕ)^8343*100000000000000^6295 ≤ 12586133760439^6295*25000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5233431 25000000 12586133760439 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5699367243/10000000000 : ℝ)^8343 ≤ (11866643182943/25000000000000 : ℝ)^6295 := by
    have hnat : (5699367243 : ℕ)^8343*25000000000000^6295 ≤ 11866643182943^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5699367243 10000000000 11866643182943 25000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5003942951/10000000000 : ℝ)^8343 ≤ (7989458700037/20000000000000 : ℝ)^6295 := by
    have hnat : (5003942951 : ℕ)^8343*20000000000000^6295 ≤ 7989458700037^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5003942951 10000000000 7989458700037 20000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5233431/25000000 : ℝ), (5699367243/10000000000 : ℝ), (5003942951/10000000000 : ℝ)] ![(12586133760439/100000000000000 : ℝ), (11866643182943/25000000000000 : ℝ), (7989458700037/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5233431/25000000 : ℝ)|^8343 ≤ (12586133760439/100000000000000 : ℝ)^6295
        have hw : |(-5233431/25000000 : ℝ)|=(5233431/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5699367243/10000000000 : ℝ)|^8343 ≤ (11866643182943/25000000000000 : ℝ)^6295
        have hw : |(5699367243/10000000000 : ℝ)|=(5699367243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5003942951/10000000000 : ℝ)|^8343 ≤ (7989458700037/20000000000000 : ℝ)^6295
        have hw : |(5003942951/10000000000 : ℝ)|=(5003942951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s1_1 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2709340207/5000000000 : ℝ)*x 0 + (-2468508499/10000000000 : ℝ)*x 1 + (1000788423/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2709340207/5000000000 : ℝ)^8343 ≤ (2774591972121/6250000000000 : ℝ)^6295 := by
    have hnat : (2709340207 : ℕ)^8343*6250000000000^6295 ≤ 2774591972121^6295*5000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709340207 5000000000 2774591972121 6250000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2468508499/10000000000 : ℝ)^8343 ≤ (3914810943421/25000000000000 : ℝ)^6295 := by
    have hnat : (2468508499 : ℕ)^8343*25000000000000^6295 ≤ 3914810943421^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2468508499 10000000000 3914810943421 25000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1000788423/2000000000 : ℝ)^8343 ≤ (19973642327491/50000000000000 : ℝ)^6295 := by
    have hnat : (1000788423 : ℕ)^8343*50000000000000^6295 ≤ 19973642327491^6295*2000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1000788423 2000000000 19973642327491 50000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2709340207/5000000000 : ℝ), (-2468508499/10000000000 : ℝ), (1000788423/2000000000 : ℝ)] ![(2774591972121/6250000000000 : ℝ), (3914810943421/25000000000000 : ℝ), (19973642327491/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2709340207/5000000000 : ℝ)|^8343 ≤ (2774591972121/6250000000000 : ℝ)^6295
        have hw : |(2709340207/5000000000 : ℝ)|=(2709340207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2468508499/10000000000 : ℝ)|^8343 ≤ (3914810943421/25000000000000 : ℝ)^6295
        have hw : |(-2468508499/10000000000 : ℝ)|=(2468508499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1000788423/2000000000 : ℝ)|^8343 ≤ (19973642327491/50000000000000 : ℝ)^6295
        have hw : |(1000788423/2000000000 : ℝ)|=(1000788423/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s1_2 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1083736491/2000000000 : ℝ)*x 0 + (625492537/1250000000 : ℝ)*x 1 + (-1234254077/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1083736491/2000000000 : ℝ)^8343 ≤ (4439349371523/10000000000000 : ℝ)^6295 := by
    have hnat : (1083736491 : ℕ)^8343*10000000000000^6295 ≤ 4439349371523^6295*2000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083736491 2000000000 4439349371523 10000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (625492537/1250000000 : ℝ)^8343 ≤ (19973632704631/50000000000000 : ℝ)^6295 := by
    have hnat : (625492537 : ℕ)^8343*50000000000000^6295 ≤ 19973632704631^6295*1250000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      625492537 1250000000 19973632704631 50000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1234254077/5000000000 : ℝ)^8343 ≤ (25054785397/160000000000 : ℝ)^6295 := by
    have hnat : (1234254077 : ℕ)^8343*160000000000^6295 ≤ 25054785397^6295*5000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1234254077 5000000000 25054785397 160000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1083736491/2000000000 : ℝ), (625492537/1250000000 : ℝ), (-1234254077/5000000000 : ℝ)] ![(4439349371523/10000000000000 : ℝ), (19973632704631/50000000000000 : ℝ), (25054785397/160000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1083736491/2000000000 : ℝ)|^8343 ≤ (4439349371523/10000000000000 : ℝ)^6295
        have hw : |(1083736491/2000000000 : ℝ)|=(1083736491/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(625492537/1250000000 : ℝ)|^8343 ≤ (19973632704631/50000000000000 : ℝ)^6295
        have hw : |(625492537/1250000000 : ℝ)|=(625492537/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1234254077/5000000000 : ℝ)|^8343 ≤ (25054785397/160000000000 : ℝ)^6295
        have hw : |(-1234254077/5000000000 : ℝ)|=(1234254077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s1_3 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4316762443/10000000000 : ℝ)*x 0 + (229909479/625000000 : ℝ)*x 1 + (5064248289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4316762443/10000000000 : ℝ)^8343 ≤ (32844404238169/100000000000000 : ℝ)^6295 := by
    have hnat : (4316762443 : ℕ)^8343*100000000000000^6295 ≤ 32844404238169^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4316762443 10000000000 32844404238169 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (229909479/625000000 : ℝ)^8343 ≤ (26569001001227/100000000000000 : ℝ)^6295 := by
    have hnat : (229909479 : ℕ)^8343*100000000000000^6295 ≤ 26569001001227^6295*625000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      229909479 625000000 26569001001227 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5064248289/10000000000 : ℝ)^8343 ≤ (20293297370629/50000000000000 : ℝ)^6295 := by
    have hnat : (5064248289 : ℕ)^8343*50000000000000^6295 ≤ 20293297370629^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5064248289 10000000000 20293297370629 50000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4316762443/10000000000 : ℝ), (229909479/625000000 : ℝ), (5064248289/10000000000 : ℝ)] ![(32844404238169/100000000000000 : ℝ), (26569001001227/100000000000000 : ℝ), (20293297370629/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4316762443/10000000000 : ℝ)|^8343 ≤ (32844404238169/100000000000000 : ℝ)^6295
        have hw : |(4316762443/10000000000 : ℝ)|=(4316762443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(229909479/625000000 : ℝ)|^8343 ≤ (26569001001227/100000000000000 : ℝ)^6295
        have hw : |(229909479/625000000 : ℝ)|=(229909479/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5064248289/10000000000 : ℝ)|^8343 ≤ (20293297370629/50000000000000 : ℝ)^6295
        have hw : |(5064248289/10000000000 : ℝ)|=(5064248289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s1_4 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-418834403/2000000000 : ℝ)*x 0 + (5013409289/10000000000 : ℝ)*x 1 + (5689710563/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (418834403/2000000000 : ℝ)^8343 ≤ (12592505826543/100000000000000 : ℝ)^6295 := by
    have hnat : (418834403 : ℕ)^8343*100000000000000^6295 ≤ 12592505826543^6295*2000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      418834403 2000000000 12592505826543 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5013409289/10000000000 : ℝ)^8343 ≤ (800949636413/2000000000000 : ℝ)^6295 := by
    have hnat : (5013409289 : ℕ)^8343*2000000000000^6295 ≤ 800949636413^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5013409289 10000000000 800949636413 2000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5689710563/10000000000 : ℝ)^8343 ≤ (47360012336817/100000000000000 : ℝ)^6295 := by
    have hnat : (5689710563 : ℕ)^8343*100000000000000^6295 ≤ 47360012336817^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5689710563 10000000000 47360012336817 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-418834403/2000000000 : ℝ), (5013409289/10000000000 : ℝ), (5689710563/10000000000 : ℝ)] ![(12592505826543/100000000000000 : ℝ), (800949636413/2000000000000 : ℝ), (47360012336817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-418834403/2000000000 : ℝ)|^8343 ≤ (12592505826543/100000000000000 : ℝ)^6295
        have hw : |(-418834403/2000000000 : ℝ)|=(418834403/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5013409289/10000000000 : ℝ)|^8343 ≤ (800949636413/2000000000000 : ℝ)^6295
        have hw : |(5013409289/10000000000 : ℝ)|=(5013409289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5689710563/10000000000 : ℝ)|^8343 ≤ (47360012336817/100000000000000 : ℝ)^6295
        have hw : |(5689710563/10000000000 : ℝ)|=(5689710563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s1_5 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2620157501/5000000000 : ℝ)*x 0 + (-1782735967/10000000000 : ℝ)*x 1 + (2844857103/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2620157501/5000000000 : ℝ)^8343 ≤ (2654201117537/6250000000000 : ℝ)^6295 := by
    have hnat : (2620157501 : ℕ)^8343*6250000000000^6295 ≤ 2654201117537^6295*5000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620157501 5000000000 2654201117537 6250000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1782735967/10000000000 : ℝ)^8343 ≤ (1271591197827/12500000000000 : ℝ)^6295 := by
    have hnat : (1782735967 : ℕ)^8343*12500000000000^6295 ≤ 1271591197827^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1782735967 10000000000 1271591197827 12500000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2844857103/5000000000 : ℝ)^8343 ≤ (5920006565729/12500000000000 : ℝ)^6295 := by
    have hnat : (2844857103 : ℕ)^8343*12500000000000^6295 ≤ 5920006565729^6295*5000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2844857103 5000000000 5920006565729 12500000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2620157501/5000000000 : ℝ), (-1782735967/10000000000 : ℝ), (2844857103/5000000000 : ℝ)] ![(2654201117537/6250000000000 : ℝ), (1271591197827/12500000000000 : ℝ), (5920006565729/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2620157501/5000000000 : ℝ)|^8343 ≤ (2654201117537/6250000000000 : ℝ)^6295
        have hw : |(2620157501/5000000000 : ℝ)|=(2620157501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1782735967/10000000000 : ℝ)|^8343 ≤ (1271591197827/12500000000000 : ℝ)^6295
        have hw : |(-1782735967/10000000000 : ℝ)|=(1782735967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2844857103/5000000000 : ℝ)|^8343 ≤ (5920006565729/12500000000000 : ℝ)^6295
        have hw : |(2844857103/5000000000 : ℝ)|=(2844857103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s1_6 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (327519607/625000000 : ℝ)*x 0 + (1422428991/2500000000 : ℝ)*x 1 + (-891367617/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (327519607/625000000 : ℝ)^8343 ≤ (21233602012699/50000000000000 : ℝ)^6295 := by
    have hnat : (327519607 : ℕ)^8343*50000000000000^6295 ≤ 21233602012699^6295*625000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327519607 625000000 21233602012699 50000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1422428991/2500000000 : ℝ)^8343 ≤ (2368003595991/5000000000000 : ℝ)^6295 := by
    have hnat : (1422428991 : ℕ)^8343*5000000000000^6295 ≤ 2368003595991^6295*2500000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1422428991 2500000000 2368003595991 5000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (891367617/5000000000 : ℝ)^8343 ≤ (2543181009789/25000000000000 : ℝ)^6295 := by
    have hnat : (891367617 : ℕ)^8343*25000000000000^6295 ≤ 2543181009789^6295*5000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      891367617 5000000000 2543181009789 25000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(327519607/625000000 : ℝ), (1422428991/2500000000 : ℝ), (-891367617/5000000000 : ℝ)] ![(21233602012699/50000000000000 : ℝ), (2368003595991/5000000000000 : ℝ), (2543181009789/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(327519607/625000000 : ℝ)|^8343 ≤ (21233602012699/50000000000000 : ℝ)^6295
        have hw : |(327519607/625000000 : ℝ)|=(327519607/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1422428991/2500000000 : ℝ)|^8343 ≤ (2368003595991/5000000000000 : ℝ)^6295
        have hw : |(1422428991/2500000000 : ℝ)|=(1422428991/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-891367617/5000000000 : ℝ)|^8343 ≤ (2543181009789/25000000000000 : ℝ)^6295
        have hw : |(-891367617/5000000000 : ℝ)|=(891367617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s1_7 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1079586187/2500000000 : ℝ)*x 0 + (5045386427/10000000000 : ℝ)*x 1 + (924446237/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079586187/2500000000 : ℝ)^8343 ≤ (6572072207923/20000000000000 : ℝ)^6295 := by
    have hnat : (1079586187 : ℕ)^8343*20000000000000^6295 ≤ 6572072207923^6295*2500000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079586187 2500000000 6572072207923 20000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5045386427/10000000000 : ℝ)^8343 ≤ (40386371137389/100000000000000 : ℝ)^6295 := by
    have hnat : (5045386427 : ℕ)^8343*100000000000000^6295 ≤ 40386371137389^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5045386427 10000000000 40386371137389 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (924446237/2500000000 : ℝ)^8343 ≤ (13376633902297/50000000000000 : ℝ)^6295 := by
    have hnat : (924446237 : ℕ)^8343*50000000000000^6295 ≤ 13376633902297^6295*2500000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      924446237 2500000000 13376633902297 50000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1079586187/2500000000 : ℝ), (5045386427/10000000000 : ℝ), (924446237/2500000000 : ℝ)] ![(6572072207923/20000000000000 : ℝ), (40386371137389/100000000000000 : ℝ), (13376633902297/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1079586187/2500000000 : ℝ)|^8343 ≤ (6572072207923/20000000000000 : ℝ)^6295
        have hw : |(1079586187/2500000000 : ℝ)|=(1079586187/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5045386427/10000000000 : ℝ)|^8343 ≤ (40386371137389/100000000000000 : ℝ)^6295
        have hw : |(5045386427/10000000000 : ℝ)|=(5045386427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(924446237/2500000000 : ℝ)|^8343 ≤ (13376633902297/50000000000000 : ℝ)^6295
        have hw : |(924446237/2500000000 : ℝ)|=(924446237/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1150_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74814911/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3473/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (223/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2847/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20401/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3473/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (223/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3473/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (223/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3473/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (223/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3473/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (223/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3473/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (223/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3473/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (223/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (223/50000 : ℝ) ^ (4171/1024 : ℝ) ≤ (26617764469/100000000000000000000 : ℝ) := by
    have hpowers : (223/50000 : ℝ)^4171 ≤ (26617764469/100000000000000000000 : ℝ)^1024 := by
      have hnat : (223 : ℕ)^4171*100000000000000000000^1024 ≤ 26617764469^1024*50000^4171 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        223 50000 26617764469 100000000000000000000 4171 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (223/50000 : ℝ)) (X := (26617764469/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4171 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3473/12500 : ℝ) ^ (4171/1024 : ℝ) ≤ (108510406180501269/20000000000000000000 : ℝ) := by
    have hpowers : (3473/12500 : ℝ)^4171 ≤ (108510406180501269/20000000000000000000 : ℝ)^1024 := by
      have hnat : (3473 : ℕ)^4171*20000000000000000000^1024 ≤ 108510406180501269^1024*12500^4171 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3473 12500 108510406180501269 20000000000000000000 4171 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3473/12500 : ℝ)) (X := (108510406180501269/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4171 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000026617764469/50000000000000000000 : ℝ) ≤ (5000000000653479/5000000000000000 : ℝ) ^ (4171/1024 : ℝ) := by
    have hpowers : (50000000026617764469/50000000000000000000 : ℝ)^1024 ≤ (5000000000653479/5000000000000000 : ℝ)^4171 := by
      have hnat : (50000000026617764469 : ℕ)^1024*5000000000000000^4171 ≤ 5000000000653479^4171*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000026617764469 50000000000000000000 5000000000653479 5000000000000000 1024 4171 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000000653479/5000000000000000 : ℝ)) (X := (50000000026617764469/50000000000000000000 : ℝ)) (by norm_num) 4171 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50271276028760135407/50000000000000000000 : ℝ) ≤ (2002658546025543/2000000000000000 : ℝ) ^ (4171/1024 : ℝ) := by
    have hpowers : (50271276028760135407/50000000000000000000 : ℝ)^1024 ≤ (2002658546025543/2000000000000000 : ℝ)^4171 := by
      have hnat : (50271276028760135407 : ℕ)^1024*2000000000000000^4171 ≤ 2002658546025543^4171*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50271276028760135407 50000000000000000000 2002658546025543 2000000000000000 1024 4171 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2002658546025543/2000000000000000 : ℝ)) (X := (50271276028760135407/50000000000000000000 : ℝ)) (by norm_num) 4171 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10108510406180501269/10000000000000000000 : ℝ) ≤ (1253323182368559/1250000000000000 : ℝ) ^ (4171/1024 : ℝ) := by
    have hpowers : (10108510406180501269/10000000000000000000 : ℝ)^1024 ≤ (1253323182368559/1250000000000000 : ℝ)^4171 := by
      have hnat : (10108510406180501269 : ℕ)^1024*1250000000000000^4171 ≤ 1253323182368559^4171*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10108510406180501269 10000000000000000000 1253323182368559 1250000000000000 1024 4171 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1253323182368559/1250000000000000 : ℝ)) (X := (10108510406180501269/10000000000000000000 : ℝ)) (by norm_num) 4171 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(26617764469/100000000000000000000 : ℝ) ≤ ((1708550893260134391/1708625000000000000 : ℝ)+2*(13292728820757/2733800000000000 : ℝ)*(223/50000 : ℝ))^(4171/1024 : ℝ) := by
    rw [show (1708550893260134391/1708625000000000000 : ℝ)+2*(13292728820757/2733800000000000 : ℝ)*(223/50000 : ℝ)=(5000000000653479/5000000000000000 : ℝ) by norm_num, show 1+2*(26617764469/100000000000000000000 : ℝ)=(50000000026617764469/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(108510406180501269/20000000000000000000 : ℝ)+(26617764469/100000000000000000000 : ℝ) ≤ ((1708550893260134391/1708625000000000000 : ℝ)+(13292728820757/2733800000000000 : ℝ)*((3473/12500 : ℝ)+(223/50000 : ℝ)))^(4171/1024 : ℝ) := by
    rw [show (1708550893260134391/1708625000000000000 : ℝ)+(13292728820757/2733800000000000 : ℝ)*((3473/12500 : ℝ)+(223/50000 : ℝ))=(2002658546025543/2000000000000000 : ℝ) by norm_num, show 1+(108510406180501269/20000000000000000000 : ℝ)+(26617764469/100000000000000000000 : ℝ)=(50271276028760135407/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(108510406180501269/20000000000000000000 : ℝ) ≤ ((1708550893260134391/1708625000000000000 : ℝ)+2*(13292728820757/2733800000000000 : ℝ)*(3473/12500 : ℝ))^(4171/1024 : ℝ) := by
    rw [show (1708550893260134391/1708625000000000000 : ℝ)+2*(13292728820757/2733800000000000 : ℝ)*(3473/12500 : ℝ)=(1253323182368559/1250000000000000 : ℝ) by norm_num, show 1+2*(108510406180501269/20000000000000000000 : ℝ)=(10108510406180501269/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1708550893260134391/1708625000000000000 : ℝ)*(X 1 0+X 2 0)+(13292728820757/2733800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4171/1024 : ℝ)) (lo := (223/50000 : ℝ)) (hi := (3473/12500 : ℝ)) (c := (1708550893260134391/1708625000000000000 : ℝ)) (alpha := (13292728820757/2733800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1708550893260134391/1708625000000000000 : ℝ)*(X 0 1+X 2 1)+(13292728820757/2733800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4171/1024 : ℝ)) (lo := (223/50000 : ℝ)) (hi := (3473/12500 : ℝ)) (c := (1708550893260134391/1708625000000000000 : ℝ)) (alpha := (13292728820757/2733800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1708550893260134391/1708625000000000000 : ℝ)*(X 0 2+X 1 2)+(13292728820757/2733800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4171/1024 : ℝ)) (lo := (223/50000 : ℝ)) (hi := (3473/12500 : ℝ)) (c := (1708550893260134391/1708625000000000000 : ℝ)) (alpha := (13292728820757/2733800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-5233431/25000000 : ℝ)*X 0 0+(5699367243/10000000000 : ℝ)*X 0 1+(5003942951/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2709340207/5000000000 : ℝ)*X 1 0+(-2468508499/10000000000 : ℝ)*X 1 1+(1000788423/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1083736491/2000000000 : ℝ)*X 2 0+(625492537/1250000000 : ℝ)*X 2 1+(-1234254077/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4316762443/10000000000 : ℝ)*X 0 0+(229909479/625000000 : ℝ)*X 0 1+(5064248289/10000000000 : ℝ)*X 0 2+(4316762443/10000000000 : ℝ)*X 1 0+(229909479/625000000 : ℝ)*X 1 1+(5064248289/10000000000 : ℝ)*X 1 2+(4316762443/10000000000 : ℝ)*X 2 0+(229909479/625000000 : ℝ)*X 2 1+(5064248289/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-418834403/2000000000 : ℝ)*X 0 0+(5013409289/10000000000 : ℝ)*X 0 1+(5689710563/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2620157501/5000000000 : ℝ)*X 1 0+(-1782735967/10000000000 : ℝ)*X 1 1+(2844857103/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((327519607/625000000 : ℝ)*X 2 0+(1422428991/2500000000 : ℝ)*X 2 1+(-891367617/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1079586187/2500000000 : ℝ)*X 0 0+(5045386427/10000000000 : ℝ)*X 0 1+(924446237/2500000000 : ℝ)*X 0 2+(1079586187/2500000000 : ℝ)*X 1 0+(5045386427/10000000000 : ℝ)*X 1 1+(924446237/2500000000 : ℝ)*X 1 2+(1079586187/2500000000 : ℝ)*X 2 0+(5045386427/10000000000 : ℝ)*X 2 1+(924446237/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (643059502644522817279439043/85431250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (660190567/100000000000000 : ℝ)*(base1) + (2495683/200000000000 : ℝ)*(base19) + (916971093/50000000000000 : ℝ)*(base23) + (12332827/25000000000000 : ℝ)*(upper3) + (105042417/100000000000000 : ℝ)*(upper5) + (1079817093220059/100000000000000 : ℝ)*(major0) + (1079817093220059/100000000000000 : ℝ)*(major1) + (1079817093220059/100000000000000 : ℝ)*(major2) + (1437972432575587/100000000000000 : ℝ)*(sp0) + (718986162925531/50000000000000 : ℝ)*(sp1) + (89873318178051/6250000000000 : ℝ)*(sp2) + (721658350551329/100000000000000 : ℝ)*(sp3) + (3152405981/100000000000000 : ℝ)*(sp4) + (1351098439/100000000000000 : ℝ)*(sp5) + (144331802148379/20000000000000 : ℝ)*(f.failure) + (718987462395501/50000000000000 : ℝ)*(f.sum) + (119189975787417/136690000000000000000000000000 : ℝ)*base66 + (168307399181327889/42715625000000000000000000000000 : ℝ)*base68 + (1355748233981449/667431640625000000000000000000 : ℝ)*base69 + (5632663059910967/5339453125000000000000000000000 : ℝ)*base71 + (828585620418787/136690000000000000000000000000 : ℝ)*base74 + (42142731042923467/5339453125000000000000000000000 : ℝ)*base75 + (99331509888553007/21357812500000000000000000000000 : ℝ)*base78 + (57554228033565861/42715625000000000000000000000000 : ℝ)*base79 + (80255768235067/136690000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (6320731/1000000000000000000000 : ℝ)*base90 + (6320731/1000000000000000000000 : ℝ)*base92 + (6320731/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6147371951259895705779/5467600000000000000000000000 : ℝ) := by norm_num
    linear_combination (2257956673/100000000000000 : ℝ)*(base19) + (1458470307/50000000000000 : ℝ)*(base23) + (53422989/12500000000000 : ℝ)*(upper2) + (621541229/100000000000000 : ℝ)*(upper3) + (182954961/50000000000000 : ℝ)*(upper5) + (222068496600037/20000000000000 : ℝ)*(major0) + (222068496600037/20000000000000 : ℝ)*(major1) + (222068496600037/20000000000000 : ℝ)*(major2) + (2596681437/20000000000000 : ℝ)*(sp1) + (9538268641/50000000000000 : ℝ)*(sp2) + (1478625312225053/100000000000000 : ℝ)*(sp4) + (739305035430597/50000000000000 : ℝ)*(sp5) + (369650829686789/25000000000000 : ℝ)*(sp6) + (92757452037217/12500000000000 : ℝ)*(sp7) + (92757452037217/12500000000000 : ℝ)*(f.failure) + (1478625312225053/100000000000000 : ℝ)*(f.sum) + (14927947598949/5467600000000000000000000000 : ℝ)*base66 + (7350153654746949/4271562500000000000000000000000 : ℝ)*base67 + (2487702652975919/1067890625000000000000000000000 : ℝ)*base70 + (5500346743301727/8543125000000000000000000000000 : ℝ)*base72 + (95913825491667/27338000000000000000000000000 : ℝ)*base73 + (904174563423989/266972656250000000000000000000 : ℝ)*base75 + (23017028461599227/8543125000000000000000000000000 : ℝ)*base78 + (1456784502249523/8543125000000000000000000000000 : ℝ)*base79 + (58185022476961/27338000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (2292687/625000000000000000000 : ℝ)*base89 + (2292687/625000000000000000000 : ℝ)*base91 + (2292687/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1150_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74814911/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3473/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (223/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2847/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20401/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1150_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1150_s2_0 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2146171843/10000000000 : ℝ)*x 0 + (2754646973/5000000000 : ℝ)*x 1 + (1032086853/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2146171843/10000000000 : ℝ)^8343 ≤ (3252144634103/25000000000000 : ℝ)^6295 := by
    have hnat : (2146171843 : ℕ)^8343*25000000000000^6295 ≤ 3252144634103^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2146171843 10000000000 3252144634103 25000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2754646973/5000000000 : ℝ)^8343 ≤ (45380024755589/100000000000000 : ℝ)^6295 := by
    have hnat : (2754646973 : ℕ)^8343*100000000000000^6295 ≤ 45380024755589^6295*5000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2754646973 5000000000 45380024755589 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1032086853/2000000000 : ℝ)^8343 ≤ (8322279339357/20000000000000 : ℝ)^6295 := by
    have hnat : (1032086853 : ℕ)^8343*20000000000000^6295 ≤ 8322279339357^6295*2000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1032086853 2000000000 8322279339357 20000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2146171843/10000000000 : ℝ), (2754646973/5000000000 : ℝ), (1032086853/2000000000 : ℝ)] ![(3252144634103/25000000000000 : ℝ), (45380024755589/100000000000000 : ℝ), (8322279339357/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2146171843/10000000000 : ℝ)|^8343 ≤ (3252144634103/25000000000000 : ℝ)^6295
        have hw : |(-2146171843/10000000000 : ℝ)|=(2146171843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2754646973/5000000000 : ℝ)|^8343 ≤ (45380024755589/100000000000000 : ℝ)^6295
        have hw : |(2754646973/5000000000 : ℝ)|=(2754646973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1032086853/2000000000 : ℝ)|^8343 ≤ (8322279339357/20000000000000 : ℝ)^6295
        have hw : |(1032086853/2000000000 : ℝ)|=(1032086853/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s2_1 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (335845059/625000000 : ℝ)*x 0 + (-2327487677/10000000000 : ℝ)*x 1 + (1290109131/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (335845059/625000000 : ℝ)^8343 ≤ (21951896750313/50000000000000 : ℝ)^6295 := by
    have hnat : (335845059 : ℕ)^8343*50000000000000^6295 ≤ 21951896750313^6295*625000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335845059 625000000 21951896750313 50000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2327487677/10000000000 : ℝ)^8343 ≤ (3621196411013/25000000000000 : ℝ)^6295 := by
    have hnat : (2327487677 : ℕ)^8343*25000000000000^6295 ≤ 3621196411013^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2327487677 10000000000 3621196411013 25000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1290109131/2500000000 : ℝ)^8343 ≤ (41611420838539/100000000000000 : ℝ)^6295 := by
    have hnat : (1290109131 : ℕ)^8343*100000000000000^6295 ≤ 41611420838539^6295*2500000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1290109131 2500000000 41611420838539 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(335845059/625000000 : ℝ), (-2327487677/10000000000 : ℝ), (1290109131/2500000000 : ℝ)] ![(21951896750313/50000000000000 : ℝ), (3621196411013/25000000000000 : ℝ), (41611420838539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(335845059/625000000 : ℝ)|^8343 ≤ (21951896750313/50000000000000 : ℝ)^6295
        have hw : |(335845059/625000000 : ℝ)|=(335845059/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2327487677/10000000000 : ℝ)|^8343 ≤ (3621196411013/25000000000000 : ℝ)^6295
        have hw : |(-2327487677/10000000000 : ℝ)|=(2327487677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1290109131/2500000000 : ℝ)|^8343 ≤ (41611420838539/100000000000000 : ℝ)^6295
        have hw : |(1290109131/2500000000 : ℝ)|=(1290109131/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s2_2 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (671690131/1250000000 : ℝ)*x 0 + (5160436207/10000000000 : ℝ)*x 1 + (-2327487951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671690131/1250000000 : ℝ)^8343 ≤ (43903794626793/100000000000000 : ℝ)^6295 := by
    have hnat : (671690131 : ℕ)^8343*100000000000000^6295 ≤ 43903794626793^6295*1250000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671690131 1250000000 43903794626793 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5160436207/10000000000 : ℝ)^8343 ≤ (8322283490157/20000000000000 : ℝ)^6295 := by
    have hnat : (5160436207 : ℕ)^8343*20000000000000^6295 ≤ 8322283490157^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5160436207 10000000000 8322283490157 20000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2327487951/10000000000 : ℝ)^8343 ≤ (14484787904017/100000000000000 : ℝ)^6295 := by
    have hnat : (2327487951 : ℕ)^8343*100000000000000^6295 ≤ 14484787904017^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2327487951 10000000000 14484787904017 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(671690131/1250000000 : ℝ), (5160436207/10000000000 : ℝ), (-2327487951/10000000000 : ℝ)] ![(43903794626793/100000000000000 : ℝ), (8322283490157/20000000000000 : ℝ), (14484787904017/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(671690131/1250000000 : ℝ)|^8343 ≤ (43903794626793/100000000000000 : ℝ)^6295
        have hw : |(671690131/1250000000 : ℝ)|=(671690131/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5160436207/10000000000 : ℝ)|^8343 ≤ (8322283490157/20000000000000 : ℝ)^6295
        have hw : |(5160436207/10000000000 : ℝ)|=(5160436207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2327487951/10000000000 : ℝ)|^8343 ≤ (14484787904017/100000000000000 : ℝ)^6295
        have hw : |(-2327487951/10000000000 : ℝ)|=(2327487951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s2_3 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (136031431/312500000 : ℝ)*x 0 + (125598927/312500000 : ℝ)*x 1 + (4714297339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (136031431/312500000 : ℝ)^8343 ≤ (16605188891299/50000000000000 : ℝ)^6295 := by
    have hnat : (136031431 : ℕ)^8343*50000000000000^6295 ≤ 16605188891299^6295*312500000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136031431 312500000 16605188891299 50000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (125598927/312500000 : ℝ)^8343 ≤ (29877650715043/100000000000000 : ℝ)^6295 := by
    have hnat : (125598927 : ℕ)^8343*100000000000000^6295 ≤ 29877650715043^6295*312500000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125598927 312500000 29877650715043 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4714297339/10000000000 : ℝ)^8343 ≤ (576749554609/1562500000000 : ℝ)^6295 := by
    have hnat : (4714297339 : ℕ)^8343*1562500000000^6295 ≤ 576749554609^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4714297339 10000000000 576749554609 1562500000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(136031431/312500000 : ℝ), (125598927/312500000 : ℝ), (4714297339/10000000000 : ℝ)] ![(16605188891299/50000000000000 : ℝ), (29877650715043/100000000000000 : ℝ), (576749554609/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(136031431/312500000 : ℝ)|^8343 ≤ (16605188891299/50000000000000 : ℝ)^6295
        have hw : |(136031431/312500000 : ℝ)|=(136031431/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(125598927/312500000 : ℝ)|^8343 ≤ (29877650715043/100000000000000 : ℝ)^6295
        have hw : |(125598927/312500000 : ℝ)|=(125598927/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4714297339/10000000000 : ℝ)|^8343 ≤ (576749554609/1562500000000 : ℝ)^6295
        have hw : |(4714297339/10000000000 : ℝ)|=(4714297339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s2_4 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1073136159/5000000000 : ℝ)*x 0 + (2581413311/5000000000 : ℝ)*x 1 + (5506877681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073136159/5000000000 : ℝ)^8343 ≤ (520375427377/4000000000000 : ℝ)^6295 := by
    have hnat : (1073136159 : ℕ)^8343*4000000000000^6295 ≤ 520375427377^6295*5000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073136159 5000000000 520375427377 4000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2581413311/5000000000 : ℝ)^8343 ≤ (8327393110431/20000000000000 : ℝ)^6295 := by
    have hnat : (2581413311 : ℕ)^8343*20000000000000^6295 ≤ 8327393110431^6295*5000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2581413311 5000000000 8327393110431 20000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5506877681/10000000000 : ℝ)^8343 ≤ (22676824379803/50000000000000 : ℝ)^6295 := by
    have hnat : (5506877681 : ℕ)^8343*50000000000000^6295 ≤ 22676824379803^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5506877681 10000000000 22676824379803 50000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1073136159/5000000000 : ℝ), (2581413311/5000000000 : ℝ), (5506877681/10000000000 : ℝ)] ![(520375427377/4000000000000 : ℝ), (8327393110431/20000000000000 : ℝ), (22676824379803/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1073136159/5000000000 : ℝ)|^8343 ≤ (520375427377/4000000000000 : ℝ)^6295
        have hw : |(-1073136159/5000000000 : ℝ)|=(1073136159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2581413311/5000000000 : ℝ)|^8343 ≤ (8327393110431/20000000000000 : ℝ)^6295
        have hw : |(2581413311/5000000000 : ℝ)|=(2581413311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5506877681/10000000000 : ℝ)|^8343 ≤ (22676824379803/50000000000000 : ℝ)^6295
        have hw : |(5506877681/10000000000 : ℝ)|=(5506877681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s2_5 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5284958993/10000000000 : ℝ)*x 0 + (-990522123/5000000000 : ℝ)*x 1 + (1101375687/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5284958993/10000000000 : ℝ)^8343 ≤ (42947378161033/100000000000000 : ℝ)^6295 := by
    have hnat : (5284958993 : ℕ)^8343*100000000000000^6295 ≤ 42947378161033^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5284958993 10000000000 42947378161033 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (990522123/5000000000 : ℝ)^8343 ≤ (1462370603913/12500000000000 : ℝ)^6295 := by
    have hnat : (990522123 : ℕ)^8343*12500000000000^6295 ≤ 1462370603913^6295*5000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      990522123 5000000000 1462370603913 12500000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1101375687/2000000000 : ℝ)^8343 ≤ (45353656989697/100000000000000 : ℝ)^6295 := by
    have hnat : (1101375687 : ℕ)^8343*100000000000000^6295 ≤ 45353656989697^6295*2000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101375687 2000000000 45353656989697 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5284958993/10000000000 : ℝ), (-990522123/5000000000 : ℝ), (1101375687/2000000000 : ℝ)] ![(42947378161033/100000000000000 : ℝ), (1462370603913/12500000000000 : ℝ), (45353656989697/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5284958993/10000000000 : ℝ)|^8343 ≤ (42947378161033/100000000000000 : ℝ)^6295
        have hw : |(5284958993/10000000000 : ℝ)|=(5284958993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-990522123/5000000000 : ℝ)|^8343 ≤ (1462370603913/12500000000000 : ℝ)^6295
        have hw : |(-990522123/5000000000 : ℝ)|=(990522123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1101375687/2000000000 : ℝ)|^8343 ≤ (45353656989697/100000000000000 : ℝ)^6295
        have hw : |(1101375687/2000000000 : ℝ)|=(1101375687/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s2_6 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1056991469/2000000000 : ℝ)*x 0 + (5506878171/10000000000 : ℝ)*x 1 + (-990523441/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1056991469/2000000000 : ℝ)^8343 ≤ (8589472082367/20000000000000 : ℝ)^6295 := by
    have hnat : (1056991469 : ℕ)^8343*20000000000000^6295 ≤ 8589472082367^6295*2000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056991469 2000000000 8589472082367 20000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5506878171/10000000000 : ℝ)^8343 ≤ (22676827054037/50000000000000 : ℝ)^6295 := by
    have hnat : (5506878171 : ℕ)^8343*50000000000000^6295 ≤ 22676827054037^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5506878171 10000000000 22676827054037 50000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (990523441/5000000000 : ℝ)^8343 ≤ (11698985462541/100000000000000 : ℝ)^6295 := by
    have hnat : (990523441 : ℕ)^8343*100000000000000^6295 ≤ 11698985462541^6295*5000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      990523441 5000000000 11698985462541 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1056991469/2000000000 : ℝ), (5506878171/10000000000 : ℝ), (-990523441/5000000000 : ℝ)] ![(8589472082367/20000000000000 : ℝ), (22676827054037/50000000000000 : ℝ), (11698985462541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1056991469/2000000000 : ℝ)|^8343 ≤ (8589472082367/20000000000000 : ℝ)^6295
        have hw : |(1056991469/2000000000 : ℝ)|=(1056991469/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5506878171/10000000000 : ℝ)|^8343 ≤ (22676827054037/50000000000000 : ℝ)^6295
        have hw : |(5506878171/10000000000 : ℝ)|=(5506878171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-990523441/5000000000 : ℝ)|^8343 ≤ (11698985462541/100000000000000 : ℝ)^6295
        have hw : |(-990523441/5000000000 : ℝ)|=(990523441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s2_7 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4353204837/10000000000 : ℝ)*x 0 + (4709532269/10000000000 : ℝ)*x 1 + (1005994631/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4353204837/10000000000 : ℝ)^8343 ≤ (33212390420203/100000000000000 : ℝ)^6295 := by
    have hnat : (4353204837 : ℕ)^8343*100000000000000^6295 ≤ 33212390420203^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4353204837 10000000000 33212390420203 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4709532269/10000000000 : ℝ)^8343 ≤ (36862531930539/100000000000000 : ℝ)^6295 := by
    have hnat : (4709532269 : ℕ)^8343*100000000000000^6295 ≤ 36862531930539^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4709532269 10000000000 36862531930539 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1005994631/2500000000 : ℝ)^8343 ≤ (29925077626393/100000000000000 : ℝ)^6295 := by
    have hnat : (1005994631 : ℕ)^8343*100000000000000^6295 ≤ 29925077626393^6295*2500000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005994631 2500000000 29925077626393 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4353204837/10000000000 : ℝ), (4709532269/10000000000 : ℝ), (1005994631/2500000000 : ℝ)] ![(33212390420203/100000000000000 : ℝ), (36862531930539/100000000000000 : ℝ), (29925077626393/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4353204837/10000000000 : ℝ)|^8343 ≤ (33212390420203/100000000000000 : ℝ)^6295
        have hw : |(4353204837/10000000000 : ℝ)|=(4353204837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4709532269/10000000000 : ℝ)|^8343 ≤ (36862531930539/100000000000000 : ℝ)^6295
        have hw : |(4709532269/10000000000 : ℝ)|=(4709532269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1005994631/2500000000 : ℝ)|^8343 ≤ (29925077626393/100000000000000 : ℝ)^6295
        have hw : |(1005994631/2500000000 : ℝ)|=(1005994631/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1150_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74814911/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20401/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2847/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (4553/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16479/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20401/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2847/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20401/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2847/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20401/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2847/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20401/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2847/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20401/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2847/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20401/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2847/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2847/50000 : ℝ) ^ (4171/1024 : ℝ) ≤ (426072895957499/50000000000000000000 : ℝ) := by
    have hpowers : (2847/50000 : ℝ)^4171 ≤ (426072895957499/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2847 : ℕ)^4171*50000000000000000000^1024 ≤ 426072895957499^1024*50000^4171 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2847 50000 426072895957499 50000000000000000000 4171 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2847/50000 : ℝ)) (X := (426072895957499/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4171 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (20401/100000 : ℝ) ^ (4171/1024 : ℝ) ≤ (154185376599768261/100000000000000000000 : ℝ) := by
    have hpowers : (20401/100000 : ℝ)^4171 ≤ (154185376599768261/100000000000000000000 : ℝ)^1024 := by
      have hnat : (20401 : ℕ)^4171*100000000000000000000^1024 ≤ 154185376599768261^1024*100000^4171 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20401 100000 154185376599768261 100000000000000000000 4171 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20401/100000 : ℝ)) (X := (154185376599768261/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4171 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000426072895957499/25000000000000000000 : ℝ) ≤ (1250005230110769/1250000000000000 : ℝ) ^ (4171/1024 : ℝ) := by
    have hpowers : (25000426072895957499/25000000000000000000 : ℝ)^1024 ≤ (1250005230110769/1250000000000000 : ℝ)^4171 := by
      have hnat : (25000426072895957499 : ℕ)^1024*1250000000000000^4171 ≤ 1250005230110769^4171*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000426072895957499 25000000000000000000 1250005230110769 1250000000000000 1024 4171 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250005230110769/1250000000000000 : ℝ)) (X := (25000426072895957499/25000000000000000000 : ℝ)) (by norm_num) 4171 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100155037522391683259/100000000000000000000 : ℝ) ≤ (5001902009747423/5000000000000000 : ℝ) ^ (4171/1024 : ℝ) := by
    have hpowers : (100155037522391683259/100000000000000000000 : ℝ)^1024 ≤ (5001902009747423/5000000000000000 : ℝ)^4171 := by
      have hnat : (100155037522391683259 : ℕ)^1024*5000000000000000^4171 ≤ 5001902009747423^4171*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100155037522391683259 100000000000000000000 5001902009747423 5000000000000000 1024 4171 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001902009747423/5000000000000000 : ℝ)) (X := (100155037522391683259/100000000000000000000 : ℝ)) (by norm_num) 4171 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50154185376599768261/50000000000000000000 : ℝ) ≤ (500378309905177/500000000000000 : ℝ) ^ (4171/1024 : ℝ) := by
    have hpowers : (50154185376599768261/50000000000000000000 : ℝ)^1024 ≤ (500378309905177/500000000000000 : ℝ)^4171 := by
      have hnat : (50154185376599768261 : ℕ)^1024*500000000000000^4171 ≤ 500378309905177^4171*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50154185376599768261 50000000000000000000 500378309905177 500000000000000 1024 4171 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500378309905177/500000000000000 : ℝ)) (X := (50154185376599768261/50000000000000000000 : ℝ)) (by norm_num) 4171 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(426072895957499/50000000000000000000 : ℝ) ≤ ((835385066272254717/835625000000000000 : ℝ)+2*(171008118577/66850000000000 : ℝ)*(2847/50000 : ℝ))^(4171/1024 : ℝ) := by
    rw [show (835385066272254717/835625000000000000 : ℝ)+2*(171008118577/66850000000000 : ℝ)*(2847/50000 : ℝ)=(1250005230110769/1250000000000000 : ℝ) by norm_num, show 1+2*(426072895957499/50000000000000000000 : ℝ)=(25000426072895957499/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(154185376599768261/100000000000000000000 : ℝ)+(426072895957499/50000000000000000000 : ℝ) ≤ ((835385066272254717/835625000000000000 : ℝ)+(171008118577/66850000000000 : ℝ)*((20401/100000 : ℝ)+(2847/50000 : ℝ)))^(4171/1024 : ℝ) := by
    rw [show (835385066272254717/835625000000000000 : ℝ)+(171008118577/66850000000000 : ℝ)*((20401/100000 : ℝ)+(2847/50000 : ℝ))=(5001902009747423/5000000000000000 : ℝ) by norm_num, show 1+(154185376599768261/100000000000000000000 : ℝ)+(426072895957499/50000000000000000000 : ℝ)=(100155037522391683259/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(154185376599768261/100000000000000000000 : ℝ) ≤ ((835385066272254717/835625000000000000 : ℝ)+2*(171008118577/66850000000000 : ℝ)*(20401/100000 : ℝ))^(4171/1024 : ℝ) := by
    rw [show (835385066272254717/835625000000000000 : ℝ)+2*(171008118577/66850000000000 : ℝ)*(20401/100000 : ℝ)=(500378309905177/500000000000000 : ℝ) by norm_num, show 1+2*(154185376599768261/100000000000000000000 : ℝ)=(50154185376599768261/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (835385066272254717/835625000000000000 : ℝ)*(X 1 0+X 2 0)+(171008118577/66850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4171/1024 : ℝ)) (lo := (2847/50000 : ℝ)) (hi := (20401/100000 : ℝ)) (c := (835385066272254717/835625000000000000 : ℝ)) (alpha := (171008118577/66850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (835385066272254717/835625000000000000 : ℝ)*(X 0 1+X 2 1)+(171008118577/66850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4171/1024 : ℝ)) (lo := (2847/50000 : ℝ)) (hi := (20401/100000 : ℝ)) (c := (835385066272254717/835625000000000000 : ℝ)) (alpha := (171008118577/66850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (835385066272254717/835625000000000000 : ℝ)*(X 0 2+X 1 2)+(171008118577/66850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4171/1024 : ℝ)) (lo := (2847/50000 : ℝ)) (hi := (20401/100000 : ℝ)) (c := (835385066272254717/835625000000000000 : ℝ)) (alpha := (171008118577/66850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2146171843/10000000000 : ℝ)*X 0 0+(2754646973/5000000000 : ℝ)*X 0 1+(1032086853/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((335845059/625000000 : ℝ)*X 1 0+(-2327487677/10000000000 : ℝ)*X 1 1+(1290109131/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((671690131/1250000000 : ℝ)*X 2 0+(5160436207/10000000000 : ℝ)*X 2 1+(-2327487951/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((136031431/312500000 : ℝ)*X 0 0+(125598927/312500000 : ℝ)*X 0 1+(4714297339/10000000000 : ℝ)*X 0 2+(136031431/312500000 : ℝ)*X 1 0+(125598927/312500000 : ℝ)*X 1 1+(4714297339/10000000000 : ℝ)*X 1 2+(136031431/312500000 : ℝ)*X 2 0+(125598927/312500000 : ℝ)*X 2 1+(4714297339/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1073136159/5000000000 : ℝ)*X 0 0+(2581413311/5000000000 : ℝ)*X 0 1+(5506877681/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5284958993/10000000000 : ℝ)*X 1 0+(-990522123/5000000000 : ℝ)*X 1 1+(1101375687/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1056991469/2000000000 : ℝ)*X 2 0+(5506878171/10000000000 : ℝ)*X 2 1+(-990523441/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4353204837/10000000000 : ℝ)*X 0 0+(4709532269/10000000000 : ℝ)*X 0 1+(1005994631/2500000000 : ℝ)*X 0 2+(4353204837/10000000000 : ℝ)*X 1 0+(4709532269/10000000000 : ℝ)*X 1 1+(1005994631/2500000000 : ℝ)*X 1 2+(4353204837/10000000000 : ℝ)*X 2 0+(4709532269/10000000000 : ℝ)*X 2 1+(1005994631/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (57979103903202161915702877/5968750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1070907669/100000000000000 : ℝ)*(base19) + (103135953/12500000000000 : ℝ)*(base23) + (112461/800000000000 : ℝ)*(upper2) + (392671327/100000000000000 : ℝ)*(upper3) + (8798073/5000000000000 : ℝ)*(upper4) + (2152561600662961/100000000000000 : ℝ)*(major0) + (2152561600662961/100000000000000 : ℝ)*(major1) + (2152561600662961/100000000000000 : ℝ)*(major2) + (2799325450483/97656250000 : ℝ)*(sp0) + (143326525359171/5000000000000 : ℝ)*(sp1) + (573306150600693/20000000000000 : ℝ)*(sp2) + (1438581920939203/100000000000000 : ℝ)*(sp3) + (11158398249/50000000000000 : ℝ)*(sp4) + (937850307/10000000000000 : ℝ)*(sp7) + (719295649721137/50000000000000 : ℝ)*(f.failure) + (2866531578091089/100000000000000 : ℝ)*(f.sum) + (806399192749/417812500000000000000000000 : ℝ)*base65 + (116705381217524537/83562500000000000000000000000000 : ℝ)*base67 + (356551180556537963/83562500000000000000000000000000 : ℝ)*base70 + (634094262284274537/83562500000000000000000000000000 : ℝ)*base71 + (1360385837989/417812500000000000000000000 : ℝ)*base73 + (657556963512587037/83562500000000000000000000000000 : ℝ)*base75 + (82444385033225463/83562500000000000000000000000000 : ℝ)*base78 + (1008856446006337037/83562500000000000000000000000000 : ℝ)*base79 + (1214956206603/835625000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (14473807/2500000000000000000000 : ℝ)*base89 + (14473807/2500000000000000000000 : ℝ)*base91 + (14473807/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12470820139951867851800361/1305664062500000000000000000000 : ℝ) := by norm_num
    linear_combination (413097843/25000000000000 : ℝ)*(base19) + (543666007/50000000000000 : ℝ)*(base23) + (182066041/50000000000000 : ℝ)*(upper2) + (6459603/6250000000000 : ℝ)*(upper3) + (297743197/100000000000000 : ℝ)*(upper5) + (136412803126651/6250000000000 : ℝ)*(major0) + (136412803126651/6250000000000 : ℝ)*(major1) + (136412803126651/6250000000000 : ℝ)*(major2) + (6193238669/25000000000000 : ℝ)*(sp1) + (125714761/3125000000000 : ℝ)*(sp2) + (1453269849409341/50000000000000 : ℝ)*(sp4) + (581302654694527/20000000000000 : ℝ)*(sp5) + (726633647153579/25000000000000 : ℝ)*(sp6) + (36466742071417/2500000000000 : ℝ)*(sp7) + (36466742071417/2500000000000 : ℝ)*(f.failure) + (1453269849409341/50000000000000 : ℝ)*(f.sum) + (5285580075381/1671250000000000000000000000 : ℝ)*base65 + (25143628364273571/2611328125000000000000000000000 : ℝ)*base67 + (91256065941422409/10445312500000000000000000000000 : ℝ)*base69 + (73394650559579193/20890625000000000000000000000000 : ℝ)*base71 + (9195538318667/3342500000000000000000000000 : ℝ)*base73 + (42555890924110443/20890625000000000000000000000000 : ℝ)*base75 + (28304333048211071/2611328125000000000000000000000 : ℝ)*base77 + (6326387445291049/652832031250000000000000000000 : ℝ)*base79 + (3218844365963/835625000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1501113/125000000000000000000 : ℝ)*base90 + (1501113/125000000000000000000 : ℝ)*base92 + (1501113/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1150_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74814911/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20401/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2847/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4553/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16479/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1150_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1150_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74814911/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4553/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16479/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1150_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1150_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1150_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74814911/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4553/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16479/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1150_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
