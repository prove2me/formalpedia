-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1415_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:49:33.466387+00:00
-- url     : https://prove2.me/submissions/6ac00351-6f5c-4e13-898d-5932d2271fce

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
theorem support_rectangle_w1415_s0_0 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-110422959/625000000 : ℝ)*x 0 + (5965979791/10000000000 : ℝ)*x 1 + (4828024979/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (110422959/625000000 : ℝ)^4375 ≤ (5201182810617/50000000000000 : ℝ)^3351 := by
    have hnat : (110422959 : ℕ)^4375*50000000000000^3351 ≤ 5201182810617^3351*625000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110422959 625000000 5201182810617 50000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5965979791/10000000000 : ℝ)^4375 ≤ (2547443290947/5000000000000 : ℝ)^3351 := by
    have hnat : (5965979791 : ℕ)^4375*5000000000000^3351 ≤ 2547443290947^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5965979791 10000000000 2547443290947 5000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4828024979/10000000000 : ℝ)^4375 ≤ (38648768549819/100000000000000 : ℝ)^3351 := by
    have hnat : (4828024979 : ℕ)^4375*100000000000000^3351 ≤ 38648768549819^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4828024979 10000000000 38648768549819 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-110422959/625000000 : ℝ), (5965979791/10000000000 : ℝ), (4828024979/10000000000 : ℝ)] ![(5201182810617/50000000000000 : ℝ), (2547443290947/5000000000000 : ℝ), (38648768549819/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-110422959/625000000 : ℝ)|^4375 ≤ (5201182810617/50000000000000 : ℝ)^3351
        have hw : |(-110422959/625000000 : ℝ)|=(110422959/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5965979791/10000000000 : ℝ)|^4375 ≤ (2547443290947/5000000000000 : ℝ)^3351
        have hw : |(5965979791/10000000000 : ℝ)|=(5965979791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4828024979/10000000000 : ℝ)|^4375 ≤ (38648768549819/100000000000000 : ℝ)^3351
        have hw : |(4828024979/10000000000 : ℝ)|=(4828024979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1415_s0_1 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (343353593/625000000 : ℝ)*x 0 + (-150638781/625000000 : ℝ)*x 1 + (4828025321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (343353593/625000000 : ℝ)^4375 ≤ (22873802896991/50000000000000 : ℝ)^3351 := by
    have hnat : (343353593 : ℕ)^4375*50000000000000^3351 ≤ 22873802896991^3351*625000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343353593 625000000 22873802896991 50000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (150638781/625000000 : ℝ)^4375 ≤ (7801811033981/50000000000000 : ℝ)^3351 := by
    have hnat : (150638781 : ℕ)^4375*50000000000000^3351 ≤ 7801811033981^3351*625000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      150638781 625000000 7801811033981 50000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4828025321/10000000000 : ℝ)^4375 ≤ (38648772124159/100000000000000 : ℝ)^3351 := by
    have hnat : (4828025321 : ℕ)^4375*100000000000000^3351 ≤ 38648772124159^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4828025321 10000000000 38648772124159 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(343353593/625000000 : ℝ), (-150638781/625000000 : ℝ), (4828025321/10000000000 : ℝ)] ![(22873802896991/50000000000000 : ℝ), (7801811033981/50000000000000 : ℝ), (38648772124159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(343353593/625000000 : ℝ)|^4375 ≤ (22873802896991/50000000000000 : ℝ)^3351
        have hw : |(343353593/625000000 : ℝ)|=(343353593/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-150638781/625000000 : ℝ)|^4375 ≤ (7801811033981/50000000000000 : ℝ)^3351
        have hw : |(-150638781/625000000 : ℝ)|=(150638781/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4828025321/10000000000 : ℝ)|^4375 ≤ (38648772124159/100000000000000 : ℝ)^3351
        have hw : |(4828025321/10000000000 : ℝ)|=(4828025321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1415_s0_2 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1373414441/2500000000 : ℝ)*x 0 + (4828025177/10000000000 : ℝ)*x 1 + (-2410220319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1373414441/2500000000 : ℝ)^4375 ≤ (2287380439733/5000000000000 : ℝ)^3351 := by
    have hnat : (1373414441 : ℕ)^4375*5000000000000^3351 ≤ 2287380439733^3351*2500000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1373414441 2500000000 2287380439733 5000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4828025177/10000000000 : ℝ)^4375 ≤ (38648770619173/100000000000000 : ℝ)^3351 := by
    have hnat : (4828025177 : ℕ)^4375*100000000000000^3351 ≤ 38648770619173^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4828025177 10000000000 38648770619173 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2410220319/10000000000 : ℝ)^4375 ≤ (7801810285957/50000000000000 : ℝ)^3351 := by
    have hnat : (2410220319 : ℕ)^4375*50000000000000^3351 ≤ 7801810285957^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2410220319 10000000000 7801810285957 50000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1373414441/2500000000 : ℝ), (4828025177/10000000000 : ℝ), (-2410220319/10000000000 : ℝ)] ![(2287380439733/5000000000000 : ℝ), (38648770619173/100000000000000 : ℝ), (7801810285957/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1373414441/2500000000 : ℝ)|^4375 ≤ (2287380439733/5000000000000 : ℝ)^3351
        have hw : |(1373414441/2500000000 : ℝ)|=(1373414441/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4828025177/10000000000 : ℝ)|^4375 ≤ (38648770619173/100000000000000 : ℝ)^3351
        have hw : |(4828025177/10000000000 : ℝ)|=(4828025177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2410220319/10000000000 : ℝ)|^4375 ≤ (7801810285957/50000000000000 : ℝ)^3351
        have hw : |(-2410220319/10000000000 : ℝ)|=(2410220319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1415_s0_3 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (521001943/1250000000 : ℝ)*x 0 + (1551864421/5000000000 : ℝ)*x 1 + (2776442111/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (521001943/1250000000 : ℝ)^4375 ≤ (31899742216581/100000000000000 : ℝ)^3351 := by
    have hnat : (521001943 : ℕ)^4375*100000000000000^3351 ≤ 31899742216581^3351*1250000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521001943 1250000000 31899742216581 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1551864421/5000000000 : ℝ)^4375 ≤ (10853839721559/50000000000000 : ℝ)^3351 := by
    have hnat : (1551864421 : ℕ)^4375*50000000000000^3351 ≤ 10853839721559^3351*5000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1551864421 5000000000 10853839721559 50000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2776442111/5000000000 : ℝ)^4375 ≤ (23196289164361/50000000000000 : ℝ)^3351 := by
    have hnat : (2776442111 : ℕ)^4375*50000000000000^3351 ≤ 23196289164361^3351*5000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2776442111 5000000000 23196289164361 50000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(521001943/1250000000 : ℝ), (1551864421/5000000000 : ℝ), (2776442111/5000000000 : ℝ)] ![(31899742216581/100000000000000 : ℝ), (10853839721559/50000000000000 : ℝ), (23196289164361/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(521001943/1250000000 : ℝ)|^4375 ≤ (31899742216581/100000000000000 : ℝ)^3351
        have hw : |(521001943/1250000000 : ℝ)|=(521001943/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1551864421/5000000000 : ℝ)|^4375 ≤ (10853839721559/50000000000000 : ℝ)^3351
        have hw : |(1551864421/5000000000 : ℝ)|=(1551864421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2776442111/5000000000 : ℝ)|^4375 ≤ (23196289164361/50000000000000 : ℝ)^3351
        have hw : |(2776442111/5000000000 : ℝ)|=(2776442111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1415_s0_4 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1770852643/10000000000 : ℝ)*x 0 + (2428585677/5000000000 : ℝ)*x 1 + (1483948147/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1770852643/10000000000 : ℝ)^4375 ≤ (10433780367329/100000000000000 : ℝ)^3351 := by
    have hnat : (1770852643 : ℕ)^4375*100000000000000^3351 ≤ 10433780367329^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1770852643 10000000000 10433780367329 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2428585677/5000000000 : ℝ)^4375 ≤ (38953666267097/100000000000000 : ℝ)^3351 := by
    have hnat : (2428585677 : ℕ)^4375*100000000000000^3351 ≤ 38953666267097^3351*5000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2428585677 5000000000 38953666267097 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1483948147/2500000000 : ℝ)^4375 ≤ (6326569168741/12500000000000 : ℝ)^3351 := by
    have hnat : (1483948147 : ℕ)^4375*12500000000000^3351 ≤ 6326569168741^3351*2500000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1483948147 2500000000 6326569168741 12500000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1770852643/10000000000 : ℝ), (2428585677/5000000000 : ℝ), (1483948147/2500000000 : ℝ)] ![(10433780367329/100000000000000 : ℝ), (38953666267097/100000000000000 : ℝ), (6326569168741/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1770852643/10000000000 : ℝ)|^4375 ≤ (10433780367329/100000000000000 : ℝ)^3351
        have hw : |(-1770852643/10000000000 : ℝ)|=(1770852643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2428585677/5000000000 : ℝ)|^4375 ≤ (38953666267097/100000000000000 : ℝ)^3351
        have hw : |(2428585677/5000000000 : ℝ)|=(2428585677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1483948147/2500000000 : ℝ)|^4375 ≤ (6326569168741/12500000000000 : ℝ)^3351
        have hw : |(1483948147/2500000000 : ℝ)|=(1483948147/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1415_s0_5 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5183130089/10000000000 : ℝ)*x 0 + (-1302452693/10000000000 : ℝ)*x 1 + (2967896341/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5183130089/10000000000 : ℝ)^4375 ≤ (42401092324153/100000000000000 : ℝ)^3351 := by
    have hnat : (5183130089 : ℕ)^4375*100000000000000^3351 ≤ 42401092324153^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183130089 10000000000 42401092324153 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1302452693/10000000000 : ℝ)^4375 ≤ (3493176633289/50000000000000 : ℝ)^3351 := by
    have hnat : (1302452693 : ℕ)^4375*50000000000000^3351 ≤ 3493176633289^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1302452693 10000000000 3493176633289 50000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2967896341/5000000000 : ℝ)^4375 ≤ (1265313859909/2500000000000 : ℝ)^3351 := by
    have hnat : (2967896341 : ℕ)^4375*2500000000000^3351 ≤ 1265313859909^3351*5000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2967896341 5000000000 1265313859909 2500000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5183130089/10000000000 : ℝ), (-1302452693/10000000000 : ℝ), (2967896341/5000000000 : ℝ)] ![(42401092324153/100000000000000 : ℝ), (3493176633289/50000000000000 : ℝ), (1265313859909/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5183130089/10000000000 : ℝ)|^4375 ≤ (42401092324153/100000000000000 : ℝ)^3351
        have hw : |(5183130089/10000000000 : ℝ)|=(5183130089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1302452693/10000000000 : ℝ)|^4375 ≤ (3493176633289/50000000000000 : ℝ)^3351
        have hw : |(-1302452693/10000000000 : ℝ)|=(1302452693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2967896341/5000000000 : ℝ)|^4375 ≤ (1265313859909/2500000000000 : ℝ)^3351
        have hw : |(2967896341/5000000000 : ℝ)|=(2967896341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1415_s0_6 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2591565053/5000000000 : ℝ)*x 0 + (1187158499/2000000000 : ℝ)*x 1 + (-325613241/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2591565053/5000000000 : ℝ)^4375 ≤ (1060027312643/2500000000000 : ℝ)^3351 := by
    have hnat : (2591565053 : ℕ)^4375*2500000000000^3351 ≤ 1060027312643^3351*5000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591565053 5000000000 1060027312643 2500000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1187158499/2000000000 : ℝ)^4375 ≤ (50612552314629/100000000000000 : ℝ)^3351 := by
    have hnat : (1187158499 : ℕ)^4375*100000000000000^3351 ≤ 50612552314629^3351*2000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1187158499 2000000000 50612552314629 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (325613241/2500000000 : ℝ)^4375 ≤ (3493177582213/50000000000000 : ℝ)^3351 := by
    have hnat : (325613241 : ℕ)^4375*50000000000000^3351 ≤ 3493177582213^3351*2500000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      325613241 2500000000 3493177582213 50000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2591565053/5000000000 : ℝ), (1187158499/2000000000 : ℝ), (-325613241/2500000000 : ℝ)] ![(1060027312643/2500000000000 : ℝ), (50612552314629/100000000000000 : ℝ), (3493177582213/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2591565053/5000000000 : ℝ)|^4375 ≤ (1060027312643/2500000000000 : ℝ)^3351
        have hw : |(2591565053/5000000000 : ℝ)|=(2591565053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1187158499/2000000000 : ℝ)|^4375 ≤ (50612552314629/100000000000000 : ℝ)^3351
        have hw : |(1187158499/2000000000 : ℝ)|=(1187158499/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-325613241/2500000000 : ℝ)|^4375 ≤ (3493177582213/50000000000000 : ℝ)^3351
        have hw : |(-325613241/2500000000 : ℝ)|=(325613241/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1415_s0_7 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (104420249/250000000 : ℝ)*x 0 + (1372538521/2500000000 : ℝ)*x 1 + (3168699297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (104420249/250000000 : ℝ)^4375 ≤ (31987646167821/100000000000000 : ℝ)^3351 := by
    have hnat : (104420249 : ℕ)^4375*100000000000000^3351 ≤ 31987646167821^3351*250000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104420249 250000000 31987646167821 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1372538521/2500000000 : ℝ)^4375 ≤ (22854760205927/50000000000000 : ℝ)^3351 := by
    have hnat : (1372538521 : ℕ)^4375*50000000000000^3351 ≤ 22854760205927^3351*2500000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1372538521 2500000000 22854760205927 50000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3168699297/10000000000 : ℝ)^4375 ≤ (11151416703047/50000000000000 : ℝ)^3351 := by
    have hnat : (3168699297 : ℕ)^4375*50000000000000^3351 ≤ 11151416703047^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3168699297 10000000000 11151416703047 50000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(104420249/250000000 : ℝ), (1372538521/2500000000 : ℝ), (3168699297/10000000000 : ℝ)] ![(31987646167821/100000000000000 : ℝ), (22854760205927/50000000000000 : ℝ), (11151416703047/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(104420249/250000000 : ℝ)|^4375 ≤ (31987646167821/100000000000000 : ℝ)^3351
        have hw : |(104420249/250000000 : ℝ)|=(104420249/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1372538521/2500000000 : ℝ)|^4375 ≤ (22854760205927/50000000000000 : ℝ)^3351
        have hw : |(1372538521/2500000000 : ℝ)|=(1372538521/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3168699297/10000000000 : ℝ)|^4375 ≤ (11151416703047/50000000000000 : ℝ)^3351
        have hw : |(3168699297/10000000000 : ℝ)|=(3168699297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1415_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157612141/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (487/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5271/20000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (2187/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2187 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2187*1^512 ≤ 0^512*1^2187 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2187 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2187 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2187/512 : ℝ) ≤ (998103262355042197/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2187 ≤ (998103262355042197/50000000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2187*50000000000000000000^512 ≤ 998103262355042197^512*5^2187 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 998103262355042197 50000000000000000000 2187 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (998103262355042197/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2187 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2187/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2187 := by
      have hnat : (1 : ℕ)^512*1^2187 ≤ 1^2187*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2187 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2187 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50998103262355042197/50000000000000000000 : ℝ) ≤ (10046380215493553/10000000000000000 : ℝ) ^ (2187/512 : ℝ) := by
    have hpowers : (50998103262355042197/50000000000000000000 : ℝ)^512 ≤ (10046380215493553/10000000000000000 : ℝ)^2187 := by
      have hnat : (50998103262355042197 : ℕ)^512*10000000000000000^2187 ≤ 10046380215493553^2187*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50998103262355042197 50000000000000000000 10046380215493553 10000000000000000 512 2187 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10046380215493553/10000000000000000 : ℝ)) (X := (50998103262355042197/50000000000000000000 : ℝ)) (by norm_num) 2187 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25998103262355042197/25000000000000000000 : ℝ) ≤ (5046380215493553/5000000000000000 : ℝ) ^ (2187/512 : ℝ) := by
    have hpowers : (25998103262355042197/25000000000000000000 : ℝ)^512 ≤ (5046380215493553/5000000000000000 : ℝ)^2187 := by
      have hnat : (25998103262355042197 : ℕ)^512*5000000000000000^2187 ≤ 5046380215493553^2187*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25998103262355042197 25000000000000000000 5046380215493553 5000000000000000 512 2187 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5046380215493553/5000000000000000 : ℝ)) (X := (25998103262355042197/25000000000000000000 : ℝ)) (by norm_num) 2187 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(46380215493553/4000000000000000 : ℝ)*(0 : ℝ))^(2187/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(46380215493553/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(998103262355042197/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(46380215493553/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2187/512 : ℝ) := by
    rw [show (1 : ℝ)+(46380215493553/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10046380215493553/10000000000000000 : ℝ) by norm_num, show 1+(998103262355042197/50000000000000000000 : ℝ)+(0 : ℝ)=(50998103262355042197/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(998103262355042197/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(46380215493553/4000000000000000 : ℝ)*(2/5 : ℝ))^(2187/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(46380215493553/4000000000000000 : ℝ)*(2/5 : ℝ)=(5046380215493553/5000000000000000 : ℝ) by norm_num, show 1+2*(998103262355042197/50000000000000000000 : ℝ)=(25998103262355042197/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(46380215493553/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2187/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (46380215493553/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(46380215493553/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2187/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (46380215493553/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(46380215493553/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2187/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (46380215493553/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-110422959/625000000 : ℝ)*X 0 0+(5965979791/10000000000 : ℝ)*X 0 1+(4828024979/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((343353593/625000000 : ℝ)*X 1 0+(-150638781/625000000 : ℝ)*X 1 1+(4828025321/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1373414441/2500000000 : ℝ)*X 2 0+(4828025177/10000000000 : ℝ)*X 2 1+(-2410220319/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((521001943/1250000000 : ℝ)*X 0 0+(1551864421/5000000000 : ℝ)*X 0 1+(2776442111/5000000000 : ℝ)*X 0 2+(521001943/1250000000 : ℝ)*X 1 0+(1551864421/5000000000 : ℝ)*X 1 1+(2776442111/5000000000 : ℝ)*X 1 2+(521001943/1250000000 : ℝ)*X 2 0+(1551864421/5000000000 : ℝ)*X 2 1+(2776442111/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1770852643/10000000000 : ℝ)*X 0 0+(2428585677/5000000000 : ℝ)*X 0 1+(1483948147/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5183130089/10000000000 : ℝ)*X 1 0+(-1302452693/10000000000 : ℝ)*X 1 1+(2967896341/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2591565053/5000000000 : ℝ)*X 2 0+(1187158499/2000000000 : ℝ)*X 2 1+(-325613241/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((104420249/250000000 : ℝ)*X 0 0+(1372538521/2500000000 : ℝ)*X 0 1+(3168699297/10000000000 : ℝ)*X 0 2+(104420249/250000000 : ℝ)*X 1 0+(1372538521/2500000000 : ℝ)*X 1 1+(3168699297/10000000000 : ℝ)*X 1 2+(104420249/250000000 : ℝ)*X 2 0+(1372538521/2500000000 : ℝ)*X 2 1+(3168699297/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1412039222816866266090213/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (206567119/12500000000000 : ℝ)*(base19) + (105933407/6250000000000 : ℝ)*(base23) + (186716367/100000000000000 : ℝ)*(upper3) + (962551/100000000000000 : ℝ)*(upper4) + (122884559/50000000000000 : ℝ)*(upper5) + (643545636739469/100000000000000 : ℝ)*(major0) + (643545636739469/100000000000000 : ℝ)*(major1) + (643545636739469/100000000000000 : ℝ)*(major2) + (878775051754143/100000000000000 : ℝ)*(sp0) + (878779700411383/100000000000000 : ℝ)*(sp1) + (878779658013823/100000000000000 : ℝ)*(sp2) + (408306849202363/100000000000000 : ℝ)*(sp3) + (393824637/6250000000000 : ℝ)*(sp4) + (2835988367/100000000000000 : ℝ)*(sp7) + (40830968519073/10000000000000 : ℝ)*(f.failure) + (175756270589667/20000000000000 : ℝ)*(f.sum) + (46486518656643/200000000000000000000000000000 : ℝ)*base66 + (1306337688143357/400000000000000000000000000000 : ℝ)*base67 + (1326697081056643/400000000000000000000000000000 : ℝ)*base70 + (294605168256643/400000000000000000000000000000 : ℝ)*base72 + (538677808943357/200000000000000000000000000000 : ℝ)*base73 + (1585753901056643/400000000000000000000000000000 : ℝ)*base76 + (1352559515456643/400000000000000000000000000000 : ℝ)*base78 + (952030947856643/400000000000000000000000000000 : ℝ)*base80 + (93829499456643/200000000000000000000000000000 : ℝ)*base82 + (4865293/1000000000000000000000 : ℝ)*base89 + (4865293/1000000000000000000000 : ℝ)*base91 + (4865293/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (74574444031956746622291/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (135090003/10000000000000 : ℝ)*(base19) + (170175873/12500000000000 : ℝ)*(base23) + (168946461/100000000000000 : ℝ)*(base32) + (52714039/25000000000000 : ℝ)*(upper3) + (20693849/20000000000000 : ℝ)*(upper5) + (84867066694951/12500000000000 : ℝ)*(major0) + (84867066694951/12500000000000 : ℝ)*(major1) + (84867066694951/12500000000000 : ℝ)*(major2) + (3131455729/100000000000000 : ℝ)*(sp1) + (814018383/25000000000000 : ℝ)*(sp2) + (46355438003779/5000000000000 : ℝ)*(sp4) + (463552138859911/50000000000000 : ℝ)*(sp5) + (115888017824383/12500000000000 : ℝ)*(sp6) + (430763939231987/100000000000000 : ℝ)*(sp7) + (26922756761153/6250000000000 : ℝ)*(f.failure) + (46355438003779/5000000000000 : ℝ)*(f.sum) + (46072856349097/25000000000000000000000000000 : ℝ)*base66 + (397041946750903/50000000000000000000000000000 : ℝ)*base67 + (261632249200903/50000000000000000000000000000 : ℝ)*base69 + (124510213349097/50000000000000000000000000000 : ℝ)*base72 + (91270891200903/25000000000000000000000000000 : ℝ)*base73 + (148000529449097/50000000000000000000000000000 : ℝ)*base76 + (38948470550903/50000000000000000000000000000 : ℝ)*base77 + (130860720550903/50000000000000000000000000000 : ℝ)*base79 + (32569289775903/25000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (41427/625000000000000000000 : ℝ)*base90 + (41427/625000000000000000000 : ℝ)*base92 + (41427/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1415_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157612141/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (487/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5271/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1415_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1415_s1_0 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1941113003/10000000000 : ℝ)*x 0 + (2805442899/5000000000 : ℝ)*x 1 + (2535686331/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1941113003/10000000000 : ℝ)^4375 ≤ (735145162363/6250000000000 : ℝ)^3351 := by
    have hnat : (1941113003 : ℕ)^4375*6250000000000^3351 ≤ 735145162363^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1941113003 10000000000 735145162363 6250000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2805442899/5000000000 : ℝ)^4375 ≤ (47026249872639/100000000000000 : ℝ)^3351 := by
    have hnat : (2805442899 : ℕ)^4375*100000000000000^3351 ≤ 47026249872639^3351*5000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2805442899 5000000000 47026249872639 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2535686331/5000000000 : ℝ)^4375 ≤ (4121142751311/10000000000000 : ℝ)^3351 := by
    have hnat : (2535686331 : ℕ)^4375*10000000000000^3351 ≤ 4121142751311^3351*5000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2535686331 5000000000 4121142751311 10000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1941113003/10000000000 : ℝ), (2805442899/5000000000 : ℝ), (2535686331/5000000000 : ℝ)] ![(735145162363/6250000000000 : ℝ), (47026249872639/100000000000000 : ℝ), (4121142751311/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1941113003/10000000000 : ℝ)|^4375 ≤ (735145162363/6250000000000 : ℝ)^3351
        have hw : |(-1941113003/10000000000 : ℝ)|=(1941113003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2805442899/5000000000 : ℝ)|^4375 ≤ (47026249872639/100000000000000 : ℝ)^3351
        have hw : |(2805442899/5000000000 : ℝ)|=(2805442899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2535686331/5000000000 : ℝ)|^4375 ≤ (4121142751311/10000000000000 : ℝ)^3351
        have hw : |(2535686331/5000000000 : ℝ)|=(2535686331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1415_s1_1 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (539821997/1000000000 : ℝ)*x 0 + (-1113652657/5000000000 : ℝ)*x 1 + (316960617/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (539821997/1000000000 : ℝ)^4375 ≤ (8942554408039/20000000000000 : ℝ)^3351 := by
    have hnat : (539821997 : ℕ)^4375*20000000000000^3351 ≤ 8942554408039^3351*1000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539821997 1000000000 8942554408039 20000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1113652657/5000000000 : ℝ)^4375 ≤ (14075830026101/100000000000000 : ℝ)^3351 := by
    have hnat : (1113652657 : ℕ)^4375*100000000000000^3351 ≤ 14075830026101^3351*5000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1113652657 5000000000 14075830026101 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (316960617/625000000 : ℝ)^4375 ≤ (824227958251/2000000000000 : ℝ)^3351 := by
    have hnat : (316960617 : ℕ)^4375*2000000000000^3351 ≤ 824227958251^3351*625000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      316960617 625000000 824227958251 2000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(539821997/1000000000 : ℝ), (-1113652657/5000000000 : ℝ), (316960617/625000000 : ℝ)] ![(8942554408039/20000000000000 : ℝ), (14075830026101/100000000000000 : ℝ), (824227958251/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(539821997/1000000000 : ℝ)|^4375 ≤ (8942554408039/20000000000000 : ℝ)^3351
        have hw : |(539821997/1000000000 : ℝ)|=(539821997/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1113652657/5000000000 : ℝ)|^4375 ≤ (14075830026101/100000000000000 : ℝ)^3351
        have hw : |(-1113652657/5000000000 : ℝ)|=(1113652657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(316960617/625000000 : ℝ)|^4375 ≤ (824227958251/2000000000000 : ℝ)^3351
        have hw : |(316960617/625000000 : ℝ)|=(316960617/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1415_s1_2 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2699109121/5000000000 : ℝ)*x 0 + (5071372549/10000000000 : ℝ)*x 1 + (-1113652069/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2699109121/5000000000 : ℝ)^4375 ≤ (22356376676839/50000000000000 : ℝ)^3351 := by
    have hnat : (2699109121 : ℕ)^4375*50000000000000^3351 ≤ 22356376676839^3351*5000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699109121 5000000000 22356376676839 50000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5071372549/10000000000 : ℝ)^4375 ≤ (20605713157117/50000000000000 : ℝ)^3351 := by
    have hnat : (5071372549 : ℕ)^4375*50000000000000^3351 ≤ 20605713157117^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5071372549 10000000000 20605713157117 50000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1113652069/5000000000 : ℝ)^4375 ≤ (175947754039/1250000000000 : ℝ)^3351 := by
    have hnat : (1113652069 : ℕ)^4375*1250000000000^3351 ≤ 175947754039^3351*5000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1113652069 5000000000 175947754039 1250000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2699109121/5000000000 : ℝ), (5071372549/10000000000 : ℝ), (-1113652069/5000000000 : ℝ)] ![(22356376676839/50000000000000 : ℝ), (20605713157117/50000000000000 : ℝ), (175947754039/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2699109121/5000000000 : ℝ)|^4375 ≤ (22356376676839/50000000000000 : ℝ)^3351
        have hw : |(2699109121/5000000000 : ℝ)|=(2699109121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5071372549/10000000000 : ℝ)|^4375 ≤ (20605713157117/50000000000000 : ℝ)^3351
        have hw : |(5071372549/10000000000 : ℝ)|=(5071372549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1113652069/5000000000 : ℝ)|^4375 ≤ (175947754039/1250000000000 : ℝ)^3351
        have hw : |(-1113652069/5000000000 : ℝ)|=(1113652069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1415_s1_3 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069795491/2500000000 : ℝ)*x 0 + (1866980933/5000000000 : ℝ)*x 1 + (4895133289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069795491/2500000000 : ℝ)^4375 ≤ (16507519610429/50000000000000 : ℝ)^3351 := by
    have hnat : (1069795491 : ℕ)^4375*50000000000000^3351 ≤ 16507519610429^3351*2500000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069795491 2500000000 16507519610429 50000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1866980933/5000000000 : ℝ)^4375 ≤ (27633339224123/100000000000000 : ℝ)^3351 := by
    have hnat : (1866980933 : ℕ)^4375*100000000000000^3351 ≤ 27633339224123^3351*5000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1866980933 5000000000 27633339224123 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4895133289/10000000000 : ℝ)^4375 ≤ (19675810766607/50000000000000 : ℝ)^3351 := by
    have hnat : (4895133289 : ℕ)^4375*50000000000000^3351 ≤ 19675810766607^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4895133289 10000000000 19675810766607 50000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069795491/2500000000 : ℝ), (1866980933/5000000000 : ℝ), (4895133289/10000000000 : ℝ)] ![(16507519610429/50000000000000 : ℝ), (27633339224123/100000000000000 : ℝ), (19675810766607/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069795491/2500000000 : ℝ)|^4375 ≤ (16507519610429/50000000000000 : ℝ)^3351
        have hw : |(1069795491/2500000000 : ℝ)|=(1069795491/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1866980933/5000000000 : ℝ)|^4375 ≤ (27633339224123/100000000000000 : ℝ)^3351
        have hw : |(1866980933/5000000000 : ℝ)|=(1866980933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4895133289/10000000000 : ℝ)|^4375 ≤ (19675810766607/50000000000000 : ℝ)^3351
        have hw : |(4895133289/10000000000 : ℝ)|=(4895133289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1415_s1_4 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-48538249/250000000 : ℝ)*x 0 + (5077767051/10000000000 : ℝ)*x 1 + (140109553/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (48538249/250000000 : ℝ)^4375 ≤ (5882810681559/50000000000000 : ℝ)^3351 := by
    have hnat : (48538249 : ℕ)^4375*50000000000000^3351 ≤ 5882810681559^3351*250000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48538249 250000000 5882810681559 50000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5077767051/10000000000 : ℝ)^4375 ≤ (41279281981103/100000000000000 : ℝ)^3351 := by
    have hnat : (5077767051 : ℕ)^4375*100000000000000^3351 ≤ 41279281981103^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5077767051 10000000000 41279281981103 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (140109553/250000000 : ℝ)^4375 ≤ (11738774159969/25000000000000 : ℝ)^3351 := by
    have hnat : (140109553 : ℕ)^4375*25000000000000^3351 ≤ 11738774159969^3351*250000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140109553 250000000 11738774159969 25000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-48538249/250000000 : ℝ), (5077767051/10000000000 : ℝ), (140109553/250000000 : ℝ)] ![(5882810681559/50000000000000 : ℝ), (41279281981103/100000000000000 : ℝ), (11738774159969/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-48538249/250000000 : ℝ)|^4375 ≤ (5882810681559/50000000000000 : ℝ)^3351
        have hw : |(-48538249/250000000 : ℝ)|=(48538249/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5077767051/10000000000 : ℝ)|^4375 ≤ (41279281981103/100000000000000 : ℝ)^3351
        have hw : |(5077767051/10000000000 : ℝ)|=(5077767051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(140109553/250000000 : ℝ)|^4375 ≤ (11738774159969/25000000000000 : ℝ)^3351
        have hw : |(140109553/250000000 : ℝ)|=(140109553/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1415_s1_5 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5257406091/10000000000 : ℝ)*x 0 + (-84714643/500000000 : ℝ)*x 1 + (5604382127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5257406091/10000000000 : ℝ)^4375 ≤ (2159806143933/5000000000000 : ℝ)^3351 := by
    have hnat : (5257406091 : ℕ)^4375*5000000000000^3351 ≤ 2159806143933^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257406091 10000000000 2159806143933 5000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84714643/500000000 : ℝ)^4375 ≤ (4924390198293/50000000000000 : ℝ)^3351 := by
    have hnat : (84714643 : ℕ)^4375*50000000000000^3351 ≤ 4924390198293^3351*500000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84714643 500000000 4924390198293 50000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5604382127/10000000000 : ℝ)^4375 ≤ (23477548358223/50000000000000 : ℝ)^3351 := by
    have hnat : (5604382127 : ℕ)^4375*50000000000000^3351 ≤ 23477548358223^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5604382127 10000000000 23477548358223 50000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5257406091/10000000000 : ℝ), (-84714643/500000000 : ℝ), (5604382127/10000000000 : ℝ)] ![(2159806143933/5000000000000 : ℝ), (4924390198293/50000000000000 : ℝ), (23477548358223/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5257406091/10000000000 : ℝ)|^4375 ≤ (2159806143933/5000000000000 : ℝ)^3351
        have hw : |(5257406091/10000000000 : ℝ)|=(5257406091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-84714643/500000000 : ℝ)|^4375 ≤ (4924390198293/50000000000000 : ℝ)^3351
        have hw : |(-84714643/500000000 : ℝ)|=(84714643/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5604382127/10000000000 : ℝ)|^4375 ≤ (23477548358223/50000000000000 : ℝ)^3351
        have hw : |(5604382127/10000000000 : ℝ)|=(5604382127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1415_s1_6 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (657175759/1250000000 : ℝ)*x 0 + (5604382093/10000000000 : ℝ)*x 1 + (-338858587/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (657175759/1250000000 : ℝ)^4375 ≤ (1349878833589/3125000000000 : ℝ)^3351 := by
    have hnat : (657175759 : ℕ)^4375*3125000000000^3351 ≤ 1349878833589^3351*1250000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657175759 1250000000 1349878833589 3125000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5604382093/10000000000 : ℝ)^4375 ≤ (5869387043067/12500000000000 : ℝ)^3351 := by
    have hnat : (5604382093 : ℕ)^4375*12500000000000^3351 ≤ 5869387043067^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5604382093 10000000000 5869387043067 12500000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338858587/2000000000 : ℝ)^4375 ≤ (4924390482889/50000000000000 : ℝ)^3351 := by
    have hnat : (338858587 : ℕ)^4375*50000000000000^3351 ≤ 4924390482889^3351*2000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338858587 2000000000 4924390482889 50000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(657175759/1250000000 : ℝ), (5604382093/10000000000 : ℝ), (-338858587/2000000000 : ℝ)] ![(1349878833589/3125000000000 : ℝ), (5869387043067/12500000000000 : ℝ), (4924390482889/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(657175759/1250000000 : ℝ)|^4375 ≤ (1349878833589/3125000000000 : ℝ)^3351
        have hw : |(657175759/1250000000 : ℝ)|=(657175759/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5604382093/10000000000 : ℝ)|^4375 ≤ (5869387043067/12500000000000 : ℝ)^3351
        have hw : |(5604382093/10000000000 : ℝ)|=(5604382093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-338858587/2000000000 : ℝ)|^4375 ≤ (4924390482889/50000000000000 : ℝ)^3351
        have hw : |(-338858587/2000000000 : ℝ)|=(338858587/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1415_s1_7 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4280078781/10000000000 : ℝ)*x 0 + (4881368389/10000000000 : ℝ)*x 1 + (149918589/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4280078781/10000000000 : ℝ)^4375 ≤ (33024073061609/100000000000000 : ℝ)^3351 := by
    have hnat : (4280078781 : ℕ)^4375*100000000000000^3351 ≤ 33024073061609^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4280078781 10000000000 33024073061609 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4881368389/10000000000 : ℝ)^4375 ≤ (19603607299241/50000000000000 : ℝ)^3351 := by
    have hnat : (4881368389 : ℕ)^4375*50000000000000^3351 ≤ 19603607299241^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4881368389 10000000000 19603607299241 50000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (149918589/400000000 : ℝ)^4375 ≤ (27768712329759/100000000000000 : ℝ)^3351 := by
    have hnat : (149918589 : ℕ)^4375*100000000000000^3351 ≤ 27768712329759^3351*400000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      149918589 400000000 27768712329759 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4280078781/10000000000 : ℝ), (4881368389/10000000000 : ℝ), (149918589/400000000 : ℝ)] ![(33024073061609/100000000000000 : ℝ), (19603607299241/50000000000000 : ℝ), (27768712329759/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4280078781/10000000000 : ℝ)|^4375 ≤ (33024073061609/100000000000000 : ℝ)^3351
        have hw : |(4280078781/10000000000 : ℝ)|=(4280078781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4881368389/10000000000 : ℝ)|^4375 ≤ (19603607299241/50000000000000 : ℝ)^3351
        have hw : |(4881368389/10000000000 : ℝ)|=(4881368389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(149918589/400000000 : ℝ)|^4375 ≤ (27768712329759/100000000000000 : ℝ)^3351
        have hw : |(149918589/400000000 : ℝ)|=(149918589/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1415_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157612141/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5271/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (487/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (1507/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (947/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5271/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (487/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5271/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (487/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5271/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (487/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5271/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (487/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5271/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (487/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5271/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (487/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (487/25000 : ℝ) ^ (2187/512 : ℝ) ≤ (2471587216479/50000000000000000000 : ℝ) := by
    have hpowers : (487/25000 : ℝ)^2187 ≤ (2471587216479/50000000000000000000 : ℝ)^512 := by
      have hnat : (487 : ℕ)^2187*50000000000000000000^512 ≤ 2471587216479^512*25000^2187 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        487 25000 2471587216479 50000000000000000000 2187 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (487/25000 : ℝ)) (X := (2471587216479/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2187 512 (by norm_num) hpowers
    exact h
  have hpowhi : (5271/20000 : ℝ) ^ (2187/512 : ℝ) ≤ (167955970066659441/50000000000000000000 : ℝ) := by
    have hpowers : (5271/20000 : ℝ)^2187 ≤ (167955970066659441/50000000000000000000 : ℝ)^512 := by
      have hnat : (5271 : ℕ)^2187*50000000000000000000^512 ≤ 167955970066659441^512*20000^2187 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5271 20000 167955970066659441 50000000000000000000 2187 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5271/20000 : ℝ)) (X := (167955970066659441/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2187 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000002471587216479/25000000000000000000 : ℝ) ≤ (10000000231449951/10000000000000000 : ℝ) ^ (2187/512 : ℝ) := by
    have hpowers : (25000002471587216479/25000000000000000000 : ℝ)^512 ≤ (10000000231449951/10000000000000000 : ℝ)^2187 := by
      have hnat : (25000002471587216479 : ℕ)^512*10000000000000000^2187 ≤ 10000000231449951^2187*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000002471587216479 25000000000000000000 10000000231449951 10000000000000000 512 2187 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000231449951/10000000000000000 : ℝ)) (X := (25000002471587216479/25000000000000000000 : ℝ)) (by norm_num) 2187 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (627099480520673449/625000000000000000 : ℝ) ≤ (5003927037897683/5000000000000000 : ℝ) ^ (2187/512 : ℝ) := by
    have hpowers : (627099480520673449/625000000000000000 : ℝ)^512 ≤ (5003927037897683/5000000000000000 : ℝ)^2187 := by
      have hnat : (627099480520673449 : ℕ)^512*5000000000000000^2187 ≤ 5003927037897683^2187*625000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        627099480520673449 625000000000000000 5003927037897683 5000000000000000 512 2187 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5003927037897683/5000000000000000 : ℝ)) (X := (627099480520673449/625000000000000000 : ℝ)) (by norm_num) 2187 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25167955970066659441/25000000000000000000 : ℝ) ≤ (10015707920140781/10000000000000000 : ℝ) ^ (2187/512 : ℝ) := by
    have hpowers : (25167955970066659441/25000000000000000000 : ℝ)^512 ≤ (10015707920140781/10000000000000000 : ℝ)^2187 := by
      have hnat : (25167955970066659441 : ℕ)^512*10000000000000000^2187 ≤ 10015707920140781^2187*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25167955970066659441 25000000000000000000 10015707920140781 10000000000000000 512 2187 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10015707920140781/10000000000000000 : ℝ)) (X := (25167955970066659441/25000000000000000000 : ℝ)) (by norm_num) 2187 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2471587216479/50000000000000000000 : ℝ) ≤ ((244039407071429217217/244070000000000000000 : ℝ)+2*(1570768869083/488140000000000 : ℝ)*(487/25000 : ℝ))^(2187/512 : ℝ) := by
    rw [show (244039407071429217217/244070000000000000000 : ℝ)+2*(1570768869083/488140000000000 : ℝ)*(487/25000 : ℝ)=(10000000231449951/10000000000000000 : ℝ) by norm_num, show 1+2*(2471587216479/50000000000000000000 : ℝ)=(25000002471587216479/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(167955970066659441/50000000000000000000 : ℝ)+(2471587216479/50000000000000000000 : ℝ) ≤ ((244039407071429217217/244070000000000000000 : ℝ)+(1570768869083/488140000000000 : ℝ)*((5271/20000 : ℝ)+(487/25000 : ℝ)))^(2187/512 : ℝ) := by
    rw [show (244039407071429217217/244070000000000000000 : ℝ)+(1570768869083/488140000000000 : ℝ)*((5271/20000 : ℝ)+(487/25000 : ℝ))=(5003927037897683/5000000000000000 : ℝ) by norm_num, show 1+(167955970066659441/50000000000000000000 : ℝ)+(2471587216479/50000000000000000000 : ℝ)=(627099480520673449/625000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(167955970066659441/50000000000000000000 : ℝ) ≤ ((244039407071429217217/244070000000000000000 : ℝ)+2*(1570768869083/488140000000000 : ℝ)*(5271/20000 : ℝ))^(2187/512 : ℝ) := by
    rw [show (244039407071429217217/244070000000000000000 : ℝ)+2*(1570768869083/488140000000000 : ℝ)*(5271/20000 : ℝ)=(10015707920140781/10000000000000000 : ℝ) by norm_num, show 1+2*(167955970066659441/50000000000000000000 : ℝ)=(25167955970066659441/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (244039407071429217217/244070000000000000000 : ℝ)*(X 1 0+X 2 0)+(1570768869083/488140000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2187/512 : ℝ)) (lo := (487/25000 : ℝ)) (hi := (5271/20000 : ℝ)) (c := (244039407071429217217/244070000000000000000 : ℝ)) (alpha := (1570768869083/488140000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (244039407071429217217/244070000000000000000 : ℝ)*(X 0 1+X 2 1)+(1570768869083/488140000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2187/512 : ℝ)) (lo := (487/25000 : ℝ)) (hi := (5271/20000 : ℝ)) (c := (244039407071429217217/244070000000000000000 : ℝ)) (alpha := (1570768869083/488140000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (244039407071429217217/244070000000000000000 : ℝ)*(X 0 2+X 1 2)+(1570768869083/488140000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2187/512 : ℝ)) (lo := (487/25000 : ℝ)) (hi := (5271/20000 : ℝ)) (c := (244039407071429217217/244070000000000000000 : ℝ)) (alpha := (1570768869083/488140000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1941113003/10000000000 : ℝ)*X 0 0+(2805442899/5000000000 : ℝ)*X 0 1+(2535686331/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((539821997/1000000000 : ℝ)*X 1 0+(-1113652657/5000000000 : ℝ)*X 1 1+(316960617/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2699109121/5000000000 : ℝ)*X 2 0+(5071372549/10000000000 : ℝ)*X 2 1+(-1113652069/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1069795491/2500000000 : ℝ)*X 0 0+(1866980933/5000000000 : ℝ)*X 0 1+(4895133289/10000000000 : ℝ)*X 0 2+(1069795491/2500000000 : ℝ)*X 1 0+(1866980933/5000000000 : ℝ)*X 1 1+(4895133289/10000000000 : ℝ)*X 1 2+(1069795491/2500000000 : ℝ)*X 2 0+(1866980933/5000000000 : ℝ)*X 2 1+(4895133289/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-48538249/250000000 : ℝ)*X 0 0+(5077767051/10000000000 : ℝ)*X 0 1+(140109553/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5257406091/10000000000 : ℝ)*X 1 0+(-84714643/500000000 : ℝ)*X 1 1+(5604382127/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((657175759/1250000000 : ℝ)*X 2 0+(5604382093/10000000000 : ℝ)*X 2 1+(-338858587/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4280078781/10000000000 : ℝ)*X 0 0+(4881368389/10000000000 : ℝ)*X 0 1+(149918589/400000000 : ℝ)*X 0 2+(4280078781/10000000000 : ℝ)*X 1 0+(4881368389/10000000000 : ℝ)*X 1 1+(149918589/400000000 : ℝ)*X 1 2+(4280078781/10000000000 : ℝ)*X 2 0+(4881368389/10000000000 : ℝ)*X 2 1+(149918589/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (78999750051147477703716957411/12203500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (137522539/100000000000000 : ℝ)*(base1) + (33684723/2000000000000 : ℝ)*(base19) + (545456519/50000000000000 : ℝ)*(base23) + (100449691/100000000000000 : ℝ)*(upper3) + (493666381/100000000000000 : ℝ)*(upper5) + (1357365521098239/100000000000000 : ℝ)*(major0) + (1357365521098239/100000000000000 : ℝ)*(major1) + (1357365521098239/100000000000000 : ℝ)*(major2) + (185352209113923/10000000000000 : ℝ)*(sp0) + (370704589595817/20000000000000 : ℝ)*(sp1) + (926761770651099/50000000000000 : ℝ)*(sp2) + (34448158793743/4000000000000 : ℝ)*(sp3) + (535719709/20000000000000 : ℝ)*(sp4) + (2086830713/100000000000000 : ℝ)*(sp7) + (215301548549207/25000000000000 : ℝ)*(f.failure) + (370704926443047/20000000000000 : ℝ)*(f.sum) + (22590939615949/6101750000000000000000000000 : ℝ)*base65 + (5736092697051680863/24407000000000000000000000000000000 : ℝ)*base67 + (94864048200974319137/24407000000000000000000000000000000 : ℝ)*base70 + (51165550551924680863/24407000000000000000000000000000000 : ℝ)*base71 + (6607612098859/12203500000000000000000000000 : ℝ)*base73 + (167721554504805680863/24407000000000000000000000000000000 : ℝ)*base75 + (102689497202262680863/24407000000000000000000000000000000 : ℝ)*base77 + (61270064222317319137/24407000000000000000000000000000000 : ℝ)*base80 + (8131265541601/4881400000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (15877813/2500000000000000000000 : ℝ)*base90 + (15877813/2500000000000000000000 : ℝ)*base92 + (15877813/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18135418579487021077230413241/6101750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10519149/50000000000000 : ℝ)*(base1) + (161656161/25000000000000 : ℝ)*(base19) + (39697733/6250000000000 : ℝ)*(base23) + (7465977/10000000000000 : ℝ)*(upper3) + (30961983/50000000000000 : ℝ)*(upper5) + (1390609177913091/100000000000000 : ℝ)*(major0) + (1390609177913091/100000000000000 : ℝ)*(major1) + (1390609177913091/100000000000000 : ℝ)*(major2) + (3735566889/100000000000000 : ℝ)*(sp1) + (1781964039/50000000000000 : ℝ)*(sp2) + (379784003517673/20000000000000 : ℝ)*(sp4) + (949457807179267/50000000000000 : ℝ)*(sp5) + (949457898729131/50000000000000 : ℝ)*(sp6) + (176459647833117/20000000000000 : ℝ)*(sp7) + (882298260203883/100000000000000 : ℝ)*(f.failure) + (474729999137517/25000000000000 : ℝ)*(f.sum) + (18554861311921/12203500000000000000000000000 : ℝ)*base66 + (13104542162696612253/24407000000000000000000000000000000 : ℝ)*base68 + (187574778121911612253/24407000000000000000000000000000000 : ℝ)*base70 + (59119099021699612253/24407000000000000000000000000000000 : ℝ)*base72 + (892977632423/244070000000000000000000000 : ℝ)*base74 + (58719767970106387747/24407000000000000000000000000000000 : ℝ)*base75 + (290032794064811612253/24407000000000000000000000000000000 : ℝ)*base78 + (2591753444907612253/24407000000000000000000000000000000 : ℝ)*base80 + (5179290429823/3050875000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (3856497/10000000000000000000000 : ℝ)*base90 + (3856497/10000000000000000000000 : ℝ)*base92 + (3856497/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1415_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157612141/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5271/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (487/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1507/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (947/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1415_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1415_s2_0 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-395060389/2000000000 : ℝ)*x 0 + (5461357383/10000000000 : ℝ)*x 1 + (5198911281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (395060389/2000000000 : ℝ)^4375 ≤ (1504190661773/12500000000000 : ℝ)^3351 := by
    have hnat : (395060389 : ℕ)^4375*12500000000000^3351 ≤ 1504190661773^3351*2000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      395060389 2000000000 1504190661773 12500000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5461357383/10000000000 : ℝ)^4375 ≤ (11349188539673/25000000000000 : ℝ)^3351 := by
    have hnat : (5461357383 : ℕ)^4375*25000000000000^3351 ≤ 11349188539673^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5461357383 10000000000 11349188539673 25000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5198911281/10000000000 : ℝ)^4375 ≤ (1064243013211/2500000000000 : ℝ)^3351 := by
    have hnat : (5198911281 : ℕ)^4375*2500000000000^3351 ≤ 1064243013211^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5198911281 10000000000 1064243013211 2500000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-395060389/2000000000 : ℝ), (5461357383/10000000000 : ℝ), (5198911281/10000000000 : ℝ)] ![(1504190661773/12500000000000 : ℝ), (11349188539673/25000000000000 : ℝ), (1064243013211/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-395060389/2000000000 : ℝ)|^4375 ≤ (1504190661773/12500000000000 : ℝ)^3351
        have hw : |(-395060389/2000000000 : ℝ)|=(395060389/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5461357383/10000000000 : ℝ)|^4375 ≤ (11349188539673/25000000000000 : ℝ)^3351
        have hw : |(5461357383/10000000000 : ℝ)|=(5461357383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5198911281/10000000000 : ℝ)|^4375 ≤ (1064243013211/2500000000000 : ℝ)^3351
        have hw : |(5198911281/10000000000 : ℝ)|=(5198911281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1415_s2_1 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5361034229/10000000000 : ℝ)*x 0 + (-2110414029/10000000000 : ℝ)*x 1 + (5198911237/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5361034229/10000000000 : ℝ)^4375 ≤ (44311070940213/100000000000000 : ℝ)^3351 := by
    have hnat : (5361034229 : ℕ)^4375*100000000000000^3351 ≤ 44311070940213^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5361034229 10000000000 44311070940213 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2110414029/10000000000 : ℝ)^4375 ≤ (13119208976461/100000000000000 : ℝ)^3351 := by
    have hnat : (2110414029 : ℕ)^4375*100000000000000^3351 ≤ 13119208976461^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110414029 10000000000 13119208976461 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5198911237/10000000000 : ℝ)^4375 ≤ (2660607503629/6250000000000 : ℝ)^3351 := by
    have hnat : (5198911237 : ℕ)^4375*6250000000000^3351 ≤ 2660607503629^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5198911237 10000000000 2660607503629 6250000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5361034229/10000000000 : ℝ), (-2110414029/10000000000 : ℝ), (5198911237/10000000000 : ℝ)] ![(44311070940213/100000000000000 : ℝ), (13119208976461/100000000000000 : ℝ), (2660607503629/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5361034229/10000000000 : ℝ)|^4375 ≤ (44311070940213/100000000000000 : ℝ)^3351
        have hw : |(5361034229/10000000000 : ℝ)|=(5361034229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2110414029/10000000000 : ℝ)|^4375 ≤ (13119208976461/100000000000000 : ℝ)^3351
        have hw : |(-2110414029/10000000000 : ℝ)|=(2110414029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5198911237/10000000000 : ℝ)|^4375 ≤ (2660607503629/6250000000000 : ℝ)^3351
        have hw : |(5198911237/10000000000 : ℝ)|=(5198911237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1415_s2_2 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5361033937/10000000000 : ℝ)*x 0 + (5198911567/10000000000 : ℝ)*x 1 + (-65950437/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5361033937/10000000000 : ℝ)^4375 ≤ (110777669473/250000000000 : ℝ)^3351 := by
    have hnat : (5361033937 : ℕ)^4375*250000000000^3351 ≤ 110777669473^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5361033937 10000000000 110777669473 250000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5198911567/10000000000 : ℝ)^4375 ≤ (42569723585881/100000000000000 : ℝ)^3351 := by
    have hnat : (5198911567 : ℕ)^4375*100000000000000^3351 ≤ 42569723585881^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5198911567 10000000000 42569723585881 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65950437/312500000 : ℝ)^4375 ≤ (327980215281/2500000000000 : ℝ)^3351 := by
    have hnat : (65950437 : ℕ)^4375*2500000000000^3351 ≤ 327980215281^3351*312500000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65950437 312500000 327980215281 2500000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5361033937/10000000000 : ℝ), (5198911567/10000000000 : ℝ), (-65950437/312500000 : ℝ)] ![(110777669473/250000000000 : ℝ), (42569723585881/100000000000000 : ℝ), (327980215281/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5361033937/10000000000 : ℝ)|^4375 ≤ (110777669473/250000000000 : ℝ)^3351
        have hw : |(5361033937/10000000000 : ℝ)|=(5361033937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5198911567/10000000000 : ℝ)|^4375 ≤ (42569723585881/100000000000000 : ℝ)^3351
        have hw : |(5198911567/10000000000 : ℝ)|=(5198911567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-65950437/312500000 : ℝ)|^4375 ≤ (327980215281/2500000000000 : ℝ)^3351
        have hw : |(-65950437/312500000 : ℝ)|=(65950437/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1415_s2_3 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2151639953/5000000000 : ℝ)*x 0 + (2014612773/5000000000 : ℝ)*x 1 + (4594073177/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2151639953/5000000000 : ℝ)^4375 ≤ (16628992030757/50000000000000 : ℝ)^3351 := by
    have hnat : (2151639953 : ℕ)^4375*50000000000000^3351 ≤ 16628992030757^3351*5000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151639953 5000000000 16628992030757 50000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2014612773/5000000000 : ℝ)^4375 ≤ (30520034593981/100000000000000 : ℝ)^3351 := by
    have hnat : (2014612773 : ℕ)^4375*100000000000000^3351 ≤ 30520034593981^3351*5000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2014612773 5000000000 30520034593981 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4594073177/10000000000 : ℝ)^4375 ≤ (7244396265681/20000000000000 : ℝ)^3351 := by
    have hnat : (4594073177 : ℕ)^4375*20000000000000^3351 ≤ 7244396265681^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4594073177 10000000000 7244396265681 20000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2151639953/5000000000 : ℝ), (2014612773/5000000000 : ℝ), (4594073177/10000000000 : ℝ)] ![(16628992030757/50000000000000 : ℝ), (30520034593981/100000000000000 : ℝ), (7244396265681/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2151639953/5000000000 : ℝ)|^4375 ≤ (16628992030757/50000000000000 : ℝ)^3351
        have hw : |(2151639953/5000000000 : ℝ)|=(2151639953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2014612773/5000000000 : ℝ)|^4375 ≤ (30520034593981/100000000000000 : ℝ)^3351
        have hw : |(2014612773/5000000000 : ℝ)|=(2014612773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4594073177/10000000000 : ℝ)|^4375 ≤ (7244396265681/20000000000000 : ℝ)^3351
        have hw : |(4594073177/10000000000 : ℝ)|=(4594073177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1415_s2_4 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-493837567/2500000000 : ℝ)*x 0 + (5200433967/10000000000 : ℝ)*x 1 + (1364955473/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (493837567/2500000000 : ℝ)^4375 ≤ (2406781927357/20000000000000 : ℝ)^3351 := by
    have hnat : (493837567 : ℕ)^4375*20000000000000^3351 ≤ 2406781927357^3351*2500000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      493837567 2500000000 2406781927357 20000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5200433967/10000000000 : ℝ)^4375 ≤ (42585999306791/100000000000000 : ℝ)^3351 := by
    have hnat : (5200433967 : ℕ)^4375*100000000000000^3351 ≤ 42585999306791^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5200433967 10000000000 42585999306791 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1364955473/2500000000 : ℝ)^4375 ≤ (45380091033703/100000000000000 : ℝ)^3351 := by
    have hnat : (1364955473 : ℕ)^4375*100000000000000^3351 ≤ 45380091033703^3351*2500000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1364955473 2500000000 45380091033703 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-493837567/2500000000 : ℝ), (5200433967/10000000000 : ℝ), (1364955473/2500000000 : ℝ)] ![(2406781927357/20000000000000 : ℝ), (42585999306791/100000000000000 : ℝ), (45380091033703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-493837567/2500000000 : ℝ)|^4375 ≤ (2406781927357/20000000000000 : ℝ)^3351
        have hw : |(-493837567/2500000000 : ℝ)|=(493837567/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5200433967/10000000000 : ℝ)|^4375 ≤ (42585999306791/100000000000000 : ℝ)^3351
        have hw : |(5200433967/10000000000 : ℝ)|=(5200433967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1364955473/2500000000 : ℝ)|^4375 ≤ (45380091033703/100000000000000 : ℝ)^3351
        have hw : |(1364955473/2500000000 : ℝ)|=(1364955473/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1415_s2_5 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5292880577/10000000000 : ℝ)*x 0 + (-73980131/400000000 : ℝ)*x 1 + (5459822137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5292880577/10000000000 : ℝ)^4375 ≤ (8715409631881/20000000000000 : ℝ)^3351 := by
    have hnat : (5292880577 : ℕ)^4375*20000000000000^3351 ≤ 8715409631881^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5292880577 10000000000 8715409631881 20000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (73980131/400000000 : ℝ)^4375 ≤ (2208571627269/20000000000000 : ℝ)^3351 := by
    have hnat : (73980131 : ℕ)^4375*20000000000000^3351 ≤ 2208571627269^3351*400000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      73980131 400000000 2208571627269 20000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5459822137/10000000000 : ℝ)^4375 ≤ (1815203747693/4000000000000 : ℝ)^3351 := by
    have hnat : (5459822137 : ℕ)^4375*4000000000000^3351 ≤ 1815203747693^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5459822137 10000000000 1815203747693 4000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5292880577/10000000000 : ℝ), (-73980131/400000000 : ℝ), (5459822137/10000000000 : ℝ)] ![(8715409631881/20000000000000 : ℝ), (2208571627269/20000000000000 : ℝ), (1815203747693/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5292880577/10000000000 : ℝ)|^4375 ≤ (8715409631881/20000000000000 : ℝ)^3351
        have hw : |(5292880577/10000000000 : ℝ)|=(5292880577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-73980131/400000000 : ℝ)|^4375 ≤ (2208571627269/20000000000000 : ℝ)^3351
        have hw : |(-73980131/400000000 : ℝ)|=(73980131/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5459822137/10000000000 : ℝ)|^4375 ≤ (1815203747693/4000000000000 : ℝ)^3351
        have hw : |(5459822137/10000000000 : ℝ)|=(5459822137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1415_s2_6 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2646440271/5000000000 : ℝ)*x 0 + (682477767/1250000000 : ℝ)*x 1 + (-462375831/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646440271/5000000000 : ℝ)^4375 ≤ (43577047783189/100000000000000 : ℝ)^3351 := by
    have hnat : (2646440271 : ℕ)^4375*100000000000000^3351 ≤ 43577047783189^3351*5000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646440271 5000000000 43577047783189 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (682477767/1250000000 : ℝ)^4375 ≤ (22690046840737/50000000000000 : ℝ)^3351 := by
    have hnat : (682477767 : ℕ)^4375*50000000000000^3351 ≤ 22690046840737^3351*1250000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      682477767 1250000000 22690046840737 50000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (462375831/2500000000 : ℝ)^4375 ≤ (1380357314789/12500000000000 : ℝ)^3351 := by
    have hnat : (462375831 : ℕ)^4375*12500000000000^3351 ≤ 1380357314789^3351*2500000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      462375831 2500000000 1380357314789 12500000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646440271/5000000000 : ℝ), (682477767/1250000000 : ℝ), (-462375831/2500000000 : ℝ)] ![(43577047783189/100000000000000 : ℝ), (22690046840737/50000000000000 : ℝ), (1380357314789/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646440271/5000000000 : ℝ)|^4375 ≤ (43577047783189/100000000000000 : ℝ)^3351
        have hw : |(2646440271/5000000000 : ℝ)|=(2646440271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(682477767/1250000000 : ℝ)|^4375 ≤ (22690046840737/50000000000000 : ℝ)^3351
        have hw : |(682477767/1250000000 : ℝ)|=(682477767/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-462375831/2500000000 : ℝ)|^4375 ≤ (1380357314789/12500000000000 : ℝ)^3351
        have hw : |(-462375831/2500000000 : ℝ)|=(462375831/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1415_s2_7 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (215169183/500000000 : ℝ)*x 0 + (918159217/2000000000 : ℝ)*x 1 + (2016265019/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215169183/500000000 : ℝ)^4375 ≤ (519672358819/1562500000000 : ℝ)^3351 := by
    have hnat : (215169183 : ℕ)^4375*1562500000000^3351 ≤ 519672358819^3351*500000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215169183 500000000 519672358819 1562500000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (918159217/2000000000 : ℝ)^4375 ≤ (9047062776341/25000000000000 : ℝ)^3351 := by
    have hnat : (918159217 : ℕ)^4375*25000000000000^3351 ≤ 9047062776341^3351*2000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      918159217 2000000000 9047062776341 25000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2016265019/5000000000 : ℝ)^4375 ≤ (763817947883/2500000000000 : ℝ)^3351 := by
    have hnat : (2016265019 : ℕ)^4375*2500000000000^3351 ≤ 763817947883^3351*5000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2016265019 5000000000 763817947883 2500000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(215169183/500000000 : ℝ), (918159217/2000000000 : ℝ), (2016265019/5000000000 : ℝ)] ![(519672358819/1562500000000 : ℝ), (9047062776341/25000000000000 : ℝ), (763817947883/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(215169183/500000000 : ℝ)|^4375 ≤ (519672358819/1562500000000 : ℝ)^3351
        have hw : |(215169183/500000000 : ℝ)|=(215169183/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(918159217/2000000000 : ℝ)|^4375 ≤ (9047062776341/25000000000000 : ℝ)^3351
        have hw : |(918159217/2000000000 : ℝ)|=(918159217/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2016265019/5000000000 : ℝ)|^4375 ≤ (763817947883/2500000000000 : ℝ)^3351
        have hw : |(2016265019/5000000000 : ℝ)|=(2016265019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1415_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157612141/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (947/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1507/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (10291/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15843/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (947/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1507/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (947/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1507/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (947/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1507/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (947/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1507/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (947/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1507/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (947/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1507/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1507/20000 : ℝ) ^ (2187/512 : ℝ) ≤ (399409770962503/25000000000000000000 : ℝ) := by
    have hpowers : (1507/20000 : ℝ)^2187 ≤ (399409770962503/25000000000000000000 : ℝ)^512 := by
      have hnat : (1507 : ℕ)^2187*25000000000000000000^512 ≤ 399409770962503^512*20000^2187 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1507 20000 399409770962503 25000000000000000000 2187 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1507/20000 : ℝ)) (X := (399409770962503/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2187 512 (by norm_num) hpowers
    exact h
  have hpowhi : (947/5000 : ℝ) ^ (2187/512 : ℝ) ≤ (81910552009558207/100000000000000000000 : ℝ) := by
    have hpowers : (947/5000 : ℝ)^2187 ≤ (81910552009558207/100000000000000000000 : ℝ)^512 := by
      have hnat : (947 : ℕ)^2187*100000000000000000000^512 ≤ 81910552009558207^512*5000^2187 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        947 5000 81910552009558207 100000000000000000000 2187 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (947/5000 : ℝ)) (X := (81910552009558207/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2187 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500399409770962503/12500000000000000000 : ℝ) ≤ (5000037401975403/5000000000000000 : ℝ) ^ (2187/512 : ℝ) := by
    have hpowers : (12500399409770962503/12500000000000000000 : ℝ)^512 ≤ (5000037401975403/5000000000000000 : ℝ)^2187 := by
      have hnat : (12500399409770962503 : ℕ)^512*5000000000000000^2187 ≤ 5000037401975403^2187*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500399409770962503 12500000000000000000 5000037401975403 5000000000000000 512 2187 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000037401975403/5000000000000000 : ℝ)) (X := (12500399409770962503/12500000000000000000 : ℝ)) (by norm_num) 2187 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100083508191093408219/100000000000000000000 : ℝ) ≤ (10001954390834317/10000000000000000 : ℝ) ^ (2187/512 : ℝ) := by
    have hpowers : (100083508191093408219/100000000000000000000 : ℝ)^512 ≤ (10001954390834317/10000000000000000 : ℝ)^2187 := by
      have hnat : (100083508191093408219 : ℕ)^512*10000000000000000^2187 ≤ 10001954390834317^2187*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100083508191093408219 100000000000000000000 10001954390834317 10000000000000000 512 2187 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001954390834317/10000000000000000 : ℝ)) (X := (100083508191093408219/100000000000000000000 : ℝ)) (by norm_num) 2187 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50081910552009558207/50000000000000000000 : ℝ) ≤ (2500958494429457/2500000000000000 : ℝ) ^ (2187/512 : ℝ) := by
    have hpowers : (50081910552009558207/50000000000000000000 : ℝ)^512 ≤ (2500958494429457/2500000000000000 : ℝ)^2187 := by
      have hnat : (50081910552009558207 : ℕ)^512*2500000000000000^2187 ≤ 2500958494429457^2187*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50081910552009558207 50000000000000000000 2500958494429457 2500000000000000 512 2187 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500958494429457/2500000000000000 : ℝ)) (X := (50081910552009558207/50000000000000000000 : ℝ)) (by norm_num) 2187 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(399409770962503/25000000000000000000 : ℝ) ≤ ((5701126388236221583/5702500000000000000 : ℝ)+2*(1879586883511/1140500000000000 : ℝ)*(1507/20000 : ℝ))^(2187/512 : ℝ) := by
    rw [show (5701126388236221583/5702500000000000000 : ℝ)+2*(1879586883511/1140500000000000 : ℝ)*(1507/20000 : ℝ)=(5000037401975403/5000000000000000 : ℝ) by norm_num, show 1+2*(399409770962503/25000000000000000000 : ℝ)=(12500399409770962503/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(81910552009558207/100000000000000000000 : ℝ)+(399409770962503/25000000000000000000 : ℝ) ≤ ((5701126388236221583/5702500000000000000 : ℝ)+(1879586883511/1140500000000000 : ℝ)*((947/5000 : ℝ)+(1507/20000 : ℝ)))^(2187/512 : ℝ) := by
    rw [show (5701126388236221583/5702500000000000000 : ℝ)+(1879586883511/1140500000000000 : ℝ)*((947/5000 : ℝ)+(1507/20000 : ℝ))=(10001954390834317/10000000000000000 : ℝ) by norm_num, show 1+(81910552009558207/100000000000000000000 : ℝ)+(399409770962503/25000000000000000000 : ℝ)=(100083508191093408219/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(81910552009558207/100000000000000000000 : ℝ) ≤ ((5701126388236221583/5702500000000000000 : ℝ)+2*(1879586883511/1140500000000000 : ℝ)*(947/5000 : ℝ))^(2187/512 : ℝ) := by
    rw [show (5701126388236221583/5702500000000000000 : ℝ)+2*(1879586883511/1140500000000000 : ℝ)*(947/5000 : ℝ)=(2500958494429457/2500000000000000 : ℝ) by norm_num, show 1+2*(81910552009558207/100000000000000000000 : ℝ)=(50081910552009558207/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5701126388236221583/5702500000000000000 : ℝ)*(X 1 0+X 2 0)+(1879586883511/1140500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2187/512 : ℝ)) (lo := (1507/20000 : ℝ)) (hi := (947/5000 : ℝ)) (c := (5701126388236221583/5702500000000000000 : ℝ)) (alpha := (1879586883511/1140500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5701126388236221583/5702500000000000000 : ℝ)*(X 0 1+X 2 1)+(1879586883511/1140500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2187/512 : ℝ)) (lo := (1507/20000 : ℝ)) (hi := (947/5000 : ℝ)) (c := (5701126388236221583/5702500000000000000 : ℝ)) (alpha := (1879586883511/1140500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5701126388236221583/5702500000000000000 : ℝ)*(X 0 2+X 1 2)+(1879586883511/1140500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2187/512 : ℝ)) (lo := (1507/20000 : ℝ)) (hi := (947/5000 : ℝ)) (c := (5701126388236221583/5702500000000000000 : ℝ)) (alpha := (1879586883511/1140500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-395060389/2000000000 : ℝ)*X 0 0+(5461357383/10000000000 : ℝ)*X 0 1+(5198911281/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5361034229/10000000000 : ℝ)*X 1 0+(-2110414029/10000000000 : ℝ)*X 1 1+(5198911237/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5361033937/10000000000 : ℝ)*X 2 0+(5198911567/10000000000 : ℝ)*X 2 1+(-65950437/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2151639953/5000000000 : ℝ)*X 0 0+(2014612773/5000000000 : ℝ)*X 0 1+(4594073177/10000000000 : ℝ)*X 0 2+(2151639953/5000000000 : ℝ)*X 1 0+(2014612773/5000000000 : ℝ)*X 1 1+(4594073177/10000000000 : ℝ)*X 1 2+(2151639953/5000000000 : ℝ)*X 2 0+(2014612773/5000000000 : ℝ)*X 2 1+(4594073177/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-493837567/2500000000 : ℝ)*X 0 0+(5200433967/10000000000 : ℝ)*X 0 1+(1364955473/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5292880577/10000000000 : ℝ)*X 1 0+(-73980131/400000000 : ℝ)*X 1 1+(5459822137/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2646440271/5000000000 : ℝ)*X 2 0+(682477767/1250000000 : ℝ)*X 2 1+(-462375831/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((215169183/500000000 : ℝ)*X 0 0+(918159217/2000000000 : ℝ)*X 0 1+(2016265019/5000000000 : ℝ)*X 0 2+(215169183/500000000 : ℝ)*X 1 0+(918159217/2000000000 : ℝ)*X 1 1+(2016265019/5000000000 : ℝ)*X 1 2+(215169183/500000000 : ℝ)*X 2 0+(918159217/2000000000 : ℝ)*X 2 1+(2016265019/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (336763056035679151014003/28512500000000000000000000000 : ℝ) := by norm_num
    linear_combination (948916807/50000000000000 : ℝ)*(base19) + (1436016893/100000000000000 : ℝ)*(base23) + (34079817/25000000000000 : ℝ)*(lower2) + (169046991/50000000000000 : ℝ)*(upper3) + (8329791/6250000000000 : ℝ)*(upper5) + (87199429871849/3125000000000 : ℝ)*(major0) + (87199429871849/3125000000000 : ℝ)*(major1) + (87199429871849/3125000000000 : ℝ)*(major2) + (59536427869821/1562500000000 : ℝ)*(sp0) + (1905175403795269/50000000000000 : ℝ)*(sp1) + (190517563470363/5000000000000 : ℝ)*(sp2) + (885199253016049/50000000000000 : ℝ)*(sp3) + (2665219451/12500000000000 : ℝ)*(sp4) + (5953319917/50000000000000 : ℝ)*(sp7) + (442602603167983/25000000000000 : ℝ)*(f.failure) + (476294088178019/12500000000000 : ℝ)*(f.sum) + (64605671333937/14256250000000000000000000000 : ℝ)*base65 + (1203535441937419/556884765625000000000000000000 : ℝ)*base68 + (12394128642297199/2227539062500000000000000000000 : ℝ)*base69 + (24467666148203449/2227539062500000000000000000000 : ℝ)*base71 + (8723540187013/14256250000000000000000000000 : ℝ)*base74 + (184269423658388033/17820312500000000000000000000000 : ℝ)*base76 + (133376340353924467/17820312500000000000000000000000 : ℝ)*base77 + (9745680352608079/8910156250000000000000000000000 : ℝ)*base80 + (131585550201449/28512500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (16718397/2500000000000000000000 : ℝ)*base90 + (16718397/2500000000000000000000 : ℝ)*base92 + (16718397/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (121668268995942397218111/28512500000000000000000000000 : ℝ) := by norm_num
    linear_combination (283844759/100000000000000 : ℝ)*(base19) + (175911287/50000000000000 : ℝ)*(base23) + (110966979/100000000000000 : ℝ)*(upper3) + (21372711/50000000000000 : ℝ)*(lower4) + (73250139/100000000000000 : ℝ)*(upper5) + (2823244414389809/100000000000000 : ℝ)*(major0) + (2823244414389809/100000000000000 : ℝ)*(major1) + (2823244414389809/100000000000000 : ℝ)*(major2) + (4306323539/100000000000000 : ℝ)*(sp1) + (5293483549/100000000000000 : ℝ)*(sp2) + (240951746215277/6250000000000 : ℝ)*(sp4) + (1927611674638067/50000000000000 : ℝ)*(sp5) + (385522229413831/10000000000000 : ℝ)*(sp6) + (895630373547749/50000000000000 : ℝ)*(sp7) + (895630373547749/50000000000000 : ℝ)*(f.failure) + (240951746215277/6250000000000 : ℝ)*(f.sum) + (198695662361201/57025000000000000000000000000 : ℝ)*base66 + (4513701434409542647/570250000000000000000000000000000 : ℝ)*base67 + (5127131647968957353/570250000000000000000000000000000 : ℝ)*base70 + (782509291720792647/570250000000000000000000000000000 : ℝ)*base71 + (1067407350087/28512500000000000000000000000 : ℝ)*base73 + (2990165824648207353/570250000000000000000000000000000 : ℝ)*base76 + (591964673330207353/570250000000000000000000000000000 : ℝ)*base78 + (338262676054792647/570250000000000000000000000000000 : ℝ)*base79 + (139664657668301/57025000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (35620609/5000000000000000000000 : ℝ)*base89 + (35620609/5000000000000000000000 : ℝ)*base91 + (35620609/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1415_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157612141/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (947/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1507/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10291/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15843/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1415_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1415_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157612141/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10291/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15843/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1415_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1415_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1415_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157612141/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10291/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15843/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1415_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
