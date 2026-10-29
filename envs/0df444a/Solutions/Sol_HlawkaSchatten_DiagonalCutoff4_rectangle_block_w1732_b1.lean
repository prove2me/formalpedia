-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1732_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:06:55.400105+00:00
-- url     : https://prove2.me/submissions/7648fce7-c7da-4d09-9d82-b3907947da3d

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
theorem support_rectangle_w1732_s3_0 (p : ℝ) (hpa : (5471/1024 : ℝ) ≤ p) (hpb : p ≤ (5487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1330473971/10000000000 : ℝ)*x 0 + (5522586007/10000000000 : ℝ)*x 1 + (158581391/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1330473971/10000000000 : ℝ)^5487 ≤ (4187806337977/50000000000000 : ℝ)^4463 := by
    have hnat : (1330473971 : ℕ)^5487*50000000000000^4463 ≤ 4187806337977^4463*10000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1330473971 10000000000 4187806337977 50000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5522586007/10000000000 : ℝ)^5487 ≤ (48192463207399/100000000000000 : ℝ)^4463 := by
    have hnat : (5522586007 : ℕ)^5487*100000000000000^4463 ≤ 48192463207399^4463*10000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5522586007 10000000000 48192463207399 100000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (158581391/312500000 : ℝ)^5487 ≤ (2171596205407/5000000000000 : ℝ)^4463 := by
    have hnat : (158581391 : ℕ)^5487*5000000000000^4463 ≤ 2171596205407^4463*312500000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      158581391 312500000 2171596205407 5000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5487/1024 : ℝ)) 5487 4463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1330473971/10000000000 : ℝ), (5522586007/10000000000 : ℝ), (158581391/312500000 : ℝ)] ![(4187806337977/50000000000000 : ℝ), (48192463207399/100000000000000 : ℝ), (2171596205407/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1330473971/10000000000 : ℝ)|^5487 ≤ (4187806337977/50000000000000 : ℝ)^4463
        have hw : |(-1330473971/10000000000 : ℝ)|=(1330473971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5522586007/10000000000 : ℝ)|^5487 ≤ (48192463207399/100000000000000 : ℝ)^4463
        have hw : |(5522586007/10000000000 : ℝ)|=(5522586007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(158581391/312500000 : ℝ)|^5487 ≤ (2171596205407/5000000000000 : ℝ)^4463
        have hw : |(158581391/312500000 : ℝ)|=(158581391/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1732_s3_1 (p : ℝ) (hpa : (5471/1024 : ℝ) ≤ p) (hpb : p ≤ (5487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674512353/5000000000 : ℝ)*x 0 + (-1565623431/10000000000 : ℝ)*x 1 + (2537302299/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674512353/5000000000 : ℝ)^5487 ≤ (1853486193031/4000000000000 : ℝ)^4463 := by
    have hnat : (2674512353 : ℕ)^5487*4000000000000^4463 ≤ 1853486193031^4463*5000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674512353 5000000000 1853486193031 4000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1565623431/10000000000 : ℝ)^5487 ≤ (5115460070793/50000000000000 : ℝ)^4463 := by
    have hnat : (1565623431 : ℕ)^5487*50000000000000^4463 ≤ 5115460070793^4463*10000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1565623431 10000000000 5115460070793 50000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2537302299/5000000000 : ℝ)^5487 ≤ (43431925013067/100000000000000 : ℝ)^4463 := by
    have hnat : (2537302299 : ℕ)^5487*100000000000000^4463 ≤ 43431925013067^4463*5000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2537302299 5000000000 43431925013067 100000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5487/1024 : ℝ)) 5487 4463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674512353/5000000000 : ℝ), (-1565623431/10000000000 : ℝ), (2537302299/5000000000 : ℝ)] ![(1853486193031/4000000000000 : ℝ), (5115460070793/50000000000000 : ℝ), (43431925013067/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674512353/5000000000 : ℝ)|^5487 ≤ (1853486193031/4000000000000 : ℝ)^4463
        have hw : |(2674512353/5000000000 : ℝ)|=(2674512353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1565623431/10000000000 : ℝ)|^5487 ≤ (5115460070793/50000000000000 : ℝ)^4463
        have hw : |(-1565623431/10000000000 : ℝ)|=(1565623431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2537302299/5000000000 : ℝ)|^5487 ≤ (43431925013067/100000000000000 : ℝ)^4463
        have hw : |(2537302299/5000000000 : ℝ)|=(2537302299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1732_s3_2 (p : ℝ) (hpa : (5471/1024 : ℝ) ≤ p) (hpb : p ≤ (5487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337256241/2500000000 : ℝ)*x 0 + (5074604313/10000000000 : ℝ)*x 1 + (-782811731/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337256241/2500000000 : ℝ)^5487 ≤ (46337157573559/100000000000000 : ℝ)^4463 := by
    have hnat : (1337256241 : ℕ)^5487*100000000000000^4463 ≤ 46337157573559^4463*2500000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337256241 2500000000 46337157573559 100000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5074604313/10000000000 : ℝ)^5487 ≤ (21715961007091/50000000000000 : ℝ)^4463 := by
    have hnat : (5074604313 : ℕ)^5487*50000000000000^4463 ≤ 21715961007091^4463*10000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5074604313 10000000000 21715961007091 50000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (782811731/5000000000 : ℝ)^5487 ≤ (5115460195321/50000000000000 : ℝ)^4463 := by
    have hnat : (782811731 : ℕ)^5487*50000000000000^4463 ≤ 5115460195321^4463*5000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      782811731 5000000000 5115460195321 50000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5487/1024 : ℝ)) 5487 4463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337256241/2500000000 : ℝ), (5074604313/10000000000 : ℝ), (-782811731/5000000000 : ℝ)] ![(46337157573559/100000000000000 : ℝ), (21715961007091/50000000000000 : ℝ), (5115460195321/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337256241/2500000000 : ℝ)|^5487 ≤ (46337157573559/100000000000000 : ℝ)^4463
        have hw : |(1337256241/2500000000 : ℝ)|=(1337256241/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5074604313/10000000000 : ℝ)|^5487 ≤ (21715961007091/50000000000000 : ℝ)^4463
        have hw : |(5074604313/10000000000 : ℝ)|=(5074604313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-782811731/5000000000 : ℝ)|^5487 ≤ (5115460195321/50000000000000 : ℝ)^4463
        have hw : |(-782811731/5000000000 : ℝ)|=(782811731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1732_s3_3 (p : ℝ) (hpa : (5471/1024 : ℝ) ≤ p) (hpb : p ≤ (5487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2030237649/5000000000 : ℝ)*x 0 + (68247419/200000000 : ℝ)*x 1 + (2388270417/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2030237649/5000000000 : ℝ)^5487 ≤ (4127413207947/12500000000000 : ℝ)^4463 := by
    have hnat : (2030237649 : ℕ)^5487*12500000000000^4463 ≤ 4127413207947^4463*5000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2030237649 5000000000 4127413207947 12500000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (68247419/200000000 : ℝ)^5487 ≤ (6665913851349/25000000000000 : ℝ)^4463 := by
    have hnat : (68247419 : ℕ)^5487*25000000000000^4463 ≤ 6665913851349^4463*200000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68247419 200000000 6665913851349 25000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2388270417/5000000000 : ℝ)^5487 ≤ (40317038914933/100000000000000 : ℝ)^4463 := by
    have hnat : (2388270417 : ℕ)^5487*100000000000000^4463 ≤ 40317038914933^4463*5000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2388270417 5000000000 40317038914933 100000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5487/1024 : ℝ)) 5487 4463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2030237649/5000000000 : ℝ), (68247419/200000000 : ℝ), (2388270417/5000000000 : ℝ)] ![(4127413207947/12500000000000 : ℝ), (6665913851349/25000000000000 : ℝ), (40317038914933/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2030237649/5000000000 : ℝ)|^5487 ≤ (4127413207947/12500000000000 : ℝ)^4463
        have hw : |(2030237649/5000000000 : ℝ)|=(2030237649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(68247419/200000000 : ℝ)|^5487 ≤ (6665913851349/25000000000000 : ℝ)^4463
        have hw : |(68247419/200000000 : ℝ)|=(68247419/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2388270417/5000000000 : ℝ)|^5487 ≤ (40317038914933/100000000000000 : ℝ)^4463
        have hw : |(2388270417/5000000000 : ℝ)|=(2388270417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1732_s3_4 (p : ℝ) (hpa : (5471/1024 : ℝ) ≤ p) (hpb : p ≤ (5487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-665433189/5000000000 : ℝ)*x 0 + (1270419071/2500000000 : ℝ)*x 1 + (2757682447/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (665433189/5000000000 : ℝ)^5487 ≤ (8378649850249/100000000000000 : ℝ)^4463 := by
    have hnat : (665433189 : ℕ)^5487*100000000000000^4463 ≤ 8378649850249^4463*5000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      665433189 5000000000 8378649850249 100000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1270419071/2500000000 : ℝ)^5487 ≤ (2719146752311/6250000000000 : ℝ)^4463 := by
    have hnat : (1270419071 : ℕ)^5487*6250000000000^4463 ≤ 2719146752311^4463*2500000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1270419071 2500000000 2719146752311 6250000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2757682447/5000000000 : ℝ)^5487 ≤ (24057501052107/50000000000000 : ℝ)^4463 := by
    have hnat : (2757682447 : ℕ)^5487*50000000000000^4463 ≤ 24057501052107^4463*5000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2757682447 5000000000 24057501052107 50000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5487/1024 : ℝ)) 5487 4463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-665433189/5000000000 : ℝ), (1270419071/2500000000 : ℝ), (2757682447/5000000000 : ℝ)] ![(8378649850249/100000000000000 : ℝ), (2719146752311/6250000000000 : ℝ), (24057501052107/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-665433189/5000000000 : ℝ)|^5487 ≤ (8378649850249/100000000000000 : ℝ)^4463
        have hw : |(-665433189/5000000000 : ℝ)|=(665433189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1270419071/2500000000 : ℝ)|^5487 ≤ (2719146752311/6250000000000 : ℝ)^4463
        have hw : |(1270419071/2500000000 : ℝ)|=(1270419071/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2757682447/5000000000 : ℝ)|^5487 ≤ (24057501052107/50000000000000 : ℝ)^4463
        have hw : |(2757682447/5000000000 : ℝ)|=(2757682447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1732_s3_5 (p : ℝ) (hpa : (5471/1024 : ℝ) ≤ p) (hpb : p ≤ (5487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5229863691/10000000000 : ℝ)*x 0 + (-1124863111/10000000000 : ℝ)*x 1 + (172355153/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5229863691/10000000000 : ℝ)^5487 ≤ (5633914188247/12500000000000 : ℝ)^4463 := by
    have hnat : (5229863691 : ℕ)^5487*12500000000000^4463 ≤ 5633914188247^4463*10000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229863691 10000000000 5633914188247 12500000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1124863111/10000000000 : ℝ)^5487 ≤ (1362736871053/20000000000000 : ℝ)^4463 := by
    have hnat : (1124863111 : ℕ)^5487*20000000000000^4463 ≤ 1362736871053^4463*10000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124863111 10000000000 1362736871053 20000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (172355153/312500000 : ℝ)^5487 ≤ (9623000425133/20000000000000 : ℝ)^4463 := by
    have hnat : (172355153 : ℕ)^5487*20000000000000^4463 ≤ 9623000425133^4463*312500000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172355153 312500000 9623000425133 20000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5487/1024 : ℝ)) 5487 4463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5229863691/10000000000 : ℝ), (-1124863111/10000000000 : ℝ), (172355153/312500000 : ℝ)] ![(5633914188247/12500000000000 : ℝ), (1362736871053/20000000000000 : ℝ), (9623000425133/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5229863691/10000000000 : ℝ)|^5487 ≤ (5633914188247/12500000000000 : ℝ)^4463
        have hw : |(5229863691/10000000000 : ℝ)|=(5229863691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1124863111/10000000000 : ℝ)|^5487 ≤ (1362736871053/20000000000000 : ℝ)^4463
        have hw : |(-1124863111/10000000000 : ℝ)|=(1124863111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(172355153/312500000 : ℝ)|^5487 ≤ (9623000425133/20000000000000 : ℝ)^4463
        have hw : |(172355153/312500000 : ℝ)|=(172355153/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1732_s3_6 (p : ℝ) (hpa : (5471/1024 : ℝ) ≤ p) (hpb : p ≤ (5487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5229863689/10000000000 : ℝ)*x 0 + (2757682449/5000000000 : ℝ)*x 1 + (-112486311/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5229863689/10000000000 : ℝ)^5487 ≤ (9014262696957/20000000000000 : ℝ)^4463 := by
    have hnat : (5229863689 : ℕ)^5487*20000000000000^4463 ≤ 9014262696957^4463*10000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229863689 10000000000 9014262696957 20000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2757682449/5000000000 : ℝ)^5487 ≤ (12028750536779/25000000000000 : ℝ)^4463 := by
    have hnat : (2757682449 : ℕ)^5487*25000000000000^4463 ≤ 12028750536779^4463*5000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2757682449 5000000000 12028750536779 25000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (112486311/1000000000 : ℝ)^5487 ≤ (3406842173909/50000000000000 : ℝ)^4463 := by
    have hnat : (112486311 : ℕ)^5487*50000000000000^4463 ≤ 3406842173909^4463*1000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112486311 1000000000 3406842173909 50000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5487/1024 : ℝ)) 5487 4463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5229863689/10000000000 : ℝ), (2757682449/5000000000 : ℝ), (-112486311/1000000000 : ℝ)] ![(9014262696957/20000000000000 : ℝ), (12028750536779/25000000000000 : ℝ), (3406842173909/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5229863689/10000000000 : ℝ)|^5487 ≤ (9014262696957/20000000000000 : ℝ)^4463
        have hw : |(5229863689/10000000000 : ℝ)|=(5229863689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2757682449/5000000000 : ℝ)|^5487 ≤ (12028750536779/25000000000000 : ℝ)^4463
        have hw : |(2757682449/5000000000 : ℝ)|=(2757682449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-112486311/1000000000 : ℝ)|^5487 ≤ (3406842173909/50000000000000 : ℝ)^4463
        have hw : |(-112486311/1000000000 : ℝ)|=(112486311/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1732_s3_7 (p : ℝ) (hpa : (5471/1024 : ℝ) ≤ p) (hpb : p ≤ (5487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (812334161/2000000000 : ℝ)*x 0 + (1188751581/2500000000 : ℝ)*x 1 + (3434360443/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (812334161/2000000000 : ℝ)^5487 ≤ (33031258361069/100000000000000 : ℝ)^4463 := by
    have hnat : (812334161 : ℕ)^5487*100000000000000^4463 ≤ 33031258361069^4463*2000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      812334161 2000000000 33031258361069 100000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1188751581/2500000000 : ℝ)^5487 ≤ (20046842579121/50000000000000 : ℝ)^4463 := by
    have hnat : (1188751581 : ℕ)^5487*50000000000000^4463 ≤ 20046842579121^4463*2500000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1188751581 2500000000 20046842579121 50000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3434360443/10000000000 : ℝ)^5487 ≤ (13437528230949/50000000000000 : ℝ)^4463 := by
    have hnat : (3434360443 : ℕ)^5487*50000000000000^4463 ≤ 13437528230949^4463*10000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3434360443 10000000000 13437528230949 50000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5487/1024 : ℝ)) 5487 4463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(812334161/2000000000 : ℝ), (1188751581/2500000000 : ℝ), (3434360443/10000000000 : ℝ)] ![(33031258361069/100000000000000 : ℝ), (20046842579121/50000000000000 : ℝ), (13437528230949/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(812334161/2000000000 : ℝ)|^5487 ≤ (33031258361069/100000000000000 : ℝ)^4463
        have hw : |(812334161/2000000000 : ℝ)|=(812334161/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1188751581/2500000000 : ℝ)|^5487 ≤ (20046842579121/50000000000000 : ℝ)^4463
        have hw : |(1188751581/2500000000 : ℝ)|=(1188751581/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3434360443/10000000000 : ℝ)|^5487 ≤ (13437528230949/50000000000000 : ℝ)^4463
        have hw : |(3434360443/10000000000 : ℝ)|=(3434360443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1732_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5471/1024 : ℝ) ≤ p) (hpb : p ≤ (5487/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40451477/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (573/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4381/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1753/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18331/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (573/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4381/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (573/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4381/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (573/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4381/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (573/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4381/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (573/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4381/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (573/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4381/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4381/50000 : ℝ) ^ (5471/1024 : ℝ) ≤ (112082737440497/50000000000000000000 : ℝ) := by
    have hpowers : (4381/50000 : ℝ)^5471 ≤ (112082737440497/50000000000000000000 : ℝ)^1024 := by
      have hnat : (4381 : ℕ)^5471*50000000000000000000^1024 ≤ 112082737440497^1024*50000^5471 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4381 50000 112082737440497 50000000000000000000 5471 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4381/50000 : ℝ)) (X := (112082737440497/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5471 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (573/3125 : ℝ) ^ (5471/1024 : ℝ) ≤ (5793931965124889/50000000000000000000 : ℝ) := by
    have hpowers : (573/3125 : ℝ)^5471 ≤ (5793931965124889/50000000000000000000 : ℝ)^1024 := by
      have hnat : (573 : ℕ)^5471*50000000000000000000^1024 ≤ 5793931965124889^1024*3125^5471 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        573 3125 5793931965124889 50000000000000000000 5471 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (573/3125 : ℝ)) (X := (5793931965124889/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5471 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000112082737440497/25000000000000000000 : ℝ) ≤ (10000008391337161/10000000000000000 : ℝ) ^ (5471/1024 : ℝ) := by
    have hpowers : (25000112082737440497/25000000000000000000 : ℝ)^1024 ≤ (10000008391337161/10000000000000000 : ℝ)^5471 := by
      have hnat : (25000112082737440497 : ℕ)^1024*10000000000000000^5471 ≤ 10000008391337161^5471*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000112082737440497 25000000000000000000 10000008391337161 10000000000000000 1024 5471 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000008391337161/10000000000000000 : ℝ)) (X := (25000112082737440497/25000000000000000000 : ℝ)) (by norm_num) 5471 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25002953007351282693/25000000000000000000 : ℝ) ≤ (10000221073615347/10000000000000000 : ℝ) ^ (5471/1024 : ℝ) := by
    have hpowers : (25002953007351282693/25000000000000000000 : ℝ)^1024 ≤ (10000221073615347/10000000000000000 : ℝ)^5471 := by
      have hnat : (25002953007351282693 : ℕ)^1024*10000000000000000^5471 ≤ 10000221073615347^5471*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002953007351282693 25000000000000000000 10000221073615347 10000000000000000 1024 5471 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000221073615347/10000000000000000 : ℝ)) (X := (25002953007351282693/25000000000000000000 : ℝ)) (by norm_num) 5471 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25005793931965124889/25000000000000000000 : ℝ) ≤ (10000433755893533/10000000000000000 : ℝ) ^ (5471/1024 : ℝ) := by
    have hpowers : (25005793931965124889/25000000000000000000 : ℝ)^1024 ≤ (10000433755893533/10000000000000000 : ℝ)^5471 := by
      have hnat : (25005793931965124889 : ℕ)^1024*10000000000000000^5471 ≤ 10000433755893533^5471*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005793931965124889 25000000000000000000 10000433755893533 10000000000000000 1024 5471 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000433755893533/10000000000000000 : ℝ)) (X := (25005793931965124889/25000000000000000000 : ℝ)) (by norm_num) 5471 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(112082737440497/50000000000000000000 : ℝ) ≤ ((1914727065888380959/1914800000000000000 : ℝ)+2*(106341139093/478700000000000 : ℝ)*(4381/50000 : ℝ))^(5471/1024 : ℝ) := by
    rw [show (1914727065888380959/1914800000000000000 : ℝ)+2*(106341139093/478700000000000 : ℝ)*(4381/50000 : ℝ)=(10000008391337161/10000000000000000 : ℝ) by norm_num, show 1+2*(112082737440497/50000000000000000000 : ℝ)=(25000112082737440497/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5793931965124889/50000000000000000000 : ℝ)+(112082737440497/50000000000000000000 : ℝ) ≤ ((1914727065888380959/1914800000000000000 : ℝ)+(106341139093/478700000000000 : ℝ)*((573/3125 : ℝ)+(4381/50000 : ℝ)))^(5471/1024 : ℝ) := by
    rw [show (1914727065888380959/1914800000000000000 : ℝ)+(106341139093/478700000000000 : ℝ)*((573/3125 : ℝ)+(4381/50000 : ℝ))=(10000221073615347/10000000000000000 : ℝ) by norm_num, show 1+(5793931965124889/50000000000000000000 : ℝ)+(112082737440497/50000000000000000000 : ℝ)=(25002953007351282693/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5793931965124889/50000000000000000000 : ℝ) ≤ ((1914727065888380959/1914800000000000000 : ℝ)+2*(106341139093/478700000000000 : ℝ)*(573/3125 : ℝ))^(5471/1024 : ℝ) := by
    rw [show (1914727065888380959/1914800000000000000 : ℝ)+2*(106341139093/478700000000000 : ℝ)*(573/3125 : ℝ)=(10000433755893533/10000000000000000 : ℝ) by norm_num, show 1+2*(5793931965124889/50000000000000000000 : ℝ)=(25005793931965124889/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1914727065888380959/1914800000000000000 : ℝ)*(X 1 0+X 2 0)+(106341139093/478700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5471/1024 : ℝ)) (lo := (4381/50000 : ℝ)) (hi := (573/3125 : ℝ)) (c := (1914727065888380959/1914800000000000000 : ℝ)) (alpha := (106341139093/478700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1914727065888380959/1914800000000000000 : ℝ)*(X 0 1+X 2 1)+(106341139093/478700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5471/1024 : ℝ)) (lo := (4381/50000 : ℝ)) (hi := (573/3125 : ℝ)) (c := (1914727065888380959/1914800000000000000 : ℝ)) (alpha := (106341139093/478700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1914727065888380959/1914800000000000000 : ℝ)*(X 0 2+X 1 2)+(106341139093/478700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5471/1024 : ℝ)) (lo := (4381/50000 : ℝ)) (hi := (573/3125 : ℝ)) (c := (1914727065888380959/1914800000000000000 : ℝ)) (alpha := (106341139093/478700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1330473971/10000000000 : ℝ)*X 0 0+(5522586007/10000000000 : ℝ)*X 0 1+(158581391/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1732_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674512353/5000000000 : ℝ)*X 1 0+(-1565623431/10000000000 : ℝ)*X 1 1+(2537302299/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1732_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337256241/2500000000 : ℝ)*X 2 0+(5074604313/10000000000 : ℝ)*X 2 1+(-782811731/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1732_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2030237649/5000000000 : ℝ)*X 0 0+(68247419/200000000 : ℝ)*X 0 1+(2388270417/5000000000 : ℝ)*X 0 2+(2030237649/5000000000 : ℝ)*X 1 0+(68247419/200000000 : ℝ)*X 1 1+(2388270417/5000000000 : ℝ)*X 1 2+(2030237649/5000000000 : ℝ)*X 2 0+(68247419/200000000 : ℝ)*X 2 1+(2388270417/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1732_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-665433189/5000000000 : ℝ)*X 0 0+(1270419071/2500000000 : ℝ)*X 0 1+(2757682447/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1732_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5229863691/10000000000 : ℝ)*X 1 0+(-1124863111/10000000000 : ℝ)*X 1 1+(172355153/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1732_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5229863689/10000000000 : ℝ)*X 2 0+(2757682449/5000000000 : ℝ)*X 2 1+(-112486311/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1732_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((812334161/2000000000 : ℝ)*X 0 0+(1188751581/2500000000 : ℝ)*X 0 1+(3434360443/10000000000 : ℝ)*X 0 2+(812334161/2000000000 : ℝ)*X 1 0+(1188751581/2500000000 : ℝ)*X 1 1+(3434360443/10000000000 : ℝ)*X 1 2+(812334161/2000000000 : ℝ)*X 2 0+(1188751581/2500000000 : ℝ)*X 2 1+(3434360443/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1732_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (37489865382703393370529/2991875000000000000000000000 : ℝ) := by norm_num
    linear_combination (367932253/20000000000000 : ℝ)*(base19) + (1922302713/100000000000000 : ℝ)*(base23) + (1338723/10000000000000 : ℝ)*(lower2) + (3621181/1250000000000 : ℝ)*(upper3) + (67610069/25000000000000 : ℝ)*(upper5) + (741329943567317/50000000000000 : ℝ)*(major0) + (741329943567317/50000000000000 : ℝ)*(major1) + (741329943567317/50000000000000 : ℝ)*(major2) + (1116124470161613/50000000000000 : ℝ)*(sp0) + (1116130760698841/50000000000000 : ℝ)*(sp1) + (1116130719378117/50000000000000 : ℝ)*(sp2) + (73305109198253/10000000000000 : ℝ)*(sp3) + (14420735721/100000000000000 : ℝ)*(sp4) + (980708499/20000000000000 : ℝ)*(sp7) + (366527997762513/50000000000000 : ℝ)*(f.failure) + (2232263361058947/100000000000000 : ℝ)*(f.sum) + (118107552425977/23935000000000000000000000000 : ℝ)*base65 + (401746072674201003/95740000000000000000000000000000 : ℝ)*base67 + (165939313790898997/95740000000000000000000000000000 : ℝ)*base70 + (19479930995261003/95740000000000000000000000000000 : ℝ)*base71 + (42150856301483/5983750000000000000000000000 : ℝ)*base73 + (147803051027898997/95740000000000000000000000000000 : ℝ)*base76 + (373771552606898997/95740000000000000000000000000000 : ℝ)*base78 + (94420874111161003/95740000000000000000000000000000 : ℝ)*base79 + (31957594476767/23935000000000000000000000000 : ℝ)*base81 + (6081701/1000000000000000000000 : ℝ)*base89 + (6081701/1000000000000000000000 : ℝ)*base91 + (6081701/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (102009512348023694125629/23935000000000000000000000000 : ℝ) := by norm_num
    linear_combination (289897389/50000000000000 : ℝ)*(base19) + (620817999/100000000000000 : ℝ)*(base23) + (41776821/25000000000000 : ℝ)*(lower1) + (23342669/25000000000000 : ℝ)*(upper3) + (1845147/10000000000000 : ℝ)*(lower4) + (89034959/100000000000000 : ℝ)*(upper5) + (1531500931286801/100000000000000 : ℝ)*(major0) + (1531500931286801/100000000000000 : ℝ)*(major1) + (1531500931286801/100000000000000 : ℝ)*(major2) + (145360761/50000000000000 : ℝ)*(sp2) + (144112359949169/6250000000000 : ℝ)*(sp4) + (1152898589695963/50000000000000 : ℝ)*(sp5) + (1152898423823591/50000000000000 : ℝ)*(sp6) + (757203961322253/100000000000000 : ℝ)*(sp7) + (757203961322253/100000000000000 : ℝ)*(f.failure) + (144112359949169/6250000000000 : ℝ)*(f.sum) + (73501013650219/11967500000000000000000000000 : ℝ)*base65 + (974818550841445841/191480000000000000000000000000000 : ℝ)*base68 + (659901265061005841/191480000000000000000000000000000 : ℝ)*base70 + (184511159386514159/191480000000000000000000000000000 : ℝ)*base71 + (49734113850417/23935000000000000000000000000 : ℝ)*base74 + (2584861255134605841/191480000000000000000000000000000 : ℝ)*base76 + (1385264864491314159/191480000000000000000000000000000 : ℝ)*base77 + (160731782267274159/191480000000000000000000000000000 : ℝ)*base79 + (7357792832583/5983750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (13182319/2000000000000000000000 : ℝ)*base90 + (13182319/2000000000000000000000 : ℝ)*base92 + (13182319/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1732_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5471/1024 : ℝ) ≤ p) (hpb : p ≤ (5487/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40451477/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (573/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4381/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1753/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18331/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1732_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1732_s4_0 (p : ℝ) (hpa : (5471/1024 : ℝ) ≤ p) (hpb : p ≤ (5487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-10394347/78125000 : ℝ)*x 0 + (5522579897/10000000000 : ℝ)*x 1 + (5074608943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10394347/78125000 : ℝ)^5487 ≤ (837563159927/10000000000000 : ℝ)^4463 := by
    have hnat : (10394347 : ℕ)^5487*10000000000000^4463 ≤ 837563159927^4463*78125000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10394347 78125000 837563159927 10000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5522579897/10000000000 : ℝ)^5487 ≤ (12048099413853/25000000000000 : ℝ)^4463 := by
    have hnat : (5522579897 : ℕ)^5487*25000000000000^4463 ≤ 12048099413853^4463*10000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5522579897 10000000000 12048099413853 25000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5074608943/10000000000 : ℝ)^5487 ≤ (43431970732913/100000000000000 : ℝ)^4463 := by
    have hnat : (5074608943 : ℕ)^5487*100000000000000^4463 ≤ 43431970732913^4463*10000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5074608943 10000000000 43431970732913 100000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5487/1024 : ℝ)) 5487 4463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-10394347/78125000 : ℝ), (5522579897/10000000000 : ℝ), (5074608943/10000000000 : ℝ)] ![(837563159927/10000000000000 : ℝ), (12048099413853/25000000000000 : ℝ), (43431970732913/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-10394347/78125000 : ℝ)|^5487 ≤ (837563159927/10000000000000 : ℝ)^4463
        have hw : |(-10394347/78125000 : ℝ)|=(10394347/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5522579897/10000000000 : ℝ)|^5487 ≤ (12048099413853/25000000000000 : ℝ)^4463
        have hw : |(5522579897/10000000000 : ℝ)|=(5522579897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5074608943/10000000000 : ℝ)|^5487 ≤ (43431970732913/100000000000000 : ℝ)^4463
        have hw : |(5074608943/10000000000 : ℝ)|=(5074608943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1732_s4_1 (p : ℝ) (hpa : (5471/1024 : ℝ) ≤ p) (hpb : p ≤ (5487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349022863/10000000000 : ℝ)*x 0 + (-1565620019/10000000000 : ℝ)*x 1 + (5074609069/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349022863/10000000000 : ℝ)^5487 ≤ (11584283799307/25000000000000 : ℝ)^4463 := by
    have hnat : (5349022863 : ℕ)^5487*25000000000000^4463 ≤ 11584283799307^4463*10000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349022863 10000000000 11584283799307 25000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1565620019/10000000000 : ℝ)^5487 ≤ (2046178545871/20000000000000 : ℝ)^4463 := by
    have hnat : (1565620019 : ℕ)^5487*20000000000000^4463 ≤ 2046178545871^4463*10000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1565620019 10000000000 2046178545871 20000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5074609069/10000000000 : ℝ)^5487 ≤ (2714498253671/6250000000000 : ℝ)^4463 := by
    have hnat : (5074609069 : ℕ)^5487*6250000000000^4463 ≤ 2714498253671^4463*10000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5074609069 10000000000 2714498253671 6250000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5487/1024 : ℝ)) 5487 4463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349022863/10000000000 : ℝ), (-1565620019/10000000000 : ℝ), (5074609069/10000000000 : ℝ)] ![(11584283799307/25000000000000 : ℝ), (2046178545871/20000000000000 : ℝ), (2714498253671/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349022863/10000000000 : ℝ)|^5487 ≤ (11584283799307/25000000000000 : ℝ)^4463
        have hw : |(5349022863/10000000000 : ℝ)|=(5349022863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1565620019/10000000000 : ℝ)|^5487 ≤ (2046178545871/20000000000000 : ℝ)^4463
        have hw : |(-1565620019/10000000000 : ℝ)|=(1565620019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5074609069/10000000000 : ℝ)|^5487 ≤ (2714498253671/6250000000000 : ℝ)^4463
        have hw : |(5074609069/10000000000 : ℝ)|=(5074609069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1732_s4_2 (p : ℝ) (hpa : (5471/1024 : ℝ) ≤ p) (hpb : p ≤ (5487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (83578483/156250000 : ℝ)*x 0 + (1268652313/2500000000 : ℝ)*x 1 + (-782809857/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83578483/156250000 : ℝ)^5487 ≤ (23168567859547/50000000000000 : ℝ)^4463 := by
    have hnat : (83578483 : ℕ)^5487*50000000000000^4463 ≤ 23168567859547^4463*156250000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83578483 156250000 23168567859547 50000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1268652313/2500000000 : ℝ)^5487 ≤ (43431973984337/100000000000000 : ℝ)^4463 := by
    have hnat : (1268652313 : ℕ)^5487*100000000000000^4463 ≤ 43431973984337^4463*2500000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1268652313 2500000000 43431973984337 100000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (782809857/5000000000 : ℝ)^5487 ≤ (5115445139483/50000000000000 : ℝ)^4463 := by
    have hnat : (782809857 : ℕ)^5487*50000000000000^4463 ≤ 5115445139483^4463*5000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      782809857 5000000000 5115445139483 50000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5487/1024 : ℝ)) 5487 4463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83578483/156250000 : ℝ), (1268652313/2500000000 : ℝ), (-782809857/5000000000 : ℝ)] ![(23168567859547/50000000000000 : ℝ), (43431973984337/100000000000000 : ℝ), (5115445139483/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83578483/156250000 : ℝ)|^5487 ≤ (23168567859547/50000000000000 : ℝ)^4463
        have hw : |(83578483/156250000 : ℝ)|=(83578483/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1268652313/2500000000 : ℝ)|^5487 ≤ (43431973984337/100000000000000 : ℝ)^4463
        have hw : |(1268652313/2500000000 : ℝ)|=(1268652313/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-782809857/5000000000 : ℝ)|^5487 ≤ (5115445139483/50000000000000 : ℝ)^4463
        have hw : |(-782809857/5000000000 : ℝ)|=(782809857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1732_s4_3 (p : ℝ) (hpa : (5471/1024 : ℝ) ≤ p) (hpb : p ≤ (5487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2030238623/5000000000 : ℝ)*x 0 + (3412387697/10000000000 : ℝ)*x 1 + (2388261727/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2030238623/5000000000 : ℝ)^5487 ≤ (33019325139053/100000000000000 : ℝ)^4463 := by
    have hnat : (2030238623 : ℕ)^5487*100000000000000^4463 ≤ 33019325139053^4463*5000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2030238623 5000000000 33019325139053 100000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3412387697/10000000000 : ℝ)^5487 ≤ (2666381628789/10000000000000 : ℝ)^4463 := by
    have hnat : (3412387697 : ℕ)^5487*10000000000000^4463 ≤ 2666381628789^4463*10000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3412387697 10000000000 2666381628789 10000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2388261727/5000000000 : ℝ)^5487 ≤ (20158429279009/50000000000000 : ℝ)^4463 := by
    have hnat : (2388261727 : ℕ)^5487*50000000000000^4463 ≤ 20158429279009^4463*5000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2388261727 5000000000 20158429279009 50000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5487/1024 : ℝ)) 5487 4463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2030238623/5000000000 : ℝ), (3412387697/10000000000 : ℝ), (2388261727/5000000000 : ℝ)] ![(33019325139053/100000000000000 : ℝ), (2666381628789/10000000000000 : ℝ), (20158429279009/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2030238623/5000000000 : ℝ)|^5487 ≤ (33019325139053/100000000000000 : ℝ)^4463
        have hw : |(2030238623/5000000000 : ℝ)|=(2030238623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3412387697/10000000000 : ℝ)|^5487 ≤ (2666381628789/10000000000000 : ℝ)^4463
        have hw : |(3412387697/10000000000 : ℝ)|=(3412387697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2388261727/5000000000 : ℝ)|^5487 ≤ (20158429279009/50000000000000 : ℝ)^4463
        have hw : |(2388261727/5000000000 : ℝ)|=(2388261727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1732_s4_4 (p : ℝ) (hpa : (5471/1024 : ℝ) ≤ p) (hpb : p ≤ (5487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-332717189/2500000000 : ℝ)*x 0 + (20326721/40000000 : ℝ)*x 1 + (1103071857/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (332717189/2500000000 : ℝ)^5487 ≤ (8378668256257/100000000000000 : ℝ)^4463 := by
    have hnat : (332717189 : ℕ)^5487*100000000000000^4463 ≤ 8378668256257^4463*2500000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332717189 2500000000 8378668256257 100000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (20326721/40000000 : ℝ)^5487 ≤ (43506389782167/100000000000000 : ℝ)^4463 := by
    have hnat : (20326721 : ℕ)^5487*100000000000000^4463 ≤ 43506389782167^4463*40000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20326721 40000000 43506389782167 100000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1103071857/2000000000 : ℝ)^5487 ≤ (48114941945337/100000000000000 : ℝ)^4463 := by
    have hnat : (1103071857 : ℕ)^5487*100000000000000^4463 ≤ 48114941945337^4463*2000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103071857 2000000000 48114941945337 100000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5487/1024 : ℝ)) 5487 4463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-332717189/2500000000 : ℝ), (20326721/40000000 : ℝ), (1103071857/2000000000 : ℝ)] ![(8378668256257/100000000000000 : ℝ), (43506389782167/100000000000000 : ℝ), (48114941945337/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-332717189/2500000000 : ℝ)|^5487 ≤ (8378668256257/100000000000000 : ℝ)^4463
        have hw : |(-332717189/2500000000 : ℝ)|=(332717189/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(20326721/40000000 : ℝ)|^5487 ≤ (43506389782167/100000000000000 : ℝ)^4463
        have hw : |(20326721/40000000 : ℝ)|=(20326721/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1103071857/2000000000 : ℝ)|^5487 ≤ (48114941945337/100000000000000 : ℝ)^4463
        have hw : |(1103071857/2000000000 : ℝ)|=(1103071857/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1732_s4_5 (p : ℝ) (hpa : (5471/1024 : ℝ) ≤ p) (hpb : p ≤ (5487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4061671993/10000000000 : ℝ)*x 0 + (2377495253/5000000000 : ℝ)*x 1 + (3434376253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4061671993/10000000000 : ℝ)^5487 ≤ (33031270239113/100000000000000 : ℝ)^4463 := by
    have hnat : (4061671993 : ℕ)^5487*100000000000000^4463 ≤ 33031270239113^4463*10000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4061671993 10000000000 33031270239113 100000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2377495253/5000000000 : ℝ)^5487 ≤ (20046760590353/50000000000000 : ℝ)^4463 := by
    have hnat : (2377495253 : ℕ)^5487*50000000000000^4463 ≤ 20046760590353^4463*5000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2377495253 5000000000 20046760590353 50000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3434376253/10000000000 : ℝ)^5487 ≤ (13437604283483/50000000000000 : ℝ)^4463 := by
    have hnat : (3434376253 : ℕ)^5487*50000000000000^4463 ≤ 13437604283483^4463*10000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3434376253 10000000000 13437604283483 50000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5487/1024 : ℝ)) 5487 4463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4061671993/10000000000 : ℝ), (2377495253/5000000000 : ℝ), (3434376253/10000000000 : ℝ)] ![(33031270239113/100000000000000 : ℝ), (20046760590353/50000000000000 : ℝ), (13437604283483/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4061671993/10000000000 : ℝ)|^5487 ≤ (33031270239113/100000000000000 : ℝ)^4463
        have hw : |(4061671993/10000000000 : ℝ)|=(4061671993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2377495253/5000000000 : ℝ)|^5487 ≤ (20046760590353/50000000000000 : ℝ)^4463
        have hw : |(2377495253/5000000000 : ℝ)|=(2377495253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3434376253/10000000000 : ℝ)|^5487 ≤ (13437604283483/50000000000000 : ℝ)^4463
        have hw : |(3434376253/10000000000 : ℝ)|=(3434376253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1732_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5471/1024 : ℝ) ≤ p) (hpb : p ≤ (5487/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40451477/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18331/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1753/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (4383/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18331/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18331/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1753/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18331/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1753/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18331/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1753/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18331/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1753/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18331/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1753/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18331/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1753/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1753/20000 : ℝ) ^ (5471/1024 : ℝ) ≤ (112287922802721/50000000000000000000 : ℝ) := by
    have hpowers : (1753/20000 : ℝ)^5471 ≤ (112287922802721/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1753 : ℕ)^5471*50000000000000000000^1024 ≤ 112287922802721^1024*20000^5471 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1753 20000 112287922802721 50000000000000000000 5471 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1753/20000 : ℝ)) (X := (112287922802721/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5471 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (18331/100000 : ℝ) ^ (5471/1024 : ℝ) ≤ (5785495735248369/50000000000000000000 : ℝ) := by
    have hpowers : (18331/100000 : ℝ)^5471 ≤ (5785495735248369/50000000000000000000 : ℝ)^1024 := by
      have hnat : (18331 : ℕ)^5471*50000000000000000000^1024 ≤ 5785495735248369^1024*100000^5471 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18331 100000 5785495735248369 50000000000000000000 5471 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18331/100000 : ℝ)) (X := (5785495735248369/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5471 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000112287922802721/25000000000000000000 : ℝ) ≤ (10000008406698817/10000000000000000 : ℝ) ^ (5471/1024 : ℝ) := by
    have hpowers : (25000112287922802721/25000000000000000000 : ℝ)^1024 ≤ (10000008406698817/10000000000000000 : ℝ)^5471 := by
      have hnat : (25000112287922802721 : ℕ)^1024*10000000000000000^5471 ≤ 10000008406698817^5471*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000112287922802721 25000000000000000000 10000008406698817 10000000000000000 1024 5471 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000008406698817/10000000000000000 : ℝ)) (X := (25000112287922802721/25000000000000000000 : ℝ)) (by norm_num) 5471 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (5000589778365805109/5000000000000000000 : ℝ) ≤ (5000110382763057/5000000000000000 : ℝ) ^ (5471/1024 : ℝ) := by
    have hpowers : (5000589778365805109/5000000000000000000 : ℝ)^1024 ≤ (5000110382763057/5000000000000000 : ℝ)^5471 := by
      have hnat : (5000589778365805109 : ℕ)^1024*5000000000000000^5471 ≤ 5000110382763057^5471*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000589778365805109 5000000000000000000 5000110382763057 5000000000000000 1024 5471 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000110382763057/5000000000000000 : ℝ)) (X := (5000589778365805109/5000000000000000000 : ℝ)) (by norm_num) 5471 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25005785495735248369/25000000000000000000 : ℝ) ≤ (10000433124353411/10000000000000000 : ℝ) ^ (5471/1024 : ℝ) := by
    have hpowers : (25005785495735248369/25000000000000000000 : ℝ)^1024 ≤ (10000433124353411/10000000000000000 : ℝ)^5471 := by
      have hnat : (25005785495735248369 : ℕ)^1024*10000000000000000^5471 ≤ 10000433124353411^5471*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005785495735248369 25000000000000000000 10000433124353411 10000000000000000 1024 5471 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000433124353411/10000000000000000 : ℝ)) (X := (25005785495735248369/25000000000000000000 : ℝ)) (by norm_num) 5471 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(112287922802721/50000000000000000000 : ℝ) ≤ ((23914089442059591753/23915000000000000000 : ℝ)+2*(212358827297/956600000000000 : ℝ)*(1753/20000 : ℝ))^(5471/1024 : ℝ) := by
    rw [show (23914089442059591753/23915000000000000000 : ℝ)+2*(212358827297/956600000000000 : ℝ)*(1753/20000 : ℝ)=(10000008406698817/10000000000000000 : ℝ) by norm_num, show 1+2*(112287922802721/50000000000000000000 : ℝ)=(25000112287922802721/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5785495735248369/50000000000000000000 : ℝ)+(112287922802721/50000000000000000000 : ℝ) ≤ ((23914089442059591753/23915000000000000000 : ℝ)+(212358827297/956600000000000 : ℝ)*((18331/100000 : ℝ)+(1753/20000 : ℝ)))^(5471/1024 : ℝ) := by
    rw [show (23914089442059591753/23915000000000000000 : ℝ)+(212358827297/956600000000000 : ℝ)*((18331/100000 : ℝ)+(1753/20000 : ℝ))=(5000110382763057/5000000000000000 : ℝ) by norm_num, show 1+(5785495735248369/50000000000000000000 : ℝ)+(112287922802721/50000000000000000000 : ℝ)=(5000589778365805109/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5785495735248369/50000000000000000000 : ℝ) ≤ ((23914089442059591753/23915000000000000000 : ℝ)+2*(212358827297/956600000000000 : ℝ)*(18331/100000 : ℝ))^(5471/1024 : ℝ) := by
    rw [show (23914089442059591753/23915000000000000000 : ℝ)+2*(212358827297/956600000000000 : ℝ)*(18331/100000 : ℝ)=(10000433124353411/10000000000000000 : ℝ) by norm_num, show 1+2*(5785495735248369/50000000000000000000 : ℝ)=(25005785495735248369/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (23914089442059591753/23915000000000000000 : ℝ)*(X 1 0+X 2 0)+(212358827297/956600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5471/1024 : ℝ)) (lo := (1753/20000 : ℝ)) (hi := (18331/100000 : ℝ)) (c := (23914089442059591753/23915000000000000000 : ℝ)) (alpha := (212358827297/956600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (23914089442059591753/23915000000000000000 : ℝ)*(X 0 1+X 2 1)+(212358827297/956600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5471/1024 : ℝ)) (lo := (1753/20000 : ℝ)) (hi := (18331/100000 : ℝ)) (c := (23914089442059591753/23915000000000000000 : ℝ)) (alpha := (212358827297/956600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (23914089442059591753/23915000000000000000 : ℝ)*(X 0 2+X 1 2)+(212358827297/956600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5471/1024 : ℝ)) (lo := (1753/20000 : ℝ)) (hi := (18331/100000 : ℝ)) (c := (23914089442059591753/23915000000000000000 : ℝ)) (alpha := (212358827297/956600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-10394347/78125000 : ℝ)*X 0 0+(5522579897/10000000000 : ℝ)*X 0 1+(5074608943/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1732_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349022863/10000000000 : ℝ)*X 1 0+(-1565620019/10000000000 : ℝ)*X 1 1+(5074609069/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1732_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((83578483/156250000 : ℝ)*X 2 0+(1268652313/2500000000 : ℝ)*X 2 1+(-782809857/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1732_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2030238623/5000000000 : ℝ)*X 0 0+(3412387697/10000000000 : ℝ)*X 0 1+(2388261727/5000000000 : ℝ)*X 0 2+(2030238623/5000000000 : ℝ)*X 1 0+(3412387697/10000000000 : ℝ)*X 1 1+(2388261727/5000000000 : ℝ)*X 1 2+(2030238623/5000000000 : ℝ)*X 2 0+(3412387697/10000000000 : ℝ)*X 2 1+(2388261727/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1732_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-332717189/2500000000 : ℝ)*X 0 0+(20326721/40000000 : ℝ)*X 0 1+(1103071857/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1732_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4061671993/10000000000 : ℝ)*X 0 0+(2377495253/5000000000 : ℝ)*X 0 1+(3434376253/10000000000 : ℝ)*X 0 2+(4061671993/10000000000 : ℝ)*X 1 0+(2377495253/5000000000 : ℝ)*X 1 1+(3434376253/10000000000 : ℝ)*X 1 2+(4061671993/10000000000 : ℝ)*X 2 0+(2377495253/5000000000 : ℝ)*X 2 1+(3434376253/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1732_s4_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (647524626888739999638821463/298937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (432802809/100000000000000 : ℝ)*(base19) + (423270707/100000000000000 : ℝ)*(base23) + (16036993/100000000000000 : ℝ)*(lower2) + (49989/12500000000000 : ℝ)*(upper3) + (127932249/100000000000000 : ℝ)*(upper5) + (741340769206143/50000000000000 : ℝ)*(major0) + (741340769206143/50000000000000 : ℝ)*(major1) + (741340769206143/50000000000000 : ℝ)*(major2) + (2232290838618327/100000000000000 : ℝ)*(sp0) + (558073967869859/25000000000000 : ℝ)*(sp1) + (1116147940505769/50000000000000 : ℝ)*(sp2) + (366532998404697/50000000000000 : ℝ)*(sp3) + (2732831959/50000000000000 : ℝ)*(sp4) + (703530021/100000000000000 : ℝ)*(sp5) + (366533350169707/50000000000000 : ℝ)*(f.failure) + (1116148152141123/50000000000000 : ℝ)*(f.sum) + (34087462689971/5978750000000000000000000000 : ℝ)*base66 + (5171085978215736321/1195750000000000000000000000000000 : ℝ)*base68 + (7494062319131513679/1195750000000000000000000000000000 : ℝ)*base69 + (182647909807763679/1195750000000000000000000000000000 : ℝ)*base71 + (175267883512929/23915000000000000000000000000 : ℝ)*base74 + (3208580301926763679/1195750000000000000000000000000000 : ℝ)*base75 + (541356901106763679/1195750000000000000000000000000000 : ℝ)*base77 + (3594529483851513679/1195750000000000000000000000000000 : ℝ)*base79 + (2665719486921/5978750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (11192761/1000000000000000000000 : ℝ)*base90 + (11192761/1000000000000000000000 : ℝ)*base92 + (11192761/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1732_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5471/1024 : ℝ) ≤ p) (hpb : p ≤ (5487/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40451477/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18331/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1753/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4383/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18331/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1732_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1732_box_0 (p : ℝ) (hpa : (5471/1024 : ℝ) ≤ p) (hpb : p ≤ (5487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-227871533/2500000000 : ℝ)*x 0 + (2722876593/5000000000 : ℝ)*x 1 + (2722876589/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (227871533/2500000000 : ℝ)^5487 ≤ (1315264099343/25000000000000 : ℝ)^4463 := by
    have hnat : (227871533 : ℕ)^5487*25000000000000^4463 ≤ 1315264099343^4463*2500000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      227871533 2500000000 1315264099343 25000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2722876593/5000000000 : ℝ)^5487 ≤ (296059198979/625000000000 : ℝ)^4463 := by
    have hnat : (2722876593 : ℕ)^5487*625000000000^4463 ≤ 296059198979^4463*5000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2722876593 5000000000 296059198979 625000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2722876589/5000000000 : ℝ)^5487 ≤ (23684735875543/50000000000000 : ℝ)^4463 := by
    have hnat : (2722876589 : ℕ)^5487*50000000000000^4463 ≤ 23684735875543^4463*5000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2722876589 5000000000 23684735875543 50000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5487/1024 : ℝ)) 5487 4463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-227871533/2500000000 : ℝ), (2722876593/5000000000 : ℝ), (2722876589/5000000000 : ℝ)] ![(1315264099343/25000000000000 : ℝ), (296059198979/625000000000 : ℝ), (23684735875543/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-227871533/2500000000 : ℝ)|^5487 ≤ (1315264099343/25000000000000 : ℝ)^4463
        have hw : |(-227871533/2500000000 : ℝ)|=(227871533/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2722876593/5000000000 : ℝ)|^5487 ≤ (296059198979/625000000000 : ℝ)^4463
        have hw : |(2722876593/5000000000 : ℝ)|=(2722876593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2722876589/5000000000 : ℝ)|^5487 ≤ (23684735875543/50000000000000 : ℝ)^4463
        have hw : |(2722876589/5000000000 : ℝ)|=(2722876589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1732_box_1 (p : ℝ) (hpa : (5471/1024 : ℝ) ≤ p) (hpb : p ≤ (5487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (649428821/1250000000 : ℝ)*x 0 + (-317948303/2500000000 : ℝ)*x 1 + (272287659/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (649428821/1250000000 : ℝ)^5487 ≤ (44706756354837/100000000000000 : ℝ)^4463 := by
    have hnat : (649428821 : ℕ)^5487*100000000000000^4463 ≤ 44706756354837^4463*1250000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      649428821 1250000000 44706756354837 100000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (317948303/2500000000 : ℝ)^5487 ≤ (1980942964709/25000000000000 : ℝ)^4463 := by
    have hnat : (317948303 : ℕ)^5487*25000000000000^4463 ≤ 1980942964709^4463*2500000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      317948303 2500000000 1980942964709 25000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (272287659/500000000 : ℝ)^5487 ≤ (23684735886237/50000000000000 : ℝ)^4463 := by
    have hnat : (272287659 : ℕ)^5487*50000000000000^4463 ≤ 23684735886237^4463*500000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272287659 500000000 23684735886237 50000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5487/1024 : ℝ)) 5487 4463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(649428821/1250000000 : ℝ), (-317948303/2500000000 : ℝ), (272287659/500000000 : ℝ)] ![(44706756354837/100000000000000 : ℝ), (1980942964709/25000000000000 : ℝ), (23684735886237/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(649428821/1250000000 : ℝ)|^5487 ≤ (44706756354837/100000000000000 : ℝ)^4463
        have hw : |(649428821/1250000000 : ℝ)|=(649428821/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-317948303/2500000000 : ℝ)|^5487 ≤ (1980942964709/25000000000000 : ℝ)^4463
        have hw : |(-317948303/2500000000 : ℝ)|=(317948303/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(272287659/500000000 : ℝ)|^5487 ≤ (23684735886237/50000000000000 : ℝ)^4463
        have hw : |(272287659/500000000 : ℝ)|=(272287659/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1732_box_2 (p : ℝ) (hpa : (5471/1024 : ℝ) ≤ p) (hpb : p ≤ (5487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (519543059/1000000000 : ℝ)*x 0 + (5445753159/10000000000 : ℝ)*x 1 + (-127179321/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (519543059/1000000000 : ℝ)^5487 ≤ (44706756587583/100000000000000 : ℝ)^4463 := by
    have hnat : (519543059 : ℕ)^5487*100000000000000^4463 ≤ 44706756587583^4463*1000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519543059 1000000000 44706756587583 100000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5445753159/10000000000 : ℝ)^5487 ≤ (5921183943487/12500000000000 : ℝ)^4463 := by
    have hnat : (5445753159 : ℕ)^5487*12500000000000^4463 ≤ 5921183943487^4463*10000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5445753159 10000000000 5921183943487 12500000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (127179321/1000000000 : ℝ)^5487 ≤ (1980942960879/25000000000000 : ℝ)^4463 := by
    have hnat : (127179321 : ℕ)^5487*25000000000000^4463 ≤ 1980942960879^4463*1000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127179321 1000000000 1980942960879 25000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5487/1024 : ℝ)) 5487 4463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(519543059/1000000000 : ℝ), (5445753159/10000000000 : ℝ), (-127179321/1000000000 : ℝ)] ![(44706756587583/100000000000000 : ℝ), (5921183943487/12500000000000 : ℝ), (1980942960879/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(519543059/1000000000 : ℝ)|^5487 ≤ (44706756587583/100000000000000 : ℝ)^4463
        have hw : |(519543059/1000000000 : ℝ)|=(519543059/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5445753159/10000000000 : ℝ)|^5487 ≤ (5921183943487/12500000000000 : ℝ)^4463
        have hw : |(5445753159/10000000000 : ℝ)|=(5445753159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-127179321/1000000000 : ℝ)|^5487 ≤ (1980942960879/25000000000000 : ℝ)^4463
        have hw : |(-127179321/1000000000 : ℝ)|=(127179321/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1732_box_3 (p : ℝ) (hpa : (5471/1024 : ℝ) ≤ p) (hpb : p ≤ (5487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4590699719/10000000000 : ℝ)*x 0 + (3837203881/10000000000 : ℝ)*x 1 + (1918601937/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4590699719/10000000000 : ℝ)^5487 ≤ (9599302627053/25000000000000 : ℝ)^4463 := by
    have hnat : (4590699719 : ℕ)^5487*25000000000000^4463 ≤ 9599302627053^4463*10000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4590699719 10000000000 9599302627053 25000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3837203881/10000000000 : ℝ)^5487 ≤ (15400697386673/50000000000000 : ℝ)^4463 := by
    have hnat : (3837203881 : ℕ)^5487*50000000000000^4463 ≤ 15400697386673^4463*10000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3837203881 10000000000 15400697386673 50000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1918601937/5000000000 : ℝ)^5487 ≤ (3850174338033/12500000000000 : ℝ)^4463 := by
    have hnat : (1918601937 : ℕ)^5487*12500000000000^4463 ≤ 3850174338033^4463*5000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1918601937 5000000000 3850174338033 12500000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5487/1024 : ℝ)) 5487 4463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4590699719/10000000000 : ℝ), (3837203881/10000000000 : ℝ), (1918601937/5000000000 : ℝ)] ![(9599302627053/25000000000000 : ℝ), (15400697386673/50000000000000 : ℝ), (3850174338033/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4590699719/10000000000 : ℝ)|^5487 ≤ (9599302627053/25000000000000 : ℝ)^4463
        have hw : |(4590699719/10000000000 : ℝ)|=(4590699719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3837203881/10000000000 : ℝ)|^5487 ≤ (15400697386673/50000000000000 : ℝ)^4463
        have hw : |(3837203881/10000000000 : ℝ)|=(3837203881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1918601937/5000000000 : ℝ)|^5487 ≤ (3850174338033/12500000000000 : ℝ)^4463
        have hw : |(1918601937/5000000000 : ℝ)|=(1918601937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1732_box_4 (p : ℝ) (hpa : (5471/1024 : ℝ) ≤ p) (hpb : p ≤ (5487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-895238497/5000000000 : ℝ)*x 0 + (2562695397/5000000000 : ℝ)*x 1 + (5125390877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (895238497/5000000000 : ℝ)^5487 ≤ (6033069731169/50000000000000 : ℝ)^4463 := by
    have hnat : (895238497 : ℕ)^5487*50000000000000^4463 ≤ 6033069731169^4463*5000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895238497 5000000000 6033069731169 50000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2562695397/5000000000 : ℝ)^5487 ≤ (27479331141/62500000000 : ℝ)^4463 := by
    have hnat : (2562695397 : ℕ)^5487*62500000000^4463 ≤ 27479331141^4463*5000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2562695397 5000000000 27479331141 62500000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5125390877/10000000000 : ℝ)^5487 ≤ (43966930700957/100000000000000 : ℝ)^4463 := by
    have hnat : (5125390877 : ℕ)^5487*100000000000000^4463 ≤ 43966930700957^4463*10000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5125390877 10000000000 43966930700957 100000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5487/1024 : ℝ)) 5487 4463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-895238497/5000000000 : ℝ), (2562695397/5000000000 : ℝ), (5125390877/10000000000 : ℝ)] ![(6033069731169/50000000000000 : ℝ), (27479331141/62500000000 : ℝ), (43966930700957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-895238497/5000000000 : ℝ)|^5487 ≤ (6033069731169/50000000000000 : ℝ)^4463
        have hw : |(-895238497/5000000000 : ℝ)|=(895238497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2562695397/5000000000 : ℝ)|^5487 ≤ (27479331141/62500000000 : ℝ)^4463
        have hw : |(2562695397/5000000000 : ℝ)|=(2562695397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5125390877/10000000000 : ℝ)|^5487 ≤ (43966930700957/100000000000000 : ℝ)^4463
        have hw : |(5125390877/10000000000 : ℝ)|=(5125390877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1732_box_5 (p : ℝ) (hpa : (5471/1024 : ℝ) ≤ p) (hpb : p ≤ (5487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (676448547/1250000000 : ℝ)*x 0 + (-353565093/2500000000 : ℝ)*x 1 + (1281347789/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (676448547/1250000000 : ℝ)^5487 ≤ (47004369609159/100000000000000 : ℝ)^4463 := by
    have hnat : (676448547 : ℕ)^5487*100000000000000^4463 ≤ 47004369609159^4463*1250000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676448547 1250000000 47004369609159 100000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (353565093/2500000000 : ℝ)^5487 ≤ (9028696727501/100000000000000 : ℝ)^4463 := by
    have hnat : (353565093 : ℕ)^5487*100000000000000^4463 ≤ 9028696727501^4463*2500000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      353565093 2500000000 9028696727501 100000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1281347789/2500000000 : ℝ)^5487 ≤ (43966933643423/100000000000000 : ℝ)^4463 := by
    have hnat : (1281347789 : ℕ)^5487*100000000000000^4463 ≤ 43966933643423^4463*2500000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1281347789 2500000000 43966933643423 100000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5487/1024 : ℝ)) 5487 4463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(676448547/1250000000 : ℝ), (-353565093/2500000000 : ℝ), (1281347789/2500000000 : ℝ)] ![(47004369609159/100000000000000 : ℝ), (9028696727501/100000000000000 : ℝ), (43966933643423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(676448547/1250000000 : ℝ)|^5487 ≤ (47004369609159/100000000000000 : ℝ)^4463
        have hw : |(676448547/1250000000 : ℝ)|=(676448547/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-353565093/2500000000 : ℝ)|^5487 ≤ (9028696727501/100000000000000 : ℝ)^4463
        have hw : |(-353565093/2500000000 : ℝ)|=(353565093/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1281347789/2500000000 : ℝ)|^5487 ≤ (43966933643423/100000000000000 : ℝ)^4463
        have hw : |(1281347789/2500000000 : ℝ)|=(1281347789/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1732_box_6 (p : ℝ) (hpa : (5471/1024 : ℝ) ≤ p) (hpb : p ≤ (5487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (676448517/1250000000 : ℝ)*x 0 + (5125391339/10000000000 : ℝ)*x 1 + (-1414260453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (676448517/1250000000 : ℝ)^5487 ≤ (11751091761563/25000000000000 : ℝ)^4463 := by
    have hnat : (676448517 : ℕ)^5487*25000000000000^4463 ≤ 11751091761563^4463*1250000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676448517 1250000000 11751091761563 25000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5125391339/10000000000 : ℝ)^5487 ≤ (43966935573427/100000000000000 : ℝ)^4463 := by
    have hnat : (5125391339 : ℕ)^5487*100000000000000^4463 ≤ 43966935573427^4463*10000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5125391339 10000000000 43966935573427 100000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1414260453/10000000000 : ℝ)^5487 ≤ (4514348681627/50000000000000 : ℝ)^4463 := by
    have hnat : (1414260453 : ℕ)^5487*50000000000000^4463 ≤ 4514348681627^4463*10000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1414260453 10000000000 4514348681627 50000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5487/1024 : ℝ)) 5487 4463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(676448517/1250000000 : ℝ), (5125391339/10000000000 : ℝ), (-1414260453/10000000000 : ℝ)] ![(11751091761563/25000000000000 : ℝ), (43966935573427/100000000000000 : ℝ), (4514348681627/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(676448517/1250000000 : ℝ)|^5487 ≤ (11751091761563/25000000000000 : ℝ)^4463
        have hw : |(676448517/1250000000 : ℝ)|=(676448517/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5125391339/10000000000 : ℝ)|^5487 ≤ (43966935573427/100000000000000 : ℝ)^4463
        have hw : |(5125391339/10000000000 : ℝ)|=(5125391339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1414260453/10000000000 : ℝ)|^5487 ≤ (4514348681627/50000000000000 : ℝ)^4463
        have hw : |(-1414260453/10000000000 : ℝ)|=(1414260453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1732_box_7 (p : ℝ) (hpa : (5471/1024 : ℝ) ≤ p) (hpb : p ≤ (5487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (437116063/1250000000 : ℝ)*x 0 + (876369203/2000000000 : ℝ)*x 1 + (4381846361/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (437116063/1250000000 : ℝ)^5487 ≤ (27478264073063/100000000000000 : ℝ)^4463 := by
    have hnat : (437116063 : ℕ)^5487*100000000000000^4463 ≤ 27478264073063^4463*1250000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437116063 1250000000 27478264073063 100000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (876369203/2000000000 : ℝ)^5487 ≤ (4532608274807/12500000000000 : ℝ)^4463 := by
    have hnat : (876369203 : ℕ)^5487*12500000000000^4463 ≤ 4532608274807^4463*2000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      876369203 2000000000 4532608274807 12500000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4381846361/10000000000 : ℝ)^5487 ≤ (36260869718639/100000000000000 : ℝ)^4463 := by
    have hnat : (4381846361 : ℕ)^5487*100000000000000^4463 ≤ 36260869718639^4463*10000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4381846361 10000000000 36260869718639 100000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5487/1024 : ℝ)) 5487 4463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(437116063/1250000000 : ℝ), (876369203/2000000000 : ℝ), (4381846361/10000000000 : ℝ)] ![(27478264073063/100000000000000 : ℝ), (4532608274807/12500000000000 : ℝ), (36260869718639/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(437116063/1250000000 : ℝ)|^5487 ≤ (27478264073063/100000000000000 : ℝ)^4463
        have hw : |(437116063/1250000000 : ℝ)|=(437116063/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(876369203/2000000000 : ℝ)|^5487 ≤ (4532608274807/12500000000000 : ℝ)^4463
        have hw : |(876369203/2000000000 : ℝ)|=(876369203/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4381846361/10000000000 : ℝ)|^5487 ≤ (36260869718639/100000000000000 : ℝ)^4463
        have hw : |(4381846361/10000000000 : ℝ)|=(4381846361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1732_box_8 (p : ℝ) (hpa : (5471/1024 : ℝ) ≤ p) (hpb : p ≤ (5487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-800005007/5000000000 : ℝ)*x 0 + (2441768789/5000000000 : ℝ)*x 1 + (2755207281/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (800005007/5000000000 : ℝ)^5487 ≤ (1050787646447/10000000000000 : ℝ)^4463 := by
    have hnat : (800005007 : ℕ)^5487*10000000000000^4463 ≤ 1050787646447^4463*5000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      800005007 5000000000 1050787646447 10000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2441768789/5000000000 : ℝ)^5487 ≤ (10357552583133/25000000000000 : ℝ)^4463 := by
    have hnat : (2441768789 : ℕ)^5487*25000000000000^4463 ≤ 10357552583133^4463*5000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2441768789 5000000000 10357552583133 25000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2755207281/5000000000 : ℝ)^5487 ≤ (9612382635943/20000000000000 : ℝ)^4463 := by
    have hnat : (2755207281 : ℕ)^5487*20000000000000^4463 ≤ 9612382635943^4463*5000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2755207281 5000000000 9612382635943 20000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5487/1024 : ℝ)) 5487 4463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-800005007/5000000000 : ℝ), (2441768789/5000000000 : ℝ), (2755207281/5000000000 : ℝ)] ![(1050787646447/10000000000000 : ℝ), (10357552583133/25000000000000 : ℝ), (9612382635943/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-800005007/5000000000 : ℝ)|^5487 ≤ (1050787646447/10000000000000 : ℝ)^4463
        have hw : |(-800005007/5000000000 : ℝ)|=(800005007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2441768789/5000000000 : ℝ)|^5487 ≤ (10357552583133/25000000000000 : ℝ)^4463
        have hw : |(2441768789/5000000000 : ℝ)|=(2441768789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2755207281/5000000000 : ℝ)|^5487 ≤ (9612382635943/20000000000000 : ℝ)^4463
        have hw : |(2755207281/5000000000 : ℝ)|=(2755207281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1732_box_9 (p : ℝ) (hpa : (5471/1024 : ℝ) ≤ p) (hpb : p ≤ (5487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (643980823/1250000000 : ℝ)*x 0 + (-310361263/2500000000 : ℝ)*x 1 + (5510417233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (643980823/1250000000 : ℝ)^5487 ≤ (22123055046247/50000000000000 : ℝ)^4463 := by
    have hnat : (643980823 : ℕ)^5487*50000000000000^4463 ≤ 22123055046247^4463*1250000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      643980823 1250000000 22123055046247 50000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (310361263/2500000000 : ℝ)^5487 ≤ (1538389615141/20000000000000 : ℝ)^4463 := by
    have hnat : (310361263 : ℕ)^5487*20000000000000^4463 ≤ 1538389615141^4463*2500000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      310361263 2500000000 1538389615141 20000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5510417233/10000000000 : ℝ)^5487 ≤ (24030970910707/50000000000000 : ℝ)^4463 := by
    have hnat : (5510417233 : ℕ)^5487*50000000000000^4463 ≤ 24030970910707^4463*10000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5510417233 10000000000 24030970910707 50000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5487/1024 : ℝ)) 5487 4463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(643980823/1250000000 : ℝ), (-310361263/2500000000 : ℝ), (5510417233/10000000000 : ℝ)] ![(22123055046247/50000000000000 : ℝ), (1538389615141/20000000000000 : ℝ), (24030970910707/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(643980823/1250000000 : ℝ)|^5487 ≤ (22123055046247/50000000000000 : ℝ)^4463
        have hw : |(643980823/1250000000 : ℝ)|=(643980823/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-310361263/2500000000 : ℝ)|^5487 ≤ (1538389615141/20000000000000 : ℝ)^4463
        have hw : |(-310361263/2500000000 : ℝ)|=(310361263/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5510417233/10000000000 : ℝ)|^5487 ≤ (24030970910707/50000000000000 : ℝ)^4463
        have hw : |(5510417233/10000000000 : ℝ)|=(5510417233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1732_box_10 (p : ℝ) (hpa : (5471/1024 : ℝ) ≤ p) (hpb : p ≤ (5487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (80497619/156250000 : ℝ)*x 0 + (5510415627/10000000000 : ℝ)*x 1 + (-1241445881/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (80497619/156250000 : ℝ)^5487 ≤ (22123060494659/50000000000000 : ℝ)^4463 := by
    have hnat : (80497619 : ℕ)^5487*50000000000000^4463 ≤ 22123060494659^4463*156250000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80497619 156250000 22123060494659 50000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5510415627/10000000000 : ℝ)^5487 ≤ (375483785937/781250000000 : ℝ)^4463 := by
    have hnat : (5510415627 : ℕ)^5487*781250000000^4463 ≤ 375483785937^4463*10000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5510415627 10000000000 375483785937 781250000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1241445881/10000000000 : ℝ)^5487 ≤ (7691954390677/100000000000000 : ℝ)^4463 := by
    have hnat : (1241445881 : ℕ)^5487*100000000000000^4463 ≤ 7691954390677^4463*10000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1241445881 10000000000 7691954390677 100000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5487/1024 : ℝ)) 5487 4463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(80497619/156250000 : ℝ), (5510415627/10000000000 : ℝ), (-1241445881/10000000000 : ℝ)] ![(22123060494659/50000000000000 : ℝ), (375483785937/781250000000 : ℝ), (7691954390677/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(80497619/156250000 : ℝ)|^5487 ≤ (22123060494659/50000000000000 : ℝ)^4463
        have hw : |(80497619/156250000 : ℝ)|=(80497619/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5510415627/10000000000 : ℝ)|^5487 ≤ (375483785937/781250000000 : ℝ)^4463
        have hw : |(5510415627/10000000000 : ℝ)|=(5510415627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1241445881/10000000000 : ℝ)|^5487 ≤ (7691954390677/100000000000000 : ℝ)^4463
        have hw : |(-1241445881/10000000000 : ℝ)|=(1241445881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1732_box_11 (p : ℝ) (hpa : (5471/1024 : ℝ) ≤ p) (hpb : p ≤ (5487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4800697163/10000000000 : ℝ)*x 0 + (3726862269/10000000000 : ℝ)*x 1 + (3726860833/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4800697163/10000000000 : ℝ)^5487 ≤ (316936413777/781250000000 : ℝ)^4463 := by
    have hnat : (4800697163 : ℕ)^5487*781250000000^4463 ≤ 316936413777^4463*10000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4800697163 10000000000 316936413777 781250000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3726862269/10000000000 : ℝ)^5487 ≤ (5943215310447/20000000000000 : ℝ)^4463 := by
    have hnat : (3726862269 : ℕ)^5487*20000000000000^4463 ≤ 5943215310447^4463*10000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3726862269 10000000000 5943215310447 20000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3726860833/10000000000 : ℝ)^5487 ≤ (29716062475219/100000000000000 : ℝ)^4463 := by
    have hnat : (3726860833 : ℕ)^5487*100000000000000^4463 ≤ 29716062475219^4463*10000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3726860833 10000000000 29716062475219 100000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5487/1024 : ℝ)) 5487 4463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4800697163/10000000000 : ℝ), (3726862269/10000000000 : ℝ), (3726860833/10000000000 : ℝ)] ![(316936413777/781250000000 : ℝ), (5943215310447/20000000000000 : ℝ), (29716062475219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4800697163/10000000000 : ℝ)|^5487 ≤ (316936413777/781250000000 : ℝ)^4463
        have hw : |(4800697163/10000000000 : ℝ)|=(4800697163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3726862269/10000000000 : ℝ)|^5487 ≤ (5943215310447/20000000000000 : ℝ)^4463
        have hw : |(3726862269/10000000000 : ℝ)|=(3726862269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3726860833/10000000000 : ℝ)|^5487 ≤ (29716062475219/100000000000000 : ℝ)^4463
        have hw : |(3726860833/10000000000 : ℝ)|=(3726860833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1732_box_12 (p : ℝ) (hpa : (5471/1024 : ℝ) ≤ p) (hpb : p ≤ (5487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1089544801/10000000000 : ℝ)*x 0 + (2836196663/5000000000 : ℝ)*x 1 + (254736183/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089544801/10000000000 : ℝ)^5487 ≤ (6551618565369/100000000000000 : ℝ)^4463 := by
    have hnat : (1089544801 : ℕ)^5487*100000000000000^4463 ≤ 6551618565369^4463*10000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089544801 10000000000 6551618565369 100000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2836196663/5000000000 : ℝ)^5487 ≤ (49804659330173/100000000000000 : ℝ)^4463 := by
    have hnat : (2836196663 : ℕ)^5487*100000000000000^4463 ≤ 49804659330173^4463*5000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2836196663 5000000000 49804659330173 100000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (254736183/500000000 : ℝ)^5487 ≤ (43643722087481/100000000000000 : ℝ)^4463 := by
    have hnat : (254736183 : ℕ)^5487*100000000000000^4463 ≤ 43643722087481^4463*500000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      254736183 500000000 43643722087481 100000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5487/1024 : ℝ)) 5487 4463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1089544801/10000000000 : ℝ), (2836196663/5000000000 : ℝ), (254736183/500000000 : ℝ)] ![(6551618565369/100000000000000 : ℝ), (49804659330173/100000000000000 : ℝ), (43643722087481/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1089544801/10000000000 : ℝ)|^5487 ≤ (6551618565369/100000000000000 : ℝ)^4463
        have hw : |(-1089544801/10000000000 : ℝ)|=(1089544801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2836196663/5000000000 : ℝ)|^5487 ≤ (49804659330173/100000000000000 : ℝ)^4463
        have hw : |(2836196663/5000000000 : ℝ)|=(2836196663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(254736183/500000000 : ℝ)|^5487 ≤ (43643722087481/100000000000000 : ℝ)^4463
        have hw : |(254736183/500000000 : ℝ)|=(254736183/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1732_box_13 (p : ℝ) (hpa : (5471/1024 : ℝ) ≤ p) (hpb : p ≤ (5487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2716174533/5000000000 : ℝ)*x 0 + (-44599011/312500000 : ℝ)*x 1 + (5094723393/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2716174533/5000000000 : ℝ)^5487 ≤ (11806541470159/25000000000000 : ℝ)^4463 := by
    have hnat : (2716174533 : ℕ)^5487*25000000000000^4463 ≤ 11806541470159^4463*5000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716174533 5000000000 11806541470159 25000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (44599011/312500000 : ℝ)^5487 ≤ (4565057415419/50000000000000 : ℝ)^4463 := by
    have hnat : (44599011 : ℕ)^5487*50000000000000^4463 ≤ 4565057415419^4463*312500000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44599011 312500000 4565057415419 50000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5094723393/10000000000 : ℝ)^5487 ≤ (5455464909431/12500000000000 : ℝ)^4463 := by
    have hnat : (5094723393 : ℕ)^5487*12500000000000^4463 ≤ 5455464909431^4463*10000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5094723393 10000000000 5455464909431 12500000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5487/1024 : ℝ)) 5487 4463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2716174533/5000000000 : ℝ), (-44599011/312500000 : ℝ), (5094723393/10000000000 : ℝ)] ![(11806541470159/25000000000000 : ℝ), (4565057415419/50000000000000 : ℝ), (5455464909431/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2716174533/5000000000 : ℝ)|^5487 ≤ (11806541470159/25000000000000 : ℝ)^4463
        have hw : |(2716174533/5000000000 : ℝ)|=(2716174533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-44599011/312500000 : ℝ)|^5487 ≤ (4565057415419/50000000000000 : ℝ)^4463
        have hw : |(-44599011/312500000 : ℝ)|=(44599011/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5094723393/10000000000 : ℝ)|^5487 ≤ (5455464909431/12500000000000 : ℝ)^4463
        have hw : |(5094723393/10000000000 : ℝ)|=(5094723393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1732_box_14 (p : ℝ) (hpa : (5471/1024 : ℝ) ≤ p) (hpb : p ≤ (5487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5432348409/10000000000 : ℝ)*x 0 + (1018944777/2000000000 : ℝ)*x 1 + (-713584293/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5432348409/10000000000 : ℝ)^5487 ≤ (47226158858513/100000000000000 : ℝ)^4463 := by
    have hnat : (5432348409 : ℕ)^5487*100000000000000^4463 ≤ 47226158858513^4463*10000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432348409 10000000000 47226158858513 100000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1018944777/2000000000 : ℝ)^5487 ≤ (43643724457173/100000000000000 : ℝ)^4463 := by
    have hnat : (1018944777 : ℕ)^5487*100000000000000^4463 ≤ 43643724457173^4463*2000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1018944777 2000000000 43643724457173 100000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (713584293/5000000000 : ℝ)^5487 ≤ (2282529167823/25000000000000 : ℝ)^4463 := by
    have hnat : (713584293 : ℕ)^5487*25000000000000^4463 ≤ 2282529167823^4463*5000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      713584293 5000000000 2282529167823 25000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5487/1024 : ℝ)) 5487 4463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5432348409/10000000000 : ℝ), (1018944777/2000000000 : ℝ), (-713584293/5000000000 : ℝ)] ![(47226158858513/100000000000000 : ℝ), (43643724457173/100000000000000 : ℝ), (2282529167823/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5432348409/10000000000 : ℝ)|^5487 ≤ (47226158858513/100000000000000 : ℝ)^4463
        have hw : |(5432348409/10000000000 : ℝ)|=(5432348409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1018944777/2000000000 : ℝ)|^5487 ≤ (43643724457173/100000000000000 : ℝ)^4463
        have hw : |(1018944777/2000000000 : ℝ)|=(1018944777/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-713584293/5000000000 : ℝ)|^5487 ≤ (2282529167823/25000000000000 : ℝ)^4463
        have hw : |(-713584293/5000000000 : ℝ)|=(713584293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1732_box_15 (p : ℝ) (hpa : (5471/1024 : ℝ) ≤ p) (hpb : p ≤ (5487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (846751629/2500000000 : ℝ)*x 0 + (4433774987/10000000000 : ℝ)*x 1 + (1108443609/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (846751629/2500000000 : ℝ)^5487 ≤ (26420196594483/100000000000000 : ℝ)^4463 := by
    have hnat : (846751629 : ℕ)^5487*100000000000000^4463 ≤ 26420196594483^4463*2500000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      846751629 2500000000 26420196594483 100000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4433774987/10000000000 : ℝ)^5487 ≤ (459873806327/1250000000000 : ℝ)^4463 := by
    have hnat : (4433774987 : ℕ)^5487*1250000000000^4463 ≤ 459873806327^4463*10000000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4433774987 10000000000 459873806327 1250000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1108443609/2500000000 : ℝ)^5487 ≤ (18394949442573/50000000000000 : ℝ)^4463 := by
    have hnat : (1108443609 : ℕ)^5487*50000000000000^4463 ≤ 18394949442573^4463*2500000000^5487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1108443609 2500000000 18394949442573 50000000000000 5487 4463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5487/1024 : ℝ)) 5487 4463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(846751629/2500000000 : ℝ), (4433774987/10000000000 : ℝ), (1108443609/2500000000 : ℝ)] ![(26420196594483/100000000000000 : ℝ), (459873806327/1250000000000 : ℝ), (18394949442573/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(846751629/2500000000 : ℝ)|^5487 ≤ (26420196594483/100000000000000 : ℝ)^4463
        have hw : |(846751629/2500000000 : ℝ)|=(846751629/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4433774987/10000000000 : ℝ)|^5487 ≤ (459873806327/1250000000000 : ℝ)^4463
        have hw : |(4433774987/10000000000 : ℝ)|=(4433774987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1108443609/2500000000 : ℝ)|^5487 ≤ (18394949442573/50000000000000 : ℝ)^4463
        have hw : |(1108443609/2500000000 : ℝ)|=(1108443609/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1732_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5471/1024 : ℝ) ≤ p) (hpb : p ≤ (5487/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40451477/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18331/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4383/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(343/500 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(57203/100000 : ℝ) ∧ (1609/2000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (11569/12500 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18331/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4383/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18331/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4383/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18331/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4383/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18331/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4383/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18331/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4383/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18331/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4383/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4383/50000 : ℝ) ^ (5471/1024 : ℝ) ≤ (56178192865871/25000000000000000000 : ℝ) := by
    have hpowers : (4383/50000 : ℝ)^5471 ≤ (56178192865871/25000000000000000000 : ℝ)^1024 := by
      have hnat : (4383 : ℕ)^5471*25000000000000000000^1024 ≤ 56178192865871^1024*50000^5471 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4383 50000 56178192865871 25000000000000000000 5471 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4383/50000 : ℝ)) (X := (56178192865871/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5471 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (18331/100000 : ℝ) ^ (5471/1024 : ℝ) ≤ (5785495735248369/50000000000000000000 : ℝ) := by
    have hpowers : (18331/100000 : ℝ)^5471 ≤ (5785495735248369/50000000000000000000 : ℝ)^1024 := by
      have hnat : (18331 : ℕ)^5471*50000000000000000000^1024 ≤ 5785495735248369^1024*100000^5471 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18331 100000 5785495735248369 50000000000000000000 5471 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18331/100000 : ℝ)) (X := (5785495735248369/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5471 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500056178192865871/12500000000000000000 : ℝ) ≤ (2000001682364889/2000000000000000 : ℝ) ^ (5471/1024 : ℝ) := by
    have hpowers : (12500056178192865871/12500000000000000000 : ℝ)^1024 ≤ (2000001682364889/2000000000000000 : ℝ)^5471 := by
      have hnat : (12500056178192865871 : ℕ)^1024*2000000000000000^5471 ≤ 2000001682364889^5471*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500056178192865871 12500000000000000000 2000001682364889 2000000000000000 1024 5471 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000001682364889/2000000000000000 : ℝ)) (X := (12500056178192865871/12500000000000000000 : ℝ)) (by norm_num) 5471 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50005897852120980111/50000000000000000000 : ℝ) ≤ (2500055192022173/2500000000000000 : ℝ) ^ (5471/1024 : ℝ) := by
    have hpowers : (50005897852120980111/50000000000000000000 : ℝ)^1024 ≤ (2500055192022173/2500000000000000 : ℝ)^5471 := by
      have hnat : (50005897852120980111 : ℕ)^1024*2500000000000000^5471 ≤ 2500055192022173^5471*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005897852120980111 50000000000000000000 2500055192022173 2500000000000000 1024 5471 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500055192022173/2500000000000000 : ℝ)) (X := (50005897852120980111/50000000000000000000 : ℝ)) (by norm_num) 5471 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25005785495735248369/25000000000000000000 : ℝ) ≤ (10000433124352939/10000000000000000 : ℝ) ^ (5471/1024 : ℝ) := by
    have hpowers : (25005785495735248369/25000000000000000000 : ℝ)^1024 ≤ (10000433124352939/10000000000000000 : ℝ)^5471 := by
      have hnat : (25005785495735248369 : ℕ)^1024*10000000000000000^5471 ≤ 10000433124352939^5471*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005785495735248369 25000000000000000000 10000433124352939 10000000000000000 1024 5471 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000433124352939/10000000000000000 : ℝ)) (X := (25005785495735248369/25000000000000000000 : ℝ)) (by norm_num) 5471 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(56178192865871/25000000000000000000 : ℝ) ≤ ((95646357429076038021/95650000000000000000 : ℝ)+2*(212356264247/956500000000000 : ℝ)*(4383/50000 : ℝ))^(5471/1024 : ℝ) := by
    rw [show (95646357429076038021/95650000000000000000 : ℝ)+2*(212356264247/956500000000000 : ℝ)*(4383/50000 : ℝ)=(2000001682364889/2000000000000000 : ℝ) by norm_num, show 1+2*(56178192865871/25000000000000000000 : ℝ)=(12500056178192865871/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5785495735248369/50000000000000000000 : ℝ)+(56178192865871/25000000000000000000 : ℝ) ≤ ((95646357429076038021/95650000000000000000 : ℝ)+(212356264247/956500000000000 : ℝ)*((18331/100000 : ℝ)+(4383/50000 : ℝ)))^(5471/1024 : ℝ) := by
    rw [show (95646357429076038021/95650000000000000000 : ℝ)+(212356264247/956500000000000 : ℝ)*((18331/100000 : ℝ)+(4383/50000 : ℝ))=(2500055192022173/2500000000000000 : ℝ) by norm_num, show 1+(5785495735248369/50000000000000000000 : ℝ)+(56178192865871/25000000000000000000 : ℝ)=(50005897852120980111/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5785495735248369/50000000000000000000 : ℝ) ≤ ((95646357429076038021/95650000000000000000 : ℝ)+2*(212356264247/956500000000000 : ℝ)*(18331/100000 : ℝ))^(5471/1024 : ℝ) := by
    rw [show (95646357429076038021/95650000000000000000 : ℝ)+2*(212356264247/956500000000000 : ℝ)*(18331/100000 : ℝ)=(10000433124352939/10000000000000000 : ℝ) by norm_num, show 1+2*(5785495735248369/50000000000000000000 : ℝ)=(25005785495735248369/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (95646357429076038021/95650000000000000000 : ℝ)*(X 1 0+X 2 0)+(212356264247/956500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5471/1024 : ℝ)) (lo := (4383/50000 : ℝ)) (hi := (18331/100000 : ℝ)) (c := (95646357429076038021/95650000000000000000 : ℝ)) (alpha := (212356264247/956500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (95646357429076038021/95650000000000000000 : ℝ)*(X 0 1+X 2 1)+(212356264247/956500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5471/1024 : ℝ)) (lo := (4383/50000 : ℝ)) (hi := (18331/100000 : ℝ)) (c := (95646357429076038021/95650000000000000000 : ℝ)) (alpha := (212356264247/956500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (95646357429076038021/95650000000000000000 : ℝ)*(X 0 2+X 1 2)+(212356264247/956500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5471/1024 : ℝ)) (lo := (4383/50000 : ℝ)) (hi := (18331/100000 : ℝ)) (c := (95646357429076038021/95650000000000000000 : ℝ)) (alpha := (212356264247/956500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-227871533/2500000000 : ℝ)*X 0 0+(2722876593/5000000000 : ℝ)*X 0 1+(2722876589/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1732_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((649428821/1250000000 : ℝ)*X 1 0+(-317948303/2500000000 : ℝ)*X 1 1+(272287659/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1732_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((519543059/1000000000 : ℝ)*X 2 0+(5445753159/10000000000 : ℝ)*X 2 1+(-127179321/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1732_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4590699719/10000000000 : ℝ)*X 0 0+(3837203881/10000000000 : ℝ)*X 0 1+(1918601937/5000000000 : ℝ)*X 0 2+(4590699719/10000000000 : ℝ)*X 1 0+(3837203881/10000000000 : ℝ)*X 1 1+(1918601937/5000000000 : ℝ)*X 1 2+(4590699719/10000000000 : ℝ)*X 2 0+(3837203881/10000000000 : ℝ)*X 2 1+(1918601937/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1732_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-895238497/5000000000 : ℝ)*X 0 0+(2562695397/5000000000 : ℝ)*X 0 1+(5125390877/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1732_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((676448547/1250000000 : ℝ)*X 1 0+(-353565093/2500000000 : ℝ)*X 1 1+(1281347789/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1732_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((676448517/1250000000 : ℝ)*X 2 0+(5125391339/10000000000 : ℝ)*X 2 1+(-1414260453/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1732_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((437116063/1250000000 : ℝ)*X 0 0+(876369203/2000000000 : ℝ)*X 0 1+(4381846361/10000000000 : ℝ)*X 0 2+(437116063/1250000000 : ℝ)*X 1 0+(876369203/2000000000 : ℝ)*X 1 1+(4381846361/10000000000 : ℝ)*X 1 2+(437116063/1250000000 : ℝ)*X 2 0+(876369203/2000000000 : ℝ)*X 2 1+(4381846361/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1732_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-800005007/5000000000 : ℝ)*X 0 0+(2441768789/5000000000 : ℝ)*X 0 1+(2755207281/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1732_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((643980823/1250000000 : ℝ)*X 1 0+(-310361263/2500000000 : ℝ)*X 1 1+(5510417233/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1732_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((80497619/156250000 : ℝ)*X 2 0+(5510415627/10000000000 : ℝ)*X 2 1+(-1241445881/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1732_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4800697163/10000000000 : ℝ)*X 0 0+(3726862269/10000000000 : ℝ)*X 0 1+(3726860833/10000000000 : ℝ)*X 0 2+(4800697163/10000000000 : ℝ)*X 1 0+(3726862269/10000000000 : ℝ)*X 1 1+(3726860833/10000000000 : ℝ)*X 1 2+(4800697163/10000000000 : ℝ)*X 2 0+(3726862269/10000000000 : ℝ)*X 2 1+(3726860833/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1732_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1089544801/10000000000 : ℝ)*X 0 0+(2836196663/5000000000 : ℝ)*X 0 1+(254736183/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1732_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2716174533/5000000000 : ℝ)*X 1 0+(-44599011/312500000 : ℝ)*X 1 1+(5094723393/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1732_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5432348409/10000000000 : ℝ)*X 2 0+(1018944777/2000000000 : ℝ)*X 2 1+(-713584293/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1732_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((846751629/2500000000 : ℝ)*X 0 0+(4433774987/10000000000 : ℝ)*X 0 1+(1108443609/2500000000 : ℝ)*X 0 2+(846751629/2500000000 : ℝ)*X 1 0+(4433774987/10000000000 : ℝ)*X 1 1+(1108443609/2500000000 : ℝ)*X 1 2+(846751629/2500000000 : ℝ)*X 2 0+(4433774987/10000000000 : ℝ)*X 2 1+(1108443609/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1732_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-343/500 : ℝ) ≤ (-328069615169458750766771558509527/478250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5397899/25000000000000 : ℝ)*(upper1) + (11309757/25000000000000 : ℝ)*(upper2) + (51027219/100000000000000 : ℝ)*(upper3) + (647659/781250000000 : ℝ)*(upper5) + (197500424265929/20000000000000 : ℝ)*(major0) + (197500424265929/20000000000000 : ℝ)*(major1) + (197500424265929/20000000000000 : ℝ)*(major2) + (3905103/20000000000000 : ℝ)*(sp2) + (364977141/100000000000000 : ℝ)*(sp3) + (188703736459333/12500000000000 : ℝ)*(sp4) + (754812878022641/50000000000000 : ℝ)*(sp5) + (1509629872149149/100000000000000 : ℝ)*(sp6) + (488239963715749/100000000000000 : ℝ)*(sp7) + (4135629383/100000000000000 : ℝ)*(sp13) + (48824032869289/10000000000000 : ℝ)*(f.failure) + (188703736459333/12500000000000 : ℝ)*(f.sum) + (38844529969/18681640625000000000000000 : ℝ)*base65 + (10887726470129186509/1913000000000000000000000000000000 : ℝ)*base67 + (14667228558402186509/1913000000000000000000000000000000 : ℝ)*base69 + (2672226469760186509/1913000000000000000000000000000000 : ℝ)*base71 + (25210653470623/9565000000000000000000000000 : ℝ)*base73 + (10448437837676813491/1913000000000000000000000000000000 : ℝ)*base76 + (14907101468708186509/1913000000000000000000000000000000 : ℝ)*base77 + (9960822148789186509/1913000000000000000000000000000000 : ℝ)*base79 + (928609519977/9565000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (2010147/200000000000000000000 : ℝ)*base90 + (2010147/200000000000000000000 : ℝ)*base92 + (2010147/200000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (57203/100000 : ℝ) ≤ (1367926645716999888634179875521281/2391250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (54519/100000000000000 : ℝ)*(upper0) + (746967/100000000000000 : ℝ)*(lower1) + (2375237/100000000000000 : ℝ)*(upper4) + (550193869740229/50000000000000 : ℝ)*(major0) + (550193869740229/50000000000000 : ℝ)*(major1) + (550193869740229/50000000000000 : ℝ)*(major2) + (1637653760995209/100000000000000 : ℝ)*(sp0) + (1637653696132661/100000000000000 : ℝ)*(sp1) + (1637653414460483/100000000000000 : ℝ)*(sp2) + (272026572141831/50000000000000 : ℝ)*(sp3) + (2374513/6250000000000 : ℝ)*(sp7) + (33919949/100000000000000 : ℝ)*(sp8) + (98782497/100000000000000 : ℝ)*(sp9) + (15218187/4000000000000 : ℝ)*(sp10) + (54405318227587/10000000000000 : ℝ)*(f.failure) + (818826897457579/50000000000000 : ℝ)*(f.sum) + (54888565560463/23912500000000000000000000000 : ℝ)*base65 + (30754822470431453191/4782500000000000000000000000000000 : ℝ)*base68 + (28025021581466453191/4782500000000000000000000000000000 : ℝ)*base70 + (19774856563391453191/4782500000000000000000000000000000 : ℝ)*base72 + (1795587945409/747265625000000000000000000 : ℝ)*base73 + (44112209716548953191/4782500000000000000000000000000000 : ℝ)*base76 + (29570172552296453191/4782500000000000000000000000000000 : ℝ)*base78 + (33314859454276453191/4782500000000000000000000000000000 : ℝ)*base80 + (119080828247949/47825000000000000000000000000 : ℝ)*base82 + (295999/200000000000000000000 : ℝ)*base89 + (295999/200000000000000000000 : ℝ)*base91 + (295999/200000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (1609/2000 : ℝ) ≤ (1923821757786077607509624596765479/2391250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (136914207/50000000000000 : ℝ)*(upper0) + (89405491/25000000000000 : ℝ)*(upper1) + (3700047/25000000000000 : ℝ)*(upper2) + (1077344965877833/100000000000000 : ℝ)*(major0) + (1077344965877833/100000000000000 : ℝ)*(major1) + (1077344965877833/100000000000000 : ℝ)*(major2) + (6519076419/5000000000000 : ℝ)*(sp1) + (1784314103/2000000000000 : ℝ)*(sp2) + (5058383111/50000000000000 : ℝ)*(sp3) + (154267677/10000000000000 : ℝ)*(sp4) + (159521048511729/10000000000000 : ℝ)*(sp8) + (19938520578321/1250000000000 : ℝ)*(sp9) + (159512281208891/10000000000000 : ℝ)*(sp10) + (532650268355357/100000000000000 : ℝ)*(sp11) + (266330192560789/50000000000000 : ℝ)*(f.failure) + (79760601389703/5000000000000 : ℝ)*(f.sum) + (219552621655337/23912500000000000000000000000 : ℝ)*base66 + (25475665303850811507/9565000000000000000000000000000000 : ℝ)*base68 + (26726471401010811507/9565000000000000000000000000000000 : ℝ)*base70 + (51236019561860811507/9565000000000000000000000000000000 : ℝ)*base72 + (10713328750203/5978125000000000000000000000 : ℝ)*base74 + (22918717308060811507/9565000000000000000000000000000000 : ℝ)*base76 + (87756338318360811507/9565000000000000000000000000000000 : ℝ)*base78 + (6334785088849188493/9565000000000000000000000000000000 : ℝ)*base79 + (8195689400339/2989062500000000000000000000 : ℝ)*base82 + (2664647/1000000000000000000000 : ℝ)*base90 + (2664647/1000000000000000000000 : ℝ)*base92 + (2664647/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-11569/12500 : ℝ) ≤ (-442620481847198263739254796877429/478250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (156440721/100000000000000 : ℝ)*(lower0) + (3722249/5000000000000 : ℝ)*(lower1) + (96481897/100000000000000 : ℝ)*(lower4) + (225859145895483/20000000000000 : ℝ)*(major0) + (225859145895483/20000000000000 : ℝ)*(major1) + (225859145895483/20000000000000 : ℝ)*(major2) + (2848707023/100000000000000 : ℝ)*(sp0) + (71952837929/100000000000000 : ℝ)*(sp5) + (1988894417/3125000000000 : ℝ)*(sp6) + (87083149/100000000000000 : ℝ)*(sp7) + (1731092760767393/100000000000000 : ℝ)*(sp12) + (1731023656636487/100000000000000 : ℝ)*(sp13) + (108189497803317/6250000000000 : ℝ)*(sp14) + (558345769844357/100000000000000 : ℝ)*(sp15) + (279172928463753/50000000000000 : ℝ)*(f.failure) + (108193475592151/6250000000000 : ℝ)*(f.sum) + (3644160082333/4782500000000000000000000000 : ℝ)*base65 + (6921802666560259143/1913000000000000000000000000000000 : ℝ)*base67 + (4532328074035259143/1913000000000000000000000000000000 : ℝ)*base69 + (12625508268028259143/1913000000000000000000000000000000 : ℝ)*base71 + (82803076720529/9565000000000000000000000000 : ℝ)*base74 + (4824234961202259143/1913000000000000000000000000000000 : ℝ)*base75 + (6204614088410259143/1913000000000000000000000000000000 : ℝ)*base77 + (4042977578659740857/1913000000000000000000000000000000 : ℝ)*base80 + (1313531410913/1195625000000000000000000000 : ℝ)*base82 + (186819/1000000000000000000000 : ℝ)*base90 + (186819/1000000000000000000000 : ℝ)*base92 + (186819/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1732_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5471/1024 : ℝ) ≤ p) (hpb : p ≤ (5487/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40451477/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18331/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4383/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(343/500 : ℝ) ≤ X j i ∧ X j i ≤ -(57203/100000 : ℝ) else (1609/2000 : ℝ) ≤ X j i ∧ X j i ≤ (11569/12500 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1732_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1732_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5471/1024 : ℝ) ≤ p) (hpb : p ≤ (5487/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40451477/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (573/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4381/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(343/500 : ℝ) ≤ X j i ∧ X j i ≤ -(57203/100000 : ℝ) else (1609/2000 : ℝ) ≤ X j i ∧ X j i ≤ (11569/12500 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1732_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1732_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1732_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5471/1024 : ℝ) ≤ p) (hpb : p ≤ (5487/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40451477/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (573/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4381/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(343/500 : ℝ) ≤ X j i ∧ X j i ≤ -(57203/100000 : ℝ) else (1609/2000 : ℝ) ≤ X j i ∧ X j i ≤ (11569/12500 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1732_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
