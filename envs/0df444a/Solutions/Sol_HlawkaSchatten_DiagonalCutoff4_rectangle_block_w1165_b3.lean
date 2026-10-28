-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1165_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:42:26.764262+00:00
-- url     : https://prove2.me/submissions/7ecfa0ac-4593-40aa-83cb-fac3eea4842a

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
theorem support_rectangle_w1165_s9_0 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-431187927/2000000000 : ℝ)*x 0 + (2696283869/5000000000 : ℝ)*x 1 + (65826873/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (431187927/2000000000 : ℝ)^4179 ≤ (65513214149/500000000000 : ℝ)^3155 := by
    have hnat : (431187927 : ℕ)^4179*500000000000^3155 ≤ 65513214149^3155*2000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431187927 2000000000 65513214149 500000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696283869/5000000000 : ℝ)^4179 ≤ (44131233851183/100000000000000 : ℝ)^3155 := by
    have hnat : (2696283869 : ℕ)^4179*100000000000000^3155 ≤ 44131233851183^3155*5000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696283869 5000000000 44131233851183 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65826873/125000000 : ℝ)^4179 ≤ (10691530826553/25000000000000 : ℝ)^3155 := by
    have hnat : (65826873 : ℕ)^4179*25000000000000^3155 ≤ 10691530826553^3155*125000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65826873 125000000 10691530826553 25000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-431187927/2000000000 : ℝ), (2696283869/5000000000 : ℝ), (65826873/125000000 : ℝ)] ![(65513214149/500000000000 : ℝ), (44131233851183/100000000000000 : ℝ), (10691530826553/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-431187927/2000000000 : ℝ)|^4179 ≤ (65513214149/500000000000 : ℝ)^3155
        have hw : |(-431187927/2000000000 : ℝ)|=(431187927/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696283869/5000000000 : ℝ)|^4179 ≤ (44131233851183/100000000000000 : ℝ)^3155
        have hw : |(2696283869/5000000000 : ℝ)|=(2696283869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(65826873/125000000 : ℝ)|^4179 ≤ (10691530826553/25000000000000 : ℝ)^3155
        have hw : |(65826873/125000000 : ℝ)|=(65826873/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s9_1 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534465667/1000000000 : ℝ)*x 0 + (-277506821/1250000000 : ℝ)*x 1 + (5266149821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534465667/1000000000 : ℝ)^4179 ≤ (43612635137511/100000000000000 : ℝ)^3155 := by
    have hnat : (534465667 : ℕ)^4179*100000000000000^3155 ≤ 43612635137511^3155*1000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534465667 1000000000 43612635137511 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (277506821/1250000000 : ℝ)^4179 ≤ (13621241744321/100000000000000 : ℝ)^3155 := by
    have hnat : (277506821 : ℕ)^4179*100000000000000^3155 ≤ 13621241744321^3155*1250000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277506821 1250000000 13621241744321 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266149821/10000000000 : ℝ)^4179 ≤ (8553224620367/20000000000000 : ℝ)^3155 := by
    have hnat : (5266149821 : ℕ)^4179*20000000000000^3155 ≤ 8553224620367^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266149821 10000000000 8553224620367 20000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534465667/1000000000 : ℝ), (-277506821/1250000000 : ℝ), (5266149821/10000000000 : ℝ)] ![(43612635137511/100000000000000 : ℝ), (13621241744321/100000000000000 : ℝ), (8553224620367/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534465667/1000000000 : ℝ)|^4179 ≤ (43612635137511/100000000000000 : ℝ)^3155
        have hw : |(534465667/1000000000 : ℝ)|=(534465667/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-277506821/1250000000 : ℝ)|^4179 ≤ (13621241744321/100000000000000 : ℝ)^3155
        have hw : |(-277506821/1250000000 : ℝ)|=(277506821/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266149821/10000000000 : ℝ)|^4179 ≤ (8553224620367/20000000000000 : ℝ)^3155
        have hw : |(5266149821/10000000000 : ℝ)|=(5266149821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s9_2 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1068931329/2000000000 : ℝ)*x 0 + (5266149839/10000000000 : ℝ)*x 1 + (-2220054577/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068931329/2000000000 : ℝ)^4179 ≤ (21806317433649/50000000000000 : ℝ)^3155 := by
    have hnat : (1068931329 : ℕ)^4179*50000000000000^3155 ≤ 21806317433649^3155*2000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068931329 2000000000 21806317433649 50000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266149839/10000000000 : ℝ)^4179 ≤ (1336441352983/3125000000000 : ℝ)^3155 := by
    have hnat : (5266149839 : ℕ)^4179*3125000000000^3155 ≤ 1336441352983^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266149839 10000000000 1336441352983 3125000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2220054577/10000000000 : ℝ)^4179 ≤ (1702655227183/12500000000000 : ℝ)^3155 := by
    have hnat : (2220054577 : ℕ)^4179*12500000000000^3155 ≤ 1702655227183^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2220054577 10000000000 1702655227183 12500000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068931329/2000000000 : ℝ), (5266149839/10000000000 : ℝ), (-2220054577/10000000000 : ℝ)] ![(21806317433649/50000000000000 : ℝ), (1336441352983/3125000000000 : ℝ), (1702655227183/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068931329/2000000000 : ℝ)|^4179 ≤ (21806317433649/50000000000000 : ℝ)^3155
        have hw : |(1068931329/2000000000 : ℝ)|=(1068931329/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266149839/10000000000 : ℝ)|^4179 ≤ (1336441352983/3125000000000 : ℝ)^3155
        have hw : |(5266149839/10000000000 : ℝ)|=(5266149839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2220054577/10000000000 : ℝ)|^4179 ≤ (1702655227183/12500000000000 : ℝ)^3155
        have hw : |(-2220054577/10000000000 : ℝ)|=(2220054577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s9_3 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (272590337/625000000 : ℝ)*x 0 + (4236935803/10000000000 : ℝ)*x 1 + (561197017/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (272590337/625000000 : ℝ)^4179 ≤ (33317114919817/100000000000000 : ℝ)^3155 := by
    have hnat : (272590337 : ℕ)^4179*100000000000000^3155 ≤ 33317114919817^3155*625000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272590337 625000000 33317114919817 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4236935803/10000000000 : ℝ)^4179 ≤ (32063157086093/100000000000000 : ℝ)^3155 := by
    have hnat : (4236935803 : ℕ)^4179*100000000000000^3155 ≤ 32063157086093^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4236935803 10000000000 32063157086093 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (561197017/1250000000 : ℝ)^4179 ≤ (34619727986383/100000000000000 : ℝ)^3155 := by
    have hnat : (561197017 : ℕ)^4179*100000000000000^3155 ≤ 34619727986383^3155*1250000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561197017 1250000000 34619727986383 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(272590337/625000000 : ℝ), (4236935803/10000000000 : ℝ), (561197017/1250000000 : ℝ)] ![(33317114919817/100000000000000 : ℝ), (32063157086093/100000000000000 : ℝ), (34619727986383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(272590337/625000000 : ℝ)|^4179 ≤ (33317114919817/100000000000000 : ℝ)^3155
        have hw : |(272590337/625000000 : ℝ)|=(272590337/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4236935803/10000000000 : ℝ)|^4179 ≤ (32063157086093/100000000000000 : ℝ)^3155
        have hw : |(4236935803/10000000000 : ℝ)|=(4236935803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(561197017/1250000000 : ℝ)|^4179 ≤ (34619727986383/100000000000000 : ℝ)^3155
        have hw : |(561197017/1250000000 : ℝ)|=(561197017/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s9_4 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-538986111/2500000000 : ℝ)*x 0 + (329154217/625000000 : ℝ)*x 1 + (1078449793/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538986111/2500000000 : ℝ)^4179 ≤ (6551340771107/50000000000000 : ℝ)^3155 := by
    have hnat : (538986111 : ℕ)^4179*50000000000000^3155 ≤ 6551340771107^3155*2500000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538986111 2500000000 6551340771107 50000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (329154217/625000000 : ℝ)^4179 ≤ (42769540016689/100000000000000 : ℝ)^3155 := by
    have hnat : (329154217 : ℕ)^4179*100000000000000^3155 ≤ 42769540016689^3155*625000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329154217 625000000 42769540016689 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078449793/2000000000 : ℝ)^4179 ≤ (4412777843127/10000000000000 : ℝ)^3155 := by
    have hnat : (1078449793 : ℕ)^4179*10000000000000^3155 ≤ 4412777843127^3155*2000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078449793 2000000000 4412777843127 10000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-538986111/2500000000 : ℝ), (329154217/625000000 : ℝ), (1078449793/2000000000 : ℝ)] ![(6551340771107/50000000000000 : ℝ), (42769540016689/100000000000000 : ℝ), (4412777843127/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-538986111/2500000000 : ℝ)|^4179 ≤ (6551340771107/50000000000000 : ℝ)^3155
        have hw : |(-538986111/2500000000 : ℝ)|=(538986111/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(329154217/625000000 : ℝ)|^4179 ≤ (42769540016689/100000000000000 : ℝ)^3155
        have hw : |(329154217/625000000 : ℝ)|=(329154217/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078449793/2000000000 : ℝ)|^4179 ≤ (4412777843127/10000000000000 : ℝ)^3155
        have hw : |(1078449793/2000000000 : ℝ)|=(1078449793/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s9_5 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (436145503/1000000000 : ℝ)*x 0 + (112223533/250000000 : ℝ)*x 1 + (847514581/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (436145503/1000000000 : ℝ)^4179 ≤ (33317212440567/100000000000000 : ℝ)^3155 := by
    have hnat : (436145503 : ℕ)^4179*100000000000000^3155 ≤ 33317212440567^3155*1000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436145503 1000000000 33317212440567 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (112223533/250000000 : ℝ)^4179 ≤ (34613244192263/100000000000000 : ℝ)^3155 := by
    have hnat : (112223533 : ℕ)^4179*100000000000000^3155 ≤ 34613244192263^3155*250000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112223533 250000000 34613244192263 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (847514581/2000000000 : ℝ)^4179 ≤ (3206954335163/10000000000000 : ℝ)^3155 := by
    have hnat : (847514581 : ℕ)^4179*10000000000000^3155 ≤ 3206954335163^3155*2000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847514581 2000000000 3206954335163 10000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(436145503/1000000000 : ℝ), (112223533/250000000 : ℝ), (847514581/2000000000 : ℝ)] ![(33317212440567/100000000000000 : ℝ), (34613244192263/100000000000000 : ℝ), (3206954335163/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(436145503/1000000000 : ℝ)|^4179 ≤ (33317212440567/100000000000000 : ℝ)^3155
        have hw : |(436145503/1000000000 : ℝ)|=(436145503/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(112223533/250000000 : ℝ)|^4179 ≤ (34613244192263/100000000000000 : ℝ)^3155
        have hw : |(112223533/250000000 : ℝ)|=(112223533/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(847514581/2000000000 : ℝ)|^4179 ≤ (3206954335163/10000000000000 : ℝ)^3155
        have hw : |(847514581/2000000000 : ℝ)|=(847514581/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1165_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18740333/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7031/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11383/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1423/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7031/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7031/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11383/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7031/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11383/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7031/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11383/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7031/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11383/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7031/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11383/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7031/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11383/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11383/100000 : ℝ) ^ (8357/2048 : ℝ) ≤ (7046329447287341/50000000000000000000 : ℝ) := by
    have hpowers : (11383/100000 : ℝ)^8357 ≤ (7046329447287341/50000000000000000000 : ℝ)^2048 := by
      have hnat : (11383 : ℕ)^8357*50000000000000000000^2048 ≤ 7046329447287341^2048*100000^8357 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11383 100000 7046329447287341 50000000000000000000 8357 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11383/100000 : ℝ)) (X := (7046329447287341/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8357 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7031/50000 : ℝ) ^ (8357/2048 : ℝ) ≤ (33384862389369967/100000000000000000000 : ℝ) := by
    have hpowers : (7031/50000 : ℝ)^8357 ≤ (33384862389369967/100000000000000000000 : ℝ)^2048 := by
      have hnat : (7031 : ℕ)^8357*100000000000000000000^2048 ≤ 33384862389369967^2048*50000^8357 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7031 50000 33384862389369967 100000000000000000000 8357 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7031/50000 : ℝ)) (X := (33384862389369967/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8357 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007046329447287341/25000000000000000000 : ℝ) ≤ (10000690647249087/10000000000000000 : ℝ) ^ (8357/2048 : ℝ) := by
    have hpowers : (25007046329447287341/25000000000000000000 : ℝ)^2048 ≤ (10000690647249087/10000000000000000 : ℝ)^8357 := by
      have hnat : (25007046329447287341 : ℕ)^2048*10000000000000000^8357 ≤ 10000690647249087^8357*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007046329447287341 25000000000000000000 10000690647249087 10000000000000000 2048 8357 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000690647249087/10000000000000000 : ℝ)) (X := (25007046329447287341/25000000000000000000 : ℝ)) (by norm_num) 8357 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047477521283944649/100000000000000000000 : ℝ) ≤ (10001163294757583/10000000000000000 : ℝ) ^ (8357/2048 : ℝ) := by
    have hpowers : (100047477521283944649/100000000000000000000 : ℝ)^2048 ≤ (10001163294757583/10000000000000000 : ℝ)^8357 := by
      have hnat : (100047477521283944649 : ℕ)^2048*10000000000000000^8357 ≤ 10001163294757583^8357*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047477521283944649 100000000000000000000 10001163294757583 10000000000000000 2048 8357 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001163294757583/10000000000000000 : ℝ)) (X := (100047477521283944649/100000000000000000000 : ℝ)) (by norm_num) 8357 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033384862389369967/50000000000000000000 : ℝ) ≤ (10001635942266079/10000000000000000 : ℝ) ^ (8357/2048 : ℝ) := by
    have hpowers : (50033384862389369967/50000000000000000000 : ℝ)^2048 ≤ (10001635942266079/10000000000000000 : ℝ)^8357 := by
      have hnat : (50033384862389369967 : ℕ)^2048*10000000000000000^8357 ≤ 10001635942266079^8357*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033384862389369967 50000000000000000000 10001635942266079 10000000000000000 2048 8357 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001635942266079/10000000000000000 : ℝ)) (X := (50033384862389369967/50000000000000000000 : ℝ)) (by norm_num) 8357 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7046329447287341/50000000000000000000 : ℝ) ≤ ((569810424485146471/570000000000000000 : ℝ)+2*(628520623/356250000000 : ℝ)*(11383/100000 : ℝ))^(8357/2048 : ℝ) := by
    rw [show (569810424485146471/570000000000000000 : ℝ)+2*(628520623/356250000000 : ℝ)*(11383/100000 : ℝ)=(10000690647249087/10000000000000000 : ℝ) by norm_num, show 1+2*(7046329447287341/50000000000000000000 : ℝ)=(25007046329447287341/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33384862389369967/100000000000000000000 : ℝ)+(7046329447287341/50000000000000000000 : ℝ) ≤ ((569810424485146471/570000000000000000 : ℝ)+(628520623/356250000000 : ℝ)*((7031/50000 : ℝ)+(11383/100000 : ℝ)))^(8357/2048 : ℝ) := by
    rw [show (569810424485146471/570000000000000000 : ℝ)+(628520623/356250000000 : ℝ)*((7031/50000 : ℝ)+(11383/100000 : ℝ))=(10001163294757583/10000000000000000 : ℝ) by norm_num, show 1+(33384862389369967/100000000000000000000 : ℝ)+(7046329447287341/50000000000000000000 : ℝ)=(100047477521283944649/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33384862389369967/100000000000000000000 : ℝ) ≤ ((569810424485146471/570000000000000000 : ℝ)+2*(628520623/356250000000 : ℝ)*(7031/50000 : ℝ))^(8357/2048 : ℝ) := by
    rw [show (569810424485146471/570000000000000000 : ℝ)+2*(628520623/356250000000 : ℝ)*(7031/50000 : ℝ)=(10001635942266079/10000000000000000 : ℝ) by norm_num, show 1+2*(33384862389369967/100000000000000000000 : ℝ)=(50033384862389369967/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (569810424485146471/570000000000000000 : ℝ)*(X 1 0+X 2 0)+(628520623/356250000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8357/2048 : ℝ)) (lo := (11383/100000 : ℝ)) (hi := (7031/50000 : ℝ)) (c := (569810424485146471/570000000000000000 : ℝ)) (alpha := (628520623/356250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (569810424485146471/570000000000000000 : ℝ)*(X 0 1+X 2 1)+(628520623/356250000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8357/2048 : ℝ)) (lo := (11383/100000 : ℝ)) (hi := (7031/50000 : ℝ)) (c := (569810424485146471/570000000000000000 : ℝ)) (alpha := (628520623/356250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (569810424485146471/570000000000000000 : ℝ)*(X 0 2+X 1 2)+(628520623/356250000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8357/2048 : ℝ)) (lo := (11383/100000 : ℝ)) (hi := (7031/50000 : ℝ)) (c := (569810424485146471/570000000000000000 : ℝ)) (alpha := (628520623/356250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-431187927/2000000000 : ℝ)*X 0 0+(2696283869/5000000000 : ℝ)*X 0 1+(65826873/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534465667/1000000000 : ℝ)*X 1 0+(-277506821/1250000000 : ℝ)*X 1 1+(5266149821/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s9_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068931329/2000000000 : ℝ)*X 2 0+(5266149839/10000000000 : ℝ)*X 2 1+(-2220054577/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s9_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((272590337/625000000 : ℝ)*X 0 0+(4236935803/10000000000 : ℝ)*X 0 1+(561197017/1250000000 : ℝ)*X 0 2+(272590337/625000000 : ℝ)*X 1 0+(4236935803/10000000000 : ℝ)*X 1 1+(561197017/1250000000 : ℝ)*X 1 2+(272590337/625000000 : ℝ)*X 2 0+(4236935803/10000000000 : ℝ)*X 2 1+(561197017/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s9_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-538986111/2500000000 : ℝ)*X 0 0+(329154217/625000000 : ℝ)*X 0 1+(1078449793/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s9_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((436145503/1000000000 : ℝ)*X 0 0+(112223533/250000000 : ℝ)*X 0 1+(847514581/2000000000 : ℝ)*X 0 2+(436145503/1000000000 : ℝ)*X 1 0+(112223533/250000000 : ℝ)*X 1 1+(847514581/2000000000 : ℝ)*X 1 2+(436145503/1000000000 : ℝ)*X 2 0+(112223533/250000000 : ℝ)*X 2 1+(847514581/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s9_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (390438232798610997816999/118750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (696367623/100000000000000 : ℝ)*(base19) + (31025007/5000000000000 : ℝ)*(base23) + (4154559/20000000000000 : ℝ)*(lower2) + (18646311/20000000000000 : ℝ)*(upper3) + (21438511/50000000000000 : ℝ)*(upper5) + (148356571488069/2500000000000 : ℝ)*(major0) + (148356571488069/2500000000000 : ℝ)*(major1) + (148356571488069/2500000000000 : ℝ)*(major2) + (3955146031211381/50000000000000 : ℝ)*(sp0) + (3955154461393589/50000000000000 : ℝ)*(sp1) + (7910308998654661/100000000000000 : ℝ)*(sp2) + (197910276726513/5000000000000 : ℝ)*(sp3) + (17556732039/100000000000000 : ℝ)*(sp4) + (2613940937/25000000000000 : ℝ)*(sp5) + (3958215990294009/100000000000000 : ℝ)*(f.failure) + (19775774047887/250000000000 : ℝ)*(f.sum) + (67632357903/9500000000000000000000000 : ℝ)*base65 + (475251580015167/475000000000000000000000000000 : ℝ)*base68 + (3514689707740167/475000000000000000000000000000 : ℝ)*base70 + (9082506995115167/475000000000000000000000000000 : ℝ)*base72 + (40663608607/4750000000000000000000000 : ℝ)*base73 + (11137037233665167/475000000000000000000000000000 : ℝ)*base76 + (3226787839509833/475000000000000000000000000000 : ℝ)*base77 + (4156483442140167/475000000000000000000000000000 : ℝ)*base80 + (18276885991/3800000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (3435003/1250000000000000000000 : ℝ)*base90 + (3435003/1250000000000000000000 : ℝ)*base92 + (3435003/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1165_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18740333/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7031/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11383/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1423/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7031/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1165_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1165_box_0 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1014897067/5000000000 : ℝ)*x 0 + (5375981183/10000000000 : ℝ)*x 1 + (5375981103/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1014897067/5000000000 : ℝ)^4179 ≤ (1512118154127/12500000000000 : ℝ)^3155 := by
    have hnat : (1014897067 : ℕ)^4179*12500000000000^3155 ≤ 1512118154127^3155*5000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1014897067 5000000000 1512118154127 12500000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5375981183/10000000000 : ℝ)^4179 ≤ (43951527809259/100000000000000 : ℝ)^3155 := by
    have hnat : (5375981183 : ℕ)^4179*100000000000000^3155 ≤ 43951527809259^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375981183 10000000000 43951527809259 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5375981103/10000000000 : ℝ)^4179 ≤ (43951526942937/100000000000000 : ℝ)^3155 := by
    have hnat : (5375981103 : ℕ)^4179*100000000000000^3155 ≤ 43951526942937^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375981103 10000000000 43951526942937 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1014897067/5000000000 : ℝ), (5375981183/10000000000 : ℝ), (5375981103/10000000000 : ℝ)] ![(1512118154127/12500000000000 : ℝ), (43951527809259/100000000000000 : ℝ), (43951526942937/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1014897067/5000000000 : ℝ)|^4179 ≤ (1512118154127/12500000000000 : ℝ)^3155
        have hw : |(-1014897067/5000000000 : ℝ)|=(1014897067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5375981183/10000000000 : ℝ)|^4179 ≤ (43951527809259/100000000000000 : ℝ)^3155
        have hw : |(5375981183/10000000000 : ℝ)|=(5375981183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5375981103/10000000000 : ℝ)|^4179 ≤ (43951526942937/100000000000000 : ℝ)^3155
        have hw : |(5375981103/10000000000 : ℝ)|=(5375981103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_box_1 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5296192563/10000000000 : ℝ)*x 0 + (-1069029129/5000000000 : ℝ)*x 1 + (5375980907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296192563/10000000000 : ℝ)^4179 ≤ (43089583126877/100000000000000 : ℝ)^3155 := by
    have hnat : (5296192563 : ℕ)^4179*100000000000000^3155 ≤ 43089583126877^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296192563 10000000000 43089583126877 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1069029129/5000000000 : ℝ)^4179 ≤ (12958892041237/100000000000000 : ℝ)^3155 := by
    have hnat : (1069029129 : ℕ)^4179*100000000000000^3155 ≤ 12958892041237^3155*5000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069029129 5000000000 12958892041237 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5375980907/10000000000 : ℝ)^4179 ≤ (43951524820449/100000000000000 : ℝ)^3155 := by
    have hnat : (5375980907 : ℕ)^4179*100000000000000^3155 ≤ 43951524820449^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375980907 10000000000 43951524820449 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296192563/10000000000 : ℝ), (-1069029129/5000000000 : ℝ), (5375980907/10000000000 : ℝ)] ![(43089583126877/100000000000000 : ℝ), (12958892041237/100000000000000 : ℝ), (43951524820449/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296192563/10000000000 : ℝ)|^4179 ≤ (43089583126877/100000000000000 : ℝ)^3155
        have hw : |(5296192563/10000000000 : ℝ)|=(5296192563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1069029129/5000000000 : ℝ)|^4179 ≤ (12958892041237/100000000000000 : ℝ)^3155
        have hw : |(-1069029129/5000000000 : ℝ)|=(1069029129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5375980907/10000000000 : ℝ)|^4179 ≤ (43951524820449/100000000000000 : ℝ)^3155
        have hw : |(5375980907/10000000000 : ℝ)|=(5375980907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_box_2 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (132404829/250000000 : ℝ)*x 0 + (5375980561/10000000000 : ℝ)*x 1 + (-1069028961/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132404829/250000000 : ℝ)^4179 ≤ (5386198695063/12500000000000 : ℝ)^3155 := by
    have hnat : (132404829 : ℕ)^4179*12500000000000^3155 ≤ 5386198695063^3155*250000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132404829 250000000 5386198695063 12500000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5375980561/10000000000 : ℝ)^4179 ≤ (43951521073607/100000000000000 : ℝ)^3155 := by
    have hnat : (5375980561 : ℕ)^4179*100000000000000^3155 ≤ 43951521073607^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375980561 10000000000 43951521073607 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1069028961/5000000000 : ℝ)^4179 ≤ (12958889343743/100000000000000 : ℝ)^3155 := by
    have hnat : (1069028961 : ℕ)^4179*100000000000000^3155 ≤ 12958889343743^3155*5000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069028961 5000000000 12958889343743 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132404829/250000000 : ℝ), (5375980561/10000000000 : ℝ), (-1069028961/5000000000 : ℝ)] ![(5386198695063/12500000000000 : ℝ), (43951521073607/100000000000000 : ℝ), (12958889343743/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132404829/250000000 : ℝ)|^4179 ≤ (5386198695063/12500000000000 : ℝ)^3155
        have hw : |(132404829/250000000 : ℝ)|=(132404829/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5375980561/10000000000 : ℝ)|^4179 ≤ (43951521073607/100000000000000 : ℝ)^3155
        have hw : |(5375980561/10000000000 : ℝ)|=(5375980561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1069028961/5000000000 : ℝ)|^4179 ≤ (12958889343743/100000000000000 : ℝ)^3155
        have hw : |(-1069028961/5000000000 : ℝ)|=(1069028961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_box_3 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2234373649/5000000000 : ℝ)*x 0 + (43098867/100000000 : ℝ)*x 1 + (4309886379/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2234373649/5000000000 : ℝ)^4179 ≤ (1720357239827/5000000000000 : ℝ)^3155 := by
    have hnat : (2234373649 : ℕ)^4179*5000000000000^3155 ≤ 1720357239827^3155*5000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2234373649 5000000000 1720357239827 5000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (43098867/100000000 : ℝ)^4179 ≤ (32796429211693/100000000000000 : ℝ)^3155 := by
    have hnat : (43098867 : ℕ)^4179*100000000000000^3155 ≤ 32796429211693^3155*100000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43098867 100000000 32796429211693 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4309886379/10000000000 : ℝ)^4179 ≤ (32796425976213/100000000000000 : ℝ)^3155 := by
    have hnat : (4309886379 : ℕ)^4179*100000000000000^3155 ≤ 32796425976213^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4309886379 10000000000 32796425976213 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2234373649/5000000000 : ℝ), (43098867/100000000 : ℝ), (4309886379/10000000000 : ℝ)] ![(1720357239827/5000000000000 : ℝ), (32796429211693/100000000000000 : ℝ), (32796425976213/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2234373649/5000000000 : ℝ)|^4179 ≤ (1720357239827/5000000000000 : ℝ)^3155
        have hw : |(2234373649/5000000000 : ℝ)|=(2234373649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(43098867/100000000 : ℝ)|^4179 ≤ (32796429211693/100000000000000 : ℝ)^3155
        have hw : |(43098867/100000000 : ℝ)|=(43098867/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4309886379/10000000000 : ℝ)|^4179 ≤ (32796425976213/100000000000000 : ℝ)^3155
        have hw : |(4309886379/10000000000 : ℝ)|=(4309886379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_box_4 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1141730707/5000000000 : ℝ)*x 0 + (5281427969/10000000000 : ℝ)*x 1 + (5281427629/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1141730707/5000000000 : ℝ)^4179 ≤ (883682338151/6250000000000 : ℝ)^3155 := by
    have hnat : (1141730707 : ℕ)^4179*6250000000000^3155 ≤ 883682338151^3155*5000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1141730707 5000000000 883682338151 6250000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5281427969/10000000000 : ℝ)^4179 ≤ (42930543116029/100000000000000 : ℝ)^3155 := by
    have hnat : (5281427969 : ℕ)^4179*100000000000000^3155 ≤ 42930543116029^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281427969 10000000000 42930543116029 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5281427629/10000000000 : ℝ)^4179 ≤ (21465269727653/50000000000000 : ℝ)^3155 := by
    have hnat : (5281427629 : ℕ)^4179*50000000000000^3155 ≤ 21465269727653^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281427629 10000000000 21465269727653 50000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1141730707/5000000000 : ℝ), (5281427969/10000000000 : ℝ), (5281427629/10000000000 : ℝ)] ![(883682338151/6250000000000 : ℝ), (42930543116029/100000000000000 : ℝ), (21465269727653/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1141730707/5000000000 : ℝ)|^4179 ≤ (883682338151/6250000000000 : ℝ)^3155
        have hw : |(-1141730707/5000000000 : ℝ)|=(1141730707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5281427969/10000000000 : ℝ)|^4179 ≤ (42930543116029/100000000000000 : ℝ)^3155
        have hw : |(5281427969/10000000000 : ℝ)|=(5281427969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5281427629/10000000000 : ℝ)|^4179 ≤ (21465269727653/50000000000000 : ℝ)^3155
        have hw : |(5281427629/10000000000 : ℝ)|=(5281427629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_box_5 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5362960969/10000000000 : ℝ)*x 0 + (-1087659657/5000000000 : ℝ)*x 1 + (2640713689/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362960969/10000000000 : ℝ)^4179 ≤ (43810587069497/100000000000000 : ℝ)^3155 := by
    have hnat : (5362960969 : ℕ)^4179*100000000000000^3155 ≤ 43810587069497^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362960969 10000000000 43810587069497 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1087659657/5000000000 : ℝ)^4179 ≤ (2651775231433/20000000000000 : ℝ)^3155 := by
    have hnat : (1087659657 : ℕ)^4179*20000000000000^3155 ≤ 2651775231433^3155*5000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087659657 5000000000 2651775231433 20000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2640713689/5000000000 : ℝ)^4179 ≤ (4293053675283/10000000000000 : ℝ)^3155 := by
    have hnat : (2640713689 : ℕ)^4179*10000000000000^3155 ≤ 4293053675283^3155*5000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640713689 5000000000 4293053675283 10000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362960969/10000000000 : ℝ), (-1087659657/5000000000 : ℝ), (2640713689/5000000000 : ℝ)] ![(43810587069497/100000000000000 : ℝ), (2651775231433/20000000000000 : ℝ), (4293053675283/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362960969/10000000000 : ℝ)|^4179 ≤ (43810587069497/100000000000000 : ℝ)^3155
        have hw : |(5362960969/10000000000 : ℝ)|=(5362960969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1087659657/5000000000 : ℝ)|^4179 ≤ (2651775231433/20000000000000 : ℝ)^3155
        have hw : |(-1087659657/5000000000 : ℝ)|=(1087659657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2640713689/5000000000 : ℝ)|^4179 ≤ (4293053675283/10000000000000 : ℝ)^3155
        have hw : |(2640713689/5000000000 : ℝ)|=(2640713689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_box_6 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5362960227/10000000000 : ℝ)*x 0 + (5281427571/10000000000 : ℝ)*x 1 + (-543830013/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362960227/10000000000 : ℝ)^4179 ≤ (10952644760171/25000000000000 : ℝ)^3155 := by
    have hnat : (5362960227 : ℕ)^4179*25000000000000^3155 ≤ 10952644760171^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362960227 10000000000 10952644760171 25000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5281427571/10000000000 : ℝ)^4179 ≤ (42930538830829/100000000000000 : ℝ)^3155 := by
    have hnat : (5281427571 : ℕ)^4179*100000000000000^3155 ≤ 42930538830829^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281427571 10000000000 42930538830829 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (543830013/2500000000 : ℝ)^4179 ≤ (13258882115337/100000000000000 : ℝ)^3155 := by
    have hnat : (543830013 : ℕ)^4179*100000000000000^3155 ≤ 13258882115337^3155*2500000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543830013 2500000000 13258882115337 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362960227/10000000000 : ℝ), (5281427571/10000000000 : ℝ), (-543830013/2500000000 : ℝ)] ![(10952644760171/25000000000000 : ℝ), (42930538830829/100000000000000 : ℝ), (13258882115337/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362960227/10000000000 : ℝ)|^4179 ≤ (10952644760171/25000000000000 : ℝ)^3155
        have hw : |(5362960227/10000000000 : ℝ)|=(5362960227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5281427571/10000000000 : ℝ)|^4179 ≤ (42930538830829/100000000000000 : ℝ)^3155
        have hw : |(5281427571/10000000000 : ℝ)|=(5281427571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-543830013/2500000000 : ℝ)|^4179 ≤ (13258882115337/100000000000000 : ℝ)^3155
        have hw : |(-543830013/2500000000 : ℝ)|=(543830013/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_box_7 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4253771719/10000000000 : ℝ)*x 0 + (4417353083/10000000000 : ℝ)*x 1 + (4417354243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4253771719/10000000000 : ℝ)^4179 ≤ (32232023728879/100000000000000 : ℝ)^3155 := by
    have hnat : (4253771719 : ℕ)^4179*100000000000000^3155 ≤ 32232023728879^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4253771719 10000000000 32232023728879 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4417353083/10000000000 : ℝ)^4179 ≤ (33883982236563/100000000000000 : ℝ)^3155 := by
    have hnat : (4417353083 : ℕ)^4179*100000000000000^3155 ≤ 33883982236563^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4417353083 10000000000 33883982236563 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4417354243/10000000000 : ℝ)^4179 ≤ (33883994022479/100000000000000 : ℝ)^3155 := by
    have hnat : (4417354243 : ℕ)^4179*100000000000000^3155 ≤ 33883994022479^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4417354243 10000000000 33883994022479 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4253771719/10000000000 : ℝ), (4417353083/10000000000 : ℝ), (4417354243/10000000000 : ℝ)] ![(32232023728879/100000000000000 : ℝ), (33883982236563/100000000000000 : ℝ), (33883994022479/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4253771719/10000000000 : ℝ)|^4179 ≤ (32232023728879/100000000000000 : ℝ)^3155
        have hw : |(4253771719/10000000000 : ℝ)|=(4253771719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4417353083/10000000000 : ℝ)|^4179 ≤ (33883982236563/100000000000000 : ℝ)^3155
        have hw : |(4417353083/10000000000 : ℝ)|=(4417353083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4417354243/10000000000 : ℝ)|^4179 ≤ (33883994022479/100000000000000 : ℝ)^3155
        have hw : |(4417354243/10000000000 : ℝ)|=(4417354243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_box_8 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1115194753/5000000000 : ℝ)*x 0 + (1043415701/2000000000 : ℝ)*x 1 + (5385591361/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1115194753/5000000000 : ℝ)^4179 ≤ (13705296359137/100000000000000 : ℝ)^3155 := by
    have hnat : (1115194753 : ℕ)^4179*100000000000000^3155 ≤ 13705296359137^3155*5000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1115194753 5000000000 13705296359137 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043415701/2000000000 : ℝ)^4179 ≤ (4223907680327/10000000000000 : ℝ)^3155 := by
    have hnat : (1043415701 : ℕ)^4179*10000000000000^3155 ≤ 4223907680327^3155*2000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043415701 2000000000 4223907680327 10000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5385591361/10000000000 : ℝ)^4179 ≤ (11013906704531/25000000000000 : ℝ)^3155 := by
    have hnat : (5385591361 : ℕ)^4179*25000000000000^3155 ≤ 11013906704531^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385591361 10000000000 11013906704531 25000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1115194753/5000000000 : ℝ), (1043415701/2000000000 : ℝ), (5385591361/10000000000 : ℝ)] ![(13705296359137/100000000000000 : ℝ), (4223907680327/10000000000000 : ℝ), (11013906704531/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1115194753/5000000000 : ℝ)|^4179 ≤ (13705296359137/100000000000000 : ℝ)^3155
        have hw : |(-1115194753/5000000000 : ℝ)|=(1115194753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043415701/2000000000 : ℝ)|^4179 ≤ (4223907680327/10000000000000 : ℝ)^3155
        have hw : |(1043415701/2000000000 : ℝ)|=(1043415701/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5385591361/10000000000 : ℝ)|^4179 ≤ (11013906704531/25000000000000 : ℝ)^3155
        have hw : |(5385591361/10000000000 : ℝ)|=(5385591361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_box_9 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (132235081/250000000 : ℝ)*x 0 + (-1067100857/5000000000 : ℝ)*x 1 + (1346397859/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132235081/250000000 : ℝ)^4179 ≤ (21508216286383/50000000000000 : ℝ)^3155 := by
    have hnat : (132235081 : ℕ)^4179*50000000000000^3155 ≤ 21508216286383^3155*250000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132235081 250000000 21508216286383 50000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1067100857/5000000000 : ℝ)^4179 ≤ (3231984943983/25000000000000 : ℝ)^3155 := by
    have hnat : (1067100857 : ℕ)^4179*25000000000000^3155 ≤ 3231984943983^3155*5000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1067100857 5000000000 3231984943983 25000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1346397859/2500000000 : ℝ)^4179 ≤ (11013906907693/25000000000000 : ℝ)^3155 := by
    have hnat : (1346397859 : ℕ)^4179*25000000000000^3155 ≤ 11013906907693^3155*2500000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346397859 2500000000 11013906907693 25000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132235081/250000000 : ℝ), (-1067100857/5000000000 : ℝ), (1346397859/2500000000 : ℝ)] ![(21508216286383/50000000000000 : ℝ), (3231984943983/25000000000000 : ℝ), (11013906907693/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132235081/250000000 : ℝ)|^4179 ≤ (21508216286383/50000000000000 : ℝ)^3155
        have hw : |(132235081/250000000 : ℝ)|=(132235081/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1067100857/5000000000 : ℝ)|^4179 ≤ (3231984943983/25000000000000 : ℝ)^3155
        have hw : |(-1067100857/5000000000 : ℝ)|=(1067100857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1346397859/2500000000 : ℝ)|^4179 ≤ (11013906907693/25000000000000 : ℝ)^3155
        have hw : |(1346397859/2500000000 : ℝ)|=(1346397859/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_box_10 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5289403321/10000000000 : ℝ)*x 0 + (269279581/500000000 : ℝ)*x 1 + (-2134201357/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289403321/10000000000 : ℝ)^4179 ≤ (43016433445307/100000000000000 : ℝ)^3155 := by
    have hnat : (5289403321 : ℕ)^4179*100000000000000^3155 ≤ 43016433445307^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289403321 10000000000 43016433445307 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269279581/500000000 : ℝ)^4179 ≤ (44055629624467/100000000000000 : ℝ)^3155 := by
    have hnat : (269279581 : ℕ)^4179*100000000000000^3155 ≤ 44055629624467^3155*500000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269279581 500000000 44055629624467 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2134201357/10000000000 : ℝ)^4179 ≤ (12927936911523/100000000000000 : ℝ)^3155 := by
    have hnat : (2134201357 : ℕ)^4179*100000000000000^3155 ≤ 12927936911523^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2134201357 10000000000 12927936911523 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289403321/10000000000 : ℝ), (269279581/500000000 : ℝ), (-2134201357/10000000000 : ℝ)] ![(43016433445307/100000000000000 : ℝ), (44055629624467/100000000000000 : ℝ), (12927936911523/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289403321/10000000000 : ℝ)|^4179 ≤ (43016433445307/100000000000000 : ℝ)^3155
        have hw : |(5289403321/10000000000 : ℝ)|=(5289403321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269279581/500000000 : ℝ)|^4179 ≤ (44055629624467/100000000000000 : ℝ)^3155
        have hw : |(269279581/500000000 : ℝ)|=(269279581/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2134201357/10000000000 : ℝ)|^4179 ≤ (12927936911523/100000000000000 : ℝ)^3155
        have hw : |(-2134201357/10000000000 : ℝ)|=(2134201357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_box_11 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4490325521/10000000000 : ℝ)*x 0 + (2149478421/5000000000 : ℝ)*x 1 + (2149478463/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4490325521/10000000000 : ℝ)^4179 ≤ (34627382332159/100000000000000 : ℝ)^3155 := by
    have hnat : (4490325521 : ℕ)^4179*100000000000000^3155 ≤ 34627382332159^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4490325521 10000000000 34627382332159 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2149478421/5000000000 : ℝ)^4179 ≤ (16343154205087/50000000000000 : ℝ)^3155 := by
    have hnat : (2149478421 : ℕ)^4179*50000000000000^3155 ≤ 16343154205087^3155*5000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149478421 5000000000 16343154205087 50000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2149478463/5000000000 : ℝ)^4179 ≤ (6537261851229/20000000000000 : ℝ)^3155 := by
    have hnat : (2149478463 : ℕ)^4179*20000000000000^3155 ≤ 6537261851229^3155*5000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149478463 5000000000 6537261851229 20000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4490325521/10000000000 : ℝ), (2149478421/5000000000 : ℝ), (2149478463/5000000000 : ℝ)] ![(34627382332159/100000000000000 : ℝ), (16343154205087/50000000000000 : ℝ), (6537261851229/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4490325521/10000000000 : ℝ)|^4179 ≤ (34627382332159/100000000000000 : ℝ)^3155
        have hw : |(4490325521/10000000000 : ℝ)|=(4490325521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2149478421/5000000000 : ℝ)|^4179 ≤ (16343154205087/50000000000000 : ℝ)^3155
        have hw : |(2149478421/5000000000 : ℝ)|=(2149478421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2149478463/5000000000 : ℝ)|^4179 ≤ (6537261851229/20000000000000 : ℝ)^3155
        have hw : |(2149478463/5000000000 : ℝ)|=(2149478463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_box_12 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1041585797/5000000000 : ℝ)*x 0 + (1087813809/2000000000 : ℝ)*x 1 + (5273378803/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1041585797/5000000000 : ℝ)^4179 ≤ (12520094161777/100000000000000 : ℝ)^3155 := by
    have hnat : (1041585797 : ℕ)^4179*100000000000000^3155 ≤ 12520094161777^3155*5000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041585797 5000000000 12520094161777 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1087813809/2000000000 : ℝ)^4179 ≤ (11159001323923/25000000000000 : ℝ)^3155 := by
    have hnat : (1087813809 : ℕ)^4179*25000000000000^3155 ≤ 11159001323923^3155*2000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087813809 2000000000 11159001323923 25000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5273378803/10000000000 : ℝ)^4179 ≤ (42843900521109/100000000000000 : ℝ)^3155 := by
    have hnat : (5273378803 : ℕ)^4179*100000000000000^3155 ≤ 42843900521109^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5273378803 10000000000 42843900521109 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1041585797/5000000000 : ℝ), (1087813809/2000000000 : ℝ), (5273378803/10000000000 : ℝ)] ![(12520094161777/100000000000000 : ℝ), (11159001323923/25000000000000 : ℝ), (42843900521109/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1041585797/5000000000 : ℝ)|^4179 ≤ (12520094161777/100000000000000 : ℝ)^3155
        have hw : |(-1041585797/5000000000 : ℝ)|=(1041585797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1087813809/2000000000 : ℝ)|^4179 ≤ (11159001323923/25000000000000 : ℝ)^3155
        have hw : |(1087813809/2000000000 : ℝ)|=(1087813809/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5273378803/10000000000 : ℝ)|^4179 ≤ (42843900521109/100000000000000 : ℝ)^3155
        have hw : |(5273378803/10000000000 : ℝ)|=(5273378803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_box_13 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2684320889/5000000000 : ℝ)*x 0 + (-2178434549/10000000000 : ℝ)*x 1 + (5273378809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684320889/5000000000 : ℝ)^4179 ≤ (5484008355447/12500000000000 : ℝ)^3155 := by
    have hnat : (2684320889 : ℕ)^4179*12500000000000^3155 ≤ 5484008355447^3155*5000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684320889 5000000000 5484008355447 12500000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2178434549/10000000000 : ℝ)^4179 ≤ (13284032552191/100000000000000 : ℝ)^3155 := by
    have hnat : (2178434549 : ℕ)^4179*100000000000000^3155 ≤ 13284032552191^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178434549 10000000000 13284032552191 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5273378809/10000000000 : ℝ)^4179 ≤ (21421950292839/50000000000000 : ℝ)^3155 := by
    have hnat : (5273378809 : ℕ)^4179*50000000000000^3155 ≤ 21421950292839^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5273378809 10000000000 21421950292839 50000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684320889/5000000000 : ℝ), (-2178434549/10000000000 : ℝ), (5273378809/10000000000 : ℝ)] ![(5484008355447/12500000000000 : ℝ), (13284032552191/100000000000000 : ℝ), (21421950292839/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684320889/5000000000 : ℝ)|^4179 ≤ (5484008355447/12500000000000 : ℝ)^3155
        have hw : |(2684320889/5000000000 : ℝ)|=(2684320889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2178434549/10000000000 : ℝ)|^4179 ≤ (13284032552191/100000000000000 : ℝ)^3155
        have hw : |(-2178434549/10000000000 : ℝ)|=(2178434549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5273378809/10000000000 : ℝ)|^4179 ≤ (21421950292839/50000000000000 : ℝ)^3155
        have hw : |(5273378809/10000000000 : ℝ)|=(5273378809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_box_14 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5368641769/10000000000 : ℝ)*x 0 + (2636689409/5000000000 : ℝ)*x 1 + (-2178434549/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368641769/10000000000 : ℝ)^4179 ≤ (21936033373079/50000000000000 : ℝ)^3155 := by
    have hnat : (5368641769 : ℕ)^4179*50000000000000^3155 ≤ 21936033373079^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368641769 10000000000 21936033373079 50000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2636689409/5000000000 : ℝ)^4179 ≤ (42843900682531/100000000000000 : ℝ)^3155 := by
    have hnat : (2636689409 : ℕ)^4179*100000000000000^3155 ≤ 42843900682531^3155*5000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636689409 5000000000 42843900682531 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2178434549/10000000000 : ℝ)^4179 ≤ (13284032552191/100000000000000 : ℝ)^3155 := by
    have hnat : (2178434549 : ℕ)^4179*100000000000000^3155 ≤ 13284032552191^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178434549 10000000000 13284032552191 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368641769/10000000000 : ℝ), (2636689409/5000000000 : ℝ), (-2178434549/10000000000 : ℝ)] ![(21936033373079/50000000000000 : ℝ), (42843900682531/100000000000000 : ℝ), (13284032552191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368641769/10000000000 : ℝ)|^4179 ≤ (21936033373079/50000000000000 : ℝ)^3155
        have hw : |(5368641769/10000000000 : ℝ)|=(5368641769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2636689409/5000000000 : ℝ)|^4179 ≤ (42843900682531/100000000000000 : ℝ)^3155
        have hw : |(2636689409/5000000000 : ℝ)|=(2636689409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2178434549/10000000000 : ℝ)|^4179 ≤ (13284032552191/100000000000000 : ℝ)^3155
        have hw : |(-2178434549/10000000000 : ℝ)|=(2178434549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_box_15 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (423524007/1000000000 : ℝ)*x 0 + (4426497149/10000000000 : ℝ)*x 1 + (34582009/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (423524007/1000000000 : ℝ)^4179 ≤ (32046160696879/100000000000000 : ℝ)^3155 := by
    have hnat : (423524007 : ℕ)^4179*100000000000000^3155 ≤ 32046160696879^3155*1000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423524007 1000000000 32046160696879 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4426497149/10000000000 : ℝ)^4179 ≤ (33976919630583/100000000000000 : ℝ)^3155 := by
    have hnat : (4426497149 : ℕ)^4179*100000000000000^3155 ≤ 33976919630583^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4426497149 10000000000 33976919630583 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (34582009/78125000 : ℝ)^4179 ≤ (8494229915271/25000000000000 : ℝ)^3155 := by
    have hnat : (34582009 : ℕ)^4179*25000000000000^3155 ≤ 8494229915271^3155*78125000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34582009 78125000 8494229915271 25000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(423524007/1000000000 : ℝ), (4426497149/10000000000 : ℝ), (34582009/78125000 : ℝ)] ![(32046160696879/100000000000000 : ℝ), (33976919630583/100000000000000 : ℝ), (8494229915271/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(423524007/1000000000 : ℝ)|^4179 ≤ (32046160696879/100000000000000 : ℝ)^3155
        have hw : |(423524007/1000000000 : ℝ)|=(423524007/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4426497149/10000000000 : ℝ)|^4179 ≤ (33976919630583/100000000000000 : ℝ)^3155
        have hw : |(4426497149/10000000000 : ℝ)|=(4426497149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(34582009/78125000 : ℝ)|^4179 ≤ (8494229915271/25000000000000 : ℝ)^3155
        have hw : |(34582009/78125000 : ℝ)|=(34582009/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1165_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18740333/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7031/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1423/12500 : ℝ)*pair X i i ≤ pair X i h) :
    -(31117/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(14829/25000 : ℝ) ∧ (39939/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (10397/12500 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7031/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1423/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7031/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1423/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7031/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1423/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7031/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1423/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7031/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1423/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7031/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1423/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1423/12500 : ℝ) ^ (8357/2048 : ℝ) ≤ (14097711500418919/100000000000000000000 : ℝ) := by
    have hpowers : (1423/12500 : ℝ)^8357 ≤ (14097711500418919/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1423 : ℕ)^8357*100000000000000000000^2048 ≤ 14097711500418919^2048*12500^8357 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1423 12500 14097711500418919 100000000000000000000 8357 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1423/12500 : ℝ)) (X := (14097711500418919/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8357 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7031/50000 : ℝ) ^ (8357/2048 : ℝ) ≤ (33384862389369967/100000000000000000000 : ℝ) := by
    have hpowers : (7031/50000 : ℝ)^8357 ≤ (33384862389369967/100000000000000000000 : ℝ)^2048 := by
      have hnat : (7031 : ℕ)^8357*100000000000000000000^2048 ≤ 33384862389369967^2048*50000^8357 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7031 50000 33384862389369967 100000000000000000000 8357 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7031/50000 : ℝ)) (X := (33384862389369967/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8357 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014097711500418919/50000000000000000000 : ℝ) ≤ (400027635793551/400000000000000 : ℝ) ^ (8357/2048 : ℝ) := by
    have hpowers : (50014097711500418919/50000000000000000000 : ℝ)^2048 ≤ (400027635793551/400000000000000 : ℝ)^8357 := by
      have hnat : (50014097711500418919 : ℕ)^2048*400000000000000^8357 ≤ 400027635793551^8357*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014097711500418919 50000000000000000000 400027635793551 400000000000000 2048 8357 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400027635793551/400000000000000 : ℝ)) (X := (50014097711500418919/50000000000000000000 : ℝ)) (by norm_num) 8357 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023741286944894443/50000000000000000000 : ℝ) ≤ (1250145427316801/1250000000000000 : ℝ) ^ (8357/2048 : ℝ) := by
    have hpowers : (50023741286944894443/50000000000000000000 : ℝ)^2048 ≤ (1250145427316801/1250000000000000 : ℝ)^8357 := by
      have hnat : (50023741286944894443 : ℕ)^2048*1250000000000000^8357 ≤ 1250145427316801^8357*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023741286944894443 50000000000000000000 1250145427316801 1250000000000000 2048 8357 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250145427316801/1250000000000000 : ℝ)) (X := (50023741286944894443/50000000000000000000 : ℝ)) (by norm_num) 8357 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033384862389369967/50000000000000000000 : ℝ) ≤ (10001635942230041/10000000000000000 : ℝ) ^ (8357/2048 : ℝ) := by
    have hpowers : (50033384862389369967/50000000000000000000 : ℝ)^2048 ≤ (10001635942230041/10000000000000000 : ℝ)^8357 := by
      have hnat : (50033384862389369967 : ℕ)^2048*10000000000000000^8357 ≤ 10001635942230041^8357*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033384862389369967 50000000000000000000 10001635942230041 10000000000000000 2048 8357 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001635942230041/10000000000000000 : ℝ)) (X := (50033384862389369967/50000000000000000000 : ℝ)) (by norm_num) 8357 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14097711500418919/100000000000000000000 : ℝ) ≤ ((13385545898438033653/13390000000000000000 : ℝ)+2*(472523695633/267800000000000 : ℝ)*(1423/12500 : ℝ))^(8357/2048 : ℝ) := by
    rw [show (13385545898438033653/13390000000000000000 : ℝ)+2*(472523695633/267800000000000 : ℝ)*(1423/12500 : ℝ)=(400027635793551/400000000000000 : ℝ) by norm_num, show 1+2*(14097711500418919/100000000000000000000 : ℝ)=(50014097711500418919/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33384862389369967/100000000000000000000 : ℝ)+(14097711500418919/100000000000000000000 : ℝ) ≤ ((13385545898438033653/13390000000000000000 : ℝ)+(472523695633/267800000000000 : ℝ)*((7031/50000 : ℝ)+(1423/12500 : ℝ)))^(8357/2048 : ℝ) := by
    rw [show (13385545898438033653/13390000000000000000 : ℝ)+(472523695633/267800000000000 : ℝ)*((7031/50000 : ℝ)+(1423/12500 : ℝ))=(1250145427316801/1250000000000000 : ℝ) by norm_num, show 1+(33384862389369967/100000000000000000000 : ℝ)+(14097711500418919/100000000000000000000 : ℝ)=(50023741286944894443/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33384862389369967/100000000000000000000 : ℝ) ≤ ((13385545898438033653/13390000000000000000 : ℝ)+2*(472523695633/267800000000000 : ℝ)*(7031/50000 : ℝ))^(8357/2048 : ℝ) := by
    rw [show (13385545898438033653/13390000000000000000 : ℝ)+2*(472523695633/267800000000000 : ℝ)*(7031/50000 : ℝ)=(10001635942230041/10000000000000000 : ℝ) by norm_num, show 1+2*(33384862389369967/100000000000000000000 : ℝ)=(50033384862389369967/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13385545898438033653/13390000000000000000 : ℝ)*(X 1 0+X 2 0)+(472523695633/267800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8357/2048 : ℝ)) (lo := (1423/12500 : ℝ)) (hi := (7031/50000 : ℝ)) (c := (13385545898438033653/13390000000000000000 : ℝ)) (alpha := (472523695633/267800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13385545898438033653/13390000000000000000 : ℝ)*(X 0 1+X 2 1)+(472523695633/267800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8357/2048 : ℝ)) (lo := (1423/12500 : ℝ)) (hi := (7031/50000 : ℝ)) (c := (13385545898438033653/13390000000000000000 : ℝ)) (alpha := (472523695633/267800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13385545898438033653/13390000000000000000 : ℝ)*(X 0 2+X 1 2)+(472523695633/267800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8357/2048 : ℝ)) (lo := (1423/12500 : ℝ)) (hi := (7031/50000 : ℝ)) (c := (13385545898438033653/13390000000000000000 : ℝ)) (alpha := (472523695633/267800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1014897067/5000000000 : ℝ)*X 0 0+(5375981183/10000000000 : ℝ)*X 0 1+(5375981103/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5296192563/10000000000 : ℝ)*X 1 0+(-1069029129/5000000000 : ℝ)*X 1 1+(5375980907/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((132404829/250000000 : ℝ)*X 2 0+(5375980561/10000000000 : ℝ)*X 2 1+(-1069028961/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2234373649/5000000000 : ℝ)*X 0 0+(43098867/100000000 : ℝ)*X 0 1+(4309886379/10000000000 : ℝ)*X 0 2+(2234373649/5000000000 : ℝ)*X 1 0+(43098867/100000000 : ℝ)*X 1 1+(4309886379/10000000000 : ℝ)*X 1 2+(2234373649/5000000000 : ℝ)*X 2 0+(43098867/100000000 : ℝ)*X 2 1+(4309886379/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1141730707/5000000000 : ℝ)*X 0 0+(5281427969/10000000000 : ℝ)*X 0 1+(5281427629/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5362960969/10000000000 : ℝ)*X 1 0+(-1087659657/5000000000 : ℝ)*X 1 1+(2640713689/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5362960227/10000000000 : ℝ)*X 2 0+(5281427571/10000000000 : ℝ)*X 2 1+(-543830013/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4253771719/10000000000 : ℝ)*X 0 0+(4417353083/10000000000 : ℝ)*X 0 1+(4417354243/10000000000 : ℝ)*X 0 2+(4253771719/10000000000 : ℝ)*X 1 0+(4417353083/10000000000 : ℝ)*X 1 1+(4417354243/10000000000 : ℝ)*X 1 2+(4253771719/10000000000 : ℝ)*X 2 0+(4417353083/10000000000 : ℝ)*X 2 1+(4417354243/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1115194753/5000000000 : ℝ)*X 0 0+(1043415701/2000000000 : ℝ)*X 0 1+(5385591361/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((132235081/250000000 : ℝ)*X 1 0+(-1067100857/5000000000 : ℝ)*X 1 1+(1346397859/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5289403321/10000000000 : ℝ)*X 2 0+(269279581/500000000 : ℝ)*X 2 1+(-2134201357/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4490325521/10000000000 : ℝ)*X 0 0+(2149478421/5000000000 : ℝ)*X 0 1+(2149478463/5000000000 : ℝ)*X 0 2+(4490325521/10000000000 : ℝ)*X 1 0+(2149478421/5000000000 : ℝ)*X 1 1+(2149478463/5000000000 : ℝ)*X 1 2+(4490325521/10000000000 : ℝ)*X 2 0+(2149478421/5000000000 : ℝ)*X 2 1+(2149478463/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1041585797/5000000000 : ℝ)*X 0 0+(1087813809/2000000000 : ℝ)*X 0 1+(5273378803/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2684320889/5000000000 : ℝ)*X 1 0+(-2178434549/10000000000 : ℝ)*X 1 1+(5273378809/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5368641769/10000000000 : ℝ)*X 2 0+(2636689409/5000000000 : ℝ)*X 2 1+(-2178434549/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((423524007/1000000000 : ℝ)*X 0 0+(4426497149/10000000000 : ℝ)*X 0 1+(34582009/78125000 : ℝ)*X 0 2+(423524007/1000000000 : ℝ)*X 1 0+(4426497149/10000000000 : ℝ)*X 1 1+(34582009/78125000 : ℝ)*X 1 2+(423524007/1000000000 : ℝ)*X 2 0+(4426497149/10000000000 : ℝ)*X 2 1+(34582009/78125000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31117/50000 : ℝ) ≤ (-208319886372394839613450370972961/334750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5550793/100000000000000 : ℝ)*(lower0) + (28382093/100000000000000 : ℝ)*(lower3) + (291549153/50000000000000 : ℝ)*(lower4) + (1969801709029121/50000000000000 : ℝ)*(major0) + (1969801709029121/50000000000000 : ℝ)*(major1) + (1969801709029121/50000000000000 : ℝ)*(major2) + (5085027839/50000000000000 : ℝ)*(sp1) + (7782441097/20000000000000 : ℝ)*(sp2) + (7410469601/100000000000000 : ℝ)*(sp3) + (2636091953368999/50000000000000 : ℝ)*(sp4) + (1318045853312299/25000000000000 : ℝ)*(sp5) + (5272154671099389/100000000000000 : ℝ)*(sp6) + (1313874834856457/50000000000000 : ℝ)*(sp7) + (15482507/160000000000 : ℝ)*(sp12) + (525551416036503/20000000000000 : ℝ)*(f.failure) + (2636096791652437/50000000000000 : ℝ)*(f.sum) + (45264464016097/6695000000000000000000000000 : ℝ)*base66 + (5260173319554159013/669500000000000000000000000000000 : ℝ)*base67 + (1064315504651340987/669500000000000000000000000000000 : ℝ)*base70 + (3614819040504340987/669500000000000000000000000000000 : ℝ)*base72 + (129171412699263/6695000000000000000000000000 : ℝ)*base73 + (3345657286207840987/669500000000000000000000000000000 : ℝ)*base76 + (1609218152921840987/669500000000000000000000000000000 : ℝ)*base78 + (11241298346047659013/669500000000000000000000000000000 : ℝ)*base79 + (734383308727/1673750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1375499/250000000000000000000 : ℝ)*base89 + (1375499/250000000000000000000 : ℝ)*base91 + (1375499/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (14829/25000 : ℝ) ≤ (30549160160485345487987165629287/51500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (24389989/12500000000000 : ℝ)*(upper0) + (31095527/20000000000000 : ℝ)*(upper3) + (16451969/4000000000000 : ℝ)*(upper4) + (4004110354348091/100000000000000 : ℝ)*(major0) + (4004110354348091/100000000000000 : ℝ)*(major1) + (4004110354348091/100000000000000 : ℝ)*(major2) + (664707922696589/12500000000000 : ℝ)*(sp0) + (332337072070251/6250000000000 : ℝ)*(sp1) + (5317531372395783/100000000000000 : ℝ)*(sp2) + (667661848953443/25000000000000 : ℝ)*(sp3) + (65009417/12500000000000 : ℝ)*(sp8) + (528805711/195312500000 : ℝ)*(sp9) + (26505850453/20000000000000 : ℝ)*(sp10) + (136492036627/100000000000000 : ℝ)*(sp11) + (2670783887850399/100000000000000 : ℝ)*(f.failure) + (332353993853003/6250000000000 : ℝ)*(f.sum) + (2463811070539/1030000000000000000000000000 : ℝ)*base66 + (316334520459573571/103000000000000000000000000000000 : ℝ)*base67 + (1233491993723573571/103000000000000000000000000000000 : ℝ)*base69 + (783477550943426429/103000000000000000000000000000000 : ℝ)*base72 + (37253793298691/1030000000000000000000000000 : ℝ)*base73 + (302854154027573571/103000000000000000000000000000000 : ℝ)*base75 + (272665495614426429/103000000000000000000000000000000 : ℝ)*base78 + (360432673998573571/103000000000000000000000000000000 : ℝ)*base79 + (4164523868661/1030000000000000000000000000 : ℝ)*base81 + (6057133/1250000000000000000000 : ℝ)*base90 + (6057133/1250000000000000000000 : ℝ)*base92 + (6057133/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (39939/50000 : ℝ) ≤ (16712558923216924970294599910613/20921875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (33703537/100000000000000 : ℝ)*(upper0) + (14774687/100000000000000 : ℝ)*(lower1) + (120235037/100000000000000 : ℝ)*(lower3) + (168131711/100000000000000 : ℝ)*(upper4) + (139744639670509/3125000000000 : ℝ)*(major0) + (139744639670509/3125000000000 : ℝ)*(major1) + (139744639670509/3125000000000 : ℝ)*(major2) + (78022448307/50000000000000 : ℝ)*(sp1) + (332862115231/100000000000000 : ℝ)*(sp2) + (27226286731/25000000000000 : ℝ)*(sp3) + (118685463991577/2000000000000 : ℝ)*(sp8) + (5934117154682237/100000000000000 : ℝ)*(sp9) + (5933940337463619/100000000000000 : ℝ)*(sp10) + (1491323952180701/50000000000000 : ℝ)*(sp11) + (1491378404754163/50000000000000 : ℝ)*(f.failure) + (118685463991577/2000000000000 : ℝ)*(f.sum) + (27423308868089/3347500000000000000000000000 : ℝ)*base66 + (333975343976426877/41843750000000000000000000000000 : ℝ)*base67 + (28687914820301877/41843750000000000000000000000000 : ℝ)*base69 + (194751352356635623/41843750000000000000000000000000 : ℝ)*base72 + (14266365883311/3347500000000000000000000000 : ℝ)*base73 + (399291465044676877/41843750000000000000000000000000 : ℝ)*base75 + (647129453240770627/41843750000000000000000000000000 : ℝ)*base77 + (737697312600833127/41843750000000000000000000000000 : ℝ)*base79 + (79521534253533/6695000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (2243721/625000000000000000000 : ℝ)*base90 + (2243721/625000000000000000000 : ℝ)*base92 + (2243721/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-10397/12500 : ℝ) ≤ (-22273830588123751438660353277509/26780000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5422479/100000000000000 : ℝ)*(lower2) + (703343/100000000000000 : ℝ)*(upper3) + (7928543/100000000000000 : ℝ)*(lower4) + (180275565268183/4000000000000 : ℝ)*(major0) + (180275565268183/4000000000000 : ℝ)*(major1) + (180275565268183/4000000000000 : ℝ)*(major2) + (842127303/100000000000000 : ℝ)*(sp0) + (1182369071/10000000000000 : ℝ)*(sp5) + (6672577271/100000000000000 : ℝ)*(sp6) + (84523363/25000000000000 : ℝ)*(sp8) + (6035358901019739/100000000000000 : ℝ)*(sp12) + (754418532193723/12500000000000 : ℝ)*(sp13) + (6035353408663223/100000000000000 : ℝ)*(sp14) + (1503071320725923/50000000000000 : ℝ)*(sp15) + (1503071320725923/50000000000000 : ℝ)*(f.failure) + (6035360081240493/100000000000000 : ℝ)*(f.sum) + (149699783399/21424000000000000000000000 : ℝ)*base65 + (370854979397967501/53560000000000000000000000000000 : ℝ)*base68 + (1084708196002287501/53560000000000000000000000000000 : ℝ)*base70 + (421479256390607501/53560000000000000000000000000000 : ℝ)*base72 + (3652721826951/2678000000000000000000000000 : ℝ)*base73 + (641711820525567501/53560000000000000000000000000000 : ℝ)*base76 + (413658856991327501/53560000000000000000000000000000 : ℝ)*base78 + (879315119987927501/53560000000000000000000000000000 : ℝ)*base80 + (8902241285299/2678000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (5002359/625000000000000000000 : ℝ)*base89 + (5002359/625000000000000000000 : ℝ)*base91 + (5002359/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1165_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18740333/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7031/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1423/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31117/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(14829/25000 : ℝ) else (39939/50000 : ℝ) ≤ X j i ∧ X j i ≤ (10397/12500 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1165_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1165_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18740333/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7031/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11383/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31117/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(14829/25000 : ℝ) else (39939/50000 : ℝ) ≤ X j i ∧ X j i ≤ (10397/12500 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1165_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1165_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18740333/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7031/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11383/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31117/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(14829/25000 : ℝ) else (39939/50000 : ℝ) ≤ X j i ∧ X j i ≤ (10397/12500 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1165_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
