-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1710_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:50:37.674302+00:00
-- url     : https://prove2.me/submissions/2cd73d6f-3579-4e69-9318-44cbee72a30c

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
theorem support_rectangle_w1710_box_0 (p : ℝ) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1093457857/10000000000 : ℝ)*x 0 + (5417225423/10000000000 : ℝ)*x 1 + (2708612869/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1093457857/10000000000 : ℝ)^5303 ≤ (643842217517/10000000000000 : ℝ)^4279 := by
    have hnat : (1093457857 : ℕ)^5303*10000000000000^4279 ≤ 643842217517^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093457857 10000000000 643842217517 10000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5417225423/10000000000 : ℝ)^5303 ≤ (23390393610023/50000000000000 : ℝ)^4279 := by
    have hnat : (5417225423 : ℕ)^5303*50000000000000^4279 ≤ 23390393610023^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417225423 10000000000 23390393610023 50000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2708612869/5000000000 : ℝ)^5303 ≤ (9356158118243/20000000000000 : ℝ)^4279 := by
    have hnat : (2708612869 : ℕ)^5303*20000000000000^4279 ≤ 9356158118243^4279*5000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708612869 5000000000 9356158118243 20000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5303/1024 : ℝ)) 5303 4279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1093457857/10000000000 : ℝ), (5417225423/10000000000 : ℝ), (2708612869/5000000000 : ℝ)] ![(643842217517/10000000000000 : ℝ), (23390393610023/50000000000000 : ℝ), (9356158118243/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1093457857/10000000000 : ℝ)|^5303 ≤ (643842217517/10000000000000 : ℝ)^4279
        have hw : |(-1093457857/10000000000 : ℝ)|=(1093457857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5417225423/10000000000 : ℝ)|^5303 ≤ (23390393610023/50000000000000 : ℝ)^4279
        have hw : |(5417225423/10000000000 : ℝ)|=(5417225423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2708612869/5000000000 : ℝ)|^5303 ≤ (9356158118243/20000000000000 : ℝ)^4279
        have hw : |(2708612869/5000000000 : ℝ)|=(2708612869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1710_box_1 (p : ℝ) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2612701941/5000000000 : ℝ)*x 0 + (-1365921771/10000000000 : ℝ)*x 1 + (5417225667/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2612701941/5000000000 : ℝ)^5303 ≤ (11184166663883/25000000000000 : ℝ)^4279 := by
    have hnat : (2612701941 : ℕ)^5303*25000000000000^4279 ≤ 11184166663883^4279*5000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2612701941 5000000000 11184166663883 25000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1365921771/10000000000 : ℝ)^5303 ≤ (8482543495353/100000000000000 : ℝ)^4279 := by
    have hnat : (1365921771 : ℕ)^5303*100000000000000^4279 ≤ 8482543495353^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1365921771 10000000000 8482543495353 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5417225667/10000000000 : ℝ)^5303 ≤ (11695197457841/25000000000000 : ℝ)^4279 := by
    have hnat : (5417225667 : ℕ)^5303*25000000000000^4279 ≤ 11695197457841^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417225667 10000000000 11695197457841 25000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5303/1024 : ℝ)) 5303 4279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2612701941/5000000000 : ℝ), (-1365921771/10000000000 : ℝ), (5417225667/10000000000 : ℝ)] ![(11184166663883/25000000000000 : ℝ), (8482543495353/100000000000000 : ℝ), (11695197457841/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2612701941/5000000000 : ℝ)|^5303 ≤ (11184166663883/25000000000000 : ℝ)^4279
        have hw : |(2612701941/5000000000 : ℝ)|=(2612701941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1365921771/10000000000 : ℝ)|^5303 ≤ (8482543495353/100000000000000 : ℝ)^4279
        have hw : |(-1365921771/10000000000 : ℝ)|=(1365921771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5417225667/10000000000 : ℝ)|^5303 ≤ (11695197457841/25000000000000 : ℝ)^4279
        have hw : |(5417225667/10000000000 : ℝ)|=(5417225667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1710_box_2 (p : ℝ) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2612701859/5000000000 : ℝ)*x 0 + (1354306469/2500000000 : ℝ)*x 1 + (-682960853/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2612701859/5000000000 : ℝ)^5303 ≤ (44736664915461/100000000000000 : ℝ)^4279 := by
    have hnat : (2612701859 : ℕ)^5303*100000000000000^4279 ≤ 44736664915461^4279*5000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2612701859 5000000000 44736664915461 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1354306469/2500000000 : ℝ)^5303 ≤ (11695198017027/25000000000000 : ℝ)^4279 := by
    have hnat : (1354306469 : ℕ)^5303*25000000000000^4279 ≤ 11695198017027^4279*2500000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354306469 2500000000 11695198017027 25000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (682960853/5000000000 : ℝ)^5303 ≤ (1060317874387/12500000000000 : ℝ)^4279 := by
    have hnat : (682960853 : ℕ)^5303*12500000000000^4279 ≤ 1060317874387^4279*5000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      682960853 5000000000 1060317874387 12500000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5303/1024 : ℝ)) 5303 4279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2612701859/5000000000 : ℝ), (1354306469/2500000000 : ℝ), (-682960853/5000000000 : ℝ)] ![(44736664915461/100000000000000 : ℝ), (11695198017027/25000000000000 : ℝ), (1060317874387/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2612701859/5000000000 : ℝ)|^5303 ≤ (44736664915461/100000000000000 : ℝ)^4279
        have hw : |(2612701859/5000000000 : ℝ)|=(2612701859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1354306469/2500000000 : ℝ)|^5303 ≤ (11695198017027/25000000000000 : ℝ)^4279
        have hw : |(1354306469/2500000000 : ℝ)|=(1354306469/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-682960853/5000000000 : ℝ)|^5303 ≤ (1060317874387/12500000000000 : ℝ)^4279
        have hw : |(-682960853/5000000000 : ℝ)|=(682960853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1710_box_3 (p : ℝ) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3589253/8000000 : ℝ)*x 0 + (3935412569/10000000000 : ℝ)*x 1 + (3935412467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3589253/8000000 : ℝ)^5303 ≤ (37035162456627/100000000000000 : ℝ)^4279 := by
    have hnat : (3589253 : ℕ)^5303*100000000000000^4279 ≤ 37035162456627^4279*8000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3589253 8000000 37035162456627 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3935412569/10000000000 : ℝ)^5303 ≤ (629648385429/2000000000000 : ℝ)^4279 := by
    have hnat : (3935412569 : ℕ)^5303*2000000000000^4279 ≤ 629648385429^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3935412569 10000000000 629648385429 2000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3935412467/10000000000 : ℝ)^5303 ≤ (31482418260203/100000000000000 : ℝ)^4279 := by
    have hnat : (3935412467 : ℕ)^5303*100000000000000^4279 ≤ 31482418260203^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3935412467 10000000000 31482418260203 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5303/1024 : ℝ)) 5303 4279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3589253/8000000 : ℝ), (3935412569/10000000000 : ℝ), (3935412467/10000000000 : ℝ)] ![(37035162456627/100000000000000 : ℝ), (629648385429/2000000000000 : ℝ), (31482418260203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3589253/8000000 : ℝ)|^5303 ≤ (37035162456627/100000000000000 : ℝ)^4279
        have hw : |(3589253/8000000 : ℝ)|=(3589253/8000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3935412569/10000000000 : ℝ)|^5303 ≤ (629648385429/2000000000000 : ℝ)^4279
        have hw : |(3935412569/10000000000 : ℝ)|=(3935412569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3935412467/10000000000 : ℝ)|^5303 ≤ (31482418260203/100000000000000 : ℝ)^4279
        have hw : |(3935412467/10000000000 : ℝ)|=(3935412467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1710_box_4 (p : ℝ) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-875666811/5000000000 : ℝ)*x 0 + (5177479251/10000000000 : ℝ)*x 1 + (5177479433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (875666811/5000000000 : ℝ)^5303 ≤ (5771262417713/50000000000000 : ℝ)^4279 := by
    have hnat : (875666811 : ℕ)^5303*50000000000000^4279 ≤ 5771262417713^4279*5000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      875666811 5000000000 5771262417713 50000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5177479251/10000000000 : ℝ)^5303 ≤ (44228736609329/100000000000000 : ℝ)^4279 := by
    have hnat : (5177479251 : ℕ)^5303*100000000000000^4279 ≤ 44228736609329^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177479251 10000000000 44228736609329 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5177479433/10000000000 : ℝ)^5303 ≤ (4422873853613/10000000000000 : ℝ)^4279 := by
    have hnat : (5177479433 : ℕ)^5303*10000000000000^4279 ≤ 4422873853613^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177479433 10000000000 4422873853613 10000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5303/1024 : ℝ)) 5303 4279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-875666811/5000000000 : ℝ), (5177479251/10000000000 : ℝ), (5177479433/10000000000 : ℝ)] ![(5771262417713/50000000000000 : ℝ), (44228736609329/100000000000000 : ℝ), (4422873853613/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-875666811/5000000000 : ℝ)|^5303 ≤ (5771262417713/50000000000000 : ℝ)^4279
        have hw : |(-875666811/5000000000 : ℝ)|=(875666811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5177479251/10000000000 : ℝ)|^5303 ≤ (44228736609329/100000000000000 : ℝ)^4279
        have hw : |(5177479251/10000000000 : ℝ)|=(5177479251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5177479433/10000000000 : ℝ)|^5303 ≤ (4422873853613/10000000000000 : ℝ)^4279
        have hw : |(5177479433/10000000000 : ℝ)|=(5177479433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1710_box_5 (p : ℝ) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1346998573/2500000000 : ℝ)*x 0 + (-294316191/2000000000 : ℝ)*x 1 + (2588739697/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1346998573/2500000000 : ℝ)^5303 ≤ (23234077152309/50000000000000 : ℝ)^4279 := by
    have hnat : (1346998573 : ℕ)^5303*50000000000000^4279 ≤ 23234077152309^4279*2500000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346998573 2500000000 23234077152309 50000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (294316191/2000000000 : ℝ)^5303 ≤ (4651553781619/50000000000000 : ℝ)^4279 := by
    have hnat : (294316191 : ℕ)^5303*50000000000000^4279 ≤ 4651553781619^4279*2000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      294316191 2000000000 4651553781619 50000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2588739697/5000000000 : ℝ)^5303 ≤ (11057184530811/25000000000000 : ℝ)^4279 := by
    have hnat : (2588739697 : ℕ)^5303*25000000000000^4279 ≤ 11057184530811^4279*5000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588739697 5000000000 11057184530811 25000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5303/1024 : ℝ)) 5303 4279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1346998573/2500000000 : ℝ), (-294316191/2000000000 : ℝ), (2588739697/5000000000 : ℝ)] ![(23234077152309/50000000000000 : ℝ), (4651553781619/50000000000000 : ℝ), (11057184530811/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1346998573/2500000000 : ℝ)|^5303 ≤ (23234077152309/50000000000000 : ℝ)^4279
        have hw : |(1346998573/2500000000 : ℝ)|=(1346998573/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-294316191/2000000000 : ℝ)|^5303 ≤ (4651553781619/50000000000000 : ℝ)^4279
        have hw : |(-294316191/2000000000 : ℝ)|=(294316191/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2588739697/5000000000 : ℝ)|^5303 ≤ (11057184530811/25000000000000 : ℝ)^4279
        have hw : |(2588739697/5000000000 : ℝ)|=(2588739697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1710_box_6 (p : ℝ) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2693997233/5000000000 : ℝ)*x 0 + (1035495861/2000000000 : ℝ)*x 1 + (-1471580837/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2693997233/5000000000 : ℝ)^5303 ≤ (23234078082189/50000000000000 : ℝ)^4279 := by
    have hnat : (2693997233 : ℕ)^5303*50000000000000^4279 ≤ 23234078082189^4279*5000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693997233 5000000000 23234078082189 50000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1035495861/2000000000 : ℝ)^5303 ≤ (44228737181017/100000000000000 : ℝ)^4279 := by
    have hnat : (1035495861 : ℕ)^5303*100000000000000^4279 ≤ 44228737181017^4279*2000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035495861 2000000000 44228737181017 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1471580837/10000000000 : ℝ)^5303 ≤ (4651553319371/50000000000000 : ℝ)^4279 := by
    have hnat : (1471580837 : ℕ)^5303*50000000000000^4279 ≤ 4651553319371^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1471580837 10000000000 4651553319371 50000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5303/1024 : ℝ)) 5303 4279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2693997233/5000000000 : ℝ), (1035495861/2000000000 : ℝ), (-1471580837/10000000000 : ℝ)] ![(23234078082189/50000000000000 : ℝ), (44228737181017/100000000000000 : ℝ), (4651553319371/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2693997233/5000000000 : ℝ)|^5303 ≤ (23234078082189/50000000000000 : ℝ)^4279
        have hw : |(2693997233/5000000000 : ℝ)|=(2693997233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1035495861/2000000000 : ℝ)|^5303 ≤ (44228737181017/100000000000000 : ℝ)^4279
        have hw : |(1035495861/2000000000 : ℝ)|=(1035495861/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1471580837/10000000000 : ℝ)|^5303 ≤ (4651553319371/50000000000000 : ℝ)^4279
        have hw : |(-1471580837/10000000000 : ℝ)|=(1471580837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1710_box_7 (p : ℝ) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3707204087/10000000000 : ℝ)*x 0 + (4324266203/10000000000 : ℝ)*x 1 + (864853309/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3707204087/10000000000 : ℝ)^5303 ≤ (29235852784537/100000000000000 : ℝ)^4279 := by
    have hnat : (3707204087 : ℕ)^5303*100000000000000^4279 ≤ 29235852784537^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3707204087 10000000000 29235852784537 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4324266203/10000000000 : ℝ)^5303 ≤ (35382071864323/100000000000000 : ℝ)^4279 := by
    have hnat : (4324266203 : ℕ)^5303*100000000000000^4279 ≤ 35382071864323^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4324266203 10000000000 35382071864323 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (864853309/2000000000 : ℝ)^5303 ≤ (353820753323/1000000000000 : ℝ)^4279 := by
    have hnat : (864853309 : ℕ)^5303*1000000000000^4279 ≤ 353820753323^4279*2000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      864853309 2000000000 353820753323 1000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5303/1024 : ℝ)) 5303 4279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3707204087/10000000000 : ℝ), (4324266203/10000000000 : ℝ), (864853309/2000000000 : ℝ)] ![(29235852784537/100000000000000 : ℝ), (35382071864323/100000000000000 : ℝ), (353820753323/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3707204087/10000000000 : ℝ)|^5303 ≤ (29235852784537/100000000000000 : ℝ)^4279
        have hw : |(3707204087/10000000000 : ℝ)|=(3707204087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4324266203/10000000000 : ℝ)|^5303 ≤ (35382071864323/100000000000000 : ℝ)^4279
        have hw : |(4324266203/10000000000 : ℝ)|=(4324266203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(864853309/2000000000 : ℝ)|^5303 ≤ (353820753323/1000000000000 : ℝ)^4279
        have hw : |(864853309/2000000000 : ℝ)|=(864853309/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1710_box_8 (p : ℝ) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-804919027/5000000000 : ℝ)*x 0 + (2500264529/5000000000 : ℝ)*x 1 + (2729984437/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (804919027/5000000000 : ℝ)^5303 ≤ (5199105469941/50000000000000 : ℝ)^4279 := by
    have hnat : (804919027 : ℕ)^5303*50000000000000^4279 ≤ 5199105469941^4279*5000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      804919027 5000000000 5199105469941 50000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2500264529/5000000000 : ℝ)^5303 ≤ (42363125116583/100000000000000 : ℝ)^4279 := by
    have hnat : (2500264529 : ℕ)^5303*100000000000000^4279 ≤ 42363125116583^4279*5000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2500264529 5000000000 42363125116583 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2729984437/5000000000 : ℝ)^5303 ≤ (47238663927373/100000000000000 : ℝ)^4279 := by
    have hnat : (2729984437 : ℕ)^5303*100000000000000^4279 ≤ 47238663927373^4279*5000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2729984437 5000000000 47238663927373 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5303/1024 : ℝ)) 5303 4279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-804919027/5000000000 : ℝ), (2500264529/5000000000 : ℝ), (2729984437/5000000000 : ℝ)] ![(5199105469941/50000000000000 : ℝ), (42363125116583/100000000000000 : ℝ), (47238663927373/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-804919027/5000000000 : ℝ)|^5303 ≤ (5199105469941/50000000000000 : ℝ)^4279
        have hw : |(-804919027/5000000000 : ℝ)|=(804919027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2500264529/5000000000 : ℝ)|^5303 ≤ (42363125116583/100000000000000 : ℝ)^4279
        have hw : |(2500264529/5000000000 : ℝ)|=(2500264529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2729984437/5000000000 : ℝ)|^5303 ≤ (47238663927373/100000000000000 : ℝ)^4279
        have hw : |(2729984437/5000000000 : ℝ)|=(2729984437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1710_box_9 (p : ℝ) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (649554429/1250000000 : ℝ)*x 0 + (-1346304367/10000000000 : ℝ)*x 1 + (34124807/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (649554429/1250000000 : ℝ)^5303 ≤ (44429510111699/100000000000000 : ℝ)^4279 := by
    have hnat : (649554429 : ℕ)^5303*100000000000000^4279 ≤ 44429510111699^4279*1250000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      649554429 1250000000 44429510111699 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1346304367/10000000000 : ℝ)^5303 ≤ (2082955825873/25000000000000 : ℝ)^4279 := by
    have hnat : (1346304367 : ℕ)^5303*25000000000000^4279 ≤ 2082955825873^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346304367 10000000000 2082955825873 25000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (34124807/62500000 : ℝ)^5303 ≤ (11809666641263/25000000000000 : ℝ)^4279 := by
    have hnat : (34124807 : ℕ)^5303*25000000000000^4279 ≤ 11809666641263^4279*62500000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34124807 62500000 11809666641263 25000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5303/1024 : ℝ)) 5303 4279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(649554429/1250000000 : ℝ), (-1346304367/10000000000 : ℝ), (34124807/62500000 : ℝ)] ![(44429510111699/100000000000000 : ℝ), (2082955825873/25000000000000 : ℝ), (11809666641263/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(649554429/1250000000 : ℝ)|^5303 ≤ (44429510111699/100000000000000 : ℝ)^4279
        have hw : |(649554429/1250000000 : ℝ)|=(649554429/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1346304367/10000000000 : ℝ)|^5303 ≤ (2082955825873/25000000000000 : ℝ)^4279
        have hw : |(-1346304367/10000000000 : ℝ)|=(1346304367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(34124807/62500000 : ℝ)|^5303 ≤ (11809666641263/25000000000000 : ℝ)^4279
        have hw : |(34124807/62500000 : ℝ)|=(34124807/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1710_box_10 (p : ℝ) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5196435923/10000000000 : ℝ)*x 0 + (1364992159/2500000000 : ℝ)*x 1 + (-673152183/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5196435923/10000000000 : ℝ)^5303 ≤ (5553689414297/12500000000000 : ℝ)^4279 := by
    have hnat : (5196435923 : ℕ)^5303*12500000000000^4279 ≤ 5553689414297^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196435923 10000000000 5553689414297 12500000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1364992159/2500000000 : ℝ)^5303 ≤ (47238661375473/100000000000000 : ℝ)^4279 := by
    have hnat : (1364992159 : ℕ)^5303*100000000000000^4279 ≤ 47238661375473^4279*2500000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1364992159 2500000000 47238661375473 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (673152183/5000000000 : ℝ)^5303 ≤ (4165911647911/50000000000000 : ℝ)^4279 := by
    have hnat : (673152183 : ℕ)^5303*50000000000000^4279 ≤ 4165911647911^4279*5000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673152183 5000000000 4165911647911 50000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5303/1024 : ℝ)) 5303 4279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5196435923/10000000000 : ℝ), (1364992159/2500000000 : ℝ), (-673152183/5000000000 : ℝ)] ![(5553689414297/12500000000000 : ℝ), (47238661375473/100000000000000 : ℝ), (4165911647911/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5196435923/10000000000 : ℝ)|^5303 ≤ (5553689414297/12500000000000 : ℝ)^4279
        have hw : |(5196435923/10000000000 : ℝ)|=(5196435923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1364992159/2500000000 : ℝ)|^5303 ≤ (47238661375473/100000000000000 : ℝ)^4279
        have hw : |(1364992159/2500000000 : ℝ)|=(1364992159/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-673152183/5000000000 : ℝ)|^5303 ≤ (4165911647911/50000000000000 : ℝ)^4279
        have hw : |(-673152183/5000000000 : ℝ)|=(673152183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1710_box_11 (p : ℝ) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2310265729/5000000000 : ℝ)*x 0 + (3865902439/10000000000 : ℝ)*x 1 + (3865903443/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2310265729/5000000000 : ℝ)^5303 ≤ (7682099715183/20000000000000 : ℝ)^4279 := by
    have hnat : (2310265729 : ℕ)^5303*20000000000000^4279 ≤ 7682099715183^4279*5000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2310265729 5000000000 7682099715183 20000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3865902439/10000000000 : ℝ)^5303 ≤ (30794745749927/100000000000000 : ℝ)^4279 := by
    have hnat : (3865902439 : ℕ)^5303*100000000000000^4279 ≤ 30794745749927^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3865902439 10000000000 30794745749927 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3865903443/10000000000 : ℝ)^5303 ≤ (15397377830707/50000000000000 : ℝ)^4279 := by
    have hnat : (3865903443 : ℕ)^5303*50000000000000^4279 ≤ 15397377830707^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3865903443 10000000000 15397377830707 50000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5303/1024 : ℝ)) 5303 4279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2310265729/5000000000 : ℝ), (3865902439/10000000000 : ℝ), (3865903443/10000000000 : ℝ)] ![(7682099715183/20000000000000 : ℝ), (30794745749927/100000000000000 : ℝ), (15397377830707/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2310265729/5000000000 : ℝ)|^5303 ≤ (7682099715183/20000000000000 : ℝ)^4279
        have hw : |(2310265729/5000000000 : ℝ)|=(2310265729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3865902439/10000000000 : ℝ)|^5303 ≤ (30794745749927/100000000000000 : ℝ)^4279
        have hw : |(3865902439/10000000000 : ℝ)|=(3865902439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3865903443/10000000000 : ℝ)|^5303 ≤ (15397377830707/50000000000000 : ℝ)^4279
        have hw : |(3865903443/10000000000 : ℝ)|=(3865903443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1710_box_12 (p : ℝ) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-15368741/125000000 : ℝ)*x 0 + (2792901597/5000000000 : ℝ)*x 1 + (5152356997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (15368741/125000000 : ℝ)^5303 ≤ (1489096154701/20000000000000 : ℝ)^4279 := by
    have hnat : (15368741 : ℕ)^5303*20000000000000^4279 ≤ 1489096154701^4279*125000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15368741 125000000 1489096154701 20000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2792901597/5000000000 : ℝ)^5303 ≤ (48591592763577/100000000000000 : ℝ)^4279 := by
    have hnat : (2792901597 : ℕ)^5303*100000000000000^4279 ≤ 48591592763577^4279*5000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2792901597 5000000000 48591592763577 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5152356997/10000000000 : ℝ)^5303 ≤ (43962926447801/100000000000000 : ℝ)^4279 := by
    have hnat : (5152356997 : ℕ)^5303*100000000000000^4279 ≤ 43962926447801^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152356997 10000000000 43962926447801 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5303/1024 : ℝ)) 5303 4279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-15368741/125000000 : ℝ), (2792901597/5000000000 : ℝ), (5152356997/10000000000 : ℝ)] ![(1489096154701/20000000000000 : ℝ), (48591592763577/100000000000000 : ℝ), (43962926447801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-15368741/125000000 : ℝ)|^5303 ≤ (1489096154701/20000000000000 : ℝ)^4279
        have hw : |(-15368741/125000000 : ℝ)|=(15368741/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2792901597/5000000000 : ℝ)|^5303 ≤ (48591592763577/100000000000000 : ℝ)^4279
        have hw : |(2792901597/5000000000 : ℝ)|=(2792901597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5152356997/10000000000 : ℝ)|^5303 ≤ (43962926447801/100000000000000 : ℝ)^4279
        have hw : |(5152356997/10000000000 : ℝ)|=(5152356997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1710_box_13 (p : ℝ) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5405062903/10000000000 : ℝ)*x 0 + (-11579731/78125000 : ℝ)*x 1 + (1030471323/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5405062903/10000000000 : ℝ)^5303 ≤ (46650657416581/100000000000000 : ℝ)^4279 := by
    have hnat : (5405062903 : ℕ)^5303*100000000000000^4279 ≤ 46650657416581^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405062903 10000000000 46650657416581 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (11579731/78125000 : ℝ)^5303 ≤ (9386420161561/100000000000000 : ℝ)^4279 := by
    have hnat : (11579731 : ℕ)^5303*100000000000000^4279 ≤ 9386420161561^4279*78125000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11579731 78125000 9386420161561 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1030471323/2000000000 : ℝ)^5303 ≤ (43962922408341/100000000000000 : ℝ)^4279 := by
    have hnat : (1030471323 : ℕ)^5303*100000000000000^4279 ≤ 43962922408341^4279*2000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030471323 2000000000 43962922408341 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5303/1024 : ℝ)) 5303 4279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5405062903/10000000000 : ℝ), (-11579731/78125000 : ℝ), (1030471323/2000000000 : ℝ)] ![(46650657416581/100000000000000 : ℝ), (9386420161561/100000000000000 : ℝ), (43962922408341/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5405062903/10000000000 : ℝ)|^5303 ≤ (46650657416581/100000000000000 : ℝ)^4279
        have hw : |(5405062903/10000000000 : ℝ)|=(5405062903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-11579731/78125000 : ℝ)|^5303 ≤ (9386420161561/100000000000000 : ℝ)^4279
        have hw : |(-11579731/78125000 : ℝ)|=(11579731/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1030471323/2000000000 : ℝ)|^5303 ≤ (43962922408341/100000000000000 : ℝ)^4279
        have hw : |(1030471323/2000000000 : ℝ)|=(1030471323/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1710_box_14 (p : ℝ) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (675632791/1250000000 : ℝ)*x 0 + (644044591/1250000000 : ℝ)*x 1 + (-1482206199/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (675632791/1250000000 : ℝ)^5303 ≤ (46650651266169/100000000000000 : ℝ)^4279 := by
    have hnat : (675632791 : ℕ)^5303*100000000000000^4279 ≤ 46650651266169^4279*1250000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675632791 1250000000 46650651266169 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (644044591/1250000000 : ℝ)^5303 ≤ (2198146180163/5000000000000 : ℝ)^4279 := by
    have hnat : (644044591 : ℕ)^5303*5000000000000^4279 ≤ 2198146180163^4279*1250000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      644044591 1250000000 2198146180163 5000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1482206199/10000000000 : ℝ)^5303 ≤ (1877285022757/20000000000000 : ℝ)^4279 := by
    have hnat : (1482206199 : ℕ)^5303*20000000000000^4279 ≤ 1877285022757^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1482206199 10000000000 1877285022757 20000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5303/1024 : ℝ)) 5303 4279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(675632791/1250000000 : ℝ), (644044591/1250000000 : ℝ), (-1482206199/10000000000 : ℝ)] ![(46650651266169/100000000000000 : ℝ), (2198146180163/5000000000000 : ℝ), (1877285022757/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(675632791/1250000000 : ℝ)|^5303 ≤ (46650651266169/100000000000000 : ℝ)^4279
        have hw : |(675632791/1250000000 : ℝ)|=(675632791/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(644044591/1250000000 : ℝ)|^5303 ≤ (2198146180163/5000000000000 : ℝ)^4279
        have hw : |(644044591/1250000000 : ℝ)|=(644044591/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1482206199/10000000000 : ℝ)|^5303 ≤ (1877285022757/20000000000000 : ℝ)^4279
        have hw : |(-1482206199/10000000000 : ℝ)|=(1482206199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1710_box_15 (p : ℝ) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1811276273/5000000000 : ℝ)*x 0 + (4364903877/10000000000 : ℝ)*x 1 + (4364902793/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1811276273/5000000000 : ℝ)^5303 ≤ (14205393756013/50000000000000 : ℝ)^4279 := by
    have hnat : (1811276273 : ℕ)^5303*50000000000000^4279 ≤ 14205393756013^4279*5000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1811276273 5000000000 14205393756013 50000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4364903877/10000000000 : ℝ)^5303 ≤ (17897305871471/50000000000000 : ℝ)^4279 := by
    have hnat : (4364903877 : ℕ)^5303*50000000000000^4279 ≤ 17897305871471^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4364903877 10000000000 17897305871471 50000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4364902793/10000000000 : ℝ)^5303 ≤ (223716254539/625000000000 : ℝ)^4279 := by
    have hnat : (4364902793 : ℕ)^5303*625000000000^4279 ≤ 223716254539^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4364902793 10000000000 223716254539 625000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5303/1024 : ℝ)) 5303 4279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1811276273/5000000000 : ℝ), (4364903877/10000000000 : ℝ), (4364902793/10000000000 : ℝ)] ![(14205393756013/50000000000000 : ℝ), (17897305871471/50000000000000 : ℝ), (223716254539/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1811276273/5000000000 : ℝ)|^5303 ≤ (14205393756013/50000000000000 : ℝ)^4279
        have hw : |(1811276273/5000000000 : ℝ)|=(1811276273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4364903877/10000000000 : ℝ)|^5303 ≤ (17897305871471/50000000000000 : ℝ)^4279
        have hw : |(4364903877/10000000000 : ℝ)|=(4364903877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4364902793/10000000000 : ℝ)|^5303 ≤ (223716254539/625000000000 : ℝ)^4279
        have hw : |(4364902793/10000000000 : ℝ)|=(4364902793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1710_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19496159/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4273/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10011/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(66747/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58403/100000 : ℝ) ∧ (40741/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (90423/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4273/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10011/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4273/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10011/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4273/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10011/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4273/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10011/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4273/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10011/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4273/25000 : ℝ)*(X 0 2+X 1 2) := by
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
  have hpowlo : (10011/100000 : ℝ) ^ (5295/1024 : ℝ) ≤ (678532207316381/100000000000000000000 : ℝ) := by
    have hpowers : (10011/100000 : ℝ)^5295 ≤ (678532207316381/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10011 : ℕ)^5295*100000000000000000000^1024 ≤ 678532207316381^1024*100000^5295 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10011 100000 678532207316381 100000000000000000000 5295 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10011/100000 : ℝ)) (X := (678532207316381/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5295 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4273/25000 : ℝ) ^ (5295/1024 : ℝ) ≤ (1078573941313607/10000000000000000000 : ℝ) := by
    have hpowers : (4273/25000 : ℝ)^5295 ≤ (1078573941313607/10000000000000000000 : ℝ)^1024 := by
      have hnat : (4273 : ℕ)^5295*10000000000000000000^1024 ≤ 1078573941313607^1024*25000^5295 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4273 25000 1078573941313607 10000000000000000000 5295 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4273/25000 : ℝ)) (X := (1078573941313607/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5295 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000678532207316381/50000000000000000000 : ℝ) ≤ (10000026244123797/10000000000000000 : ℝ) ^ (5295/1024 : ℝ) := by
    have hpowers : (50000678532207316381/50000000000000000000 : ℝ)^1024 ≤ (10000026244123797/10000000000000000 : ℝ)^5295 := by
      have hnat : (50000678532207316381 : ℕ)^1024*10000000000000000^5295 ≤ 10000026244123797^5295*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000678532207316381 50000000000000000000 10000026244123797 10000000000000000 1024 5295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000026244123797/10000000000000000 : ℝ)) (X := (50000678532207316381/50000000000000000000 : ℝ)) (by norm_num) 5295 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100011464271620452451/100000000000000000000 : ℝ) ≤ (2000044339457577/2000000000000000 : ℝ) ^ (5295/1024 : ℝ) := by
    have hpowers : (100011464271620452451/100000000000000000000 : ℝ)^1024 ≤ (2000044339457577/2000000000000000 : ℝ)^5295 := by
      have hnat : (100011464271620452451 : ℕ)^1024*2000000000000000^5295 ≤ 2000044339457577^5295*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100011464271620452451 100000000000000000000 2000044339457577 2000000000000000 1024 5295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000044339457577/2000000000000000 : ℝ)) (X := (100011464271620452451/100000000000000000000 : ℝ)) (by norm_num) 5295 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5001078573941313607/5000000000000000000 : ℝ) ≤ (10000417150451973/10000000000000000 : ℝ) ^ (5295/1024 : ℝ) := by
    have hpowers : (5001078573941313607/5000000000000000000 : ℝ)^1024 ≤ (10000417150451973/10000000000000000 : ℝ)^5295 := by
      have hnat : (5001078573941313607 : ℕ)^1024*10000000000000000^5295 ≤ 10000417150451973^5295*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001078573941313607 5000000000000000000 10000417150451973 10000000000000000 1024 5295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000417150451973/10000000000000000 : ℝ)) (X := (5001078573941313607/5000000000000000000 : ℝ)) (by norm_num) 5295 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(678532207316381/100000000000000000000 : ℝ) ≤ ((70806272471389236621/70810000000000000000 : ℝ)+2*(24431645511/88512500000000 : ℝ)*(10011/100000 : ℝ))^(5295/1024 : ℝ) := by
    rw [show (70806272471389236621/70810000000000000000 : ℝ)+2*(24431645511/88512500000000 : ℝ)*(10011/100000 : ℝ)=(10000026244123797/10000000000000000 : ℝ) by norm_num, show 1+2*(678532207316381/100000000000000000000 : ℝ)=(50000678532207316381/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1078573941313607/10000000000000000000 : ℝ)+(678532207316381/100000000000000000000 : ℝ) ≤ ((70806272471389236621/70810000000000000000 : ℝ)+(24431645511/88512500000000 : ℝ)*((4273/25000 : ℝ)+(10011/100000 : ℝ)))^(5295/1024 : ℝ) := by
    rw [show (70806272471389236621/70810000000000000000 : ℝ)+(24431645511/88512500000000 : ℝ)*((4273/25000 : ℝ)+(10011/100000 : ℝ))=(2000044339457577/2000000000000000 : ℝ) by norm_num, show 1+(1078573941313607/10000000000000000000 : ℝ)+(678532207316381/100000000000000000000 : ℝ)=(100011464271620452451/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1078573941313607/10000000000000000000 : ℝ) ≤ ((70806272471389236621/70810000000000000000 : ℝ)+2*(24431645511/88512500000000 : ℝ)*(4273/25000 : ℝ))^(5295/1024 : ℝ) := by
    rw [show (70806272471389236621/70810000000000000000 : ℝ)+2*(24431645511/88512500000000 : ℝ)*(4273/25000 : ℝ)=(10000417150451973/10000000000000000 : ℝ) by norm_num, show 1+2*(1078573941313607/10000000000000000000 : ℝ)=(5001078573941313607/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (70806272471389236621/70810000000000000000 : ℝ)*(X 1 0+X 2 0)+(24431645511/88512500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5295/1024 : ℝ)) (lo := (10011/100000 : ℝ)) (hi := (4273/25000 : ℝ)) (c := (70806272471389236621/70810000000000000000 : ℝ)) (alpha := (24431645511/88512500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (70806272471389236621/70810000000000000000 : ℝ)*(X 0 1+X 2 1)+(24431645511/88512500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5295/1024 : ℝ)) (lo := (10011/100000 : ℝ)) (hi := (4273/25000 : ℝ)) (c := (70806272471389236621/70810000000000000000 : ℝ)) (alpha := (24431645511/88512500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (70806272471389236621/70810000000000000000 : ℝ)*(X 0 2+X 1 2)+(24431645511/88512500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5295/1024 : ℝ)) (lo := (10011/100000 : ℝ)) (hi := (4273/25000 : ℝ)) (c := (70806272471389236621/70810000000000000000 : ℝ)) (alpha := (24431645511/88512500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1093457857/10000000000 : ℝ)*X 0 0+(5417225423/10000000000 : ℝ)*X 0 1+(2708612869/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1710_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2612701941/5000000000 : ℝ)*X 1 0+(-1365921771/10000000000 : ℝ)*X 1 1+(5417225667/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1710_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2612701859/5000000000 : ℝ)*X 2 0+(1354306469/2500000000 : ℝ)*X 2 1+(-682960853/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1710_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((3589253/8000000 : ℝ)*X 0 0+(3935412569/10000000000 : ℝ)*X 0 1+(3935412467/10000000000 : ℝ)*X 0 2+(3589253/8000000 : ℝ)*X 1 0+(3935412569/10000000000 : ℝ)*X 1 1+(3935412467/10000000000 : ℝ)*X 1 2+(3589253/8000000 : ℝ)*X 2 0+(3935412569/10000000000 : ℝ)*X 2 1+(3935412467/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1710_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-875666811/5000000000 : ℝ)*X 0 0+(5177479251/10000000000 : ℝ)*X 0 1+(5177479433/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1710_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1346998573/2500000000 : ℝ)*X 1 0+(-294316191/2000000000 : ℝ)*X 1 1+(2588739697/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1710_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2693997233/5000000000 : ℝ)*X 2 0+(1035495861/2000000000 : ℝ)*X 2 1+(-1471580837/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1710_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3707204087/10000000000 : ℝ)*X 0 0+(4324266203/10000000000 : ℝ)*X 0 1+(864853309/2000000000 : ℝ)*X 0 2+(3707204087/10000000000 : ℝ)*X 1 0+(4324266203/10000000000 : ℝ)*X 1 1+(864853309/2000000000 : ℝ)*X 1 2+(3707204087/10000000000 : ℝ)*X 2 0+(4324266203/10000000000 : ℝ)*X 2 1+(864853309/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1710_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-804919027/5000000000 : ℝ)*X 0 0+(2500264529/5000000000 : ℝ)*X 0 1+(2729984437/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1710_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((649554429/1250000000 : ℝ)*X 1 0+(-1346304367/10000000000 : ℝ)*X 1 1+(34124807/62500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1710_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5196435923/10000000000 : ℝ)*X 2 0+(1364992159/2500000000 : ℝ)*X 2 1+(-673152183/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1710_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2310265729/5000000000 : ℝ)*X 0 0+(3865902439/10000000000 : ℝ)*X 0 1+(3865903443/10000000000 : ℝ)*X 0 2+(2310265729/5000000000 : ℝ)*X 1 0+(3865902439/10000000000 : ℝ)*X 1 1+(3865903443/10000000000 : ℝ)*X 1 2+(2310265729/5000000000 : ℝ)*X 2 0+(3865902439/10000000000 : ℝ)*X 2 1+(3865903443/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1710_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-15368741/125000000 : ℝ)*X 0 0+(2792901597/5000000000 : ℝ)*X 0 1+(5152356997/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1710_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5405062903/10000000000 : ℝ)*X 1 0+(-11579731/78125000 : ℝ)*X 1 1+(1030471323/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1710_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((675632791/1250000000 : ℝ)*X 2 0+(644044591/1250000000 : ℝ)*X 2 1+(-1482206199/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1710_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1811276273/5000000000 : ℝ)*X 0 0+(4364903877/10000000000 : ℝ)*X 0 1+(4364902793/10000000000 : ℝ)*X 0 2+(1811276273/5000000000 : ℝ)*X 1 0+(4364903877/10000000000 : ℝ)*X 1 1+(4364902793/10000000000 : ℝ)*X 1 2+(1811276273/5000000000 : ℝ)*X 2 0+(4364903877/10000000000 : ℝ)*X 2 1+(4364902793/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1710_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-66747/100000 : ℝ) ≤ (-2363076012271478440005655143/3540500000000000000000000000 : ℝ) := by norm_num
    linear_combination (7234507/100000000000000 : ℝ)*(upper0) + (56959/312500000000 : ℝ)*(lower2) + (2417431/12500000000000 : ℝ)*(lower3) + (32299981/100000000000000 : ℝ)*(upper5) + (16958195970589/1250000000000 : ℝ)*(major0) + (16958195970589/1250000000000 : ℝ)*(major1) + (16958195970589/1250000000000 : ℝ)*(major2) + (586080847/100000000000000 : ℝ)*(sp2) + (8978053/50000000000000 : ℝ)*(sp3) + (81588058918819/4000000000000 : ℝ)*(sp4) + (509924235345283/25000000000000 : ℝ)*(sp5) + (509925221722407/25000000000000 : ℝ)*(sp6) + (17396447713619/2500000000000 : ℝ)*(sp7) + (141612167/3125000000000 : ℝ)*(sp13) + (347928963250433/50000000000000 : ℝ)*(f.failure) + (81588058918819/4000000000000 : ℝ)*(f.sum) + (15609377297771/3540500000000000000000000000 : ℝ)*base65 + (594108184719202269/88512500000000000000000000000000 : ℝ)*base67 + (374118194191727269/88512500000000000000000000000000 : ℝ)*base69 + (340203563545010231/88512500000000000000000000000000 : ℝ)*base72 + (18539523419/708100000000000000000000000 : ℝ)*base74 + (521943754887435231/88512500000000000000000000000000 : ℝ)*base76 + (378324658966764769/88512500000000000000000000000000 : ℝ)*base77 + (551016202071385231/88512500000000000000000000000000 : ℝ)*base80 + (10189998001627/1770250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1413153/500000000000000000000 : ℝ)*base90 + (1413153/500000000000000000000 : ℝ)*base92 + (1413153/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (58403/100000 : ℝ) ≤ (1033915675916778065551477238799339/1770250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9890783/50000000000000 : ℝ)*(lower0) + (832517/10000000000000 : ℝ)*(lower1) + (989519/12500000000000 : ℝ)*(lower4) + (1461466481941747/100000000000000 : ℝ)*(major0) + (1461466481941747/100000000000000 : ℝ)*(major1) + (1461466481941747/100000000000000 : ℝ)*(major2) + (538461388823837/25000000000000 : ℝ)*(sp0) + (2153846392946217/100000000000000 : ℝ)*(sp1) + (430768941461589/20000000000000 : ℝ)*(sp2) + (37480878629563/5000000000000 : ℝ)*(sp3) + (569502419/100000000000000 : ℝ)*(sp5) + (2255140691/100000000000000 : ℝ)*(sp6) + (9200429/12500000000000 : ℝ)*(sp7) + (175894161/12500000000000 : ℝ)*(sp12) + (187404411548673/25000000000000 : ℝ)*(f.failure) + (538461740612159/25000000000000 : ℝ)*(f.sum) + (3491813345001/8851250000000000000000000000 : ℝ)*base66 + (23355681087622716887/7081000000000000000000000000000000 : ℝ)*base67 + (15045036348874716887/7081000000000000000000000000000000 : ℝ)*base69 + (8229117081888716887/7081000000000000000000000000000000 : ℝ)*base71 + (2851938850973/4425625000000000000000000000 : ℝ)*base74 + (6431515318190283113/7081000000000000000000000000000000 : ℝ)*base76 + (21313751613194716887/7081000000000000000000000000000000 : ℝ)*base77 + (13066630504203716887/7081000000000000000000000000000000 : ℝ)*base79 + (40907222894079/35405000000000000000000000000 : ℝ)*base82 + (2452993/250000000000000000000 : ℝ)*base90 + (2452993/250000000000000000000 : ℝ)*base92 + (2452993/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (40741/50000 : ℝ) ≤ (72123683274459782644580690157273/88512500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (588383/5000000000000 : ℝ)*(upper0) + (233819/781250000000 : ℝ)*(lower1) + (5822771/6250000000000 : ℝ)*(lower3) + (20735599/100000000000000 : ℝ)*(upper4) + (37047946076571/2500000000000 : ℝ)*(major0) + (37047946076571/2500000000000 : ℝ)*(major1) + (37047946076571/2500000000000 : ℝ)*(major2) + (301595673/12500000000000 : ℝ)*(sp0) + (29733667317/100000000000000 : ℝ)*(sp1) + (12362465441/100000000000000 : ℝ)*(sp3) + (1088282145333653/50000000000000 : ℝ)*(sp8) + (2176536969765373/100000000000000 : ℝ)*(sp9) + (217656670343269/10000000000000 : ℝ)*(sp10) + (380047613738597/50000000000000 : ℝ)*(sp11) + (380053794971317/50000000000000 : ℝ)*(f.failure) + (217656670343269/10000000000000 : ℝ)*(f.sum) + (3927317030853/3540500000000000000000000000 : ℝ)*base66 + (96916071228768409/177025000000000000000000000000000 : ℝ)*base68 + (529242888365018409/177025000000000000000000000000000 : ℝ)*base70 + (823858832768306591/177025000000000000000000000000000 : ℝ)*base71 + (29753414726573/7081000000000000000000000000 : ℝ)*base74 + (89101831874906591/177025000000000000000000000000000 : ℝ)*base75 + (308446553565193409/177025000000000000000000000000000 : ℝ)*base78 + (297728922440268409/177025000000000000000000000000000 : ℝ)*base80 + (3512334296057/1416200000000000000000000000 : ℝ)*base82 + (3328597/500000000000000000000 : ℝ)*base90 + (3328597/500000000000000000000 : ℝ)*base92 + (3328597/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-90423/100000 : ℝ) ≤ (-50020952545986507197487977961741/55320312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (15633069/25000000000000 : ℝ)*(upper1) + (170965849/100000000000000 : ℝ)*(upper3) + (12815859/10000000000000 : ℝ)*(lower4) + (23924418907907/1562500000000 : ℝ)*(major0) + (23924418907907/1562500000000 : ℝ)*(major1) + (23924418907907/1562500000000 : ℝ)*(major2) + (1264129173/25000000000000 : ℝ)*(sp4) + (83298098863/100000000000000 : ℝ)*(sp5) + (10083179883/12500000000000 : ℝ)*(sp6) + (32425437509/100000000000000 : ℝ)*(sp7) + (576773591396203/25000000000000 : ℝ)*(sp12) + (2307016124002641/100000000000000 : ℝ)*(sp13) + (57675468916561/2500000000000 : ℝ)*(sp14) + (157066793818979/20000000000000 : ℝ)*(sp15) + (196341598633101/25000000000000 : ℝ)*(f.failure) + (563256694849/24414062500 : ℝ)*(f.sum) + (51832554969221/35405000000000000000000000000 : ℝ)*base66 + (297592920262118497/110640625000000000000000000000000 : ℝ)*base67 + (410976182489725253/110640625000000000000000000000000 : ℝ)*base70 + (9937771822899747/110640625000000000000000000000000 : ℝ)*base71 + (8364484008679/35405000000000000000000000000 : ℝ)*base73 + (351247380354214189/55320312500000000000000000000000 : ℝ)*base76 + (186974742908910811/55320312500000000000000000000000 : ℝ)*base77 + (469659049493055997/110640625000000000000000000000000 : ℝ)*base79 + (73529878775159/8851250000000000000000000000 : ℝ)*base82 + (240941/250000000000000000000 : ℝ)*base90 + (240941/250000000000000000000 : ℝ)*base92 + (240941/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1710_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19496159/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4273/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10011/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66747/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58403/100000 : ℝ) else (40741/50000 : ℝ) ≤ X j i ∧ X j i ≤ (90423/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1710_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1710_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19496159/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4273/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10011/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66747/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58403/100000 : ℝ) else (40741/50000 : ℝ) ≤ X j i ∧ X j i ≤ (90423/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1710_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19496159/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4273/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10011/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66747/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58403/100000 : ℝ) else (40741/50000 : ℝ) ≤ X j i ∧ X j i ≤ (90423/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1710_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
