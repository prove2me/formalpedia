-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1368_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:19:39.052042+00:00
-- url     : https://prove2.me/submissions/1116c235-1a04-42e0-9526-c44f79f6556c

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
theorem support_rectangle_w1368_s0_0 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1793875101/10000000000 : ℝ)*x 0 + (5985762853/10000000000 : ℝ)*x 1 + (4817074433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1793875101/10000000000 : ℝ)^541 ≤ (526613505471/5000000000000 : ℝ)^413 := by
    have hnat : (1793875101 : ℕ)^541*5000000000000^413 ≤ 526613505471^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1793875101 10000000000 526613505471 5000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5985762853/10000000000 : ℝ)^541 ≤ (25527762343341/50000000000000 : ℝ)^413 := by
    have hnat : (5985762853 : ℕ)^541*50000000000000^413 ≤ 25527762343341^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5985762853 10000000000 25527762343341 50000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4817074433/10000000000 : ℝ)^541 ≤ (19206102594651/50000000000000 : ℝ)^413 := by
    have hnat : (4817074433 : ℕ)^541*50000000000000^413 ≤ 19206102594651^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4817074433 10000000000 19206102594651 50000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1793875101/10000000000 : ℝ), (5985762853/10000000000 : ℝ), (4817074433/10000000000 : ℝ)] ![(526613505471/5000000000000 : ℝ), (25527762343341/50000000000000 : ℝ), (19206102594651/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1793875101/10000000000 : ℝ)|^541 ≤ (526613505471/5000000000000 : ℝ)^413
        have hw : |(-1793875101/10000000000 : ℝ)|=(1793875101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5985762853/10000000000 : ℝ)|^541 ≤ (25527762343341/50000000000000 : ℝ)^413
        have hw : |(5985762853/10000000000 : ℝ)|=(5985762853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4817074433/10000000000 : ℝ)|^541 ≤ (19206102594651/50000000000000 : ℝ)^413
        have hw : |(4817074433/10000000000 : ℝ)|=(4817074433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_s0_1 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2749451633/5000000000 : ℝ)*x 0 + (-1228453429/5000000000 : ℝ)*x 1 + (4817074991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2749451633/5000000000 : ℝ)^541 ≤ (45685725999993/100000000000000 : ℝ)^413 := by
    have hnat : (2749451633 : ℕ)^541*100000000000000^413 ≤ 45685725999993^413*5000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2749451633 5000000000 45685725999993 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1228453429/5000000000 : ℝ)^541 ≤ (3975515743321/25000000000000 : ℝ)^413 := by
    have hnat : (1228453429 : ℕ)^541*25000000000000^413 ≤ 3975515743321^413*5000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1228453429 5000000000 3975515743321 25000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4817074991/10000000000 : ℝ)^541 ≤ (38412211017943/100000000000000 : ℝ)^413 := by
    have hnat : (4817074991 : ℕ)^541*100000000000000^413 ≤ 38412211017943^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4817074991 10000000000 38412211017943 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2749451633/5000000000 : ℝ), (-1228453429/5000000000 : ℝ), (4817074991/10000000000 : ℝ)] ![(45685725999993/100000000000000 : ℝ), (3975515743321/25000000000000 : ℝ), (38412211017943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2749451633/5000000000 : ℝ)|^541 ≤ (45685725999993/100000000000000 : ℝ)^413
        have hw : |(2749451633/5000000000 : ℝ)|=(2749451633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1228453429/5000000000 : ℝ)|^541 ≤ (3975515743321/25000000000000 : ℝ)^413
        have hw : |(-1228453429/5000000000 : ℝ)|=(1228453429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4817074991/10000000000 : ℝ)|^541 ≤ (38412211017943/100000000000000 : ℝ)^413
        have hw : |(4817074991/10000000000 : ℝ)|=(4817074991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_s0_2 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5498903153/10000000000 : ℝ)*x 0 + (2408537189/5000000000 : ℝ)*x 1 + (-1228453879/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5498903153/10000000000 : ℝ)^541 ≤ (22842862385103/50000000000000 : ℝ)^413 := by
    have hnat : (5498903153 : ℕ)^541*50000000000000^413 ≤ 22842862385103^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5498903153 10000000000 22842862385103 50000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2408537189/5000000000 : ℝ)^541 ≤ (7682440922959/20000000000000 : ℝ)^413 := by
    have hnat : (2408537189 : ℕ)^541*20000000000000^413 ≤ 7682440922959^413*5000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2408537189 5000000000 7682440922959 20000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1228453879/5000000000 : ℝ)^541 ≤ (15902070603811/100000000000000 : ℝ)^413 := by
    have hnat : (1228453879 : ℕ)^541*100000000000000^413 ≤ 15902070603811^413*5000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1228453879 5000000000 15902070603811 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5498903153/10000000000 : ℝ), (2408537189/5000000000 : ℝ), (-1228453879/5000000000 : ℝ)] ![(22842862385103/50000000000000 : ℝ), (7682440922959/20000000000000 : ℝ), (15902070603811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5498903153/10000000000 : ℝ)|^541 ≤ (22842862385103/50000000000000 : ℝ)^413
        have hw : |(5498903153/10000000000 : ℝ)|=(5498903153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2408537189/5000000000 : ℝ)|^541 ≤ (7682440922959/20000000000000 : ℝ)^413
        have hw : |(2408537189/5000000000 : ℝ)|=(2408537189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1228453879/5000000000 : ℝ)|^541 ≤ (15902070603811/100000000000000 : ℝ)^413
        have hw : |(-1228453879/5000000000 : ℝ)|=(1228453879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_s0_3 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4174880559/10000000000 : ℝ)*x 0 + (3105377067/10000000000 : ℝ)*x 1 + (5577246329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4174880559/10000000000 : ℝ)^541 ≤ (31847200954157/100000000000000 : ℝ)^413 := by
    have hnat : (4174880559 : ℕ)^541*100000000000000^413 ≤ 31847200954157^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4174880559 10000000000 31847200954157 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3105377067/10000000000 : ℝ)^541 ≤ (432251665557/2000000000000 : ℝ)^413 := by
    have hnat : (3105377067 : ℕ)^541*2000000000000^413 ≤ 432251665557^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3105377067 10000000000 432251665557 2000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5577246329/10000000000 : ℝ)^541 ≤ (11635053939569/25000000000000 : ℝ)^413 := by
    have hnat : (5577246329 : ℕ)^541*25000000000000^413 ≤ 11635053939569^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5577246329 10000000000 11635053939569 25000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4174880559/10000000000 : ℝ), (3105377067/10000000000 : ℝ), (5577246329/10000000000 : ℝ)] ![(31847200954157/100000000000000 : ℝ), (432251665557/2000000000000 : ℝ), (11635053939569/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4174880559/10000000000 : ℝ)|^541 ≤ (31847200954157/100000000000000 : ℝ)^413
        have hw : |(4174880559/10000000000 : ℝ)|=(4174880559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3105377067/10000000000 : ℝ)|^541 ≤ (432251665557/2000000000000 : ℝ)^413
        have hw : |(3105377067/10000000000 : ℝ)|=(3105377067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5577246329/10000000000 : ℝ)|^541 ≤ (11635053939569/25000000000000 : ℝ)^413
        have hw : |(5577246329/10000000000 : ℝ)|=(5577246329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_s0_4 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1798197129/10000000000 : ℝ)*x 0 + (4847105153/10000000000 : ℝ)*x 1 + (186083093/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1798197129/10000000000 : ℝ)^541 ≤ (10565522785617/100000000000000 : ℝ)^413 := by
    have hnat : (1798197129 : ℕ)^541*100000000000000^413 ≤ 10565522785617^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1798197129 10000000000 10565522785617 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4847105153/10000000000 : ℝ)^541 ≤ (38726196479721/100000000000000 : ℝ)^413 := by
    have hnat : (4847105153 : ℕ)^541*100000000000000^413 ≤ 38726196479721^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4847105153 10000000000 38726196479721 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (186083093/312500000 : ℝ)^541 ≤ (50708280722819/100000000000000 : ℝ)^413 := by
    have hnat : (186083093 : ℕ)^541*100000000000000^413 ≤ 50708280722819^413*312500000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      186083093 312500000 50708280722819 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1798197129/10000000000 : ℝ), (4847105153/10000000000 : ℝ), (186083093/312500000 : ℝ)] ![(10565522785617/100000000000000 : ℝ), (38726196479721/100000000000000 : ℝ), (50708280722819/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1798197129/10000000000 : ℝ)|^541 ≤ (10565522785617/100000000000000 : ℝ)^413
        have hw : |(-1798197129/10000000000 : ℝ)|=(1798197129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4847105153/10000000000 : ℝ)|^541 ≤ (38726196479721/100000000000000 : ℝ)^413
        have hw : |(4847105153/10000000000 : ℝ)|=(4847105153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(186083093/312500000 : ℝ)|^541 ≤ (50708280722819/100000000000000 : ℝ)^413
        have hw : |(186083093/312500000 : ℝ)|=(186083093/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_s0_5 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (518024043/1000000000 : ℝ)*x 0 + (-1319325289/10000000000 : ℝ)*x 1 + (2977328957/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (518024043/1000000000 : ℝ)^541 ≤ (8449852664159/20000000000000 : ℝ)^413 := by
    have hnat : (518024043 : ℕ)^541*20000000000000^413 ≤ 8449852664159^413*1000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518024043 1000000000 8449852664159 20000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1319325289/10000000000 : ℝ)^541 ≤ (7042467786131/100000000000000 : ℝ)^413 := by
    have hnat : (1319325289 : ℕ)^541*100000000000000^413 ≤ 7042467786131^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319325289 10000000000 7042467786131 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2977328957/5000000000 : ℝ)^541 ≤ (50708268876219/100000000000000 : ℝ)^413 := by
    have hnat : (2977328957 : ℕ)^541*100000000000000^413 ≤ 50708268876219^413*5000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2977328957 5000000000 50708268876219 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(518024043/1000000000 : ℝ), (-1319325289/10000000000 : ℝ), (2977328957/5000000000 : ℝ)] ![(8449852664159/20000000000000 : ℝ), (7042467786131/100000000000000 : ℝ), (50708268876219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(518024043/1000000000 : ℝ)|^541 ≤ (8449852664159/20000000000000 : ℝ)^413
        have hw : |(518024043/1000000000 : ℝ)|=(518024043/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1319325289/10000000000 : ℝ)|^541 ≤ (7042467786131/100000000000000 : ℝ)^413
        have hw : |(-1319325289/10000000000 : ℝ)|=(1319325289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2977328957/5000000000 : ℝ)|^541 ≤ (50708268876219/100000000000000 : ℝ)^413
        have hw : |(2977328957/5000000000 : ℝ)|=(2977328957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_s0_6 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5180239799/10000000000 : ℝ)*x 0 + (2977329823/5000000000 : ℝ)*x 1 + (-1319323491/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5180239799/10000000000 : ℝ)^541 ≤ (21124628289731/50000000000000 : ℝ)^413 := by
    have hnat : (5180239799 : ℕ)^541*50000000000000^413 ≤ 21124628289731^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180239799 10000000000 21124628289731 50000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2977329823/5000000000 : ℝ)^541 ≤ (50708288196663/100000000000000 : ℝ)^413 := by
    have hnat : (2977329823 : ℕ)^541*100000000000000^413 ≤ 50708288196663^413*5000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2977329823 5000000000 50708288196663 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1319323491/10000000000 : ℝ)^541 ≤ (281698208559/4000000000000 : ℝ)^413 := by
    have hnat : (1319323491 : ℕ)^541*4000000000000^413 ≤ 281698208559^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319323491 10000000000 281698208559 4000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5180239799/10000000000 : ℝ), (2977329823/5000000000 : ℝ), (-1319323491/10000000000 : ℝ)] ![(21124628289731/50000000000000 : ℝ), (50708288196663/100000000000000 : ℝ), (281698208559/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5180239799/10000000000 : ℝ)|^541 ≤ (21124628289731/50000000000000 : ℝ)^413
        have hw : |(5180239799/10000000000 : ℝ)|=(5180239799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2977329823/5000000000 : ℝ)|^541 ≤ (50708288196663/100000000000000 : ℝ)^413
        have hw : |(2977329823/5000000000 : ℝ)|=(2977329823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1319323491/10000000000 : ℝ)|^541 ≤ (281698208559/4000000000000 : ℝ)^413
        have hw : |(-1319323491/10000000000 : ℝ)|=(1319323491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_s0_7 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2092007863/5000000000 : ℝ)*x 0 + (5513731379/10000000000 : ℝ)*x 1 + (3171165193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2092007863/5000000000 : ℝ)^541 ≤ (6387703020771/20000000000000 : ℝ)^413 := by
    have hnat : (2092007863 : ℕ)^541*20000000000000^413 ≤ 6387703020771^413*5000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2092007863 5000000000 6387703020771 20000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5513731379/10000000000 : ℝ)^541 ≤ (45847168873547/100000000000000 : ℝ)^413 := by
    have hnat : (5513731379 : ℕ)^541*100000000000000^413 ≤ 45847168873547^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5513731379 10000000000 45847168873547 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3171165193/10000000000 : ℝ)^541 ≤ (11107158001579/50000000000000 : ℝ)^413 := by
    have hnat : (3171165193 : ℕ)^541*50000000000000^413 ≤ 11107158001579^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3171165193 10000000000 11107158001579 50000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2092007863/5000000000 : ℝ), (5513731379/10000000000 : ℝ), (3171165193/10000000000 : ℝ)] ![(6387703020771/20000000000000 : ℝ), (45847168873547/100000000000000 : ℝ), (11107158001579/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2092007863/5000000000 : ℝ)|^541 ≤ (6387703020771/20000000000000 : ℝ)^413
        have hw : |(2092007863/5000000000 : ℝ)|=(2092007863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5513731379/10000000000 : ℝ)|^541 ≤ (45847168873547/100000000000000 : ℝ)^413
        have hw : |(5513731379/10000000000 : ℝ)|=(5513731379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3171165193/10000000000 : ℝ)|^541 ≤ (11107158001579/50000000000000 : ℝ)^413
        have hw : |(3171165193/10000000000 : ℝ)|=(3171165193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1368_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7787701/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (201/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5337/20000 : ℝ)*pair X 0 0 := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (4327/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4327 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4327*1^1024 ≤ 0^1024*1^4327 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4327 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4327 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4327/1024 : ℝ) ≤ (2081950000384144489/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4327 ≤ (2081950000384144489/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4327*100000000000000000000^1024 ≤ 2081950000384144489^1024*5^4327 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2081950000384144489 100000000000000000000 4327 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2081950000384144489/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4327 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4327/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4327 := by
      have hnat : (1 : ℕ)^1024*1^4327 ≤ 1^4327*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4327 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (102081950000384144489/100000000000000000000 : ℝ) ≤ (5024441650563261/5000000000000000 : ℝ) ^ (4327/1024 : ℝ) := by
    have hpowers : (102081950000384144489/100000000000000000000 : ℝ)^1024 ≤ (5024441650563261/5000000000000000 : ℝ)^4327 := by
      have hnat : (102081950000384144489 : ℕ)^1024*5000000000000000^4327 ≤ 5024441650563261^4327*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102081950000384144489 100000000000000000000 5024441650563261 5000000000000000 1024 4327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5024441650563261/5000000000000000 : ℝ)) (X := (102081950000384144489/100000000000000000000 : ℝ)) (by norm_num) 4327 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (52081950000384144489/50000000000000000000 : ℝ) ≤ (2524441650563261/2500000000000000 : ℝ) ^ (4327/1024 : ℝ) := by
    have hpowers : (52081950000384144489/50000000000000000000 : ℝ)^1024 ≤ (2524441650563261/2500000000000000 : ℝ)^4327 := by
      have hnat : (52081950000384144489 : ℕ)^1024*2500000000000000^4327 ≤ 2524441650563261^4327*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52081950000384144489 50000000000000000000 2524441650563261 2500000000000000 1024 4327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2524441650563261/2500000000000000 : ℝ)) (X := (52081950000384144489/50000000000000000000 : ℝ)) (by norm_num) 4327 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(24441650563261/2000000000000000 : ℝ)*(0 : ℝ))^(4327/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(24441650563261/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2081950000384144489/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(24441650563261/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4327/1024 : ℝ) := by
    rw [show (1 : ℝ)+(24441650563261/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5024441650563261/5000000000000000 : ℝ) by norm_num, show 1+(2081950000384144489/100000000000000000000 : ℝ)+(0 : ℝ)=(102081950000384144489/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2081950000384144489/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(24441650563261/2000000000000000 : ℝ)*(2/5 : ℝ))^(4327/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(24441650563261/2000000000000000 : ℝ)*(2/5 : ℝ)=(2524441650563261/2500000000000000 : ℝ) by norm_num, show 1+2*(2081950000384144489/100000000000000000000 : ℝ)=(52081950000384144489/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(24441650563261/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4327/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (24441650563261/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(24441650563261/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4327/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (24441650563261/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(24441650563261/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4327/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (24441650563261/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1793875101/10000000000 : ℝ)*X 0 0+(5985762853/10000000000 : ℝ)*X 0 1+(4817074433/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2749451633/5000000000 : ℝ)*X 1 0+(-1228453429/5000000000 : ℝ)*X 1 1+(4817074991/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5498903153/10000000000 : ℝ)*X 2 0+(2408537189/5000000000 : ℝ)*X 2 1+(-1228453879/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4174880559/10000000000 : ℝ)*X 0 0+(3105377067/10000000000 : ℝ)*X 0 1+(5577246329/10000000000 : ℝ)*X 0 2+(4174880559/10000000000 : ℝ)*X 1 0+(3105377067/10000000000 : ℝ)*X 1 1+(5577246329/10000000000 : ℝ)*X 1 2+(4174880559/10000000000 : ℝ)*X 2 0+(3105377067/10000000000 : ℝ)*X 2 1+(5577246329/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1798197129/10000000000 : ℝ)*X 0 0+(4847105153/10000000000 : ℝ)*X 0 1+(186083093/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((518024043/1000000000 : ℝ)*X 1 0+(-1319325289/10000000000 : ℝ)*X 1 1+(2977328957/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5180239799/10000000000 : ℝ)*X 2 0+(2977329823/5000000000 : ℝ)*X 2 1+(-1319323491/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2092007863/5000000000 : ℝ)*X 0 0+(5513731379/10000000000 : ℝ)*X 0 1+(3171165193/10000000000 : ℝ)*X 0 2+(2092007863/5000000000 : ℝ)*X 1 0+(5513731379/10000000000 : ℝ)*X 1 1+(3171165193/10000000000 : ℝ)*X 1 2+(2092007863/5000000000 : ℝ)*X 2 0+(5513731379/10000000000 : ℝ)*X 2 1+(3171165193/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (107711388804873700712523/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (154418461/100000000000000 : ℝ)*(base1) + (27256233/50000000000000 : ℝ)*(base16) + (218969129/50000000000000 : ℝ)*(base19) + (59358407/12500000000000 : ℝ)*(base23) + (56450303/100000000000000 : ℝ)*(upper3) + (315053887025219/50000000000000 : ℝ)*(major0) + (315053887025219/50000000000000 : ℝ)*(major1) + (315053887025219/50000000000000 : ℝ)*(major2) + (17113229191433/2000000000000 : ℝ)*(sp0) + (53478865422169/6250000000000 : ℝ)*(sp1) + (213915466084543/25000000000000 : ℝ)*(sp2) + (404552488521741/100000000000000 : ℝ)*(sp3) + (1034052239/100000000000000 : ℝ)*(sp4) + (7721057/1562500000000 : ℝ)*(sp7) + (8091062741757/2000000000000 : ℝ)*(f.failure) + (213915584801357/25000000000000 : ℝ)*(f.sum) + (67364202579159/50000000000000000000000000000 : ℝ)*base65 + (74465463720841/100000000000000000000000000000 : ℝ)*base68 + (398408405179159/100000000000000000000000000000 : ℝ)*base69 + (444020168779159/100000000000000000000000000000 : ℝ)*base71 + (16948948470841/50000000000000000000000000000 : ℝ)*base74 + (20505189820841/100000000000000000000000000000 : ℝ)*base76 + (549760863579159/100000000000000000000000000000 : ℝ)*base77 + (102320663620841/100000000000000000000000000000 : ℝ)*base80 + (119080238029159/50000000000000000000000000000 : ℝ)*base81 + (69343/10000000000000000000 : ℝ)*base90 + (69343/10000000000000000000 : ℝ)*base92 + (69343/10000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (254262085432751210031687/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21782351/6250000000000 : ℝ)*(base19) + (756669181/100000000000000 : ℝ)*(base23) + (243913321/100000000000000 : ℝ)*(base39) + (106661827/100000000000000 : ℝ)*(upper2) + (14537771/10000000000000 : ℝ)*(upper5) + (664885641683749/100000000000000 : ℝ)*(major0) + (664885641683749/100000000000000 : ℝ)*(major1) + (664885397770429/100000000000000 : ℝ)*(major2) + (49557359/12500000000000 : ℝ)*(sp1) + (25008901/1562500000000 : ℝ)*(sp2) + (18057780403309/2000000000000 : ℝ)*(sp4) + (451444137594481/50000000000000 : ℝ)*(sp5) + (451443453419963/50000000000000 : ℝ)*(sp6) + (426881849780667/100000000000000 : ℝ)*(sp7) + (426881849780667/100000000000000 : ℝ)*(f.failure) + (902889264078771/100000000000000 : ℝ)*(f.sum) + (179206230677229/100000000000000000000000000000 : ℝ)*base65 + (1082601308991031/200000000000000000000000000000 : ℝ)*base68 + (210705693945489/200000000000000000000000000000 : ℝ)*base69 + (1039274351191031/200000000000000000000000000000 : ℝ)*base72 + (67760710022771/100000000000000000000000000000 : ℝ)*base74 + (642218449945489/200000000000000000000000000000 : ℝ)*base75 + (711220661454511/200000000000000000000000000000 : ℝ)*base78 + (1704382716054511/200000000000000000000000000000 : ℝ)*base80 + (67350595154511/100000000000000000000000000000 : ℝ)*base82 + (5176567/500000000000000000000 : ℝ)*base89 + (5176567/500000000000000000000 : ℝ)*base91 + (176567/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1368_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7787701/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (201/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5337/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1368_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1368_s1_0 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-197494663/1000000000 : ℝ)*x 0 + (2815328279/5000000000 : ℝ)*x 1 + (5056191953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (197494663/1000000000 : ℝ)^541 ≤ (2986542544103/25000000000000 : ℝ)^413 := by
    have hnat : (197494663 : ℕ)^541*25000000000000^413 ≤ 2986542544103^413*1000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197494663 1000000000 2986542544103 25000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2815328279/5000000000 : ℝ)^541 ≤ (47124901931707/100000000000000 : ℝ)^413 := by
    have hnat : (2815328279 : ℕ)^541*100000000000000^413 ≤ 47124901931707^413*5000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2815328279 5000000000 47124901931707 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5056191953/10000000000 : ℝ)^541 ≤ (20464463941101/50000000000000 : ℝ)^413 := by
    have hnat : (5056191953 : ℕ)^541*50000000000000^413 ≤ 20464463941101^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5056191953 10000000000 20464463941101 50000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-197494663/1000000000 : ℝ), (2815328279/5000000000 : ℝ), (5056191953/10000000000 : ℝ)] ![(2986542544103/25000000000000 : ℝ), (47124901931707/100000000000000 : ℝ), (20464463941101/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-197494663/1000000000 : ℝ)|^541 ≤ (2986542544103/25000000000000 : ℝ)^413
        have hw : |(-197494663/1000000000 : ℝ)|=(197494663/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2815328279/5000000000 : ℝ)|^541 ≤ (47124901931707/100000000000000 : ℝ)^413
        have hw : |(2815328279/5000000000 : ℝ)|=(2815328279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5056191953/10000000000 : ℝ)|^541 ≤ (20464463941101/50000000000000 : ℝ)^413
        have hw : |(5056191953/10000000000 : ℝ)|=(5056191953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_s1_1 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2701509021/5000000000 : ℝ)*x 0 + (-285102967/1250000000 : ℝ)*x 1 + (1011238629/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2701509021/5000000000 : ℝ)^541 ≤ (22322515473541/50000000000000 : ℝ)^413 := by
    have hnat : (2701509021 : ℕ)^541*50000000000000^413 ≤ 22322515473541^413*5000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701509021 5000000000 22322515473541 50000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (285102967/1250000000 : ℝ)^541 ≤ (7213014253619/50000000000000 : ℝ)^413 := by
    have hnat : (285102967 : ℕ)^541*50000000000000^413 ≤ 7213014253619^413*1250000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      285102967 1250000000 7213014253619 50000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1011238629/2000000000 : ℝ)^541 ≤ (20464470260857/50000000000000 : ℝ)^413 := by
    have hnat : (1011238629 : ℕ)^541*50000000000000^413 ≤ 20464470260857^413*2000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1011238629 2000000000 20464470260857 50000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2701509021/5000000000 : ℝ), (-285102967/1250000000 : ℝ), (1011238629/2000000000 : ℝ)] ![(22322515473541/50000000000000 : ℝ), (7213014253619/50000000000000 : ℝ), (20464470260857/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2701509021/5000000000 : ℝ)|^541 ≤ (22322515473541/50000000000000 : ℝ)^413
        have hw : |(2701509021/5000000000 : ℝ)|=(2701509021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-285102967/1250000000 : ℝ)|^541 ≤ (7213014253619/50000000000000 : ℝ)^413
        have hw : |(-285102967/1250000000 : ℝ)|=(285102967/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1011238629/2000000000 : ℝ)|^541 ≤ (20464470260857/50000000000000 : ℝ)^413
        have hw : |(1011238629/2000000000 : ℝ)|=(1011238629/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_s1_2 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (337688651/625000000 : ℝ)*x 0 + (5056192149/10000000000 : ℝ)*x 1 + (-2280824523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (337688651/625000000 : ℝ)^541 ≤ (22322517497611/50000000000000 : ℝ)^413 := by
    have hnat : (337688651 : ℕ)^541*50000000000000^413 ≤ 22322517497611^413*625000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337688651 625000000 22322517497611 50000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5056192149/10000000000 : ℝ)^541 ≤ (40928929960511/100000000000000 : ℝ)^413 := by
    have hnat : (5056192149 : ℕ)^541*100000000000000^413 ≤ 40928929960511^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5056192149 10000000000 40928929960511 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2280824523/10000000000 : ℝ)^541 ≤ (90162718923/625000000000 : ℝ)^413 := by
    have hnat : (2280824523 : ℕ)^541*625000000000^413 ≤ 90162718923^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2280824523 10000000000 90162718923 625000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(337688651/625000000 : ℝ), (5056192149/10000000000 : ℝ), (-2280824523/10000000000 : ℝ)] ![(22322517497611/50000000000000 : ℝ), (40928929960511/100000000000000 : ℝ), (90162718923/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(337688651/625000000 : ℝ)|^541 ≤ (22322517497611/50000000000000 : ℝ)^413
        have hw : |(337688651/625000000 : ℝ)|=(337688651/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5056192149/10000000000 : ℝ)|^541 ≤ (40928929960511/100000000000000 : ℝ)^413
        have hw : |(5056192149/10000000000 : ℝ)|=(5056192149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2280824523/10000000000 : ℝ)|^541 ≤ (90162718923/625000000000 : ℝ)^413
        have hw : |(-2280824523/10000000000 : ℝ)|=(2280824523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_s1_3 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (267978769/625000000 : ℝ)*x 0 + (929895589/2500000000 : ℝ)*x 1 + (2467308181/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267978769/625000000 : ℝ)^541 ≤ (4122355235797/12500000000000 : ℝ)^413 := by
    have hnat : (267978769 : ℕ)^541*12500000000000^413 ≤ 4122355235797^413*625000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267978769 625000000 4122355235797 12500000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (929895589/2500000000 : ℝ)^541 ≤ (27376540926007/100000000000000 : ℝ)^413 := by
    have hnat : (929895589 : ℕ)^541*100000000000000^413 ≤ 27376540926007^413*2500000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      929895589 2500000000 27376540926007 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2467308181/5000000000 : ℝ)^541 ≤ (39644617179751/100000000000000 : ℝ)^413 := by
    have hnat : (2467308181 : ℕ)^541*100000000000000^413 ≤ 39644617179751^413*5000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2467308181 5000000000 39644617179751 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267978769/625000000 : ℝ), (929895589/2500000000 : ℝ), (2467308181/5000000000 : ℝ)] ![(4122355235797/12500000000000 : ℝ), (27376540926007/100000000000000 : ℝ), (39644617179751/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267978769/625000000 : ℝ)|^541 ≤ (4122355235797/12500000000000 : ℝ)^413
        have hw : |(267978769/625000000 : ℝ)|=(267978769/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(929895589/2500000000 : ℝ)|^541 ≤ (27376540926007/100000000000000 : ℝ)^413
        have hw : |(929895589/2500000000 : ℝ)|=(929895589/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2467308181/5000000000 : ℝ)|^541 ≤ (39644617179751/100000000000000 : ℝ)^413
        have hw : |(2467308181/5000000000 : ℝ)|=(2467308181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_s1_4 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-31607/160000 : ℝ)*x 0 + (2531628613/5000000000 : ℝ)*x 1 + (702933169/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (31607/160000 : ℝ)^541 ≤ (11950059765859/100000000000000 : ℝ)^413 := by
    have hnat : (31607 : ℕ)^541*100000000000000^413 ≤ 11950059765859^413*160000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31607 160000 11950059765859 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2531628613/5000000000 : ℝ)^541 ≤ (41003861547749/100000000000000 : ℝ)^413 := by
    have hnat : (2531628613 : ℕ)^541*100000000000000^413 ≤ 41003861547749^413*5000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2531628613 5000000000 41003861547749 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (702933169/1250000000 : ℝ)^541 ≤ (23523039337147/50000000000000 : ℝ)^413 := by
    have hnat : (702933169 : ℕ)^541*50000000000000^413 ≤ 23523039337147^413*1250000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      702933169 1250000000 23523039337147 50000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-31607/160000 : ℝ), (2531628613/5000000000 : ℝ), (702933169/1250000000 : ℝ)] ![(11950059765859/100000000000000 : ℝ), (41003861547749/100000000000000 : ℝ), (23523039337147/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-31607/160000 : ℝ)|^541 ≤ (11950059765859/100000000000000 : ℝ)^413
        have hw : |(-31607/160000 : ℝ)|=(31607/160000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2531628613/5000000000 : ℝ)|^541 ≤ (41003861547749/100000000000000 : ℝ)^413
        have hw : |(2531628613/5000000000 : ℝ)|=(2531628613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(702933169/1250000000 : ℝ)|^541 ≤ (23523039337147/50000000000000 : ℝ)^413
        have hw : |(702933169/1250000000 : ℝ)|=(702933169/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_s1_5 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5253633621/10000000000 : ℝ)*x 0 + (-342710267/2000000000 : ℝ)*x 1 + (1124693087/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5253633621/10000000000 : ℝ)^541 ≤ (5379385076051/12500000000000 : ℝ)^413 := by
    have hnat : (5253633621 : ℕ)^541*12500000000000^413 ≤ 5379385076051^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253633621 10000000000 5379385076051 12500000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (342710267/2000000000 : ℝ)^541 ≤ (9918839797411/100000000000000 : ℝ)^413 := by
    have hnat : (342710267 : ℕ)^541*100000000000000^413 ≤ 9918839797411^413*2000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      342710267 2000000000 9918839797411 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1124693087/2000000000 : ℝ)^541 ≤ (23523039791941/50000000000000 : ℝ)^413 := by
    have hnat : (1124693087 : ℕ)^541*50000000000000^413 ≤ 23523039791941^413*2000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124693087 2000000000 23523039791941 50000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5253633621/10000000000 : ℝ), (-342710267/2000000000 : ℝ), (1124693087/2000000000 : ℝ)] ![(5379385076051/12500000000000 : ℝ), (9918839797411/100000000000000 : ℝ), (23523039791941/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5253633621/10000000000 : ℝ)|^541 ≤ (5379385076051/12500000000000 : ℝ)^413
        have hw : |(5253633621/10000000000 : ℝ)|=(5253633621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-342710267/2000000000 : ℝ)|^541 ≤ (9918839797411/100000000000000 : ℝ)^413
        have hw : |(-342710267/2000000000 : ℝ)|=(342710267/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1124693087/2000000000 : ℝ)|^541 ≤ (23523039791941/50000000000000 : ℝ)^413
        have hw : |(1124693087/2000000000 : ℝ)|=(1124693087/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_s1_6 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5253633513/10000000000 : ℝ)*x 0 + (1405866383/2500000000 : ℝ)*x 1 + (-856775673/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5253633513/10000000000 : ℝ)^541 ≤ (43035079449541/100000000000000 : ℝ)^413 := by
    have hnat : (5253633513 : ℕ)^541*100000000000000^413 ≤ 43035079449541^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253633513 10000000000 43035079449541 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1405866383/2500000000 : ℝ)^541 ≤ (9409216129379/20000000000000 : ℝ)^413 := by
    have hnat : (1405866383 : ℕ)^541*20000000000000^413 ≤ 9409216129379^413*2500000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1405866383 2500000000 9409216129379 20000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (856775673/5000000000 : ℝ)^541 ≤ (9918839880819/100000000000000 : ℝ)^413 := by
    have hnat : (856775673 : ℕ)^541*100000000000000^413 ≤ 9918839880819^413*5000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      856775673 5000000000 9918839880819 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5253633513/10000000000 : ℝ), (1405866383/2500000000 : ℝ), (-856775673/5000000000 : ℝ)] ![(43035079449541/100000000000000 : ℝ), (9409216129379/20000000000000 : ℝ), (9918839880819/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5253633513/10000000000 : ℝ)|^541 ≤ (43035079449541/100000000000000 : ℝ)^413
        have hw : |(5253633513/10000000000 : ℝ)|=(5253633513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1405866383/2500000000 : ℝ)|^541 ≤ (9409216129379/20000000000000 : ℝ)^413
        have hw : |(1405866383/2500000000 : ℝ)|=(1405866383/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-856775673/5000000000 : ℝ)|^541 ≤ (9918839880819/100000000000000 : ℝ)^413
        have hw : |(-856775673/5000000000 : ℝ)|=(856775673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_s1_7 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4288699259/10000000000 : ℝ)*x 0 + (2459837269/5000000000 : ℝ)*x 1 + (3734789141/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4288699259/10000000000 : ℝ)^541 ≤ (32989310165339/100000000000000 : ℝ)^413 := by
    have hnat : (4288699259 : ℕ)^541*100000000000000^413 ≤ 32989310165339^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4288699259 10000000000 32989310165339 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2459837269/5000000000 : ℝ)^541 ≤ (39487444270227/100000000000000 : ℝ)^413 := by
    have hnat : (2459837269 : ℕ)^541*100000000000000^413 ≤ 39487444270227^413*5000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2459837269 5000000000 39487444270227 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3734789141/10000000000 : ℝ)^541 ≤ (13761622776373/50000000000000 : ℝ)^413 := by
    have hnat : (3734789141 : ℕ)^541*50000000000000^413 ≤ 13761622776373^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3734789141 10000000000 13761622776373 50000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4288699259/10000000000 : ℝ), (2459837269/5000000000 : ℝ), (3734789141/10000000000 : ℝ)] ![(32989310165339/100000000000000 : ℝ), (39487444270227/100000000000000 : ℝ), (13761622776373/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4288699259/10000000000 : ℝ)|^541 ≤ (32989310165339/100000000000000 : ℝ)^413
        have hw : |(4288699259/10000000000 : ℝ)|=(4288699259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2459837269/5000000000 : ℝ)|^541 ≤ (39487444270227/100000000000000 : ℝ)^413
        have hw : |(2459837269/5000000000 : ℝ)|=(2459837269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3734789141/10000000000 : ℝ)|^541 ≤ (13761622776373/50000000000000 : ℝ)^413
        have hw : |(3734789141/10000000000 : ℝ)|=(3734789141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1368_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7787701/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5337/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (201/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (7127/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1927/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5337/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (201/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5337/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (201/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5337/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (201/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5337/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (201/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5337/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (201/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5337/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (201/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (201/12500 : ℝ) ^ (4327/1024 : ℝ) ≤ (1316671810931/50000000000000000000 : ℝ) := by
    have hpowers : (201/12500 : ℝ)^4327 ≤ (1316671810931/50000000000000000000 : ℝ)^1024 := by
      have hnat : (201 : ℕ)^4327*50000000000000000000^1024 ≤ 1316671810931^1024*12500^4327 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        201 12500 1316671810931 50000000000000000000 4327 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (201/12500 : ℝ)) (X := (1316671810931/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4327 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (5337/20000 : ℝ) ^ (4327/1024 : ℝ) ≤ (376394075204207699/100000000000000000000 : ℝ) := by
    have hpowers : (5337/20000 : ℝ)^4327 ≤ (376394075204207699/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5337 : ℕ)^4327*100000000000000000000^1024 ≤ 376394075204207699^1024*20000^4327 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5337 20000 376394075204207699 100000000000000000000 4327 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5337/20000 : ℝ)) (X := (376394075204207699/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4327 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000001316671810931/25000000000000000000 : ℝ) ≤ (625000007789877/625000000000000 : ℝ) ^ (4327/1024 : ℝ) := by
    have hpowers : (25000001316671810931/25000000000000000000 : ℝ)^1024 ≤ (625000007789877/625000000000000 : ℝ)^4327 := by
      have hnat : (25000001316671810931 : ℕ)^1024*625000000000000^4327 ≤ 625000007789877^4327*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000001316671810931 25000000000000000000 625000007789877 625000000000000 1024 4327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625000007789877/625000000000000 : ℝ)) (X := (25000001316671810931/25000000000000000000 : ℝ)) (by norm_num) 4327 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100376396708547829561/100000000000000000000 : ℝ) ≤ (5004447397044687/5000000000000000 : ℝ) ^ (4327/1024 : ℝ) := by
    have hpowers : (100376396708547829561/100000000000000000000 : ℝ)^1024 ≤ (5004447397044687/5000000000000000 : ℝ)^4327 := by
      have hnat : (100376396708547829561 : ℕ)^1024*5000000000000000^4327 ≤ 5004447397044687^4327*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100376396708547829561 100000000000000000000 5004447397044687 5000000000000000 1024 4327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5004447397044687/5000000000000000 : ℝ)) (X := (100376396708547829561/100000000000000000000 : ℝ)) (by norm_num) 4327 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50376394075204207699/50000000000000000000 : ℝ) ≤ (2504447365885179/2500000000000000 : ℝ) ^ (4327/1024 : ℝ) := by
    have hpowers : (50376394075204207699/50000000000000000000 : ℝ)^1024 ≤ (2504447365885179/2500000000000000 : ℝ)^4327 := by
      have hnat : (50376394075204207699 : ℕ)^1024*2500000000000000^4327 ≤ 2504447365885179^4327*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50376394075204207699 50000000000000000000 2504447365885179 2500000000000000 1024 4327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2504447365885179/2500000000000000 : ℝ)) (X := (50376394075204207699/50000000000000000000 : ℝ)) (by norm_num) 4327 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1316671810931/50000000000000000000 : ℝ) ≤ ((5223779122262341929/5224375000000000000 : ℝ)+2*(1482444908557/417950000000000 : ℝ)*(201/12500 : ℝ))^(4327/1024 : ℝ) := by
    rw [show (5223779122262341929/5224375000000000000 : ℝ)+2*(1482444908557/417950000000000 : ℝ)*(201/12500 : ℝ)=(625000007789877/625000000000000 : ℝ) by norm_num, show 1+2*(1316671810931/50000000000000000000 : ℝ)=(25000001316671810931/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(376394075204207699/100000000000000000000 : ℝ)+(1316671810931/50000000000000000000 : ℝ) ≤ ((5223779122262341929/5224375000000000000 : ℝ)+(1482444908557/417950000000000 : ℝ)*((5337/20000 : ℝ)+(201/12500 : ℝ)))^(4327/1024 : ℝ) := by
    rw [show (5223779122262341929/5224375000000000000 : ℝ)+(1482444908557/417950000000000 : ℝ)*((5337/20000 : ℝ)+(201/12500 : ℝ))=(5004447397044687/5000000000000000 : ℝ) by norm_num, show 1+(376394075204207699/100000000000000000000 : ℝ)+(1316671810931/50000000000000000000 : ℝ)=(100376396708547829561/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(376394075204207699/100000000000000000000 : ℝ) ≤ ((5223779122262341929/5224375000000000000 : ℝ)+2*(1482444908557/417950000000000 : ℝ)*(5337/20000 : ℝ))^(4327/1024 : ℝ) := by
    rw [show (5223779122262341929/5224375000000000000 : ℝ)+2*(1482444908557/417950000000000 : ℝ)*(5337/20000 : ℝ)=(2504447365885179/2500000000000000 : ℝ) by norm_num, show 1+2*(376394075204207699/100000000000000000000 : ℝ)=(50376394075204207699/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5223779122262341929/5224375000000000000 : ℝ)*(X 1 0+X 2 0)+(1482444908557/417950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4327/1024 : ℝ)) (lo := (201/12500 : ℝ)) (hi := (5337/20000 : ℝ)) (c := (5223779122262341929/5224375000000000000 : ℝ)) (alpha := (1482444908557/417950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5223779122262341929/5224375000000000000 : ℝ)*(X 0 1+X 2 1)+(1482444908557/417950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4327/1024 : ℝ)) (lo := (201/12500 : ℝ)) (hi := (5337/20000 : ℝ)) (c := (5223779122262341929/5224375000000000000 : ℝ)) (alpha := (1482444908557/417950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5223779122262341929/5224375000000000000 : ℝ)*(X 0 2+X 1 2)+(1482444908557/417950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4327/1024 : ℝ)) (lo := (201/12500 : ℝ)) (hi := (5337/20000 : ℝ)) (c := (5223779122262341929/5224375000000000000 : ℝ)) (alpha := (1482444908557/417950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-197494663/1000000000 : ℝ)*X 0 0+(2815328279/5000000000 : ℝ)*X 0 1+(5056191953/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2701509021/5000000000 : ℝ)*X 1 0+(-285102967/1250000000 : ℝ)*X 1 1+(1011238629/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((337688651/625000000 : ℝ)*X 2 0+(5056192149/10000000000 : ℝ)*X 2 1+(-2280824523/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((267978769/625000000 : ℝ)*X 0 0+(929895589/2500000000 : ℝ)*X 0 1+(2467308181/5000000000 : ℝ)*X 0 2+(267978769/625000000 : ℝ)*X 1 0+(929895589/2500000000 : ℝ)*X 1 1+(2467308181/5000000000 : ℝ)*X 1 2+(267978769/625000000 : ℝ)*X 2 0+(929895589/2500000000 : ℝ)*X 2 1+(2467308181/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-31607/160000 : ℝ)*X 0 0+(2531628613/5000000000 : ℝ)*X 0 1+(702933169/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5253633621/10000000000 : ℝ)*X 1 0+(-342710267/2000000000 : ℝ)*X 1 1+(1124693087/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5253633513/10000000000 : ℝ)*X 2 0+(1405866383/2500000000 : ℝ)*X 2 1+(-856775673/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4288699259/10000000000 : ℝ)*X 0 0+(2459837269/5000000000 : ℝ)*X 0 1+(3734789141/10000000000 : ℝ)*X 0 2+(4288699259/10000000000 : ℝ)*X 1 0+(2459837269/5000000000 : ℝ)*X 1 1+(3734789141/10000000000 : ℝ)*X 1 2+(4288699259/10000000000 : ℝ)*X 2 0+(2459837269/5000000000 : ℝ)*X 2 1+(3734789141/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (98783120582141651760889359/10046875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3288533/50000000000000 : ℝ)*(base1) + (1626410809/100000000000000 : ℝ)*(base19) + (873454197/50000000000000 : ℝ)*(base23) + (156302867/50000000000000 : ℝ)*(upper3) + (799481/10000000000000 : ℝ)*(upper5) + (640952822731247/50000000000000 : ℝ)*(major0) + (640952822731247/50000000000000 : ℝ)*(major1) + (640952822731247/50000000000000 : ℝ)*(major2) + (54398955187211/3125000000000 : ℝ)*(sp0) + (435194298949299/25000000000000 : ℝ)*(sp1) + (1740777075299611/100000000000000 : ℝ)*(sp2) + (82302630825467/10000000000000 : ℝ)*(sp3) + (12262794319/100000000000000 : ℝ)*(sp4) + (5826144461/100000000000000 : ℝ)*(sp7) + (823032140976197/100000000000000 : ℝ)*(f.failure) + (348155764441601/20000000000000 : ℝ)*(f.sum) + (313741678247/3215000000000000000000000000 : ℝ)*base65 + (3095891474592849/20093750000000000000000000000000 : ℝ)*base68 + (39065215768061599/20093750000000000000000000000000 : ℝ)*base70 + (107916888709249099/20093750000000000000000000000000 : ℝ)*base72 + (8012970149851/1607500000000000000000000000 : ℝ)*base73 + (36888409113936599/20093750000000000000000000000000 : ℝ)*base76 + (115745935021499099/20093750000000000000000000000000 : ℝ)*base78 + (19498486491686599/20093750000000000000000000000000 : ℝ)*base80 + (269233075307/200937500000000000000000000 : ℝ)*base81 + (353097/500000000000000000000 : ℝ)*base89 + (353097/500000000000000000000 : ℝ)*base91 + (353097/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1334372720101795819850172099/130609375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (52959331/50000000000000 : ℝ)*(base1) + (2060894409/100000000000000 : ℝ)*(base19) + (1012342149/50000000000000 : ℝ)*(base23) + (120105813/50000000000000 : ℝ)*(upper3) + (228432289/100000000000000 : ℝ)*(upper5) + (164313405392621/12500000000000 : ℝ)*(major0) + (164313405392621/12500000000000 : ℝ)*(major1) + (164313405392621/12500000000000 : ℝ)*(major2) + (10876590893/100000000000000 : ℝ)*(sp1) + (10893629741/100000000000000 : ℝ)*(sp2) + (1785050645997409/100000000000000 : ℝ)*(sp4) + (892518801296723/50000000000000 : ℝ)*(sp5) + (446259405441177/25000000000000 : ℝ)*(sp6) + (421981749867/50000000000 : ℝ)*(sp7) + (421981802826331/50000000000000 : ℝ)*(f.failure) + (1785050540078747/100000000000000 : ℝ)*(f.sum) + (6226693992213/10448750000000000000000000000 : ℝ)*base65 + (194305200168539233/32652343750000000000000000000000 : ℝ)*base68 + (303508435780094091/65304687500000000000000000000000 : ℝ)*base70 + (574103535115531591/65304687500000000000000000000000 : ℝ)*base72 + (26123762578731/20897500000000000000000000000 : ℝ)*base73 + (1534512511422578807/130609375000000000000000000000000 : ℝ)*base76 + (628047165347500341/65304687500000000000000000000000 : ℝ)*base78 + (765808235901172557/130609375000000000000000000000000 : ℝ)*base80 + (45692919621403/41795000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (755031/250000000000000000000 : ℝ)*base89 + (755031/250000000000000000000 : ℝ)*base91 + (755031/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1368_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7787701/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5337/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (201/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (7127/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1927/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1368_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1368_s2_0 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-503221399/2500000000 : ℝ)*x 0 + (5472846523/10000000000 : ℝ)*x 1 + (162177003/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (503221399/2500000000 : ℝ)^541 ≤ (3061918236353/25000000000000 : ℝ)^413 := by
    have hnat : (503221399 : ℕ)^541*25000000000000^413 ≤ 3061918236353^413*2500000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      503221399 2500000000 3061918236353 25000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5472846523/10000000000 : ℝ)^541 ≤ (11350589235671/25000000000000 : ℝ)^413 := by
    have hnat : (5472846523 : ℕ)^541*25000000000000^413 ≤ 11350589235671^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5472846523 10000000000 11350589235671 25000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (162177003/312500000 : ℝ)^541 ≤ (8469994018897/20000000000000 : ℝ)^413 := by
    have hnat : (162177003 : ℕ)^541*20000000000000^413 ≤ 8469994018897^413*312500000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162177003 312500000 8469994018897 20000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-503221399/2500000000 : ℝ), (5472846523/10000000000 : ℝ), (162177003/312500000 : ℝ)] ![(3061918236353/25000000000000 : ℝ), (11350589235671/25000000000000 : ℝ), (8469994018897/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-503221399/2500000000 : ℝ)|^541 ≤ (3061918236353/25000000000000 : ℝ)^413
        have hw : |(-503221399/2500000000 : ℝ)|=(503221399/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5472846523/10000000000 : ℝ)|^541 ≤ (11350589235671/25000000000000 : ℝ)^413
        have hw : |(5472846523/10000000000 : ℝ)|=(5472846523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(162177003/312500000 : ℝ)|^541 ≤ (8469994018897/20000000000000 : ℝ)^413
        have hw : |(162177003/312500000 : ℝ)|=(162177003/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_s2_1 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5364152493/10000000000 : ℝ)*x 0 + (-539751479/2500000000 : ℝ)*x 1 + (2594832171/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5364152493/10000000000 : ℝ)^541 ≤ (1768992947619/4000000000000 : ℝ)^413 := by
    have hnat : (5364152493 : ℕ)^541*4000000000000^413 ≤ 1768992947619^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5364152493 10000000000 1768992947619 4000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539751479/2500000000 : ℝ)^541 ≤ (1678150446023/12500000000000 : ℝ)^413 := by
    have hnat : (539751479 : ℕ)^541*12500000000000^413 ≤ 1678150446023^413*2500000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539751479 2500000000 1678150446023 12500000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2594832171/5000000000 : ℝ)^541 ≤ (338799781793/800000000000 : ℝ)^413 := by
    have hnat : (2594832171 : ℕ)^541*800000000000^413 ≤ 338799781793^413*5000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2594832171 5000000000 338799781793 800000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5364152493/10000000000 : ℝ), (-539751479/2500000000 : ℝ), (2594832171/5000000000 : ℝ)] ![(1768992947619/4000000000000 : ℝ), (1678150446023/12500000000000 : ℝ), (338799781793/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5364152493/10000000000 : ℝ)|^541 ≤ (1768992947619/4000000000000 : ℝ)^413
        have hw : |(5364152493/10000000000 : ℝ)|=(5364152493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-539751479/2500000000 : ℝ)|^541 ≤ (1678150446023/12500000000000 : ℝ)^413
        have hw : |(-539751479/2500000000 : ℝ)|=(539751479/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2594832171/5000000000 : ℝ)|^541 ≤ (338799781793/800000000000 : ℝ)^413
        have hw : |(2594832171/5000000000 : ℝ)|=(2594832171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_s2_2 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5364152503/10000000000 : ℝ)*x 0 + (2594832159/5000000000 : ℝ)*x 1 + (-431801187/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5364152503/10000000000 : ℝ)^541 ≤ (5528102974809/12500000000000 : ℝ)^413 := by
    have hnat : (5364152503 : ℕ)^541*12500000000000^413 ≤ 5528102974809^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5364152503 10000000000 5528102974809 12500000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2594832159/5000000000 : ℝ)^541 ≤ (21174986233787/50000000000000 : ℝ)^413 := by
    have hnat : (2594832159 : ℕ)^541*50000000000000^413 ≤ 21174986233787^413*5000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2594832159 5000000000 21174986233787 50000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (431801187/2000000000 : ℝ)^541 ≤ (3356300930737/25000000000000 : ℝ)^413 := by
    have hnat : (431801187 : ℕ)^541*25000000000000^413 ≤ 3356300930737^413*2000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431801187 2000000000 3356300930737 25000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5364152503/10000000000 : ℝ), (2594832159/5000000000 : ℝ), (-431801187/2000000000 : ℝ)] ![(5528102974809/12500000000000 : ℝ), (21174986233787/50000000000000 : ℝ), (3356300930737/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5364152503/10000000000 : ℝ)|^541 ≤ (5528102974809/12500000000000 : ℝ)^413
        have hw : |(5364152503/10000000000 : ℝ)|=(5364152503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2594832159/5000000000 : ℝ)|^541 ≤ (21174986233787/50000000000000 : ℝ)^413
        have hw : |(2594832159/5000000000 : ℝ)|=(2594832159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-431801187/2000000000 : ℝ)|^541 ≤ (3356300930737/25000000000000 : ℝ)^413
        have hw : |(-431801187/2000000000 : ℝ)|=(431801187/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_s2_3 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (862853621/2000000000 : ℝ)*x 0 + (1006092881/2500000000 : ℝ)*x 1 + (577915561/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (862853621/2000000000 : ℝ)^541 ≤ (33247183528623/100000000000000 : ℝ)^413 := by
    have hnat : (862853621 : ℕ)^541*100000000000000^413 ≤ 33247183528623^413*2000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      862853621 2000000000 33247183528623 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1006092881/2500000000 : ℝ)^541 ≤ (3793963912341/12500000000000 : ℝ)^413 := by
    have hnat : (1006092881 : ℕ)^541*12500000000000^413 ≤ 3793963912341^413*2500000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1006092881 2500000000 3793963912341 12500000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (577915561/1250000000 : ℝ)^541 ≤ (2275069072573/6250000000000 : ℝ)^413 := by
    have hnat : (577915561 : ℕ)^541*6250000000000^413 ≤ 2275069072573^413*1250000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      577915561 1250000000 2275069072573 6250000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(862853621/2000000000 : ℝ), (1006092881/2500000000 : ℝ), (577915561/1250000000 : ℝ)] ![(33247183528623/100000000000000 : ℝ), (3793963912341/12500000000000 : ℝ), (2275069072573/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(862853621/2000000000 : ℝ)|^541 ≤ (33247183528623/100000000000000 : ℝ)^413
        have hw : |(862853621/2000000000 : ℝ)|=(862853621/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1006092881/2500000000 : ℝ)|^541 ≤ (3793963912341/12500000000000 : ℝ)^413
        have hw : |(1006092881/2500000000 : ℝ)|=(1006092881/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(577915561/1250000000 : ℝ)|^541 ≤ (2275069072573/6250000000000 : ℝ)^413
        have hw : |(577915561/1250000000 : ℝ)|=(577915561/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_s2_4 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1006472229/5000000000 : ℝ)*x 0 + (648923831/1250000000 : ℝ)*x 1 + (2735552411/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1006472229/5000000000 : ℝ)^541 ≤ (2449628420587/20000000000000 : ℝ)^413 := by
    have hnat : (1006472229 : ℕ)^541*20000000000000^413 ≤ 2449628420587^413*5000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1006472229 5000000000 2449628420587 20000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (648923831/1250000000 : ℝ)^541 ≤ (42368427179953/100000000000000 : ℝ)^413 := by
    have hnat : (648923831 : ℕ)^541*100000000000000^413 ≤ 42368427179953^413*1250000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      648923831 1250000000 42368427179953 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2735552411/5000000000 : ℝ)^541 ≤ (22691715347393/50000000000000 : ℝ)^413 := by
    have hnat : (2735552411 : ℕ)^541*50000000000000^413 ≤ 22691715347393^413*5000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2735552411 5000000000 22691715347393 50000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1006472229/5000000000 : ℝ), (648923831/1250000000 : ℝ), (2735552411/5000000000 : ℝ)] ![(2449628420587/20000000000000 : ℝ), (42368427179953/100000000000000 : ℝ), (22691715347393/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1006472229/5000000000 : ℝ)|^541 ≤ (2449628420587/20000000000000 : ℝ)^413
        have hw : |(-1006472229/5000000000 : ℝ)|=(1006472229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(648923831/1250000000 : ℝ)|^541 ≤ (42368427179953/100000000000000 : ℝ)^413
        have hw : |(648923831/1250000000 : ℝ)|=(648923831/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2735552411/5000000000 : ℝ)|^541 ≤ (22691715347393/50000000000000 : ℝ)^413
        have hw : |(2735552411/5000000000 : ℝ)|=(2735552411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_s2_5 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (42327681/80000000 : ℝ)*x 0 + (-938782587/5000000000 : ℝ)*x 1 + (136777619/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42327681/80000000 : ℝ)^541 ≤ (339344092031/781250000000 : ℝ)^413 := by
    have hnat : (42327681 : ℕ)^541*781250000000^413 ≤ 339344092031^413*80000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42327681 80000000 339344092031 781250000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (938782587/5000000000 : ℝ)^541 ≤ (5590263094287/50000000000000 : ℝ)^413 := by
    have hnat : (938782587 : ℕ)^541*50000000000000^413 ≤ 5590263094287^413*5000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      938782587 5000000000 5590263094287 50000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (136777619/250000000 : ℝ)^541 ≤ (9076686004219/20000000000000 : ℝ)^413 := by
    have hnat : (136777619 : ℕ)^541*20000000000000^413 ≤ 9076686004219^413*250000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136777619 250000000 9076686004219 20000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42327681/80000000 : ℝ), (-938782587/5000000000 : ℝ), (136777619/250000000 : ℝ)] ![(339344092031/781250000000 : ℝ), (5590263094287/50000000000000 : ℝ), (9076686004219/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42327681/80000000 : ℝ)|^541 ≤ (339344092031/781250000000 : ℝ)^413
        have hw : |(42327681/80000000 : ℝ)|=(42327681/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-938782587/5000000000 : ℝ)|^541 ≤ (5590263094287/50000000000000 : ℝ)^413
        have hw : |(-938782587/5000000000 : ℝ)|=(938782587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(136777619/250000000 : ℝ)|^541 ≤ (9076686004219/20000000000000 : ℝ)^413
        have hw : |(136777619/250000000 : ℝ)|=(136777619/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_s2_6 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2645480039/5000000000 : ℝ)*x 0 + (5471104823/10000000000 : ℝ)*x 1 + (-1877565149/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2645480039/5000000000 : ℝ)^541 ≤ (21718021637269/50000000000000 : ℝ)^413 := by
    have hnat : (2645480039 : ℕ)^541*50000000000000^413 ≤ 21718021637269^413*5000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2645480039 5000000000 21718021637269 50000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5471104823/10000000000 : ℝ)^541 ≤ (11345857676413/25000000000000 : ℝ)^413 := by
    have hnat : (5471104823 : ℕ)^541*25000000000000^413 ≤ 11345857676413^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5471104823 10000000000 11345857676413 25000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1877565149/10000000000 : ℝ)^541 ≤ (2236105198713/20000000000000 : ℝ)^413 := by
    have hnat : (1877565149 : ℕ)^541*20000000000000^413 ≤ 2236105198713^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1877565149 10000000000 2236105198713 20000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2645480039/5000000000 : ℝ), (5471104823/10000000000 : ℝ), (-1877565149/10000000000 : ℝ)] ![(21718021637269/50000000000000 : ℝ), (11345857676413/25000000000000 : ℝ), (2236105198713/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2645480039/5000000000 : ℝ)|^541 ≤ (21718021637269/50000000000000 : ℝ)^413
        have hw : |(2645480039/5000000000 : ℝ)|=(2645480039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5471104823/10000000000 : ℝ)|^541 ≤ (11345857676413/25000000000000 : ℝ)^413
        have hw : |(5471104823/10000000000 : ℝ)|=(5471104823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1877565149/10000000000 : ℝ)|^541 ≤ (2236105198713/20000000000000 : ℝ)^413
        have hw : |(-1877565149/10000000000 : ℝ)|=(1877565149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_s2_7 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4314392817/10000000000 : ℝ)*x 0 + (1154918287/2500000000 : ℝ)*x 1 + (25175343/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4314392817/10000000000 : ℝ)^541 ≤ (8312110617229/25000000000000 : ℝ)^413 := by
    have hnat : (4314392817 : ℕ)^541*25000000000000^413 ≤ 8312110617229^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4314392817 10000000000 8312110617229 25000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1154918287/2500000000 : ℝ)^541 ≤ (18181725780003/50000000000000 : ℝ)^413 := by
    have hnat : (1154918287 : ℕ)^541*50000000000000^413 ≤ 18181725780003^413*2500000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1154918287 2500000000 18181725780003 50000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (25175343/62500000 : ℝ)^541 ≤ (6077621190703/20000000000000 : ℝ)^413 := by
    have hnat : (25175343 : ℕ)^541*20000000000000^413 ≤ 6077621190703^413*62500000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25175343 62500000 6077621190703 20000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4314392817/10000000000 : ℝ), (1154918287/2500000000 : ℝ), (25175343/62500000 : ℝ)] ![(8312110617229/25000000000000 : ℝ), (18181725780003/50000000000000 : ℝ), (6077621190703/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4314392817/10000000000 : ℝ)|^541 ≤ (8312110617229/25000000000000 : ℝ)^413
        have hw : |(4314392817/10000000000 : ℝ)|=(4314392817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1154918287/2500000000 : ℝ)|^541 ≤ (18181725780003/50000000000000 : ℝ)^413
        have hw : |(1154918287/2500000000 : ℝ)|=(1154918287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(25175343/62500000 : ℝ)|^541 ≤ (6077621190703/20000000000000 : ℝ)^413
        have hw : |(25175343/62500000 : ℝ)|=(25175343/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1368_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7787701/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1927/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7127/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10017/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3201/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1927/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (7127/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1927/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (7127/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1927/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (7127/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1927/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (7127/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1927/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (7127/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1927/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (7127/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (7127/100000 : ℝ) ^ (4327/1024 : ℝ) ≤ (142186685641613/10000000000000000000 : ℝ) := by
    have hpowers : (7127/100000 : ℝ)^4327 ≤ (142186685641613/10000000000000000000 : ℝ)^1024 := by
      have hnat : (7127 : ℕ)^4327*10000000000000000000^1024 ≤ 142186685641613^1024*100000^4327 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7127 100000 142186685641613 10000000000000000000 4327 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7127/100000 : ℝ)) (X := (142186685641613/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4327 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1927/10000 : ℝ) ^ (4327/1024 : ℝ) ≤ (5944101916387577/6250000000000000000 : ℝ) := by
    have hpowers : (1927/10000 : ℝ)^4327 ≤ (5944101916387577/6250000000000000000 : ℝ)^1024 := by
      have hnat : (1927 : ℕ)^4327*6250000000000000000^1024 ≤ 5944101916387577^1024*10000^4327 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1927 10000 5944101916387577 6250000000000000000 4327 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1927/10000 : ℝ)) (X := (5944101916387577/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4327 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000142186685641613/5000000000000000000 : ℝ) ≤ (400002691889731/400000000000000 : ℝ) ^ (4327/1024 : ℝ) := by
    have hpowers : (5000142186685641613/5000000000000000000 : ℝ)^1024 ≤ (400002691889731/400000000000000 : ℝ)^4327 := by
      have hnat : (5000142186685641613 : ℕ)^1024*400000000000000^4327 ≤ 400002691889731^4327*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000142186685641613 5000000000000000000 400002691889731 400000000000000 1024 4327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400002691889731/400000000000000 : ℝ)) (X := (5000142186685641613/5000000000000000000 : ℝ)) (by norm_num) 4327 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50048263748759308681/50000000000000000000 : ℝ) ≤ (5001141758284973/5000000000000000 : ℝ) ^ (4327/1024 : ℝ) := by
    have hpowers : (50048263748759308681/50000000000000000000 : ℝ)^1024 ≤ (5001141758284973/5000000000000000 : ℝ)^4327 := by
      have hnat : (50048263748759308681 : ℕ)^1024*5000000000000000^4327 ≤ 5001141758284973^4327*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50048263748759308681 50000000000000000000 5001141758284973 5000000000000000 1024 4327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001141758284973/5000000000000000 : ℝ)) (X := (50048263748759308681/50000000000000000000 : ℝ)) (by norm_num) 4327 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3130944101916387577/3125000000000000000 : ℝ) ≤ (10004499735896617/10000000000000000 : ℝ) ^ (4327/1024 : ℝ) := by
    have hpowers : (3130944101916387577/3125000000000000000 : ℝ)^1024 ≤ (10004499735896617/10000000000000000 : ℝ)^4327 := by
      have hnat : (3130944101916387577 : ℕ)^1024*10000000000000000^4327 ≤ 10004499735896617^4327*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3130944101916387577 3125000000000000000 10004499735896617 10000000000000000 1024 4327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004499735896617/10000000000000000 : ℝ)) (X := (3130944101916387577/3125000000000000000 : ℝ)) (by norm_num) 4327 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(142186685641613/10000000000000000000 : ℝ) ≤ ((121399227200142719891/121430000000000000000 : ℝ)+2*(2216219326671/1214300000000000 : ℝ)*(7127/100000 : ℝ))^(4327/1024 : ℝ) := by
    rw [show (121399227200142719891/121430000000000000000 : ℝ)+2*(2216219326671/1214300000000000 : ℝ)*(7127/100000 : ℝ)=(400002691889731/400000000000000 : ℝ) by norm_num, show 1+2*(142186685641613/10000000000000000000 : ℝ)=(5000142186685641613/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5944101916387577/6250000000000000000 : ℝ)+(142186685641613/10000000000000000000 : ℝ) ≤ ((121399227200142719891/121430000000000000000 : ℝ)+(2216219326671/1214300000000000 : ℝ)*((1927/10000 : ℝ)+(7127/100000 : ℝ)))^(4327/1024 : ℝ) := by
    rw [show (121399227200142719891/121430000000000000000 : ℝ)+(2216219326671/1214300000000000 : ℝ)*((1927/10000 : ℝ)+(7127/100000 : ℝ))=(5001141758284973/5000000000000000 : ℝ) by norm_num, show 1+(5944101916387577/6250000000000000000 : ℝ)+(142186685641613/10000000000000000000 : ℝ)=(50048263748759308681/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5944101916387577/6250000000000000000 : ℝ) ≤ ((121399227200142719891/121430000000000000000 : ℝ)+2*(2216219326671/1214300000000000 : ℝ)*(1927/10000 : ℝ))^(4327/1024 : ℝ) := by
    rw [show (121399227200142719891/121430000000000000000 : ℝ)+2*(2216219326671/1214300000000000 : ℝ)*(1927/10000 : ℝ)=(10004499735896617/10000000000000000 : ℝ) by norm_num, show 1+2*(5944101916387577/6250000000000000000 : ℝ)=(3130944101916387577/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (121399227200142719891/121430000000000000000 : ℝ)*(X 1 0+X 2 0)+(2216219326671/1214300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4327/1024 : ℝ)) (lo := (7127/100000 : ℝ)) (hi := (1927/10000 : ℝ)) (c := (121399227200142719891/121430000000000000000 : ℝ)) (alpha := (2216219326671/1214300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (121399227200142719891/121430000000000000000 : ℝ)*(X 0 1+X 2 1)+(2216219326671/1214300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4327/1024 : ℝ)) (lo := (7127/100000 : ℝ)) (hi := (1927/10000 : ℝ)) (c := (121399227200142719891/121430000000000000000 : ℝ)) (alpha := (2216219326671/1214300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (121399227200142719891/121430000000000000000 : ℝ)*(X 0 2+X 1 2)+(2216219326671/1214300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4327/1024 : ℝ)) (lo := (7127/100000 : ℝ)) (hi := (1927/10000 : ℝ)) (c := (121399227200142719891/121430000000000000000 : ℝ)) (alpha := (2216219326671/1214300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-503221399/2500000000 : ℝ)*X 0 0+(5472846523/10000000000 : ℝ)*X 0 1+(162177003/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5364152493/10000000000 : ℝ)*X 1 0+(-539751479/2500000000 : ℝ)*X 1 1+(2594832171/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5364152503/10000000000 : ℝ)*X 2 0+(2594832159/5000000000 : ℝ)*X 2 1+(-431801187/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((862853621/2000000000 : ℝ)*X 0 0+(1006092881/2500000000 : ℝ)*X 0 1+(577915561/1250000000 : ℝ)*X 0 2+(862853621/2000000000 : ℝ)*X 1 0+(1006092881/2500000000 : ℝ)*X 1 1+(577915561/1250000000 : ℝ)*X 1 2+(862853621/2000000000 : ℝ)*X 2 0+(1006092881/2500000000 : ℝ)*X 2 1+(577915561/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1006472229/5000000000 : ℝ)*X 0 0+(648923831/1250000000 : ℝ)*X 0 1+(2735552411/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((42327681/80000000 : ℝ)*X 1 0+(-938782587/5000000000 : ℝ)*X 1 1+(136777619/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2645480039/5000000000 : ℝ)*X 2 0+(5471104823/10000000000 : ℝ)*X 2 1+(-1877565149/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4314392817/10000000000 : ℝ)*X 0 0+(1154918287/2500000000 : ℝ)*X 0 1+(25175343/62500000 : ℝ)*X 0 2+(4314392817/10000000000 : ℝ)*X 1 0+(1154918287/2500000000 : ℝ)*X 1 1+(25175343/62500000 : ℝ)*X 1 2+(4314392817/10000000000 : ℝ)*X 2 0+(1154918287/2500000000 : ℝ)*X 2 1+(25175343/62500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8985550390736492377875712299/1517875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (945623247/100000000000000 : ℝ)*(base19) + (912125639/100000000000000 : ℝ)*(base23) + (429999/2000000000000 : ℝ)*(lower2) + (138461949/100000000000000 : ℝ)*(upper3) + (46316317/50000000000000 : ℝ)*(upper5) + (1300228580587637/50000000000000 : ℝ)*(major0) + (1300228580587637/50000000000000 : ℝ)*(major1) + (1300228580587637/50000000000000 : ℝ)*(major2) + (441413434049931/12500000000000 : ℝ)*(sp0) + (353132085608439/10000000000000 : ℝ)*(sp1) + (1765660444790999/50000000000000 : ℝ)*(sp2) + (41739648714053/2500000000000 : ℝ)*(sp3) + (14329308189/100000000000000 : ℝ)*(sp4) + (6374753371/100000000000000 : ℝ)*(sp7) + (1669592323315491/100000000000000 : ℝ)*(f.failure) + (882830450426909/25000000000000 : ℝ)*(f.sum) + (156080469899899/60715000000000000000000000000 : ℝ)*base65 + (51696758182585287567/6071500000000000000000000000000000 : ℝ)*base67 + (30122212112382287567/6071500000000000000000000000000000 : ℝ)*base69 + (41612569925944212433/6071500000000000000000000000000000 : ℝ)*base72 + (122301457473017/30357500000000000000000000000 : ℝ)*base73 + (45252298954881287567/6071500000000000000000000000000000 : ℝ)*base75 + (41211452924289787567/6071500000000000000000000000000000 : ℝ)*base77 + (46733843726043287567/6071500000000000000000000000000000 : ℝ)*base79 + (3936288014449/15178750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (2576191/500000000000000000000 : ℝ)*base89 + (2576191/500000000000000000000 : ℝ)*base91 + (2576191/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12671850778365182277859420131/1517875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1720731121/100000000000000 : ℝ)*(base19) + (933353891/50000000000000 : ℝ)*(base23) + (23945923/12500000000000 : ℝ)*(upper3) + (9221361/12500000000000 : ℝ)*(lower4) + (2935923/2000000000000 : ℝ)*(upper5) + (1316338874098547/50000000000000 : ℝ)*(major0) + (1316338874098547/50000000000000 : ℝ)*(major1) + (1316338874098547/50000000000000 : ℝ)*(major2) + (2511935949/12500000000000 : ℝ)*(sp1) + (11432280183/50000000000000 : ℝ)*(sp2) + (1787538026721469/50000000000000 : ℝ)*(sp4) + (143002169488969/4000000000000 : ℝ)*(sp5) + (357505132217479/10000000000000 : ℝ)*(sp6) + (845139582335369/50000000000000 : ℝ)*(sp7) + (845139582335369/50000000000000 : ℝ)*(f.failure) + (1787538026721469/50000000000000 : ℝ)*(f.sum) + (1111169247429/948671875000000000000000000 : ℝ)*base66 + (26910694809877201623/6071500000000000000000000000000000 : ℝ)*base68 + (40562835519979201623/6071500000000000000000000000000000 : ℝ)*base70 + (1816559210725701623/6071500000000000000000000000000000 : ℝ)*base72 + (92871892129839/15178750000000000000000000000 : ℝ)*base74 + (41151822190581201623/6071500000000000000000000000000000 : ℝ)*base76 + (13573875233578798377/6071500000000000000000000000000000 : ℝ)*base77 + (39481060008358201623/6071500000000000000000000000000000 : ℝ)*base80 + (142202833101363/30357500000000000000000000000 : ℝ)*base82 + (496669/250000000000000000000 : ℝ)*base89 + (496669/250000000000000000000 : ℝ)*base91 + (496669/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1368_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7787701/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1927/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7127/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10017/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3201/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1368_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1368_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7787701/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10017/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3201/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1368_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1368_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1368_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7787701/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10017/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3201/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1368_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
