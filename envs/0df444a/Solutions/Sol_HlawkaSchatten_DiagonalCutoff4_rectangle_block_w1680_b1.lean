-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1680_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:32:13.763993+00:00
-- url     : https://prove2.me/submissions/c55d8f50-2784-43d8-a13a-dc7f14766a66

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
theorem support_rectangle_w1680_s3_0 (p : ℝ) (hpa : (5055/1024 : ℝ) ≤ p) (hpb : p ≤ (5063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1528310887/10000000000 : ℝ)*x 0 + (5490111121/10000000000 : ℝ)*x 1 + (513335941/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1528310887/10000000000 : ℝ)^5063 ≤ (9492627739983/100000000000000 : ℝ)^4039 := by
    have hnat : (1528310887 : ℕ)^5063*100000000000000^4039 ≤ 9492627739983^4039*10000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1528310887 10000000000 9492627739983 100000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5490111121/10000000000 : ℝ)^5063 ≤ (47158244997283/100000000000000 : ℝ)^4039 := by
    have hnat : (5490111121 : ℕ)^5063*100000000000000^4039 ≤ 47158244997283^4039*10000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5490111121 10000000000 47158244997283 100000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (513335941/1000000000 : ℝ)^5063 ≤ (43349127245531/100000000000000 : ℝ)^4039 := by
    have hnat : (513335941 : ℕ)^5063*100000000000000^4039 ≤ 43349127245531^4039*1000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513335941 1000000000 43349127245531 100000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5063/1024 : ℝ)) 5063 4039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1528310887/10000000000 : ℝ), (5490111121/10000000000 : ℝ), (513335941/1000000000 : ℝ)] ![(9492627739983/100000000000000 : ℝ), (47158244997283/100000000000000 : ℝ), (43349127245531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1528310887/10000000000 : ℝ)|^5063 ≤ (9492627739983/100000000000000 : ℝ)^4039
        have hw : |(-1528310887/10000000000 : ℝ)|=(1528310887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5490111121/10000000000 : ℝ)|^5063 ≤ (47158244997283/100000000000000 : ℝ)^4039
        have hw : |(5490111121/10000000000 : ℝ)|=(5490111121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(513335941/1000000000 : ℝ)|^5063 ≤ (43349127245531/100000000000000 : ℝ)^4039
        have hw : |(513335941/1000000000 : ℝ)|=(513335941/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1680_s3_1 (p : ℝ) (hpa : (5055/1024 : ℝ) ≤ p) (hpb : p ≤ (5063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070709071/2000000000 : ℝ)*x 0 + (-1713801533/10000000000 : ℝ)*x 1 + (5133359221/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070709071/2000000000 : ℝ)^5063 ≤ (5711556676339/12500000000000 : ℝ)^4039 := by
    have hnat : (1070709071 : ℕ)^5063*12500000000000^4039 ≤ 5711556676339^4039*2000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070709071 2000000000 5711556676339 12500000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1713801533/10000000000 : ℝ)^5063 ≤ (10958421326843/100000000000000 : ℝ)^4039 := by
    have hnat : (1713801533 : ℕ)^5063*100000000000000^4039 ≤ 10958421326843^4039*10000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1713801533 10000000000 10958421326843 100000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5133359221/10000000000 : ℝ)^5063 ≤ (21674562622433/50000000000000 : ℝ)^4039 := by
    have hnat : (5133359221 : ℕ)^5063*50000000000000^4039 ≤ 21674562622433^4039*10000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5133359221 10000000000 21674562622433 50000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5063/1024 : ℝ)) 5063 4039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070709071/2000000000 : ℝ), (-1713801533/10000000000 : ℝ), (5133359221/10000000000 : ℝ)] ![(5711556676339/12500000000000 : ℝ), (10958421326843/100000000000000 : ℝ), (21674562622433/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070709071/2000000000 : ℝ)|^5063 ≤ (5711556676339/12500000000000 : ℝ)^4039
        have hw : |(1070709071/2000000000 : ℝ)|=(1070709071/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1713801533/10000000000 : ℝ)|^5063 ≤ (10958421326843/100000000000000 : ℝ)^4039
        have hw : |(-1713801533/10000000000 : ℝ)|=(1713801533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5133359221/10000000000 : ℝ)|^5063 ≤ (21674562622433/50000000000000 : ℝ)^4039
        have hw : |(5133359221/10000000000 : ℝ)|=(5133359221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1680_s3_2 (p : ℝ) (hpa : (5055/1024 : ℝ) ≤ p) (hpb : p ≤ (5063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353545369/10000000000 : ℝ)*x 0 + (2566679613/5000000000 : ℝ)*x 1 + (-1713801507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353545369/10000000000 : ℝ)^5063 ≤ (2855778347531/6250000000000 : ℝ)^4039 := by
    have hnat : (5353545369 : ℕ)^5063*6250000000000^4039 ≤ 2855778347531^4039*10000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353545369 10000000000 2855778347531 6250000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2566679613/5000000000 : ℝ)^5063 ≤ (43349125297793/100000000000000 : ℝ)^4039 := by
    have hnat : (2566679613 : ℕ)^5063*100000000000000^4039 ≤ 43349125297793^4039*5000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2566679613 5000000000 43349125297793 100000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1713801507/10000000000 : ℝ)^5063 ≤ (2739605279611/25000000000000 : ℝ)^4039 := by
    have hnat : (1713801507 : ℕ)^5063*25000000000000^4039 ≤ 2739605279611^4039*10000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1713801507 10000000000 2739605279611 25000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5063/1024 : ℝ)) 5063 4039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353545369/10000000000 : ℝ), (2566679613/5000000000 : ℝ), (-1713801507/10000000000 : ℝ)] ![(2855778347531/6250000000000 : ℝ), (43349125297793/100000000000000 : ℝ), (2739605279611/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353545369/10000000000 : ℝ)|^5063 ≤ (2855778347531/6250000000000 : ℝ)^4039
        have hw : |(5353545369/10000000000 : ℝ)|=(5353545369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2566679613/5000000000 : ℝ)|^5063 ≤ (43349125297793/100000000000000 : ℝ)^4039
        have hw : |(2566679613/5000000000 : ℝ)|=(2566679613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1713801507/10000000000 : ℝ)|^5063 ≤ (2739605279611/25000000000000 : ℝ)^4039
        have hw : |(-1713801507/10000000000 : ℝ)|=(1713801507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1680_s3_3 (p : ℝ) (hpa : (5055/1024 : ℝ) ≤ p) (hpb : p ≤ (5063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1036295847/2500000000 : ℝ)*x 0 + (1841246667/5000000000 : ℝ)*x 1 + (464631577/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1036295847/2500000000 : ℝ)^5063 ≤ (33157390342009/100000000000000 : ℝ)^4039 := by
    have hnat : (1036295847 : ℕ)^5063*100000000000000^4039 ≤ 33157390342009^4039*2500000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036295847 2500000000 33157390342009 100000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1841246667/5000000000 : ℝ)^5063 ≤ (28585564090489/100000000000000 : ℝ)^4039 := by
    have hnat : (1841246667 : ℕ)^5063*100000000000000^4039 ≤ 28585564090489^4039*5000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1841246667 5000000000 28585564090489 100000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (464631577/1000000000 : ℝ)^5063 ≤ (38257045555083/100000000000000 : ℝ)^4039 := by
    have hnat : (464631577 : ℕ)^5063*100000000000000^4039 ≤ 38257045555083^4039*1000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      464631577 1000000000 38257045555083 100000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5063/1024 : ℝ)) 5063 4039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1036295847/2500000000 : ℝ), (1841246667/5000000000 : ℝ), (464631577/1000000000 : ℝ)] ![(33157390342009/100000000000000 : ℝ), (28585564090489/100000000000000 : ℝ), (38257045555083/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1036295847/2500000000 : ℝ)|^5063 ≤ (33157390342009/100000000000000 : ℝ)^4039
        have hw : |(1036295847/2500000000 : ℝ)|=(1036295847/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1841246667/5000000000 : ℝ)|^5063 ≤ (28585564090489/100000000000000 : ℝ)^4039
        have hw : |(1841246667/5000000000 : ℝ)|=(1841246667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(464631577/1000000000 : ℝ)|^5063 ≤ (38257045555083/100000000000000 : ℝ)^4039
        have hw : |(464631577/1000000000 : ℝ)|=(464631577/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1680_s3_4 (p : ℝ) (hpa : (5055/1024 : ℝ) ≤ p) (hpb : p ≤ (5063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-382119829/2500000000 : ℝ)*x 0 + (1027441681/2000000000 : ℝ)*x 1 + (548620463/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (382119829/2500000000 : ℝ)^5063 ≤ (4746969564821/50000000000000 : ℝ)^4039 := by
    have hnat : (382119829 : ℕ)^5063*50000000000000^4039 ≤ 4746969564821^4039*2500000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      382119829 2500000000 4746969564821 50000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1027441681/2000000000 : ℝ)^5063 ≤ (21694937391891/50000000000000 : ℝ)^4039 := by
    have hnat : (1027441681 : ℕ)^5063*50000000000000^4039 ≤ 21694937391891^4039*2000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027441681 2000000000 21694937391891 50000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (548620463/1000000000 : ℝ)^5063 ≤ (23558093033619/50000000000000 : ℝ)^4039 := by
    have hnat : (548620463 : ℕ)^5063*50000000000000^4039 ≤ 23558093033619^4039*1000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548620463 1000000000 23558093033619 50000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5063/1024 : ℝ)) 5063 4039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-382119829/2500000000 : ℝ), (1027441681/2000000000 : ℝ), (548620463/1000000000 : ℝ)] ![(4746969564821/50000000000000 : ℝ), (21694937391891/50000000000000 : ℝ), (23558093033619/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-382119829/2500000000 : ℝ)|^5063 ≤ (4746969564821/50000000000000 : ℝ)^4039
        have hw : |(-382119829/2500000000 : ℝ)|=(382119829/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1027441681/2000000000 : ℝ)|^5063 ≤ (21694937391891/50000000000000 : ℝ)^4039
        have hw : |(1027441681/2000000000 : ℝ)|=(1027441681/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(548620463/1000000000 : ℝ)|^5063 ≤ (23558093033619/50000000000000 : ℝ)^4039
        have hw : |(548620463/1000000000 : ℝ)|=(548620463/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1680_s3_5 (p : ℝ) (hpa : (5055/1024 : ℝ) ≤ p) (hpb : p ≤ (5063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2629142603/5000000000 : ℝ)*x 0 + (-54438249/400000000 : ℝ)*x 1 + (5486204561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2629142603/5000000000 : ℝ)^5063 ≤ (1396112142823/3125000000000 : ℝ)^4039 := by
    have hnat : (2629142603 : ℕ)^5063*3125000000000^4039 ≤ 1396112142823^4039*5000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629142603 5000000000 1396112142823 3125000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (54438249/400000000 : ℝ)^5063 ≤ (4104113044109/50000000000000 : ℝ)^4039 := by
    have hnat : (54438249 : ℕ)^5063*50000000000000^4039 ≤ 4104113044109^4039*400000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54438249 400000000 4104113044109 50000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5486204561/10000000000 : ℝ)^5063 ≤ (23558092662211/50000000000000 : ℝ)^4039 := by
    have hnat : (5486204561 : ℕ)^5063*50000000000000^4039 ≤ 23558092662211^4039*10000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5486204561 10000000000 23558092662211 50000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5063/1024 : ℝ)) 5063 4039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2629142603/5000000000 : ℝ), (-54438249/400000000 : ℝ), (5486204561/10000000000 : ℝ)] ![(1396112142823/3125000000000 : ℝ), (4104113044109/50000000000000 : ℝ), (23558092662211/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2629142603/5000000000 : ℝ)|^5063 ≤ (1396112142823/3125000000000 : ℝ)^4039
        have hw : |(2629142603/5000000000 : ℝ)|=(2629142603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-54438249/400000000 : ℝ)|^5063 ≤ (4104113044109/50000000000000 : ℝ)^4039
        have hw : |(-54438249/400000000 : ℝ)|=(54438249/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5486204561/10000000000 : ℝ)|^5063 ≤ (23558092662211/50000000000000 : ℝ)^4039
        have hw : |(5486204561/10000000000 : ℝ)|=(5486204561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1680_s3_6 (p : ℝ) (hpa : (5055/1024 : ℝ) ≤ p) (hpb : p ≤ (5063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1314571321/2500000000 : ℝ)*x 0 + (5486204521/10000000000 : ℝ)*x 1 + (-1360956173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1314571321/2500000000 : ℝ)^5063 ≤ (44675589401057/100000000000000 : ℝ)^4039 := by
    have hnat : (1314571321 : ℕ)^5063*100000000000000^4039 ≤ 44675589401057^4039*2500000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314571321 2500000000 44675589401057 100000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5486204521/10000000000 : ℝ)^5063 ≤ (11779046223451/25000000000000 : ℝ)^4039 := by
    have hnat : (5486204521 : ℕ)^5063*25000000000000^4039 ≤ 11779046223451^4039*10000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5486204521 10000000000 11779046223451 25000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1360956173/10000000000 : ℝ)^5063 ≤ (4104112847541/50000000000000 : ℝ)^4039 := by
    have hnat : (1360956173 : ℕ)^5063*50000000000000^4039 ≤ 4104112847541^4039*10000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1360956173 10000000000 4104112847541 50000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5063/1024 : ℝ)) 5063 4039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1314571321/2500000000 : ℝ), (5486204521/10000000000 : ℝ), (-1360956173/10000000000 : ℝ)] ![(44675589401057/100000000000000 : ℝ), (11779046223451/25000000000000 : ℝ), (4104112847541/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1314571321/2500000000 : ℝ)|^5063 ≤ (44675589401057/100000000000000 : ℝ)^4039
        have hw : |(1314571321/2500000000 : ℝ)|=(1314571321/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5486204521/10000000000 : ℝ)|^5063 ≤ (11779046223451/25000000000000 : ℝ)^4039
        have hw : |(5486204521/10000000000 : ℝ)|=(5486204521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1360956173/10000000000 : ℝ)|^5063 ≤ (4104112847541/50000000000000 : ℝ)^4039
        have hw : |(-1360956173/10000000000 : ℝ)|=(1360956173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1680_s3_7 (p : ℝ) (hpa : (5055/1024 : ℝ) ≤ p) (hpb : p ≤ (5063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2072819259/5000000000 : ℝ)*x 0 + (4635916451/10000000000 : ℝ)*x 1 + (3693048063/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2072819259/5000000000 : ℝ)^5063 ≤ (1658097699519/5000000000000 : ℝ)^4039 := by
    have hnat : (2072819259 : ℕ)^5063*5000000000000^4039 ≤ 1658097699519^4039*5000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2072819259 5000000000 1658097699519 5000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4635916451/10000000000 : ℝ)^5063 ≤ (9537435236537/25000000000000 : ℝ)^4039 := by
    have hnat : (4635916451 : ℕ)^5063*25000000000000^4039 ≤ 9537435236537^4039*10000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4635916451 10000000000 9537435236537 25000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3693048063/10000000000 : ℝ)^5063 ≤ (1793019065513/6250000000000 : ℝ)^4039 := by
    have hnat : (3693048063 : ℕ)^5063*6250000000000^4039 ≤ 1793019065513^4039*10000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3693048063 10000000000 1793019065513 6250000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5063/1024 : ℝ)) 5063 4039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2072819259/5000000000 : ℝ), (4635916451/10000000000 : ℝ), (3693048063/10000000000 : ℝ)] ![(1658097699519/5000000000000 : ℝ), (9537435236537/25000000000000 : ℝ), (1793019065513/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2072819259/5000000000 : ℝ)|^5063 ≤ (1658097699519/5000000000000 : ℝ)^4039
        have hw : |(2072819259/5000000000 : ℝ)|=(2072819259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4635916451/10000000000 : ℝ)|^5063 ≤ (9537435236537/25000000000000 : ℝ)^4039
        have hw : |(4635916451/10000000000 : ℝ)|=(4635916451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3693048063/10000000000 : ℝ)|^5063 ≤ (1793019065513/6250000000000 : ℝ)^4039
        have hw : |(3693048063/10000000000 : ℝ)|=(3693048063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1680_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5055/1024 : ℝ) ≤ p) (hpb : p ≤ (5063/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (185082949/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8669/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4849/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (389/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8653/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8669/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4849/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8669/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4849/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8669/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4849/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8669/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4849/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8669/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4849/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8669/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4849/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4849/50000 : ℝ) ^ (5055/1024 : ℝ) ≤ (497396626223623/50000000000000000000 : ℝ) := by
    have hpowers : (4849/50000 : ℝ)^5055 ≤ (497396626223623/50000000000000000000 : ℝ)^1024 := by
      have hnat : (4849 : ℕ)^5055*50000000000000000000^1024 ≤ 497396626223623^1024*50000^5055 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4849 50000 497396626223623 50000000000000000000 5055 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4849/50000 : ℝ)) (X := (497396626223623/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5055 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8669/50000 : ℝ) ^ (5055/1024 : ℝ) ≤ (17510587633278521/100000000000000000000 : ℝ) := by
    have hpowers : (8669/50000 : ℝ)^5055 ≤ (17510587633278521/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8669 : ℕ)^5055*100000000000000000000^1024 ≤ 17510587633278521^1024*50000^5055 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8669 50000 17510587633278521 100000000000000000000 5055 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8669/50000 : ℝ)) (X := (17510587633278521/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5055 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000497396626223623/25000000000000000000 : ℝ) ≤ (1000004030307457/1000000000000000 : ℝ) ^ (5055/1024 : ℝ) := by
    have hpowers : (25000497396626223623/25000000000000000000 : ℝ)^1024 ≤ (1000004030307457/1000000000000000 : ℝ)^5055 := by
      have hnat : (25000497396626223623 : ℕ)^1024*1000000000000000^5055 ≤ 1000004030307457^5055*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000497396626223623 25000000000000000000 1000004030307457 1000000000000000 1024 5055 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000004030307457/1000000000000000 : ℝ)) (X := (25000497396626223623/25000000000000000000 : ℝ)) (by norm_num) 5055 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100018505380885725767/100000000000000000000 : ℝ) ≤ (5000187419505633/5000000000000000 : ℝ) ^ (5055/1024 : ℝ) := by
    have hpowers : (100018505380885725767/100000000000000000000 : ℝ)^1024 ≤ (5000187419505633/5000000000000000 : ℝ)^5055 := by
      have hnat : (100018505380885725767 : ℕ)^1024*5000000000000000^5055 ≤ 5000187419505633^5055*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100018505380885725767 100000000000000000000 5000187419505633 5000000000000000 1024 5055 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000187419505633/5000000000000000 : ℝ)) (X := (100018505380885725767/100000000000000000000 : ℝ)) (by norm_num) 5055 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50017510587633278521/50000000000000000000 : ℝ) ≤ (5000354687473981/5000000000000000 : ℝ) ^ (5055/1024 : ℝ) := by
    have hpowers : (50017510587633278521/50000000000000000000 : ℝ)^1024 ≤ (5000354687473981/5000000000000000 : ℝ)^5055 := by
      have hnat : (50017510587633278521 : ℕ)^1024*5000000000000000^5055 ≤ 5000354687473981^5055*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50017510587633278521 50000000000000000000 5000354687473981 5000000000000000 1024 5055 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000354687473981/5000000000000000 : ℝ)) (X := (50017510587633278521/50000000000000000000 : ℝ)) (by norm_num) 5055 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(497396626223623/50000000000000000000 : ℝ) ≤ ((4774613703528847449/4775000000000000000 : ℝ)+2*(41816992087/95500000000000 : ℝ)*(4849/50000 : ℝ))^(5055/1024 : ℝ) := by
    rw [show (4774613703528847449/4775000000000000000 : ℝ)+2*(41816992087/95500000000000 : ℝ)*(4849/50000 : ℝ)=(1000004030307457/1000000000000000 : ℝ) by norm_num, show 1+2*(497396626223623/50000000000000000000 : ℝ)=(25000497396626223623/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17510587633278521/100000000000000000000 : ℝ)+(497396626223623/50000000000000000000 : ℝ) ≤ ((4774613703528847449/4775000000000000000 : ℝ)+(41816992087/95500000000000 : ℝ)*((8669/50000 : ℝ)+(4849/50000 : ℝ)))^(5055/1024 : ℝ) := by
    rw [show (4774613703528847449/4775000000000000000 : ℝ)+(41816992087/95500000000000 : ℝ)*((8669/50000 : ℝ)+(4849/50000 : ℝ))=(5000187419505633/5000000000000000 : ℝ) by norm_num, show 1+(17510587633278521/100000000000000000000 : ℝ)+(497396626223623/50000000000000000000 : ℝ)=(100018505380885725767/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17510587633278521/100000000000000000000 : ℝ) ≤ ((4774613703528847449/4775000000000000000 : ℝ)+2*(41816992087/95500000000000 : ℝ)*(8669/50000 : ℝ))^(5055/1024 : ℝ) := by
    rw [show (4774613703528847449/4775000000000000000 : ℝ)+2*(41816992087/95500000000000 : ℝ)*(8669/50000 : ℝ)=(5000354687473981/5000000000000000 : ℝ) by norm_num, show 1+2*(17510587633278521/100000000000000000000 : ℝ)=(50017510587633278521/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4774613703528847449/4775000000000000000 : ℝ)*(X 1 0+X 2 0)+(41816992087/95500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5055/1024 : ℝ)) (lo := (4849/50000 : ℝ)) (hi := (8669/50000 : ℝ)) (c := (4774613703528847449/4775000000000000000 : ℝ)) (alpha := (41816992087/95500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4774613703528847449/4775000000000000000 : ℝ)*(X 0 1+X 2 1)+(41816992087/95500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5055/1024 : ℝ)) (lo := (4849/50000 : ℝ)) (hi := (8669/50000 : ℝ)) (c := (4774613703528847449/4775000000000000000 : ℝ)) (alpha := (41816992087/95500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4774613703528847449/4775000000000000000 : ℝ)*(X 0 2+X 1 2)+(41816992087/95500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5055/1024 : ℝ)) (lo := (4849/50000 : ℝ)) (hi := (8669/50000 : ℝ)) (c := (4774613703528847449/4775000000000000000 : ℝ)) (alpha := (41816992087/95500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1528310887/10000000000 : ℝ)*X 0 0+(5490111121/10000000000 : ℝ)*X 0 1+(513335941/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1680_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070709071/2000000000 : ℝ)*X 1 0+(-1713801533/10000000000 : ℝ)*X 1 1+(5133359221/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1680_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353545369/10000000000 : ℝ)*X 2 0+(2566679613/5000000000 : ℝ)*X 2 1+(-1713801507/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1680_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1036295847/2500000000 : ℝ)*X 0 0+(1841246667/5000000000 : ℝ)*X 0 1+(464631577/1000000000 : ℝ)*X 0 2+(1036295847/2500000000 : ℝ)*X 1 0+(1841246667/5000000000 : ℝ)*X 1 1+(464631577/1000000000 : ℝ)*X 1 2+(1036295847/2500000000 : ℝ)*X 2 0+(1841246667/5000000000 : ℝ)*X 2 1+(464631577/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1680_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-382119829/2500000000 : ℝ)*X 0 0+(1027441681/2000000000 : ℝ)*X 0 1+(548620463/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1680_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2629142603/5000000000 : ℝ)*X 1 0+(-54438249/400000000 : ℝ)*X 1 1+(5486204561/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1680_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1314571321/2500000000 : ℝ)*X 2 0+(5486204521/10000000000 : ℝ)*X 2 1+(-1360956173/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1680_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2072819259/5000000000 : ℝ)*X 0 0+(4635916451/10000000000 : ℝ)*X 0 1+(3693048063/10000000000 : ℝ)*X 0 2+(2072819259/5000000000 : ℝ)*X 1 0+(4635916451/10000000000 : ℝ)*X 1 1+(3693048063/10000000000 : ℝ)*X 1 2+(2072819259/5000000000 : ℝ)*X 2 0+(4635916451/10000000000 : ℝ)*X 2 1+(3693048063/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1680_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (246387750861745269370384107/59687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (162172821/25000000000000 : ℝ)*(base19) + (125511281/20000000000000 : ℝ)*(base23) + (15238963/100000000000000 : ℝ)*(lower2) + (4849909/5000000000000 : ℝ)*(upper3) + (1444897/1562500000000 : ℝ)*(upper5) + (480077406655973/25000000000000 : ℝ)*(major0) + (480077406655973/25000000000000 : ℝ)*(major1) + (480077406655973/25000000000000 : ℝ)*(major2) + (280307442033163/10000000000000 : ℝ)*(sp0) + (2803078468271059/100000000000000 : ℝ)*(sp1) + (1401539244702969/50000000000000 : ℝ)*(sp2) + (518768842656493/50000000000000 : ℝ)*(sp3) + (4696630713/100000000000000 : ℝ)*(sp4) + (1156686853/50000000000000 : ℝ)*(sp7) + (1037539998686693/100000000000000 : ℝ)*(f.failure) + (2803079116962343/100000000000000 : ℝ)*(f.sum) + (4453108744077/2387500000000000000000000000 : ℝ)*base65 + (299329248677337877/119375000000000000000000000000000 : ℝ)*base67 + (679719182781712877/119375000000000000000000000000000 : ℝ)*base69 + (508690019467337877/119375000000000000000000000000000 : ℝ)*base71 + (11047599066279/4775000000000000000000000000 : ℝ)*base73 + (34718682869837877/119375000000000000000000000000000 : ℝ)*base75 + (251959735837962877/119375000000000000000000000000000 : ℝ)*base77 + (213894472012962877/119375000000000000000000000000000 : ℝ)*base79 + (909607794519/298437500000000000000000000 : ℝ)*base81 + (67497657/10000000000000000000000 : ℝ)*base89 + (67497657/10000000000000000000000 : ℝ)*base91 + (67497657/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (864142102774326903804851643/238750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (124449833/25000000000000 : ℝ)*(base19) + (294801313/50000000000000 : ℝ)*(base23) + (71623991/50000000000000 : ℝ)*(lower1) + (61677483/100000000000000 : ℝ)*(upper3) + (11141051/50000000000000 : ℝ)*(lower4) + (95837881/100000000000000 : ℝ)*(upper5) + (1962974352985169/100000000000000 : ℝ)*(major0) + (1962974352985169/100000000000000 : ℝ)*(major1) + (1962974352985169/100000000000000 : ℝ)*(major2) + (15288289/4000000000000 : ℝ)*(sp2) + (1432678454067901/50000000000000 : ℝ)*(sp4) + (286535641033647/10000000000000 : ℝ)*(sp5) + (57307118726519/2000000000000 : ℝ)*(sp6) + (1060591677186411/100000000000000 : ℝ)*(sp7) + (1060591677186411/100000000000000 : ℝ)*(f.failure) + (1432678454067901/50000000000000 : ℝ)*(f.sum) + (16489501792447/4775000000000000000000000000 : ℝ)*base66 + (1736060407106866119/477500000000000000000000000000000 : ℝ)*base68 + (3377453278511866119/477500000000000000000000000000000 : ℝ)*base70 + (253746913299366119/477500000000000000000000000000000 : ℝ)*base72 + (6157632167411/2387500000000000000000000000 : ℝ)*base74 + (40458898264286866119/477500000000000000000000000000000 : ℝ)*base76 + (879767414313133881/477500000000000000000000000000000 : ℝ)*base77 + (746265367668133881/477500000000000000000000000000000 : ℝ)*base79 + (32130087773003/4775000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (70606039/10000000000000000000000 : ℝ)*base89 + (70606039/10000000000000000000000 : ℝ)*base91 + (70606039/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1680_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5055/1024 : ℝ) ≤ p) (hpb : p ≤ (5063/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (185082949/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8669/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4849/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (389/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8653/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1680_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1680_s4_0 (p : ℝ) (hpa : (5055/1024 : ℝ) ≤ p) (hpb : p ≤ (5063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-764166389/5000000000 : ℝ)*x 0 + (137250723/250000000 : ℝ)*x 1 + (2566713461/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (764166389/5000000000 : ℝ)^5063 ≤ (2373199545357/25000000000000 : ℝ)^4039 := by
    have hnat : (764166389 : ℕ)^5063*25000000000000^4039 ≤ 2373199545357^4039*5000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      764166389 5000000000 2373199545357 25000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (137250723/250000000 : ℝ)^5063 ≤ (47157359908473/100000000000000 : ℝ)^4039 := by
    have hnat : (137250723 : ℕ)^5063*100000000000000^4039 ≤ 47157359908473^4039*250000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137250723 250000000 47157359908473 100000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2566713461/5000000000 : ℝ)^5063 ≤ (10837460474319/25000000000000 : ℝ)^4039 := by
    have hnat : (2566713461 : ℕ)^5063*25000000000000^4039 ≤ 10837460474319^4039*5000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2566713461 5000000000 10837460474319 25000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5063/1024 : ℝ)) 5063 4039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-764166389/5000000000 : ℝ), (137250723/250000000 : ℝ), (2566713461/5000000000 : ℝ)] ![(2373199545357/25000000000000 : ℝ), (47157359908473/100000000000000 : ℝ), (10837460474319/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-764166389/5000000000 : ℝ)|^5063 ≤ (2373199545357/25000000000000 : ℝ)^4039
        have hw : |(-764166389/5000000000 : ℝ)|=(764166389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(137250723/250000000 : ℝ)|^5063 ≤ (47157359908473/100000000000000 : ℝ)^4039
        have hw : |(137250723/250000000 : ℝ)|=(137250723/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2566713461/5000000000 : ℝ)|^5063 ≤ (10837460474319/25000000000000 : ℝ)^4039
        have hw : |(2566713461/5000000000 : ℝ)|=(2566713461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1680_s4_1 (p : ℝ) (hpa : (5055/1024 : ℝ) ≤ p) (hpb : p ≤ (5063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676761323/5000000000 : ℝ)*x 0 + (-1713742853/10000000000 : ℝ)*x 1 + (2566713303/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676761323/5000000000 : ℝ)^5063 ≤ (11423052612669/25000000000000 : ℝ)^4039 := by
    have hnat : (2676761323 : ℕ)^5063*25000000000000^4039 ≤ 11423052612669^4039*5000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676761323 5000000000 11423052612669 25000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1713742853/10000000000 : ℝ)^5063 ≤ (438318039567/4000000000000 : ℝ)^4039 := by
    have hnat : (1713742853 : ℕ)^5063*4000000000000^4039 ≤ 438318039567^4039*10000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1713742853 10000000000 438318039567 4000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2566713303/5000000000 : ℝ)^5063 ≤ (10837459638059/25000000000000 : ℝ)^4039 := by
    have hnat : (2566713303 : ℕ)^5063*25000000000000^4039 ≤ 10837459638059^4039*5000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2566713303 5000000000 10837459638059 25000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5063/1024 : ℝ)) 5063 4039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676761323/5000000000 : ℝ), (-1713742853/10000000000 : ℝ), (2566713303/5000000000 : ℝ)] ![(11423052612669/25000000000000 : ℝ), (438318039567/4000000000000 : ℝ), (10837459638059/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676761323/5000000000 : ℝ)|^5063 ≤ (11423052612669/25000000000000 : ℝ)^4039
        have hw : |(2676761323/5000000000 : ℝ)|=(2676761323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1713742853/10000000000 : ℝ)|^5063 ≤ (438318039567/4000000000000 : ℝ)^4039
        have hw : |(-1713742853/10000000000 : ℝ)|=(1713742853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2566713303/5000000000 : ℝ)|^5063 ≤ (10837459638059/25000000000000 : ℝ)^4039
        have hw : |(2566713303/5000000000 : ℝ)|=(2566713303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1680_s4_2 (p : ℝ) (hpa : (5055/1024 : ℝ) ≤ p) (hpb : p ≤ (5063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676761409/5000000000 : ℝ)*x 0 + (5133426407/10000000000 : ℝ)*x 1 + (-342748577/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676761409/5000000000 : ℝ)^5063 ≤ (11423053072719/25000000000000 : ℝ)^4039 := by
    have hnat : (2676761409 : ℕ)^5063*25000000000000^4039 ≤ 11423053072719^4039*5000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676761409 5000000000 11423053072719 25000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5133426407/10000000000 : ℝ)^5063 ≤ (10837459111427/25000000000000 : ℝ)^4039 := by
    have hnat : (5133426407 : ℕ)^5063*25000000000000^4039 ≤ 10837459111427^4039*10000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5133426407 10000000000 10837459111427 25000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (342748577/2000000000 : ℝ)^5063 ≤ (10957951245663/100000000000000 : ℝ)^4039 := by
    have hnat : (342748577 : ℕ)^5063*100000000000000^4039 ≤ 10957951245663^4039*2000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      342748577 2000000000 10957951245663 100000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5063/1024 : ℝ)) 5063 4039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676761409/5000000000 : ℝ), (5133426407/10000000000 : ℝ), (-342748577/2000000000 : ℝ)] ![(11423053072719/25000000000000 : ℝ), (10837459111427/25000000000000 : ℝ), (10957951245663/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676761409/5000000000 : ℝ)|^5063 ≤ (11423053072719/25000000000000 : ℝ)^4039
        have hw : |(2676761409/5000000000 : ℝ)|=(2676761409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5133426407/10000000000 : ℝ)|^5063 ≤ (10837459111427/25000000000000 : ℝ)^4039
        have hw : |(5133426407/10000000000 : ℝ)|=(5133426407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-342748577/2000000000 : ℝ)|^5063 ≤ (10957951245663/100000000000000 : ℝ)^4039
        have hw : |(-342748577/2000000000 : ℝ)|=(342748577/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1680_s4_3 (p : ℝ) (hpa : (5055/1024 : ℝ) ≤ p) (hpb : p ≤ (5063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (16192181/39062500 : ℝ)*x 0 + (57542089/156250000 : ℝ)*x 1 + (4646112353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16192181/39062500 : ℝ)^5063 ≤ (33157540225553/100000000000000 : ℝ)^4039 := by
    have hnat : (16192181 : ℕ)^5063*100000000000000^4039 ≤ 33157540225553^4039*39062500^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16192181 39062500 33157540225553 100000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (57542089/156250000 : ℝ)^5063 ≤ (7146878435763/25000000000000 : ℝ)^4039 := by
    have hnat : (57542089 : ℕ)^5063*25000000000000^4039 ≤ 7146878435763^4039*156250000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      57542089 156250000 7146878435763 25000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4646112353/10000000000 : ℝ)^5063 ≤ (4781868253419/12500000000000 : ℝ)^4039 := by
    have hnat : (4646112353 : ℕ)^5063*12500000000000^4039 ≤ 4781868253419^4039*10000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4646112353 10000000000 4781868253419 12500000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5063/1024 : ℝ)) 5063 4039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(16192181/39062500 : ℝ), (57542089/156250000 : ℝ), (4646112353/10000000000 : ℝ)] ![(33157540225553/100000000000000 : ℝ), (7146878435763/25000000000000 : ℝ), (4781868253419/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(16192181/39062500 : ℝ)|^5063 ≤ (33157540225553/100000000000000 : ℝ)^4039
        have hw : |(16192181/39062500 : ℝ)|=(16192181/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(57542089/156250000 : ℝ)|^5063 ≤ (7146878435763/25000000000000 : ℝ)^4039
        have hw : |(57542089/156250000 : ℝ)|=(57542089/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4646112353/10000000000 : ℝ)|^5063 ≤ (4781868253419/12500000000000 : ℝ)^4039
        have hw : |(4646112353/10000000000 : ℝ)|=(4646112353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1680_s4_4 (p : ℝ) (hpa : (5055/1024 : ℝ) ≤ p) (hpb : p ≤ (5063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-47765661/312500000 : ℝ)*x 0 + (5137272583/10000000000 : ℝ)*x 1 + (137153143/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (47765661/312500000 : ℝ)^5063 ≤ (949410914761/10000000000000 : ℝ)^4039 := by
    have hnat : (47765661 : ℕ)^5063*10000000000000^4039 ≤ 949410914761^4039*312500000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47765661 312500000 949410914761 10000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5137272583/10000000000 : ℝ)^5063 ≤ (10847638568087/25000000000000 : ℝ)^4039 := by
    have hnat : (5137272583 : ℕ)^5063*25000000000000^4039 ≤ 10847638568087^4039*10000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5137272583 10000000000 10847638568087 25000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (137153143/250000000 : ℝ)^5063 ≤ (736177133861/1562500000000 : ℝ)^4039 := by
    have hnat : (137153143 : ℕ)^5063*1562500000000^4039 ≤ 736177133861^4039*250000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137153143 250000000 736177133861 1562500000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5063/1024 : ℝ)) 5063 4039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-47765661/312500000 : ℝ), (5137272583/10000000000 : ℝ), (137153143/250000000 : ℝ)] ![(949410914761/10000000000000 : ℝ), (10847638568087/25000000000000 : ℝ), (736177133861/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-47765661/312500000 : ℝ)|^5063 ≤ (949410914761/10000000000000 : ℝ)^4039
        have hw : |(-47765661/312500000 : ℝ)|=(47765661/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5137272583/10000000000 : ℝ)|^5063 ≤ (10847638568087/25000000000000 : ℝ)^4039
        have hw : |(5137272583/10000000000 : ℝ)|=(5137272583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(137153143/250000000 : ℝ)|^5063 ≤ (736177133861/1562500000000 : ℝ)^4039
        have hw : |(137153143/250000000 : ℝ)|=(137153143/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1680_s4_5 (p : ℝ) (hpa : (5055/1024 : ℝ) ≤ p) (hpb : p ≤ (5063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5258302429/10000000000 : ℝ)*x 0 + (-340260843/2500000000 : ℝ)*x 1 + (5486126321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5258302429/10000000000 : ℝ)^5063 ≤ (11168942999961/25000000000000 : ℝ)^4039 := by
    have hnat : (5258302429 : ℕ)^5063*25000000000000^4039 ≤ 11168942999961^4039*10000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258302429 10000000000 11168942999961 25000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (340260843/2500000000 : ℝ)^5063 ≤ (2052221237833/25000000000000 : ℝ)^4039 := by
    have hnat : (340260843 : ℕ)^5063*25000000000000^4039 ≤ 2052221237833^4039*2500000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340260843 2500000000 2052221237833 25000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5486126321/10000000000 : ℝ)^5063 ≤ (11778835759279/25000000000000 : ℝ)^4039 := by
    have hnat : (5486126321 : ℕ)^5063*25000000000000^4039 ≤ 11778835759279^4039*10000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5486126321 10000000000 11778835759279 25000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5063/1024 : ℝ)) 5063 4039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5258302429/10000000000 : ℝ), (-340260843/2500000000 : ℝ), (5486126321/10000000000 : ℝ)] ![(11168942999961/25000000000000 : ℝ), (2052221237833/25000000000000 : ℝ), (11778835759279/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5258302429/10000000000 : ℝ)|^5063 ≤ (11168942999961/25000000000000 : ℝ)^4039
        have hw : |(5258302429/10000000000 : ℝ)|=(5258302429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-340260843/2500000000 : ℝ)|^5063 ≤ (2052221237833/25000000000000 : ℝ)^4039
        have hw : |(-340260843/2500000000 : ℝ)|=(340260843/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5486126321/10000000000 : ℝ)|^5063 ≤ (11778835759279/25000000000000 : ℝ)^4039
        have hw : |(5486126321/10000000000 : ℝ)|=(5486126321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1680_s4_6 (p : ℝ) (hpa : (5055/1024 : ℝ) ≤ p) (hpb : p ≤ (5063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5258302647/10000000000 : ℝ)*x 0 + (2743062817/5000000000 : ℝ)*x 1 + (-1361044043/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5258302647/10000000000 : ℝ)^5063 ≤ (44675774321603/100000000000000 : ℝ)^4039 := by
    have hnat : (5258302647 : ℕ)^5063*100000000000000^4039 ≤ 44675774321603^4039*10000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258302647 10000000000 44675774321603 100000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2743062817/5000000000 : ℝ)^5063 ≤ (47115335641279/100000000000000 : ℝ)^4039 := by
    have hnat : (2743062817 : ℕ)^5063*100000000000000^4039 ≤ 47115335641279^4039*5000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2743062817 5000000000 47115335641279 100000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1361044043/10000000000 : ℝ)^5063 ≤ (4104445012189/50000000000000 : ℝ)^4039 := by
    have hnat : (1361044043 : ℕ)^5063*50000000000000^4039 ≤ 4104445012189^4039*10000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1361044043 10000000000 4104445012189 50000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5063/1024 : ℝ)) 5063 4039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5258302647/10000000000 : ℝ), (2743062817/5000000000 : ℝ), (-1361044043/10000000000 : ℝ)] ![(44675774321603/100000000000000 : ℝ), (47115335641279/100000000000000 : ℝ), (4104445012189/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5258302647/10000000000 : ℝ)|^5063 ≤ (44675774321603/100000000000000 : ℝ)^4039
        have hw : |(5258302647/10000000000 : ℝ)|=(5258302647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2743062817/5000000000 : ℝ)|^5063 ≤ (47115335641279/100000000000000 : ℝ)^4039
        have hw : |(2743062817/5000000000 : ℝ)|=(2743062817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1361044043/10000000000 : ℝ)|^5063 ≤ (4104445012189/50000000000000 : ℝ)^4039
        have hw : |(-1361044043/10000000000 : ℝ)|=(1361044043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1680_s4_7 (p : ℝ) (hpa : (5055/1024 : ℝ) ≤ p) (hpb : p ≤ (5063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4145652639/10000000000 : ℝ)*x 0 + (2317860937/5000000000 : ℝ)*x 1 + (1846619821/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4145652639/10000000000 : ℝ)^5063 ≤ (129539435881/390625000000 : ℝ)^4039 := by
    have hnat : (4145652639 : ℕ)^5063*390625000000^4039 ≤ 129539435881^4039*10000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4145652639 10000000000 129539435881 390625000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2317860937/5000000000 : ℝ)^5063 ≤ (298029170303/781250000000 : ℝ)^4039 := by
    have hnat : (2317860937 : ℕ)^5063*781250000000^4039 ≤ 298029170303^4039*5000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2317860937 5000000000 298029170303 781250000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1846619821/5000000000 : ℝ)^5063 ≤ (14345085294527/50000000000000 : ℝ)^4039 := by
    have hnat : (1846619821 : ℕ)^5063*50000000000000^4039 ≤ 14345085294527^4039*5000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1846619821 5000000000 14345085294527 50000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5063/1024 : ℝ)) 5063 4039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4145652639/10000000000 : ℝ), (2317860937/5000000000 : ℝ), (1846619821/5000000000 : ℝ)] ![(129539435881/390625000000 : ℝ), (298029170303/781250000000 : ℝ), (14345085294527/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4145652639/10000000000 : ℝ)|^5063 ≤ (129539435881/390625000000 : ℝ)^4039
        have hw : |(4145652639/10000000000 : ℝ)|=(4145652639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2317860937/5000000000 : ℝ)|^5063 ≤ (298029170303/781250000000 : ℝ)^4039
        have hw : |(2317860937/5000000000 : ℝ)|=(2317860937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1846619821/5000000000 : ℝ)|^5063 ≤ (14345085294527/50000000000000 : ℝ)^4039
        have hw : |(1846619821/5000000000 : ℝ)|=(1846619821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1680_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5055/1024 : ℝ) ≤ p) (hpb : p ≤ (5063/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (185082949/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8653/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (389/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (4863/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3461/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8653/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (389/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8653/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (389/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8653/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (389/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8653/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (389/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8653/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (389/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8653/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (389/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (389/4000 : ℝ) ^ (5055/1024 : ℝ) ≤ (25213512240911/2500000000000000000 : ℝ) := by
    have hpowers : (389/4000 : ℝ)^5055 ≤ (25213512240911/2500000000000000000 : ℝ)^1024 := by
      have hnat : (389 : ℕ)^5055*2500000000000000000^1024 ≤ 25213512240911^1024*4000^5055 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        389 4000 25213512240911 2500000000000000000 5055 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (389/4000 : ℝ)) (X := (25213512240911/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 5055 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8653/50000 : ℝ) ^ (5055/1024 : ℝ) ≤ (17351624940123319/100000000000000000000 : ℝ) := by
    have hpowers : (8653/50000 : ℝ)^5055 ≤ (17351624940123319/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8653 : ℕ)^5055*100000000000000000000^1024 ≤ 17351624940123319^1024*50000^5055 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8653 50000 17351624940123319 100000000000000000000 5055 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8653/50000 : ℝ)) (X := (17351624940123319/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5055 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1250025213512240911/1250000000000000000 : ℝ) ≤ (2000008172005189/2000000000000000 : ℝ) ^ (5055/1024 : ℝ) := by
    have hpowers : (1250025213512240911/1250000000000000000 : ℝ)^1024 ≤ (2000008172005189/2000000000000000 : ℝ)^5055 := by
      have hnat : (1250025213512240911 : ℕ)^1024*2000000000000000^5055 ≤ 2000008172005189^5055*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250025213512240911 1250000000000000000 2000008172005189 2000000000000000 1024 5055 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000008172005189/2000000000000000 : ℝ)) (X := (1250025213512240911/1250000000000000000 : ℝ)) (by norm_num) 5055 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100018360165429759759/100000000000000000000 : ℝ) ≤ (5000185948894621/5000000000000000 : ℝ) ^ (5055/1024 : ℝ) := by
    have hpowers : (100018360165429759759/100000000000000000000 : ℝ)^1024 ≤ (5000185948894621/5000000000000000 : ℝ)^5055 := by
      have hnat : (100018360165429759759 : ℕ)^1024*5000000000000000^5055 ≤ 5000185948894621^5055*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100018360165429759759 100000000000000000000 5000185948894621 5000000000000000 1024 5055 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000185948894621/5000000000000000 : ℝ)) (X := (100018360165429759759/100000000000000000000 : ℝ)) (by norm_num) 5055 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50017351624940123319/50000000000000000000 : ℝ) ≤ (10000702935552539/10000000000000000 : ℝ) ^ (5055/1024 : ℝ) := by
    have hpowers : (50017351624940123319/50000000000000000000 : ℝ)^1024 ≤ (10000702935552539/10000000000000000 : ℝ)^5055 := by
      have hnat : (50017351624940123319 : ℕ)^1024*10000000000000000^5055 ≤ 10000702935552539^5055*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50017351624940123319 50000000000000000000 10000702935552539 10000000000000000 1024 5055 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000702935552539/10000000000000000 : ℝ)) (X := (50017351624940123319/50000000000000000000 : ℝ)) (by norm_num) 5055 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(25213512240911/2500000000000000000 : ℝ) ≤ ((5053591405024037493/5054000000000000000 : ℝ)+2*(110345921099/252700000000000 : ℝ)*(389/4000 : ℝ))^(5055/1024 : ℝ) := by
    rw [show (5053591405024037493/5054000000000000000 : ℝ)+2*(110345921099/252700000000000 : ℝ)*(389/4000 : ℝ)=(2000008172005189/2000000000000000 : ℝ) by norm_num, show 1+2*(25213512240911/2500000000000000000 : ℝ)=(1250025213512240911/1250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17351624940123319/100000000000000000000 : ℝ)+(25213512240911/2500000000000000000 : ℝ) ≤ ((5053591405024037493/5054000000000000000 : ℝ)+(110345921099/252700000000000 : ℝ)*((8653/50000 : ℝ)+(389/4000 : ℝ)))^(5055/1024 : ℝ) := by
    rw [show (5053591405024037493/5054000000000000000 : ℝ)+(110345921099/252700000000000 : ℝ)*((8653/50000 : ℝ)+(389/4000 : ℝ))=(5000185948894621/5000000000000000 : ℝ) by norm_num, show 1+(17351624940123319/100000000000000000000 : ℝ)+(25213512240911/2500000000000000000 : ℝ)=(100018360165429759759/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17351624940123319/100000000000000000000 : ℝ) ≤ ((5053591405024037493/5054000000000000000 : ℝ)+2*(110345921099/252700000000000 : ℝ)*(8653/50000 : ℝ))^(5055/1024 : ℝ) := by
    rw [show (5053591405024037493/5054000000000000000 : ℝ)+2*(110345921099/252700000000000 : ℝ)*(8653/50000 : ℝ)=(10000702935552539/10000000000000000 : ℝ) by norm_num, show 1+2*(17351624940123319/100000000000000000000 : ℝ)=(50017351624940123319/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5053591405024037493/5054000000000000000 : ℝ)*(X 1 0+X 2 0)+(110345921099/252700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5055/1024 : ℝ)) (lo := (389/4000 : ℝ)) (hi := (8653/50000 : ℝ)) (c := (5053591405024037493/5054000000000000000 : ℝ)) (alpha := (110345921099/252700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5053591405024037493/5054000000000000000 : ℝ)*(X 0 1+X 2 1)+(110345921099/252700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5055/1024 : ℝ)) (lo := (389/4000 : ℝ)) (hi := (8653/50000 : ℝ)) (c := (5053591405024037493/5054000000000000000 : ℝ)) (alpha := (110345921099/252700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5053591405024037493/5054000000000000000 : ℝ)*(X 0 2+X 1 2)+(110345921099/252700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5055/1024 : ℝ)) (lo := (389/4000 : ℝ)) (hi := (8653/50000 : ℝ)) (c := (5053591405024037493/5054000000000000000 : ℝ)) (alpha := (110345921099/252700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-764166389/5000000000 : ℝ)*X 0 0+(137250723/250000000 : ℝ)*X 0 1+(2566713461/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1680_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676761323/5000000000 : ℝ)*X 1 0+(-1713742853/10000000000 : ℝ)*X 1 1+(2566713303/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1680_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676761409/5000000000 : ℝ)*X 2 0+(5133426407/10000000000 : ℝ)*X 2 1+(-342748577/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1680_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((16192181/39062500 : ℝ)*X 0 0+(57542089/156250000 : ℝ)*X 0 1+(4646112353/10000000000 : ℝ)*X 0 2+(16192181/39062500 : ℝ)*X 1 0+(57542089/156250000 : ℝ)*X 1 1+(4646112353/10000000000 : ℝ)*X 1 2+(16192181/39062500 : ℝ)*X 2 0+(57542089/156250000 : ℝ)*X 2 1+(4646112353/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1680_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-47765661/312500000 : ℝ)*X 0 0+(5137272583/10000000000 : ℝ)*X 0 1+(137153143/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1680_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5258302429/10000000000 : ℝ)*X 1 0+(-340260843/2500000000 : ℝ)*X 1 1+(5486126321/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1680_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5258302647/10000000000 : ℝ)*X 2 0+(2743062817/5000000000 : ℝ)*X 2 1+(-1361044043/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1680_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4145652639/10000000000 : ℝ)*X 0 0+(2317860937/5000000000 : ℝ)*X 0 1+(1846619821/5000000000 : ℝ)*X 0 2+(4145652639/10000000000 : ℝ)*X 1 0+(2317860937/5000000000 : ℝ)*X 1 1+(1846619821/5000000000 : ℝ)*X 1 2+(4145652639/10000000000 : ℝ)*X 2 0+(2317860937/5000000000 : ℝ)*X 2 1+(1846619821/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1680_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (30810975892390500764634651/3325000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1450276921/100000000000000 : ℝ)*(base19) + (685914547/50000000000000 : ℝ)*(base23) + (18046119/20000000000000 : ℝ)*(lower2) + (67472681/25000000000000 : ℝ)*(upper3) + (69871253/50000000000000 : ℝ)*(upper5) + (480280926731363/25000000000000 : ℝ)*(major0) + (480280926731363/25000000000000 : ℝ)*(major1) + (480280926731363/25000000000000 : ℝ)*(major2) + (56085148273259/2000000000000 : ℝ)*(sp0) + (560853161962843/20000000000000 : ℝ)*(sp1) + (2804265888262041/100000000000000 : ℝ)*(sp2) + (1037974479723941/100000000000000 : ℝ)*(sp3) + (1969285637/20000000000000 : ℝ)*(sp4) + (83830529/1562500000000 : ℝ)*(sp7) + (1037979844877797/100000000000000 : ℝ)*(f.failure) + (10954168984731/390625000000 : ℝ)*(f.sum) + (152002916251/83125000000000000000000000 : ℝ)*base66 + (79630918032762261/6650000000000000000000000000000 : ℝ)*base67 + (51103263314262261/6650000000000000000000000000000 : ℝ)*base69 + (4984580818012261/6650000000000000000000000000000 : ℝ)*base71 + (2502309044567/665000000000000000000000000 : ℝ)*base73 + (30005166150762261/6650000000000000000000000000000 : ℝ)*base75 + (32904348808812261/6650000000000000000000000000000 : ℝ)*base77 + (88318139999962261/6650000000000000000000000000000 : ℝ)*base79 + (263583221873/166250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (13383353/10000000000000000000000 : ℝ)*base89 + (13383353/10000000000000000000000 : ℝ)*base91 + (13383353/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (22275805857171523088319/1805000000000000000000000000 : ℝ) := by norm_num
    linear_combination (309892723/20000000000000 : ℝ)*(base19) + (418224813/25000000000000 : ℝ)*(base23) + (437664679/100000000000000 : ℝ)*(lower1) + (277817761/100000000000000 : ℝ)*(upper3) + (1783489/4000000000000 : ℝ)*(lower4) + (133657837/50000000000000 : ℝ)*(upper5) + (1963773069840379/100000000000000 : ℝ)*(major0) + (1963773069840379/100000000000000 : ℝ)*(major1) + (1963773069840379/100000000000000 : ℝ)*(major2) + (110720153/2500000000000 : ℝ)*(sp1) + (179157656610921/6250000000000 : ℝ)*(sp4) + (2866516527505001/100000000000000 : ℝ)*(sp5) + (716630208218871/25000000000000 : ℝ)*(sp6) + (530511611266897/50000000000000 : ℝ)*(sp7) + (530511611266897/50000000000000 : ℝ)*(f.failure) + (179157656610921/6250000000000 : ℝ)*(f.sum) + (2001435942167/1805000000000000000000000000 : ℝ)*base66 + (324498351383692879/72200000000000000000000000000000 : ℝ)*base68 + (218510727963507121/72200000000000000000000000000000 : ℝ)*base69 + (45181840949892879/72200000000000000000000000000000 : ℝ)*base72 + (259899254817/1805000000000000000000000000 : ℝ)*base74 + (364856509227307121/72200000000000000000000000000000 : ℝ)*base75 + (182886388317692879/72200000000000000000000000000000 : ℝ)*base78 + (233196558566707121/72200000000000000000000000000000 : ℝ)*base79 + (10828082695023/1805000000000000000000000000 : ℝ)*base81 + (27160747/5000000000000000000000 : ℝ)*base90 + (27160747/5000000000000000000000 : ℝ)*base92 + (27160747/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1680_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5055/1024 : ℝ) ≤ p) (hpb : p ≤ (5063/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (185082949/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8653/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (389/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4863/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3461/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1680_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1680_box_0 (p : ℝ) (hpa : (5055/1024 : ℝ) ≤ p) (hpb : p ≤ (5063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1184521477/10000000000 : ℝ)*x 0 + (543368883/1000000000 : ℝ)*x 1 + (2716842923/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1184521477/10000000000 : ℝ)^5063 ≤ (1379399410093/20000000000000 : ℝ)^4039 := by
    have hnat : (1184521477 : ℕ)^5063*20000000000000^4039 ≤ 1379399410093^4039*10000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1184521477 10000000000 1379399410093 20000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (543368883/1000000000 : ℝ)^5063 ≤ (46551517492733/100000000000000 : ℝ)^4039 := by
    have hnat : (543368883 : ℕ)^5063*100000000000000^4039 ≤ 46551517492733^4039*1000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543368883 1000000000 46551517492733 100000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2716842923/5000000000 : ℝ)^5063 ≤ (5818935680859/12500000000000 : ℝ)^4039 := by
    have hnat : (2716842923 : ℕ)^5063*12500000000000^4039 ≤ 5818935680859^4039*5000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716842923 5000000000 5818935680859 12500000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5063/1024 : ℝ)) 5063 4039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1184521477/10000000000 : ℝ), (543368883/1000000000 : ℝ), (2716842923/5000000000 : ℝ)] ![(1379399410093/20000000000000 : ℝ), (46551517492733/100000000000000 : ℝ), (5818935680859/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1184521477/10000000000 : ℝ)|^5063 ≤ (1379399410093/20000000000000 : ℝ)^4039
        have hw : |(-1184521477/10000000000 : ℝ)|=(1184521477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(543368883/1000000000 : ℝ)|^5063 ≤ (46551517492733/100000000000000 : ℝ)^4039
        have hw : |(543368883/1000000000 : ℝ)|=(543368883/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2716842923/5000000000 : ℝ)|^5063 ≤ (5818935680859/12500000000000 : ℝ)^4039
        have hw : |(2716842923/5000000000 : ℝ)|=(2716842923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1680_box_1 (p : ℝ) (hpa : (5055/1024 : ℝ) ≤ p) (hpb : p ≤ (5063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (522608567/1000000000 : ℝ)*x 0 + (-184960713/1250000000 : ℝ)*x 1 + (27168437/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (522608567/1000000000 : ℝ)^5063 ≤ (5541615217757/12500000000000 : ℝ)^4039 := by
    have hnat : (522608567 : ℕ)^5063*12500000000000^4039 ≤ 5541615217757^4039*1000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522608567 1000000000 5541615217757 12500000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (184960713/1250000000 : ℝ)^5063 ≤ (4557788054093/50000000000000 : ℝ)^4039 := by
    have hnat : (184960713 : ℕ)^5063*50000000000000^4039 ≤ 4557788054093^4039*1250000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      184960713 1250000000 4557788054093 50000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (27168437/50000000 : ℝ)^5063 ≤ (23275751067817/50000000000000 : ℝ)^4039 := by
    have hnat : (27168437 : ℕ)^5063*50000000000000^4039 ≤ 23275751067817^4039*50000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27168437 50000000 23275751067817 50000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5063/1024 : ℝ)) 5063 4039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(522608567/1000000000 : ℝ), (-184960713/1250000000 : ℝ), (27168437/50000000 : ℝ)] ![(5541615217757/12500000000000 : ℝ), (4557788054093/50000000000000 : ℝ), (23275751067817/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(522608567/1000000000 : ℝ)|^5063 ≤ (5541615217757/12500000000000 : ℝ)^4039
        have hw : |(522608567/1000000000 : ℝ)|=(522608567/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-184960713/1250000000 : ℝ)|^5063 ≤ (4557788054093/50000000000000 : ℝ)^4039
        have hw : |(-184960713/1250000000 : ℝ)|=(184960713/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(27168437/50000000 : ℝ)|^5063 ≤ (23275751067817/50000000000000 : ℝ)^4039
        have hw : |(27168437/50000000 : ℝ)|=(27168437/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1680_box_2 (p : ℝ) (hpa : (5055/1024 : ℝ) ≤ p) (hpb : p ≤ (5063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2613043293/5000000000 : ℝ)*x 0 + (2716842931/5000000000 : ℝ)*x 1 + (-1479686581/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2613043293/5000000000 : ℝ)^5063 ≤ (22166465741257/50000000000000 : ℝ)^4039 := by
    have hnat : (2613043293 : ℕ)^5063*50000000000000^4039 ≤ 22166465741257^4039*5000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613043293 5000000000 22166465741257 50000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2716842931/5000000000 : ℝ)^5063 ≤ (465514856187/1000000000000 : ℝ)^4039 := by
    have hnat : (2716842931 : ℕ)^5063*1000000000000^4039 ≤ 465514856187^4039*5000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716842931 5000000000 465514856187 1000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1479686581/10000000000 : ℝ)^5063 ≤ (364623315227/4000000000000 : ℝ)^4039 := by
    have hnat : (1479686581 : ℕ)^5063*4000000000000^4039 ≤ 364623315227^4039*10000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1479686581 10000000000 364623315227 4000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5063/1024 : ℝ)) 5063 4039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2613043293/5000000000 : ℝ), (2716842931/5000000000 : ℝ), (-1479686581/10000000000 : ℝ)] ![(22166465741257/50000000000000 : ℝ), (465514856187/1000000000000 : ℝ), (364623315227/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2613043293/5000000000 : ℝ)|^5063 ≤ (22166465741257/50000000000000 : ℝ)^4039
        have hw : |(2613043293/5000000000 : ℝ)|=(2613043293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2716842931/5000000000 : ℝ)|^5063 ≤ (465514856187/1000000000000 : ℝ)^4039
        have hw : |(2716842931/5000000000 : ℝ)|=(2716842931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1479686581/10000000000 : ℝ)|^5063 ≤ (364623315227/4000000000000 : ℝ)^4039
        have hw : |(-1479686581/10000000000 : ℝ)|=(1479686581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1680_box_3 (p : ℝ) (hpa : (5055/1024 : ℝ) ≤ p) (hpb : p ≤ (5063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4530985499/10000000000 : ℝ)*x 0 + (3975489153/10000000000 : ℝ)*x 1 + (496935793/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4530985499/10000000000 : ℝ)^5063 ≤ (296563596833/800000000000 : ℝ)^4039 := by
    have hnat : (4530985499 : ℕ)^5063*800000000000^4039 ≤ 296563596833^4039*10000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4530985499 10000000000 296563596833 800000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3975489153/10000000000 : ℝ)^5063 ≤ (15732394563919/50000000000000 : ℝ)^4039 := by
    have hnat : (3975489153 : ℕ)^5063*50000000000000^4039 ≤ 15732394563919^4039*10000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3975489153 10000000000 15732394563919 50000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (496935793/1250000000 : ℝ)^5063 ≤ (1258590450357/4000000000000 : ℝ)^4039 := by
    have hnat : (496935793 : ℕ)^5063*4000000000000^4039 ≤ 1258590450357^4039*1250000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      496935793 1250000000 1258590450357 4000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5063/1024 : ℝ)) 5063 4039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4530985499/10000000000 : ℝ), (3975489153/10000000000 : ℝ), (496935793/1250000000 : ℝ)] ![(296563596833/800000000000 : ℝ), (15732394563919/50000000000000 : ℝ), (1258590450357/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4530985499/10000000000 : ℝ)|^5063 ≤ (296563596833/800000000000 : ℝ)^4039
        have hw : |(4530985499/10000000000 : ℝ)|=(4530985499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3975489153/10000000000 : ℝ)|^5063 ≤ (15732394563919/50000000000000 : ℝ)^4039
        have hw : |(3975489153/10000000000 : ℝ)|=(3975489153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(496935793/1250000000 : ℝ)|^5063 ≤ (1258590450357/4000000000000 : ℝ)^4039
        have hw : |(496935793/1250000000 : ℝ)|=(496935793/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1680_box_4 (p : ℝ) (hpa : (5055/1024 : ℝ) ≤ p) (hpb : p ≤ (5063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1893261183/10000000000 : ℝ)*x 0 + (1035036043/2000000000 : ℝ)*x 1 + (5175177769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1893261183/10000000000 : ℝ)^5063 ≤ (12415467837283/100000000000000 : ℝ)^4039 := by
    have hnat : (1893261183 : ℕ)^5063*100000000000000^4039 ≤ 12415467837283^4039*10000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1893261183 10000000000 12415467837283 100000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1035036043/2000000000 : ℝ)^5063 ≤ (43792279048767/100000000000000 : ℝ)^4039 := by
    have hnat : (1035036043 : ℕ)^5063*100000000000000^4039 ≤ 43792279048767^4039*2000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035036043 2000000000 43792279048767 100000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5175177769/10000000000 : ℝ)^5063 ≤ (10948063275809/25000000000000 : ℝ)^4039 := by
    have hnat : (5175177769 : ℕ)^5063*25000000000000^4039 ≤ 10948063275809^4039*10000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5175177769 10000000000 10948063275809 25000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5063/1024 : ℝ)) 5063 4039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1893261183/10000000000 : ℝ), (1035036043/2000000000 : ℝ), (5175177769/10000000000 : ℝ)] ![(12415467837283/100000000000000 : ℝ), (43792279048767/100000000000000 : ℝ), (10948063275809/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1893261183/10000000000 : ℝ)|^5063 ≤ (12415467837283/100000000000000 : ℝ)^4039
        have hw : |(-1893261183/10000000000 : ℝ)|=(1893261183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1035036043/2000000000 : ℝ)|^5063 ≤ (43792279048767/100000000000000 : ℝ)^4039
        have hw : |(1035036043/2000000000 : ℝ)|=(1035036043/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5175177769/10000000000 : ℝ)|^5063 ≤ (10948063275809/25000000000000 : ℝ)^4039
        have hw : |(5175177769/10000000000 : ℝ)|=(5175177769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1680_box_5 (p : ℝ) (hpa : (5055/1024 : ℝ) ≤ p) (hpb : p ≤ (5063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2701354473/5000000000 : ℝ)*x 0 + (-397923061/2500000000 : ℝ)*x 1 + (5175178907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2701354473/5000000000 : ℝ)^5063 ≤ (46219058183199/100000000000000 : ℝ)^4039 := by
    have hnat : (2701354473 : ℕ)^5063*100000000000000^4039 ≤ 46219058183199^4039*5000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701354473 5000000000 46219058183199 100000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (397923061/2500000000 : ℝ)^5063 ≤ (9988676622867/100000000000000 : ℝ)^4039 := by
    have hnat : (397923061 : ℕ)^5063*100000000000000^4039 ≤ 9988676622867^4039*2500000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397923061 2500000000 9988676622867 100000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5175178907/10000000000 : ℝ)^5063 ≤ (21896132587189/50000000000000 : ℝ)^4039 := by
    have hnat : (5175178907 : ℕ)^5063*50000000000000^4039 ≤ 21896132587189^4039*10000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5175178907 10000000000 21896132587189 50000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5063/1024 : ℝ)) 5063 4039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2701354473/5000000000 : ℝ), (-397923061/2500000000 : ℝ), (5175178907/10000000000 : ℝ)] ![(46219058183199/100000000000000 : ℝ), (9988676622867/100000000000000 : ℝ), (21896132587189/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2701354473/5000000000 : ℝ)|^5063 ≤ (46219058183199/100000000000000 : ℝ)^4039
        have hw : |(2701354473/5000000000 : ℝ)|=(2701354473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-397923061/2500000000 : ℝ)|^5063 ≤ (9988676622867/100000000000000 : ℝ)^4039
        have hw : |(-397923061/2500000000 : ℝ)|=(397923061/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5175178907/10000000000 : ℝ)|^5063 ≤ (21896132587189/50000000000000 : ℝ)^4039
        have hw : |(5175178907/10000000000 : ℝ)|=(5175178907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1680_box_6 (p : ℝ) (hpa : (5055/1024 : ℝ) ≤ p) (hpb : p ≤ (5063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1350677051/2500000000 : ℝ)*x 0 + (1035035949/2000000000 : ℝ)*x 1 + (-795846063/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1350677051/2500000000 : ℝ)^5063 ≤ (23109525113117/50000000000000 : ℝ)^4039 := by
    have hnat : (1350677051 : ℕ)^5063*50000000000000^4039 ≤ 23109525113117^4039*2500000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350677051 2500000000 23109525113117 50000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1035035949/2000000000 : ℝ)^5063 ≤ (21896137031661/50000000000000 : ℝ)^4039 := by
    have hnat : (1035035949 : ℕ)^5063*50000000000000^4039 ≤ 21896137031661^4039*2000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035035949 2000000000 21896137031661 50000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (795846063/5000000000 : ℝ)^5063 ≤ (9988675694617/100000000000000 : ℝ)^4039 := by
    have hnat : (795846063 : ℕ)^5063*100000000000000^4039 ≤ 9988675694617^4039*5000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      795846063 5000000000 9988675694617 100000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5063/1024 : ℝ)) 5063 4039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1350677051/2500000000 : ℝ), (1035035949/2000000000 : ℝ), (-795846063/5000000000 : ℝ)] ![(23109525113117/50000000000000 : ℝ), (21896137031661/50000000000000 : ℝ), (9988675694617/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1350677051/2500000000 : ℝ)|^5063 ≤ (23109525113117/50000000000000 : ℝ)^4039
        have hw : |(1350677051/2500000000 : ℝ)|=(1350677051/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1035035949/2000000000 : ℝ)|^5063 ≤ (21896137031661/50000000000000 : ℝ)^4039
        have hw : |(1035035949/2000000000 : ℝ)|=(1035035949/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-795846063/5000000000 : ℝ)|^5063 ≤ (9988675694617/100000000000000 : ℝ)^4039
        have hw : |(-795846063/5000000000 : ℝ)|=(795846063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1680_box_7 (p : ℝ) (hpa : (5055/1024 : ℝ) ≤ p) (hpb : p ≤ (5063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3745399579/10000000000 : ℝ)*x 0 + (4367400911/10000000000 : ℝ)*x 1 + (4367399457/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3745399579/10000000000 : ℝ)^5063 ≤ (7299749613241/25000000000000 : ℝ)^4039 := by
    have hnat : (3745399579 : ℕ)^5063*25000000000000^4039 ≤ 7299749613241^4039*10000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3745399579 10000000000 7299749613241 25000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4367400911/10000000000 : ℝ)^5063 ≤ (35400508148871/100000000000000 : ℝ)^4039 := by
    have hnat : (4367400911 : ℕ)^5063*100000000000000^4039 ≤ 35400508148871^4039*10000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4367400911 10000000000 35400508148871 100000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4367399457/10000000000 : ℝ)^5063 ≤ (885012334383/2500000000000 : ℝ)^4039 := by
    have hnat : (4367399457 : ℕ)^5063*2500000000000^4039 ≤ 885012334383^4039*10000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4367399457 10000000000 885012334383 2500000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5063/1024 : ℝ)) 5063 4039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3745399579/10000000000 : ℝ), (4367400911/10000000000 : ℝ), (4367399457/10000000000 : ℝ)] ![(7299749613241/25000000000000 : ℝ), (35400508148871/100000000000000 : ℝ), (885012334383/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3745399579/10000000000 : ℝ)|^5063 ≤ (7299749613241/25000000000000 : ℝ)^4039
        have hw : |(3745399579/10000000000 : ℝ)|=(3745399579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4367400911/10000000000 : ℝ)|^5063 ≤ (35400508148871/100000000000000 : ℝ)^4039
        have hw : |(4367400911/10000000000 : ℝ)|=(4367400911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4367399457/10000000000 : ℝ)|^5063 ≤ (885012334383/2500000000000 : ℝ)^4039
        have hw : |(4367399457/10000000000 : ℝ)|=(4367399457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1680_box_8 (p : ℝ) (hpa : (5055/1024 : ℝ) ≤ p) (hpb : p ≤ (5063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1741407033/10000000000 : ℝ)*x 0 + (4986042229/10000000000 : ℝ)*x 1 + (342355107/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1741407033/10000000000 : ℝ)^5063 ≤ (1397517323923/12500000000000 : ℝ)^4039 := by
    have hnat : (1741407033 : ℕ)^5063*12500000000000^4039 ≤ 1397517323923^4039*10000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1741407033 10000000000 1397517323923 12500000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4986042229/10000000000 : ℝ)^5063 ≤ (8359082059791/20000000000000 : ℝ)^4039 := by
    have hnat : (4986042229 : ℕ)^5063*20000000000000^4039 ≤ 8359082059791^4039*10000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4986042229 10000000000 8359082059791 20000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (342355107/625000000 : ℝ)^5063 ≤ (47024451093087/100000000000000 : ℝ)^4039 := by
    have hnat : (342355107 : ℕ)^5063*100000000000000^4039 ≤ 47024451093087^4039*625000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      342355107 625000000 47024451093087 100000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5063/1024 : ℝ)) 5063 4039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1741407033/10000000000 : ℝ), (4986042229/10000000000 : ℝ), (342355107/625000000 : ℝ)] ![(1397517323923/12500000000000 : ℝ), (8359082059791/20000000000000 : ℝ), (47024451093087/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1741407033/10000000000 : ℝ)|^5063 ≤ (1397517323923/12500000000000 : ℝ)^4039
        have hw : |(-1741407033/10000000000 : ℝ)|=(1741407033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4986042229/10000000000 : ℝ)|^5063 ≤ (8359082059791/20000000000000 : ℝ)^4039
        have hw : |(4986042229/10000000000 : ℝ)|=(4986042229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(342355107/625000000 : ℝ)|^5063 ≤ (47024451093087/100000000000000 : ℝ)^4039
        have hw : |(342355107/625000000 : ℝ)|=(342355107/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1680_box_9 (p : ℝ) (hpa : (5055/1024 : ℝ) ≤ p) (hpb : p ≤ (5063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2598016703/5000000000 : ℝ)*x 0 + (-145975877/1000000000 : ℝ)*x 1 + (5477681997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2598016703/5000000000 : ℝ)^5063 ≤ (44013588631859/100000000000000 : ℝ)^4039 := by
    have hnat : (2598016703 : ℕ)^5063*100000000000000^4039 ≤ 44013588631859^4039*5000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598016703 5000000000 44013588631859 100000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (145975877/1000000000 : ℝ)^5063 ≤ (179239144063/2000000000000 : ℝ)^4039 := by
    have hnat : (145975877 : ℕ)^5063*2000000000000^4039 ≤ 179239144063^4039*1000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      145975877 1000000000 179239144063 2000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5477681997/10000000000 : ℝ)^5063 ≤ (47024454160031/100000000000000 : ℝ)^4039 := by
    have hnat : (5477681997 : ℕ)^5063*100000000000000^4039 ≤ 47024454160031^4039*10000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5477681997 10000000000 47024454160031 100000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5063/1024 : ℝ)) 5063 4039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2598016703/5000000000 : ℝ), (-145975877/1000000000 : ℝ), (5477681997/10000000000 : ℝ)] ![(44013588631859/100000000000000 : ℝ), (179239144063/2000000000000 : ℝ), (47024454160031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2598016703/5000000000 : ℝ)|^5063 ≤ (44013588631859/100000000000000 : ℝ)^4039
        have hw : |(2598016703/5000000000 : ℝ)|=(2598016703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-145975877/1000000000 : ℝ)|^5063 ≤ (179239144063/2000000000000 : ℝ)^4039
        have hw : |(-145975877/1000000000 : ℝ)|=(145975877/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5477681997/10000000000 : ℝ)|^5063 ≤ (47024454160031/100000000000000 : ℝ)^4039
        have hw : |(5477681997/10000000000 : ℝ)|=(5477681997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1680_box_10 (p : ℝ) (hpa : (5055/1024 : ℝ) ≤ p) (hpb : p ≤ (5063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2598016699/5000000000 : ℝ)*x 0 + (1369420597/2500000000 : ℝ)*x 1 + (-729879117/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2598016699/5000000000 : ℝ)^5063 ≤ (22006794273457/50000000000000 : ℝ)^4039 := by
    have hnat : (2598016699 : ℕ)^5063*50000000000000^4039 ≤ 22006794273457^4039*5000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598016699 5000000000 22006794273457 50000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1369420597/2500000000 : ℝ)^5063 ≤ (2939028647979/6250000000000 : ℝ)^4039 := by
    have hnat : (1369420597 : ℕ)^5063*6250000000000^4039 ≤ 2939028647979^4039*2500000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1369420597 2500000000 2939028647979 6250000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (729879117/5000000000 : ℝ)^5063 ≤ (8961953078181/100000000000000 : ℝ)^4039 := by
    have hnat : (729879117 : ℕ)^5063*100000000000000^4039 ≤ 8961953078181^4039*5000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      729879117 5000000000 8961953078181 100000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5063/1024 : ℝ)) 5063 4039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2598016699/5000000000 : ℝ), (1369420597/2500000000 : ℝ), (-729879117/5000000000 : ℝ)] ![(22006794273457/50000000000000 : ℝ), (2939028647979/6250000000000 : ℝ), (8961953078181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2598016699/5000000000 : ℝ)|^5063 ≤ (22006794273457/50000000000000 : ℝ)^4039
        have hw : |(2598016699/5000000000 : ℝ)|=(2598016699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1369420597/2500000000 : ℝ)|^5063 ≤ (2939028647979/6250000000000 : ℝ)^4039
        have hw : |(1369420597/2500000000 : ℝ)|=(1369420597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-729879117/5000000000 : ℝ)|^5063 ≤ (8961953078181/100000000000000 : ℝ)^4039
        have hw : |(-729879117/5000000000 : ℝ)|=(729879117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1680_box_11 (p : ℝ) (hpa : (5055/1024 : ℝ) ≤ p) (hpb : p ≤ (5063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4659631767/10000000000 : ℝ)*x 0 + (39086157/100000000 : ℝ)*x 1 + (1954307247/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4659631767/10000000000 : ℝ)^5063 ≤ (38394534603407/100000000000000 : ℝ)^4039 := by
    have hnat : (4659631767 : ℕ)^5063*100000000000000^4039 ≤ 38394534603407^4039*10000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4659631767 10000000000 38394534603407 100000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (39086157/100000000 : ℝ)^5063 ≤ (30802738649193/100000000000000 : ℝ)^4039 := by
    have hnat : (39086157 : ℕ)^5063*100000000000000^4039 ≤ 30802738649193^4039*100000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39086157 100000000 30802738649193 100000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1954307247/5000000000 : ℝ)^5063 ≤ (3850340841933/12500000000000 : ℝ)^4039 := by
    have hnat : (1954307247 : ℕ)^5063*12500000000000^4039 ≤ 3850340841933^4039*5000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1954307247 5000000000 3850340841933 12500000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5063/1024 : ℝ)) 5063 4039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4659631767/10000000000 : ℝ), (39086157/100000000 : ℝ), (1954307247/5000000000 : ℝ)] ![(38394534603407/100000000000000 : ℝ), (30802738649193/100000000000000 : ℝ), (3850340841933/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4659631767/10000000000 : ℝ)|^5063 ≤ (38394534603407/100000000000000 : ℝ)^4039
        have hw : |(4659631767/10000000000 : ℝ)|=(4659631767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(39086157/100000000 : ℝ)|^5063 ≤ (30802738649193/100000000000000 : ℝ)^4039
        have hw : |(39086157/100000000 : ℝ)|=(39086157/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1954307247/5000000000 : ℝ)|^5063 ≤ (3850340841933/12500000000000 : ℝ)^4039
        have hw : |(1954307247/5000000000 : ℝ)|=(1954307247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1680_box_12 (p : ℝ) (hpa : (5055/1024 : ℝ) ≤ p) (hpb : p ≤ (5063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1331938063/10000000000 : ℝ)*x 0 + (5613191113/10000000000 : ℝ)*x 1 + (5149808737/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1331938063/10000000000 : ℝ)^5063 ≤ (3994718060371/50000000000000 : ℝ)^4039 := by
    have hnat : (1331938063 : ℕ)^5063*50000000000000^4039 ≤ 3994718060371^4039*10000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1331938063 10000000000 3994718060371 50000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5613191113/10000000000 : ℝ)^5063 ≤ (9697448207737/20000000000000 : ℝ)^4039 := by
    have hnat : (5613191113 : ℕ)^5063*20000000000000^4039 ≤ 9697448207737^4039*10000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5613191113 10000000000 9697448207737 20000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5149808737/10000000000 : ℝ)^5063 ≤ (21761661412447/50000000000000 : ℝ)^4039 := by
    have hnat : (5149808737 : ℕ)^5063*50000000000000^4039 ≤ 21761661412447^4039*10000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5149808737 10000000000 21761661412447 50000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5063/1024 : ℝ)) 5063 4039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1331938063/10000000000 : ℝ), (5613191113/10000000000 : ℝ), (5149808737/10000000000 : ℝ)] ![(3994718060371/50000000000000 : ℝ), (9697448207737/20000000000000 : ℝ), (21761661412447/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1331938063/10000000000 : ℝ)|^5063 ≤ (3994718060371/50000000000000 : ℝ)^4039
        have hw : |(-1331938063/10000000000 : ℝ)|=(1331938063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5613191113/10000000000 : ℝ)|^5063 ≤ (9697448207737/20000000000000 : ℝ)^4039
        have hw : |(5613191113/10000000000 : ℝ)|=(5613191113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5149808737/10000000000 : ℝ)|^5063 ≤ (21761661412447/50000000000000 : ℝ)^4039
        have hw : |(5149808737/10000000000 : ℝ)|=(5149808737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1680_box_13 (p : ℝ) (hpa : (5055/1024 : ℝ) ≤ p) (hpb : p ≤ (5063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (169377131/312500000 : ℝ)*x 0 + (-200274709/1250000000 : ℝ)*x 1 + (41198471/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (169377131/312500000 : ℝ)^5063 ≤ (46405288834799/100000000000000 : ℝ)^4039 := by
    have hnat : (169377131 : ℕ)^5063*100000000000000^4039 ≤ 46405288834799^4039*312500000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169377131 312500000 46405288834799 100000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (200274709/1250000000 : ℝ)^5063 ≤ (10071386864573/100000000000000 : ℝ)^4039 := by
    have hnat : (200274709 : ℕ)^5063*100000000000000^4039 ≤ 10071386864573^4039*1250000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200274709 1250000000 10071386864573 100000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41198471/80000000 : ℝ)^5063 ≤ (43523324286883/100000000000000 : ℝ)^4039 := by
    have hnat : (41198471 : ℕ)^5063*100000000000000^4039 ≤ 43523324286883^4039*80000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41198471 80000000 43523324286883 100000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5063/1024 : ℝ)) 5063 4039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(169377131/312500000 : ℝ), (-200274709/1250000000 : ℝ), (41198471/80000000 : ℝ)] ![(46405288834799/100000000000000 : ℝ), (10071386864573/100000000000000 : ℝ), (43523324286883/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(169377131/312500000 : ℝ)|^5063 ≤ (46405288834799/100000000000000 : ℝ)^4039
        have hw : |(169377131/312500000 : ℝ)|=(169377131/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-200274709/1250000000 : ℝ)|^5063 ≤ (10071386864573/100000000000000 : ℝ)^4039
        have hw : |(-200274709/1250000000 : ℝ)|=(200274709/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(41198471/80000000 : ℝ)|^5063 ≤ (43523324286883/100000000000000 : ℝ)^4039
        have hw : |(41198471/80000000 : ℝ)|=(41198471/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1680_box_14 (p : ℝ) (hpa : (5055/1024 : ℝ) ≤ p) (hpb : p ≤ (5063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2710034149/5000000000 : ℝ)*x 0 + (514980857/1000000000 : ℝ)*x 1 + (-1602197937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2710034149/5000000000 : ℝ)^5063 ≤ (46405289972433/100000000000000 : ℝ)^4039 := by
    have hnat : (2710034149 : ℕ)^5063*100000000000000^4039 ≤ 46405289972433^4039*5000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2710034149 5000000000 46405289972433 100000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (514980857/1000000000 : ℝ)^5063 ≤ (10880830263919/25000000000000 : ℝ)^4039 := by
    have hnat : (514980857 : ℕ)^5063*25000000000000^4039 ≤ 10880830263919^4039*1000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      514980857 1000000000 10880830263919 25000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1602197937/10000000000 : ℝ)^5063 ≤ (5035694476341/50000000000000 : ℝ)^4039 := by
    have hnat : (1602197937 : ℕ)^5063*50000000000000^4039 ≤ 5035694476341^4039*10000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1602197937 10000000000 5035694476341 50000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5063/1024 : ℝ)) 5063 4039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2710034149/5000000000 : ℝ), (514980857/1000000000 : ℝ), (-1602197937/10000000000 : ℝ)] ![(46405289972433/100000000000000 : ℝ), (10880830263919/25000000000000 : ℝ), (5035694476341/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2710034149/5000000000 : ℝ)|^5063 ≤ (46405289972433/100000000000000 : ℝ)^4039
        have hw : |(2710034149/5000000000 : ℝ)|=(2710034149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(514980857/1000000000 : ℝ)|^5063 ≤ (10880830263919/25000000000000 : ℝ)^4039
        have hw : |(514980857/1000000000 : ℝ)|=(514980857/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1602197937/10000000000 : ℝ)|^5063 ≤ (5035694476341/50000000000000 : ℝ)^4039
        have hw : |(-1602197937/10000000000 : ℝ)|=(1602197937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1680_box_15 (p : ℝ) (hpa : (5055/1024 : ℝ) ≤ p) (hpb : p ≤ (5063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3665322311/10000000000 : ℝ)*x 0 + (4405761713/10000000000 : ℝ)*x 1 + (2202880813/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3665322311/10000000000 : ℝ)^5063 ≤ (14209289448939/50000000000000 : ℝ)^4039 := by
    have hnat : (3665322311 : ℕ)^5063*50000000000000^4039 ≤ 14209289448939^4039*10000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3665322311 10000000000 14209289448939 50000000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4405761713/10000000000 : ℝ)^5063 ≤ (2236919436561/6250000000000 : ℝ)^4039 := by
    have hnat : (4405761713 : ℕ)^5063*6250000000000^4039 ≤ 2236919436561^4039*10000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4405761713 10000000000 2236919436561 6250000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2202880813/5000000000 : ℝ)^5063 ≤ (223691938119/625000000000 : ℝ)^4039 := by
    have hnat : (2202880813 : ℕ)^5063*625000000000^4039 ≤ 223691938119^4039*5000000000^5063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2202880813 5000000000 223691938119 625000000000 5063 4039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5063/1024 : ℝ)) 5063 4039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3665322311/10000000000 : ℝ), (4405761713/10000000000 : ℝ), (2202880813/5000000000 : ℝ)] ![(14209289448939/50000000000000 : ℝ), (2236919436561/6250000000000 : ℝ), (223691938119/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3665322311/10000000000 : ℝ)|^5063 ≤ (14209289448939/50000000000000 : ℝ)^4039
        have hw : |(3665322311/10000000000 : ℝ)|=(3665322311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4405761713/10000000000 : ℝ)|^5063 ≤ (2236919436561/6250000000000 : ℝ)^4039
        have hw : |(4405761713/10000000000 : ℝ)|=(4405761713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2202880813/5000000000 : ℝ)|^5063 ≤ (223691938119/625000000000 : ℝ)^4039
        have hw : |(2202880813/5000000000 : ℝ)|=(2202880813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1680_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5055/1024 : ℝ) ≤ p) (hpb : p ≤ (5063/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (185082949/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3461/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4863/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(2078/3125 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(57691/100000 : ℝ) ∧ (16089/20000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (89981/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3461/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4863/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3461/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4863/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3461/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4863/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3461/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4863/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3461/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4863/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3461/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4863/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4863/50000 : ℝ) ^ (5055/1024 : ℝ) ≤ (1009052540177489/100000000000000000000 : ℝ) := by
    have hpowers : (4863/50000 : ℝ)^5055 ≤ (1009052540177489/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4863 : ℕ)^5055*100000000000000000000^1024 ≤ 1009052540177489^1024*50000^5055 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4863 50000 1009052540177489 100000000000000000000 5055 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4863/50000 : ℝ)) (X := (1009052540177489/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5055 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3461/20000 : ℝ) ^ (5055/1024 : ℝ) ≤ (2168334495637449/12500000000000000000 : ℝ) := by
    have hpowers : (3461/20000 : ℝ)^5055 ≤ (2168334495637449/12500000000000000000 : ℝ)^1024 := by
      have hnat : (3461 : ℕ)^5055*12500000000000000000^1024 ≤ 2168334495637449^1024*20000^5055 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3461 20000 2168334495637449 12500000000000000000 5055 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3461/20000 : ℝ)) (X := (2168334495637449/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 5055 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001009052540177489/50000000000000000000 : ℝ) ≤ (5000020440385501/5000000000000000 : ℝ) ^ (5055/1024 : ℝ) := by
    have hpowers : (50001009052540177489/50000000000000000000 : ℝ)^1024 ≤ (5000020440385501/5000000000000000 : ℝ)^5055 := by
      have hnat : (50001009052540177489 : ℕ)^1024*5000000000000000^5055 ≤ 5000020440385501^5055*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001009052540177489 50000000000000000000 5000020440385501 5000000000000000 1024 5055 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000020440385501/5000000000000000 : ℝ)) (X := (50001009052540177489/50000000000000000000 : ℝ)) (by norm_num) 5055 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100018355728505277081/100000000000000000000 : ℝ) ≤ (10000371807922859/10000000000000000 : ℝ) ^ (5055/1024 : ℝ) := by
    have hpowers : (100018355728505277081/100000000000000000000 : ℝ)^1024 ≤ (10000371807922859/10000000000000000 : ℝ)^5055 := by
      have hnat : (100018355728505277081 : ℕ)^1024*10000000000000000^5055 ≤ 10000371807922859^5055*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100018355728505277081 100000000000000000000 10000371807922859 10000000000000000 1024 5055 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000371807922859/10000000000000000 : ℝ)) (X := (100018355728505277081/100000000000000000000 : ℝ)) (by norm_num) 5055 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6252168334495637449/6250000000000000000 : ℝ) ≤ (2500175683768679/2500000000000000 : ℝ) ^ (5055/1024 : ℝ) := by
    have hpowers : (6252168334495637449/6250000000000000000 : ℝ)^1024 ≤ (2500175683768679/2500000000000000 : ℝ)^5055 := by
      have hnat : (6252168334495637449 : ℕ)^1024*2500000000000000^5055 ≤ 2500175683768679^5055*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252168334495637449 6250000000000000000 2500175683768679 2500000000000000 1024 5055 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500175683768679/2500000000000000 : ℝ)) (X := (6252168334495637449/6250000000000000000 : ℝ)) (by norm_num) 5055 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1009052540177489/100000000000000000000 : ℝ) ≤ ((37891936320202750897/37895000000000000000 : ℝ)+2*(330927151857/757900000000000 : ℝ)*(4863/50000 : ℝ))^(5055/1024 : ℝ) := by
    rw [show (37891936320202750897/37895000000000000000 : ℝ)+2*(330927151857/757900000000000 : ℝ)*(4863/50000 : ℝ)=(5000020440385501/5000000000000000 : ℝ) by norm_num, show 1+2*(1009052540177489/100000000000000000000 : ℝ)=(50001009052540177489/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2168334495637449/12500000000000000000 : ℝ)+(1009052540177489/100000000000000000000 : ℝ) ≤ ((37891936320202750897/37895000000000000000 : ℝ)+(330927151857/757900000000000 : ℝ)*((3461/20000 : ℝ)+(4863/50000 : ℝ)))^(5055/1024 : ℝ) := by
    rw [show (37891936320202750897/37895000000000000000 : ℝ)+(330927151857/757900000000000 : ℝ)*((3461/20000 : ℝ)+(4863/50000 : ℝ))=(10000371807922859/10000000000000000 : ℝ) by norm_num, show 1+(2168334495637449/12500000000000000000 : ℝ)+(1009052540177489/100000000000000000000 : ℝ)=(100018355728505277081/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2168334495637449/12500000000000000000 : ℝ) ≤ ((37891936320202750897/37895000000000000000 : ℝ)+2*(330927151857/757900000000000 : ℝ)*(3461/20000 : ℝ))^(5055/1024 : ℝ) := by
    rw [show (37891936320202750897/37895000000000000000 : ℝ)+2*(330927151857/757900000000000 : ℝ)*(3461/20000 : ℝ)=(2500175683768679/2500000000000000 : ℝ) by norm_num, show 1+2*(2168334495637449/12500000000000000000 : ℝ)=(6252168334495637449/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (37891936320202750897/37895000000000000000 : ℝ)*(X 1 0+X 2 0)+(330927151857/757900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5055/1024 : ℝ)) (lo := (4863/50000 : ℝ)) (hi := (3461/20000 : ℝ)) (c := (37891936320202750897/37895000000000000000 : ℝ)) (alpha := (330927151857/757900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (37891936320202750897/37895000000000000000 : ℝ)*(X 0 1+X 2 1)+(330927151857/757900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5055/1024 : ℝ)) (lo := (4863/50000 : ℝ)) (hi := (3461/20000 : ℝ)) (c := (37891936320202750897/37895000000000000000 : ℝ)) (alpha := (330927151857/757900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (37891936320202750897/37895000000000000000 : ℝ)*(X 0 2+X 1 2)+(330927151857/757900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5055/1024 : ℝ)) (lo := (4863/50000 : ℝ)) (hi := (3461/20000 : ℝ)) (c := (37891936320202750897/37895000000000000000 : ℝ)) (alpha := (330927151857/757900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1184521477/10000000000 : ℝ)*X 0 0+(543368883/1000000000 : ℝ)*X 0 1+(2716842923/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1680_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((522608567/1000000000 : ℝ)*X 1 0+(-184960713/1250000000 : ℝ)*X 1 1+(27168437/50000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1680_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2613043293/5000000000 : ℝ)*X 2 0+(2716842931/5000000000 : ℝ)*X 2 1+(-1479686581/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1680_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4530985499/10000000000 : ℝ)*X 0 0+(3975489153/10000000000 : ℝ)*X 0 1+(496935793/1250000000 : ℝ)*X 0 2+(4530985499/10000000000 : ℝ)*X 1 0+(3975489153/10000000000 : ℝ)*X 1 1+(496935793/1250000000 : ℝ)*X 1 2+(4530985499/10000000000 : ℝ)*X 2 0+(3975489153/10000000000 : ℝ)*X 2 1+(496935793/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1680_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1893261183/10000000000 : ℝ)*X 0 0+(1035036043/2000000000 : ℝ)*X 0 1+(5175177769/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1680_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2701354473/5000000000 : ℝ)*X 1 0+(-397923061/2500000000 : ℝ)*X 1 1+(5175178907/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1680_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1350677051/2500000000 : ℝ)*X 2 0+(1035035949/2000000000 : ℝ)*X 2 1+(-795846063/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1680_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3745399579/10000000000 : ℝ)*X 0 0+(4367400911/10000000000 : ℝ)*X 0 1+(4367399457/10000000000 : ℝ)*X 0 2+(3745399579/10000000000 : ℝ)*X 1 0+(4367400911/10000000000 : ℝ)*X 1 1+(4367399457/10000000000 : ℝ)*X 1 2+(3745399579/10000000000 : ℝ)*X 2 0+(4367400911/10000000000 : ℝ)*X 2 1+(4367399457/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1680_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1741407033/10000000000 : ℝ)*X 0 0+(4986042229/10000000000 : ℝ)*X 0 1+(342355107/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1680_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2598016703/5000000000 : ℝ)*X 1 0+(-145975877/1000000000 : ℝ)*X 1 1+(5477681997/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1680_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2598016699/5000000000 : ℝ)*X 2 0+(1369420597/2500000000 : ℝ)*X 2 1+(-729879117/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1680_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4659631767/10000000000 : ℝ)*X 0 0+(39086157/100000000 : ℝ)*X 0 1+(1954307247/5000000000 : ℝ)*X 0 2+(4659631767/10000000000 : ℝ)*X 1 0+(39086157/100000000 : ℝ)*X 1 1+(1954307247/5000000000 : ℝ)*X 1 2+(4659631767/10000000000 : ℝ)*X 2 0+(39086157/100000000 : ℝ)*X 2 1+(1954307247/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1680_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1331938063/10000000000 : ℝ)*X 0 0+(5613191113/10000000000 : ℝ)*X 0 1+(5149808737/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1680_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((169377131/312500000 : ℝ)*X 1 0+(-200274709/1250000000 : ℝ)*X 1 1+(41198471/80000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1680_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2710034149/5000000000 : ℝ)*X 2 0+(514980857/1000000000 : ℝ)*X 2 1+(-1602197937/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1680_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((3665322311/10000000000 : ℝ)*X 0 0+(4405761713/10000000000 : ℝ)*X 0 1+(2202880813/5000000000 : ℝ)*X 0 2+(3665322311/10000000000 : ℝ)*X 1 0+(4405761713/10000000000 : ℝ)*X 1 1+(2202880813/5000000000 : ℝ)*X 1 2+(3665322311/10000000000 : ℝ)*X 2 0+(4405761713/10000000000 : ℝ)*X 2 1+(2202880813/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1680_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-2078/3125 : ℝ) ≤ (-62994323098911665167816839656577/94737500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (54184941/100000000000000 : ℝ)*(lower0) + (61125787/100000000000000 : ℝ)*(upper3) + (2785793/25000000000000 : ℝ)*(lower4) + (4337937/10000000000000 : ℝ)*(lower5) + (63980412169549/5000000000000 : ℝ)*(major0) + (63980412169549/5000000000000 : ℝ)*(major1) + (63980412169549/5000000000000 : ℝ)*(major2) + (4575108611/100000000000000 : ℝ)*(sp1) + (472500465767677/25000000000000 : ℝ)*(sp4) + (37800125742279/2000000000000 : ℝ)*(sp5) + (944991523189349/50000000000000 : ℝ)*(sp6) + (13827402797553/2000000000000 : ℝ)*(sp7) + (4499575927/50000000000000 : ℝ)*(sp8) + (27815843863/100000000000000 : ℝ)*(sp14) + (13827402797553/2000000000000 : ℝ)*(f.failure) + (945005431111281/50000000000000 : ℝ)*(f.sum) + (482366452121/118421875000000000000000000 : ℝ)*base66 + (30490774471298881/14575000000000000000000000000000 : ℝ)*base67 + (129036771322248881/14575000000000000000000000000000 : ℝ)*base69 + (33188803966998881/14575000000000000000000000000000 : ℝ)*base71 + (13712055726651/3789500000000000000000000000 : ℝ)*base74 + (145298542630998881/14575000000000000000000000000000 : ℝ)*base75 + (101509225837798881/14575000000000000000000000000000 : ℝ)*base77 + (110170942043248881/14575000000000000000000000000000 : ℝ)*base79 + (15869749293263/7579000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (776203/200000000000000000000 : ℝ)*base90 + (776203/200000000000000000000 : ℝ)*base92 + (776203/200000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (57691/100000 : ℝ) ≤ (546572086471160455800738534211569/947375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (68086397/50000000000000 : ℝ)*(upper3) + (98500677/100000000000000 : ℝ)*(upper4) + (193992069/100000000000000 : ℝ)*(lower5) + (687894572849141/50000000000000 : ℝ)*(major0) + (687894572849141/50000000000000 : ℝ)*(major1) + (687894572849141/50000000000000 : ℝ)*(major2) + (124312598815749/6250000000000 : ℝ)*(sp0) + (49725138146183/2500000000000 : ℝ)*(sp1) + (1989010264329991/100000000000000 : ℝ)*(sp2) + (185833289309129/25000000000000 : ℝ)*(sp3) + (1285634327/25000000000000 : ℝ)*(sp5) + (404054637/100000000000000 : ℝ)*(sp6) + (839811307/25000000000000 : ℝ)*(sp7) + (2271833161/25000000000000 : ℝ)*(sp8) + (46458532280109/6250000000000 : ℝ)*(f.failure) + (497252667096157/25000000000000 : ℝ)*(f.sum) + (32561997158173/18947500000000000000000000000 : ℝ)*base66 + (315165073473209271/145750000000000000000000000000000 : ℝ)*base68 + (144817868846790729/145750000000000000000000000000000 : ℝ)*base69 + (56785076977790729/145750000000000000000000000000000 : ℝ)*base71 + (14930549213097/18947500000000000000000000000 : ℝ)*base73 + (191529962043790729/145750000000000000000000000000000 : ℝ)*base75 + (101022984928290729/145750000000000000000000000000000 : ℝ)*base77 + (491617691526459271/145750000000000000000000000000000 : ℝ)*base80 + (33415155671291/37895000000000000000000000000 : ℝ)*base82 + (5261441/625000000000000000000 : ℝ)*base89 + (5261441/625000000000000000000 : ℝ)*base91 + (5261441/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (16089/20000 : ℝ) ≤ (13857003386820069086918828626233/17225000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (624501/25000000000000 : ℝ)*(upper1) + (1354843/4000000000000 : ℝ)*(upper2) + (7709001/12500000000000 : ℝ)*(upper3) + (9668453/6250000000000 : ℝ)*(upper4) + (282362831083607/20000000000000 : ℝ)*(major0) + (282362831083607/20000000000000 : ℝ)*(major1) + (282362831083607/20000000000000 : ℝ)*(major2) + (273813589/100000000000000 : ℝ)*(sp0) + (40744889717/100000000000000 : ℝ)*(sp2) + (9014942009/100000000000000 : ℝ)*(sp3) + (203401158811269/10000000000000 : ℝ)*(sp8) + (50850296548157/2500000000000 : ℝ)*(sp9) + (1016985558518281/50000000000000 : ℝ)*(sp10) + (190697938130637/25000000000000 : ℝ)*(sp11) + (762800767464557/100000000000000 : ℝ)*(f.failure) + (50850296548157/2500000000000 : ℝ)*(f.sum) + (20760437881563/7579000000000000000000000000 : ℝ)*base65 + (328976842730068883/58300000000000000000000000000000 : ℝ)*base67 + (518405580222568883/58300000000000000000000000000000 : ℝ)*base69 + (356629079001068883/58300000000000000000000000000000 : ℝ)*base71 + (2585119456729/1894750000000000000000000000 : ℝ)*base73 + (186866694141231117/58300000000000000000000000000000 : ℝ)*base76 + (320901430589668883/58300000000000000000000000000000 : ℝ)*base77 + (350591321121068883/58300000000000000000000000000000 : ℝ)*base79 + (3094055577709/3789500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (37461407/10000000000000000000000 : ℝ)*base90 + (37461407/10000000000000000000000 : ℝ)*base92 + (37461407/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-89981/100000 : ℝ) ≤ (-213108904567576373023799854405119/236843750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (65363633/100000000000000 : ℝ)*(upper3) + (5824333/25000000000000 : ℝ)*(lower4) + (7315897/25000000000000 : ℝ)*(upper5) + (182233651239553/12500000000000 : ℝ)*(major0) + (182233651239553/12500000000000 : ℝ)*(major1) + (182233651239553/12500000000000 : ℝ)*(major2) + (327417397/25000000000000 : ℝ)*(sp4) + (7667528473/50000000000000 : ℝ)*(sp5) + (20965650837/50000000000000 : ℝ)*(sp6) + (3819454907/50000000000000 : ℝ)*(sp7) + (107902288626143/5000000000000 : ℝ)*(sp12) + (1079015873567751/50000000000000 : ℝ)*(sp13) + (86320206035631/4000000000000 : ℝ)*(sp14) + (393838297766929/50000000000000 : ℝ)*(sp15) + (787684234443673/100000000000000 : ℝ)*(f.failure) + (33719485659257/1562500000000 : ℝ)*(f.sum) + (2660206389021/4736875000000000000000000000 : ℝ)*base65 + (238947690931379157/36437500000000000000000000000000 : ℝ)*base67 + (590334282070754157/36437500000000000000000000000000 : ℝ)*base69 + (398762509963379157/36437500000000000000000000000000 : ℝ)*base71 + (13919832474767/9473750000000000000000000000 : ℝ)*base73 + (477487297930754157/36437500000000000000000000000000 : ℝ)*base75 + (271993053456004157/36437500000000000000000000000000 : ℝ)*base77 + (105871007603879157/36437500000000000000000000000000 : ℝ)*base79 + (261092479304103/37895000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (26768323/10000000000000000000000 : ℝ)*base90 + (26768323/10000000000000000000000 : ℝ)*base92 + (26768323/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1680_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5055/1024 : ℝ) ≤ p) (hpb : p ≤ (5063/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (185082949/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3461/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4863/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2078/3125 : ℝ) ≤ X j i ∧ X j i ≤ -(57691/100000 : ℝ) else (16089/20000 : ℝ) ≤ X j i ∧ X j i ≤ (89981/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1680_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1680_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5055/1024 : ℝ) ≤ p) (hpb : p ≤ (5063/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (185082949/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8669/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4849/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2078/3125 : ℝ) ≤ X j i ∧ X j i ≤ -(57691/100000 : ℝ) else (16089/20000 : ℝ) ≤ X j i ∧ X j i ≤ (89981/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1680_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1680_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1680_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5055/1024 : ℝ) ≤ p) (hpb : p ≤ (5063/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (185082949/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8669/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4849/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2078/3125 : ℝ) ≤ X j i ∧ X j i ≤ -(57691/100000 : ℝ) else (16089/20000 : ℝ) ≤ X j i ∧ X j i ≤ (89981/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1680_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
