-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1679_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:28:00.1202+00:00
-- url     : https://prove2.me/submissions/5e68b461-c04d-4293-9e6f-6ac275e3149c

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
theorem support_rectangle_w1679_s0_0 (p : ℝ) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-716540837/5000000000 : ℝ)*x 0 + (5764401747/10000000000 : ℝ)*x 1 + (1231127489/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (716540837/5000000000 : ℝ)^5055 ≤ (4374288198369/50000000000000 : ℝ)^4031 := by
    have hnat : (716540837 : ℕ)^5055*50000000000000^4031 ≤ 4374288198369^4031*5000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      716540837 5000000000 4374288198369 50000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5764401747/10000000000 : ℝ)^5055 ≤ (6264527976787/12500000000000 : ℝ)^4031 := by
    have hnat : (5764401747 : ℕ)^5055*12500000000000^4031 ≤ 6264527976787^4031*10000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5764401747 10000000000 6264527976787 12500000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1231127489/2500000000 : ℝ)^5055 ≤ (41135199773293/100000000000000 : ℝ)^4031 := by
    have hnat : (1231127489 : ℕ)^5055*100000000000000^4031 ≤ 41135199773293^4031*2500000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1231127489 2500000000 41135199773293 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5055/1024 : ℝ)) 5055 4031 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-716540837/5000000000 : ℝ), (5764401747/10000000000 : ℝ), (1231127489/2500000000 : ℝ)] ![(4374288198369/50000000000000 : ℝ), (6264527976787/12500000000000 : ℝ), (41135199773293/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-716540837/5000000000 : ℝ)|^5055 ≤ (4374288198369/50000000000000 : ℝ)^4031
        have hw : |(-716540837/5000000000 : ℝ)|=(716540837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5764401747/10000000000 : ℝ)|^5055 ≤ (6264527976787/12500000000000 : ℝ)^4031
        have hw : |(5764401747/10000000000 : ℝ)|=(5764401747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1231127489/2500000000 : ℝ)|^5055 ≤ (41135199773293/100000000000000 : ℝ)^4031
        have hw : |(1231127489/2500000000 : ℝ)|=(1231127489/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1679_s0_1 (p : ℝ) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (339173557/625000000 : ℝ)*x 0 + (-118303769/625000000 : ℝ)*x 1 + (492451087/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (339173557/625000000 : ℝ)^5055 ≤ (23231504460089/50000000000000 : ℝ)^4031 := by
    have hnat : (339173557 : ℕ)^5055*50000000000000^4031 ≤ 23231504460089^4031*625000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339173557 625000000 23231504460089 50000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (118303769/625000000 : ℝ)^5055 ≤ (620089085779/5000000000000 : ℝ)^4031 := by
    have hnat : (118303769 : ℕ)^5055*5000000000000^4031 ≤ 620089085779^4031*625000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      118303769 625000000 620089085779 5000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (492451087/1000000000 : ℝ)^5055 ≤ (41135209347551/100000000000000 : ℝ)^4031 := by
    have hnat : (492451087 : ℕ)^5055*100000000000000^4031 ≤ 41135209347551^4031*1000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      492451087 1000000000 41135209347551 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5055/1024 : ℝ)) 5055 4031 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(339173557/625000000 : ℝ), (-118303769/625000000 : ℝ), (492451087/1000000000 : ℝ)] ![(23231504460089/50000000000000 : ℝ), (620089085779/5000000000000 : ℝ), (41135209347551/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(339173557/625000000 : ℝ)|^5055 ≤ (23231504460089/50000000000000 : ℝ)^4031
        have hw : |(339173557/625000000 : ℝ)|=(339173557/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-118303769/625000000 : ℝ)|^5055 ≤ (620089085779/5000000000000 : ℝ)^4031
        have hw : |(-118303769/625000000 : ℝ)|=(118303769/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(492451087/1000000000 : ℝ)|^5055 ≤ (41135209347551/100000000000000 : ℝ)^4031
        have hw : |(492451087/1000000000 : ℝ)|=(492451087/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1679_s0_2 (p : ℝ) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5426778403/10000000000 : ℝ)*x 0 + (4924509893/10000000000 : ℝ)*x 1 + (-946429801/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5426778403/10000000000 : ℝ)^5055 ≤ (23231512464353/50000000000000 : ℝ)^4031 := by
    have hnat : (5426778403 : ℕ)^5055*50000000000000^4031 ≤ 23231512464353^4031*10000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426778403 10000000000 23231512464353 50000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4924509893/10000000000 : ℝ)^5055 ≤ (514189988917/1250000000000 : ℝ)^4031 := by
    have hnat : (4924509893 : ℕ)^5055*1250000000000^4031 ≤ 514189988917^4031*10000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4924509893 10000000000 514189988917 1250000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (946429801/5000000000 : ℝ)^5055 ≤ (12401775947769/100000000000000 : ℝ)^4031 := by
    have hnat : (946429801 : ℕ)^5055*100000000000000^4031 ≤ 12401775947769^4031*5000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      946429801 5000000000 12401775947769 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5055/1024 : ℝ)) 5055 4031 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5426778403/10000000000 : ℝ), (4924509893/10000000000 : ℝ), (-946429801/5000000000 : ℝ)] ![(23231512464353/50000000000000 : ℝ), (514189988917/1250000000000 : ℝ), (12401775947769/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5426778403/10000000000 : ℝ)|^5055 ≤ (23231512464353/50000000000000 : ℝ)^4031
        have hw : |(5426778403/10000000000 : ℝ)|=(5426778403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4924509893/10000000000 : ℝ)|^5055 ≤ (514189988917/1250000000000 : ℝ)^4031
        have hw : |(4924509893/10000000000 : ℝ)|=(4924509893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-946429801/5000000000 : ℝ)|^5055 ≤ (12401775947769/100000000000000 : ℝ)^4031
        have hw : |(-946429801/5000000000 : ℝ)|=(946429801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1679_s0_3 (p : ℝ) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1016574583/2500000000 : ℝ)*x 0 + (152092783/500000000 : ℝ)*x 1 + (530545103/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1016574583/2500000000 : ℝ)^5055 ≤ (6470735159949/20000000000000 : ℝ)^4031 := by
    have hnat : (1016574583 : ℕ)^5055*20000000000000^4031 ≤ 6470735159949^4031*2500000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1016574583 2500000000 6470735159949 20000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (152092783/500000000 : ℝ)^5055 ≤ (22482243717353/100000000000000 : ℝ)^4031 := by
    have hnat : (152092783 : ℕ)^5055*100000000000000^4031 ≤ 22482243717353^4031*500000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      152092783 500000000 22482243717353 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (530545103/1000000000 : ℝ)^5055 ≤ (451640804723/1000000000000 : ℝ)^4031 := by
    have hnat : (530545103 : ℕ)^5055*1000000000000^4031 ≤ 451640804723^4031*1000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530545103 1000000000 451640804723 1000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5055/1024 : ℝ)) 5055 4031 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1016574583/2500000000 : ℝ), (152092783/500000000 : ℝ), (530545103/1000000000 : ℝ)] ![(6470735159949/20000000000000 : ℝ), (22482243717353/100000000000000 : ℝ), (451640804723/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1016574583/2500000000 : ℝ)|^5055 ≤ (6470735159949/20000000000000 : ℝ)^4031
        have hw : |(1016574583/2500000000 : ℝ)|=(1016574583/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(152092783/500000000 : ℝ)|^5055 ≤ (22482243717353/100000000000000 : ℝ)^4031
        have hw : |(152092783/500000000 : ℝ)|=(152092783/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(530545103/1000000000 : ℝ)|^5055 ≤ (451640804723/1000000000000 : ℝ)^4031
        have hw : |(530545103/1000000000 : ℝ)|=(530545103/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1679_s0_4 (p : ℝ) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1435307991/10000000000 : ℝ)*x 0 + (1236456453/2500000000 : ℝ)*x 1 + (717792029/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1435307991/10000000000 : ℝ)^5055 ≤ (8765623377243/100000000000000 : ℝ)^4031 := by
    have hnat : (1435307991 : ℕ)^5055*100000000000000^4031 ≤ 8765623377243^4031*10000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1435307991 10000000000 8765623377243 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1236456453/2500000000 : ℝ)^5055 ≤ (5169826065453/12500000000000 : ℝ)^4031 := by
    have hnat : (1236456453 : ℕ)^5055*12500000000000^4031 ≤ 5169826065453^4031*2500000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1236456453 2500000000 5169826065453 12500000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (717792029/1250000000 : ℝ)^5055 ≤ (24937884044779/50000000000000 : ℝ)^4031 := by
    have hnat : (717792029 : ℕ)^5055*50000000000000^4031 ≤ 24937884044779^4031*1250000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      717792029 1250000000 24937884044779 50000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5055/1024 : ℝ)) 5055 4031 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1435307991/10000000000 : ℝ), (1236456453/2500000000 : ℝ), (717792029/1250000000 : ℝ)] ![(8765623377243/100000000000000 : ℝ), (5169826065453/12500000000000 : ℝ), (24937884044779/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1435307991/10000000000 : ℝ)|^5055 ≤ (8765623377243/100000000000000 : ℝ)^4031
        have hw : |(-1435307991/10000000000 : ℝ)|=(1435307991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1236456453/2500000000 : ℝ)|^5055 ≤ (5169826065453/12500000000000 : ℝ)^4031
        have hw : |(1236456453/2500000000 : ℝ)|=(1236456453/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(717792029/1250000000 : ℝ)|^5055 ≤ (24937884044779/50000000000000 : ℝ)^4031
        have hw : |(717792029/1250000000 : ℝ)|=(717792029/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1679_s0_5 (p : ℝ) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5198345377/10000000000 : ℝ)*x 0 + (-537517711/5000000000 : ℝ)*x 1 + (71779167/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5198345377/10000000000 : ℝ)^5055 ≤ (44023644449801/100000000000000 : ℝ)^4031 := by
    have hnat : (5198345377 : ℕ)^5055*100000000000000^4031 ≤ 44023644449801^4031*10000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5198345377 10000000000 44023644449801 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (537517711/5000000000 : ℝ)^5055 ≤ (6100618725621/100000000000000 : ℝ)^4031 := by
    have hnat : (537517711 : ℕ)^5055*100000000000000^4031 ≤ 6100618725621^4031*5000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537517711 5000000000 6100618725621 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (71779167/125000000 : ℝ)^5055 ≤ (49875736807613/100000000000000 : ℝ)^4031 := by
    have hnat : (71779167 : ℕ)^5055*100000000000000^4031 ≤ 49875736807613^4031*125000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71779167 125000000 49875736807613 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5055/1024 : ℝ)) 5055 4031 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5198345377/10000000000 : ℝ), (-537517711/5000000000 : ℝ), (71779167/125000000 : ℝ)] ![(44023644449801/100000000000000 : ℝ), (6100618725621/100000000000000 : ℝ), (49875736807613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5198345377/10000000000 : ℝ)|^5055 ≤ (44023644449801/100000000000000 : ℝ)^4031
        have hw : |(5198345377/10000000000 : ℝ)|=(5198345377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-537517711/5000000000 : ℝ)|^5055 ≤ (6100618725621/100000000000000 : ℝ)^4031
        have hw : |(-537517711/5000000000 : ℝ)|=(537517711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(71779167/125000000 : ℝ)|^5055 ≤ (49875736807613/100000000000000 : ℝ)^4031
        have hw : |(71779167/125000000 : ℝ)|=(71779167/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1679_s0_6 (p : ℝ) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (519834543/1000000000 : ℝ)*x 0 + (5742331983/10000000000 : ℝ)*x 1 + (-21500749/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (519834543/1000000000 : ℝ)^5055 ≤ (44023645012667/100000000000000 : ℝ)^4031 := by
    have hnat : (519834543 : ℕ)^5055*100000000000000^4031 ≤ 44023645012667^4031*1000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519834543 1000000000 44023645012667 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5742331983/10000000000 : ℝ)^5055 ≤ (49875721809273/100000000000000 : ℝ)^4031 := by
    have hnat : (5742331983 : ℕ)^5055*100000000000000^4031 ≤ 49875721809273^4031*10000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5742331983 10000000000 49875721809273 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21500749/200000000 : ℝ)^5055 ≤ (3050316578827/50000000000000 : ℝ)^4031 := by
    have hnat : (21500749 : ℕ)^5055*50000000000000^4031 ≤ 3050316578827^4031*200000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21500749 200000000 3050316578827 50000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5055/1024 : ℝ)) 5055 4031 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(519834543/1000000000 : ℝ), (5742331983/10000000000 : ℝ), (-21500749/200000000 : ℝ)] ![(44023645012667/100000000000000 : ℝ), (49875721809273/100000000000000 : ℝ), (3050316578827/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(519834543/1000000000 : ℝ)|^5055 ≤ (44023645012667/100000000000000 : ℝ)^4031
        have hw : |(519834543/1000000000 : ℝ)|=(519834543/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5742331983/10000000000 : ℝ)|^5055 ≤ (49875721809273/100000000000000 : ℝ)^4031
        have hw : |(5742331983/10000000000 : ℝ)|=(5742331983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-21500749/200000000 : ℝ)|^5055 ≤ (3050316578827/50000000000000 : ℝ)^4031
        have hw : |(-21500749/200000000 : ℝ)|=(21500749/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1679_s0_7 (p : ℝ) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1018074509/2500000000 : ℝ)*x 0 + (2624000639/5000000000 : ℝ)*x 1 + (1550663461/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1018074509/2500000000 : ℝ)^5055 ≤ (4051693822459/12500000000000 : ℝ)^4031 := by
    have hnat : (1018074509 : ℕ)^5055*12500000000000^4031 ≤ 4051693822459^4031*2500000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1018074509 2500000000 4051693822459 12500000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2624000639/5000000000 : ℝ)^5055 ≤ (22275817073943/50000000000000 : ℝ)^4031 := by
    have hnat : (2624000639 : ℕ)^5055*50000000000000^4031 ≤ 22275817073943^4031*5000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2624000639 5000000000 22275817073943 50000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1550663461/5000000000 : ℝ)^5055 ≤ (11517407631527/50000000000000 : ℝ)^4031 := by
    have hnat : (1550663461 : ℕ)^5055*50000000000000^4031 ≤ 11517407631527^4031*5000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1550663461 5000000000 11517407631527 50000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5055/1024 : ℝ)) 5055 4031 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1018074509/2500000000 : ℝ), (2624000639/5000000000 : ℝ), (1550663461/5000000000 : ℝ)] ![(4051693822459/12500000000000 : ℝ), (22275817073943/50000000000000 : ℝ), (11517407631527/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1018074509/2500000000 : ℝ)|^5055 ≤ (4051693822459/12500000000000 : ℝ)^4031
        have hw : |(1018074509/2500000000 : ℝ)|=(1018074509/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2624000639/5000000000 : ℝ)|^5055 ≤ (22275817073943/50000000000000 : ℝ)^4031
        have hw : |(2624000639/5000000000 : ℝ)|=(2624000639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1550663461/5000000000 : ℝ)|^5055 ≤ (11517407631527/50000000000000 : ℝ)^4031
        have hw : |(1550663461/5000000000 : ℝ)|=(1550663461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1679_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (184755181/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (2529/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (11533/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (5047/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5047 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5047*1^1024 ≤ 0^1024*1^5047 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5047 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5047 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5047/1024 : ℝ) ≤ (1093122231204603507/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5047 ≤ (1093122231204603507/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5047*100000000000000000000^1024 ≤ 1093122231204603507^1024*5^5047 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1093122231204603507 100000000000000000000 5047 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1093122231204603507/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5047 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5047/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5047 := by
      have hnat : (1 : ℕ)^1024*1^5047 ≤ 1^5047*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5047 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5047 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101093122231204603507/100000000000000000000 : ℝ) ≤ (501104133324157/500000000000000 : ℝ) ^ (5047/1024 : ℝ) := by
    have hpowers : (101093122231204603507/100000000000000000000 : ℝ)^1024 ≤ (501104133324157/500000000000000 : ℝ)^5047 := by
      have hnat : (101093122231204603507 : ℕ)^1024*500000000000000^5047 ≤ 501104133324157^5047*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101093122231204603507 100000000000000000000 501104133324157 500000000000000 1024 5047 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (501104133324157/500000000000000 : ℝ)) (X := (101093122231204603507/100000000000000000000 : ℝ)) (by norm_num) 5047 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51093122231204603507/50000000000000000000 : ℝ) ≤ (251104133324157/250000000000000 : ℝ) ^ (5047/1024 : ℝ) := by
    have hpowers : (51093122231204603507/50000000000000000000 : ℝ)^1024 ≤ (251104133324157/250000000000000 : ℝ)^5047 := by
      have hnat : (51093122231204603507 : ℕ)^1024*250000000000000^5047 ≤ 251104133324157^5047*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51093122231204603507 50000000000000000000 251104133324157 250000000000000 1024 5047 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (251104133324157/250000000000000 : ℝ)) (X := (51093122231204603507/50000000000000000000 : ℝ)) (by norm_num) 5047 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(1104133324157/200000000000000 : ℝ)*(0 : ℝ))^(5047/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(1104133324157/200000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1093122231204603507/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(1104133324157/200000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5047/1024 : ℝ) := by
    rw [show (1 : ℝ)+(1104133324157/200000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(501104133324157/500000000000000 : ℝ) by norm_num, show 1+(1093122231204603507/100000000000000000000 : ℝ)+(0 : ℝ)=(101093122231204603507/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1093122231204603507/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(1104133324157/200000000000000 : ℝ)*(2/5 : ℝ))^(5047/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(1104133324157/200000000000000 : ℝ)*(2/5 : ℝ)=(251104133324157/250000000000000 : ℝ) by norm_num, show 1+2*(1093122231204603507/100000000000000000000 : ℝ)=(51093122231204603507/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(1104133324157/200000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5047/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1104133324157/200000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(1104133324157/200000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5047/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1104133324157/200000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(1104133324157/200000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5047/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1104133324157/200000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-716540837/5000000000 : ℝ)*X 0 0+(5764401747/10000000000 : ℝ)*X 0 1+(1231127489/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1679_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((339173557/625000000 : ℝ)*X 1 0+(-118303769/625000000 : ℝ)*X 1 1+(492451087/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1679_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5426778403/10000000000 : ℝ)*X 2 0+(4924509893/10000000000 : ℝ)*X 2 1+(-946429801/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1679_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1016574583/2500000000 : ℝ)*X 0 0+(152092783/500000000 : ℝ)*X 0 1+(530545103/1000000000 : ℝ)*X 0 2+(1016574583/2500000000 : ℝ)*X 1 0+(152092783/500000000 : ℝ)*X 1 1+(530545103/1000000000 : ℝ)*X 1 2+(1016574583/2500000000 : ℝ)*X 2 0+(152092783/500000000 : ℝ)*X 2 1+(530545103/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1679_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1435307991/10000000000 : ℝ)*X 0 0+(1236456453/2500000000 : ℝ)*X 0 1+(717792029/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1679_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5198345377/10000000000 : ℝ)*X 1 0+(-537517711/5000000000 : ℝ)*X 1 1+(71779167/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1679_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((519834543/1000000000 : ℝ)*X 2 0+(5742331983/10000000000 : ℝ)*X 2 1+(-21500749/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1679_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1018074509/2500000000 : ℝ)*X 0 0+(2624000639/5000000000 : ℝ)*X 0 1+(1550663461/5000000000 : ℝ)*X 0 2+(1018074509/2500000000 : ℝ)*X 1 0+(2624000639/5000000000 : ℝ)*X 1 1+(1550663461/5000000000 : ℝ)*X 1 2+(1018074509/2500000000 : ℝ)*X 2 0+(2624000639/5000000000 : ℝ)*X 2 1+(1550663461/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1679_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16343744790406559038227/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (42825079/50000000000000 : ℝ)*(base1) + (1162984911/100000000000000 : ℝ)*(base19) + (1482199059/100000000000000 : ℝ)*(base23) + (316513/4000000000000 : ℝ)*(base24) + (1494877/500000000000 : ℝ)*(upper5) + (408105517321663/50000000000000 : ℝ)*(major0) + (408105517321663/50000000000000 : ℝ)*(major1) + (408105517321663/50000000000000 : ℝ)*(major2) + (1190634123189131/100000000000000 : ℝ)*(sp0) + (595320453520617/50000000000000 : ℝ)*(sp1) + (595320289957131/50000000000000 : ℝ)*(sp2) + (441777686772289/100000000000000 : ℝ)*(sp3) + (2008121793/25000000000000 : ℝ)*(sp4) + (2008921453/100000000000000 : ℝ)*(sp7) + (441779781343899/100000000000000 : ℝ)*(f.failure) + (238128414005229/20000000000000 : ℝ)*(f.sum) + (5618440236909/5000000000000000000000000000 : ℝ)*base66 + (10354435363091/10000000000000000000000000000 : ℝ)*base67 + (66370922553091/10000000000000000000000000000 : ℝ)*base69 + (63332840673091/10000000000000000000000000000 : ℝ)*base71 + (26296620376909/5000000000000000000000000000 : ℝ)*base74 + (71971828153091/10000000000000000000000000000 : ℝ)*base75 + (6231898893091/10000000000000000000000000000 : ℝ)*base77 + (5089450913091/10000000000000000000000000000 : ℝ)*base79 + (3615009253091/5000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (117009281/10000000000000000000000 : ℝ)*base90 + (117009281/10000000000000000000000 : ℝ)*base92 + (117009281/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3922112599496157419529/1000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (299991/25000000000 : ℝ)*(base19) + (219086013/20000000000000 : ℝ)*(base23) + (7073407/50000000000000 : ℝ)*(base32) + (23924063/100000000000000 : ℝ)*(base37) + (38745477/50000000000000 : ℝ)*(upper3) + (172131622197001/20000000000000 : ℝ)*(major0) + (172131622197001/20000000000000 : ℝ)*(major1) + (172131622197001/20000000000000 : ℝ)*(major2) + (222433839/12500000000000 : ℝ)*(sp0) + (2670138467/100000000000000 : ℝ)*(sp1) + (313869311909873/25000000000000 : ℝ)*(sp4) + (1255475157007737/100000000000000 : ℝ)*(sp5) + (62773896584007/5000000000000 : ℝ)*(sp6) + (116459256512959/25000000000000 : ℝ)*(sp7) + (465837064122713/100000000000000 : ℝ)*(f.failure) + (313869756777551/25000000000000 : ℝ)*(f.sum) + (2508917018843/2000000000000000000000000000 : ℝ)*base66 + (10703455149157/4000000000000000000000000000 : ℝ)*base67 + (17983999821157/4000000000000000000000000000 : ℝ)*base69 + (7870246857157/4000000000000000000000000000 : ℝ)*base71 + (658701401157/2000000000000000000000000000 : ℝ)*base73 + (9744960645157/4000000000000000000000000000 : ℝ)*base75 + (10709370930843/4000000000000000000000000000 : ℝ)*base78 + (30319009858843/4000000000000000000000000000 : ℝ)*base80 + (6695474669157/2000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (53473947/10000000000000000000000 : ℝ)*base90 + (53473947/10000000000000000000000 : ℝ)*base92 + (53473947/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1679_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (184755181/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2529/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (11533/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1679_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1679_s1_0 (p : ℝ) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1525374969/10000000000 : ℝ)*x 0 + (5518798897/10000000000 : ℝ)*x 1 + (2554933481/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1525374969/10000000000 : ℝ)^5055 ≤ (378432774051/4000000000000 : ℝ)^4031 := by
    have hnat : (1525374969 : ℕ)^5055*4000000000000^4031 ≤ 378432774051^4031*10000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1525374969 10000000000 378432774051 4000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5518798897/10000000000 : ℝ)^5055 ≤ (47453147072661/100000000000000 : ℝ)^4031 := by
    have hnat : (5518798897 : ℕ)^5055*100000000000000^4031 ≤ 47453147072661^4031*10000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5518798897 10000000000 47453147072661 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2554933481/5000000000 : ℝ)^5055 ≤ (43086033562967/100000000000000 : ℝ)^4031 := by
    have hnat : (2554933481 : ℕ)^5055*100000000000000^4031 ≤ 43086033562967^4031*5000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2554933481 5000000000 43086033562967 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5055/1024 : ℝ)) 5055 4031 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1525374969/10000000000 : ℝ), (5518798897/10000000000 : ℝ), (2554933481/5000000000 : ℝ)] ![(378432774051/4000000000000 : ℝ), (47453147072661/100000000000000 : ℝ), (43086033562967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1525374969/10000000000 : ℝ)|^5055 ≤ (378432774051/4000000000000 : ℝ)^4031
        have hw : |(-1525374969/10000000000 : ℝ)|=(1525374969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5518798897/10000000000 : ℝ)|^5055 ≤ (47453147072661/100000000000000 : ℝ)^4031
        have hw : |(5518798897/10000000000 : ℝ)|=(5518798897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2554933481/5000000000 : ℝ)|^5055 ≤ (43086033562967/100000000000000 : ℝ)^4031
        have hw : |(2554933481/5000000000 : ℝ)|=(2554933481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1679_s1_1 (p : ℝ) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (42890703/80000000 : ℝ)*x 0 + (-869595209/5000000000 : ℝ)*x 1 + (2554933451/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42890703/80000000 : ℝ)^5055 ≤ (9152296855889/20000000000000 : ℝ)^4031 := by
    have hnat : (42890703 : ℕ)^5055*20000000000000^4031 ≤ 9152296855889^4031*80000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42890703 80000000 9152296855889 20000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (869595209/5000000000 : ℝ)^5055 ≤ (11152482771767/100000000000000 : ℝ)^4031 := by
    have hnat : (869595209 : ℕ)^5055*100000000000000^4031 ≤ 11152482771767^4031*5000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      869595209 5000000000 11152482771767 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2554933451/5000000000 : ℝ)^5055 ≤ (43086032928533/100000000000000 : ℝ)^4031 := by
    have hnat : (2554933451 : ℕ)^5055*100000000000000^4031 ≤ 43086032928533^4031*5000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2554933451 5000000000 43086032928533 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5055/1024 : ℝ)) 5055 4031 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42890703/80000000 : ℝ), (-869595209/5000000000 : ℝ), (2554933451/5000000000 : ℝ)] ![(9152296855889/20000000000000 : ℝ), (11152482771767/100000000000000 : ℝ), (43086032928533/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42890703/80000000 : ℝ)|^5055 ≤ (9152296855889/20000000000000 : ℝ)^4031
        have hw : |(42890703/80000000 : ℝ)|=(42890703/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-869595209/5000000000 : ℝ)|^5055 ≤ (11152482771767/100000000000000 : ℝ)^4031
        have hw : |(-869595209/5000000000 : ℝ)|=(869595209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2554933451/5000000000 : ℝ)|^5055 ≤ (43086032928533/100000000000000 : ℝ)^4031
        have hw : |(2554933451/5000000000 : ℝ)|=(2554933451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1679_s1_2 (p : ℝ) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1072267479/2000000000 : ℝ)*x 0 + (5109867353/10000000000 : ℝ)*x 1 + (-347838093/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072267479/2000000000 : ℝ)^5055 ≤ (45761479141653/100000000000000 : ℝ)^4031 := by
    have hnat : (1072267479 : ℕ)^5055*100000000000000^4031 ≤ 45761479141653^4031*2000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072267479 2000000000 45761479141653 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5109867353/10000000000 : ℝ)^5055 ≤ (43086037697363/100000000000000 : ℝ)^4031 := by
    have hnat : (5109867353 : ℕ)^5055*100000000000000^4031 ≤ 43086037697363^4031*10000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5109867353 10000000000 43086037697363 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (347838093/2000000000 : ℝ)^5055 ≤ (5576241574857/50000000000000 : ℝ)^4031 := by
    have hnat : (347838093 : ℕ)^5055*50000000000000^4031 ≤ 5576241574857^4031*2000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      347838093 2000000000 5576241574857 50000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5055/1024 : ℝ)) 5055 4031 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072267479/2000000000 : ℝ), (5109867353/10000000000 : ℝ), (-347838093/2000000000 : ℝ)] ![(45761479141653/100000000000000 : ℝ), (43086037697363/100000000000000 : ℝ), (5576241574857/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072267479/2000000000 : ℝ)|^5055 ≤ (45761479141653/100000000000000 : ℝ)^4031
        have hw : |(1072267479/2000000000 : ℝ)|=(1072267479/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5109867353/10000000000 : ℝ)|^5055 ≤ (43086037697363/100000000000000 : ℝ)^4031
        have hw : |(5109867353/10000000000 : ℝ)|=(5109867353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-347838093/2000000000 : ℝ)|^5055 ≤ (5576241574857/50000000000000 : ℝ)^4031
        have hw : |(-347838093/2000000000 : ℝ)|=(347838093/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1679_s1_3 (p : ℝ) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2070597997/5000000000 : ℝ)*x 0 + (3615338147/10000000000 : ℝ)*x 1 + (4717451701/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2070597997/5000000000 : ℝ)^5055 ≤ (16551363289941/50000000000000 : ℝ)^4031 := by
    have hnat : (2070597997 : ℕ)^5055*50000000000000^4031 ≤ 16551363289941^4031*5000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2070597997 5000000000 16551363289941 50000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3615338147/10000000000 : ℝ)^5055 ≤ (27919326589639/100000000000000 : ℝ)^4031 := by
    have hnat : (3615338147 : ℕ)^5055*100000000000000^4031 ≤ 27919326589639^4031*10000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3615338147 10000000000 27919326589639 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4717451701/10000000000 : ℝ)^5055 ≤ (38977946814031/100000000000000 : ℝ)^4031 := by
    have hnat : (4717451701 : ℕ)^5055*100000000000000^4031 ≤ 38977946814031^4031*10000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4717451701 10000000000 38977946814031 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5055/1024 : ℝ)) 5055 4031 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2070597997/5000000000 : ℝ), (3615338147/10000000000 : ℝ), (4717451701/10000000000 : ℝ)] ![(16551363289941/50000000000000 : ℝ), (27919326589639/100000000000000 : ℝ), (38977946814031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2070597997/5000000000 : ℝ)|^5055 ≤ (16551363289941/50000000000000 : ℝ)^4031
        have hw : |(2070597997/5000000000 : ℝ)|=(2070597997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3615338147/10000000000 : ℝ)|^5055 ≤ (27919326589639/100000000000000 : ℝ)^4031
        have hw : |(3615338147/10000000000 : ℝ)|=(3615338147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4717451701/10000000000 : ℝ)|^5055 ≤ (38977946814031/100000000000000 : ℝ)^4031
        have hw : |(4717451701/10000000000 : ℝ)|=(4717451701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1679_s1_4 (p : ℝ) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-95351777/625000000 : ℝ)*x 0 + (5114901049/10000000000 : ℝ)*x 1 + (5513678251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (95351777/625000000 : ℝ)^5055 ≤ (9462790794311/100000000000000 : ℝ)^4031 := by
    have hnat : (95351777 : ℕ)^5055*100000000000000^4031 ≤ 9462790794311^4031*625000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      95351777 625000000 9462790794311 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5114901049/10000000000 : ℝ)^5055 ≤ (43139270165067/100000000000000 : ℝ)^4031 := by
    have hnat : (5114901049 : ℕ)^5055*100000000000000^4031 ≤ 43139270165067^4031*10000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5114901049 10000000000 43139270165067 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5513678251/10000000000 : ℝ)^5055 ≤ (5924742378451/12500000000000 : ℝ)^4031 := by
    have hnat : (5513678251 : ℕ)^5055*12500000000000^4031 ≤ 5924742378451^4031*10000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5513678251 10000000000 5924742378451 12500000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5055/1024 : ℝ)) 5055 4031 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-95351777/625000000 : ℝ), (5114901049/10000000000 : ℝ), (5513678251/10000000000 : ℝ)] ![(9462790794311/100000000000000 : ℝ), (43139270165067/100000000000000 : ℝ), (5924742378451/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-95351777/625000000 : ℝ)|^5055 ≤ (9462790794311/100000000000000 : ℝ)^4031
        have hw : |(-95351777/625000000 : ℝ)|=(95351777/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5114901049/10000000000 : ℝ)|^5055 ≤ (43139270165067/100000000000000 : ℝ)^4031
        have hw : |(5114901049/10000000000 : ℝ)|=(5114901049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5513678251/10000000000 : ℝ)|^5055 ≤ (5924742378451/12500000000000 : ℝ)^4031
        have hw : |(5513678251/10000000000 : ℝ)|=(5513678251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1679_s1_5 (p : ℝ) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5252059433/10000000000 : ℝ)*x 0 + (-333845107/2500000000 : ℝ)*x 1 + (1102735797/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5252059433/10000000000 : ℝ)^5055 ≤ (22297420336733/50000000000000 : ℝ)^4031 := by
    have hnat : (5252059433 : ℕ)^5055*50000000000000^4031 ≤ 22297420336733^4031*10000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252059433 10000000000 22297420336733 50000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (333845107/2500000000 : ℝ)^5055 ≤ (320288494523/4000000000000 : ℝ)^4031 := by
    have hnat : (333845107 : ℕ)^5055*4000000000000^4031 ≤ 320288494523^4031*2500000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      333845107 2500000000 320288494523 4000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1102735797/2000000000 : ℝ)^5055 ≤ (47397946940267/100000000000000 : ℝ)^4031 := by
    have hnat : (1102735797 : ℕ)^5055*100000000000000^4031 ≤ 47397946940267^4031*2000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102735797 2000000000 47397946940267 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5055/1024 : ℝ)) 5055 4031 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5252059433/10000000000 : ℝ), (-333845107/2500000000 : ℝ), (1102735797/2000000000 : ℝ)] ![(22297420336733/50000000000000 : ℝ), (320288494523/4000000000000 : ℝ), (47397946940267/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5252059433/10000000000 : ℝ)|^5055 ≤ (22297420336733/50000000000000 : ℝ)^4031
        have hw : |(5252059433/10000000000 : ℝ)|=(5252059433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-333845107/2500000000 : ℝ)|^5055 ≤ (320288494523/4000000000000 : ℝ)^4031
        have hw : |(-333845107/2500000000 : ℝ)|=(333845107/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1102735797/2000000000 : ℝ)|^5055 ≤ (47397946940267/100000000000000 : ℝ)^4031
        have hw : |(1102735797/2000000000 : ℝ)|=(1102735797/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1679_s1_6 (p : ℝ) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1313015049/2500000000 : ℝ)*x 0 + (2756839377/5000000000 : ℝ)*x 1 + (-1335379679/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1313015049/2500000000 : ℝ)^5055 ≤ (22297424398901/50000000000000 : ℝ)^4031 := by
    have hnat : (1313015049 : ℕ)^5055*50000000000000^4031 ≤ 22297424398901^4031*2500000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313015049 2500000000 22297424398901 50000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2756839377/5000000000 : ℝ)^5055 ≤ (47397944450043/100000000000000 : ℝ)^4031 := by
    have hnat : (2756839377 : ℕ)^5055*100000000000000^4031 ≤ 47397944450043^4031*5000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2756839377 5000000000 47397944450043 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1335379679/10000000000 : ℝ)^5055 ≤ (320288269241/4000000000000 : ℝ)^4031 := by
    have hnat : (1335379679 : ℕ)^5055*4000000000000^4031 ≤ 320288269241^4031*10000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1335379679 10000000000 320288269241 4000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5055/1024 : ℝ)) 5055 4031 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1313015049/2500000000 : ℝ), (2756839377/5000000000 : ℝ), (-1335379679/10000000000 : ℝ)] ![(22297424398901/50000000000000 : ℝ), (47397944450043/100000000000000 : ℝ), (320288269241/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1313015049/2500000000 : ℝ)|^5055 ≤ (22297424398901/50000000000000 : ℝ)^4031
        have hw : |(1313015049/2500000000 : ℝ)|=(1313015049/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2756839377/5000000000 : ℝ)|^5055 ≤ (47397944450043/100000000000000 : ℝ)^4031
        have hw : |(2756839377/5000000000 : ℝ)|=(2756839377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1335379679/10000000000 : ℝ)|^5055 ≤ (320288269241/4000000000000 : ℝ)^4031
        have hw : |(-1335379679/10000000000 : ℝ)|=(1335379679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1679_s1_7 (p : ℝ) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2070939181/5000000000 : ℝ)*x 0 + (4703882451/10000000000 : ℝ)*x 1 + (3629137973/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2070939181/5000000000 : ℝ)^5055 ≤ (33109566863111/100000000000000 : ℝ)^4031 := by
    have hnat : (2070939181 : ℕ)^5055*100000000000000^4031 ≤ 33109566863111^4031*5000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2070939181 5000000000 33109566863111 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4703882451/10000000000 : ℝ)^5055 ≤ (38837401331407/100000000000000 : ℝ)^4031 := by
    have hnat : (4703882451 : ℕ)^5055*100000000000000^4031 ≤ 38837401331407^4031*10000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4703882451 10000000000 38837401331407 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3629137973/10000000000 : ℝ)^5055 ≤ (5610606357587/20000000000000 : ℝ)^4031 := by
    have hnat : (3629137973 : ℕ)^5055*20000000000000^4031 ≤ 5610606357587^4031*10000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3629137973 10000000000 5610606357587 20000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5055/1024 : ℝ)) 5055 4031 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2070939181/5000000000 : ℝ), (4703882451/10000000000 : ℝ), (3629137973/10000000000 : ℝ)] ![(33109566863111/100000000000000 : ℝ), (38837401331407/100000000000000 : ℝ), (5610606357587/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2070939181/5000000000 : ℝ)|^5055 ≤ (33109566863111/100000000000000 : ℝ)^4031
        have hw : |(2070939181/5000000000 : ℝ)|=(2070939181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4703882451/10000000000 : ℝ)|^5055 ≤ (38837401331407/100000000000000 : ℝ)^4031
        have hw : |(4703882451/10000000000 : ℝ)|=(4703882451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3629137973/10000000000 : ℝ)|^5055 ≤ (5610606357587/20000000000000 : ℝ)^4031
        have hw : |(3629137973/10000000000 : ℝ)|=(3629137973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1679_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (184755181/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (11533/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2529/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1151/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8949/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (11533/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2529/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (11533/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2529/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (11533/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2529/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (11533/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2529/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (11533/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2529/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (11533/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2529/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2529/50000 : ℝ) ^ (5047/1024 : ℝ) ≤ (40953050752091/100000000000000000000 : ℝ) := by
    have hpowers : (2529/50000 : ℝ)^5047 ≤ (40953050752091/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2529 : ℕ)^5047*100000000000000000000^1024 ≤ 40953050752091^1024*50000^5047 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2529 50000 40953050752091 100000000000000000000 5047 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2529/50000 : ℝ)) (X := (40953050752091/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5047 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (11533/50000 : ℝ) ^ (5047/1024 : ℝ) ≤ (18122351743280343/25000000000000000000 : ℝ) := by
    have hpowers : (11533/50000 : ℝ)^5047 ≤ (18122351743280343/25000000000000000000 : ℝ)^1024 := by
      have hnat : (11533 : ℕ)^5047*25000000000000000000^1024 ≤ 18122351743280343^1024*50000^5047 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11533 50000 18122351743280343 25000000000000000000 5047 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11533/50000 : ℝ)) (X := (18122351743280343/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5047 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000040953050752091/50000000000000000000 : ℝ) ≤ (10000001661815347/10000000000000000 : ℝ) ^ (5047/1024 : ℝ) := by
    have hpowers : (50000040953050752091/50000000000000000000 : ℝ)^1024 ≤ (10000001661815347/10000000000000000 : ℝ)^5047 := by
      have hnat : (50000040953050752091 : ℕ)^1024*10000000000000000^5047 ≤ 10000001661815347^5047*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000040953050752091 50000000000000000000 10000001661815347 10000000000000000 1024 5047 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001661815347/10000000000000000 : ℝ)) (X := (50000040953050752091/50000000000000000000 : ℝ)) (by norm_num) 5047 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100072530360023873463/100000000000000000000 : ℝ) ≤ (1250183895453411/1250000000000000 : ℝ) ^ (5047/1024 : ℝ) := by
    have hpowers : (100072530360023873463/100000000000000000000 : ℝ)^1024 ≤ (1250183895453411/1250000000000000 : ℝ)^5047 := by
      have hnat : (100072530360023873463 : ℕ)^1024*1250000000000000^5047 ≤ 1250183895453411^5047*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100072530360023873463 100000000000000000000 1250183895453411 1250000000000000 1024 5047 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250183895453411/1250000000000000 : ℝ)) (X := (100072530360023873463/100000000000000000000 : ℝ)) (by norm_num) 5047 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12518122351743280343/12500000000000000000 : ℝ) ≤ (10002940665439229/10000000000000000 : ℝ) ^ (5047/1024 : ℝ) := by
    have hpowers : (12518122351743280343/12500000000000000000 : ℝ)^1024 ≤ (10002940665439229/10000000000000000 : ℝ)^5047 := by
      have hnat : (12518122351743280343 : ℕ)^1024*10000000000000000^5047 ≤ 10002940665439229^5047*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12518122351743280343 12500000000000000000 10002940665439229 10000000000000000 1024 5047 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002940665439229/10000000000000000 : ℝ)) (X := (12518122351743280343/12500000000000000000 : ℝ)) (by norm_num) 5047 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(40953050752091/100000000000000000000 : ℝ) ≤ ((9003258222282058681/9004000000000000000 : ℝ)+2*(1469501811941/1800800000000000 : ℝ)*(2529/50000 : ℝ))^(5047/1024 : ℝ) := by
    rw [show (9003258222282058681/9004000000000000000 : ℝ)+2*(1469501811941/1800800000000000 : ℝ)*(2529/50000 : ℝ)=(10000001661815347/10000000000000000 : ℝ) by norm_num, show 1+2*(40953050752091/100000000000000000000 : ℝ)=(50000040953050752091/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18122351743280343/25000000000000000000 : ℝ)+(40953050752091/100000000000000000000 : ℝ) ≤ ((9003258222282058681/9004000000000000000 : ℝ)+(1469501811941/1800800000000000 : ℝ)*((11533/50000 : ℝ)+(2529/50000 : ℝ)))^(5047/1024 : ℝ) := by
    rw [show (9003258222282058681/9004000000000000000 : ℝ)+(1469501811941/1800800000000000 : ℝ)*((11533/50000 : ℝ)+(2529/50000 : ℝ))=(1250183895453411/1250000000000000 : ℝ) by norm_num, show 1+(18122351743280343/25000000000000000000 : ℝ)+(40953050752091/100000000000000000000 : ℝ)=(100072530360023873463/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18122351743280343/25000000000000000000 : ℝ) ≤ ((9003258222282058681/9004000000000000000 : ℝ)+2*(1469501811941/1800800000000000 : ℝ)*(11533/50000 : ℝ))^(5047/1024 : ℝ) := by
    rw [show (9003258222282058681/9004000000000000000 : ℝ)+2*(1469501811941/1800800000000000 : ℝ)*(11533/50000 : ℝ)=(10002940665439229/10000000000000000 : ℝ) by norm_num, show 1+2*(18122351743280343/25000000000000000000 : ℝ)=(12518122351743280343/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9003258222282058681/9004000000000000000 : ℝ)*(X 1 0+X 2 0)+(1469501811941/1800800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5047/1024 : ℝ)) (lo := (2529/50000 : ℝ)) (hi := (11533/50000 : ℝ)) (c := (9003258222282058681/9004000000000000000 : ℝ)) (alpha := (1469501811941/1800800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9003258222282058681/9004000000000000000 : ℝ)*(X 0 1+X 2 1)+(1469501811941/1800800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5047/1024 : ℝ)) (lo := (2529/50000 : ℝ)) (hi := (11533/50000 : ℝ)) (c := (9003258222282058681/9004000000000000000 : ℝ)) (alpha := (1469501811941/1800800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9003258222282058681/9004000000000000000 : ℝ)*(X 0 2+X 1 2)+(1469501811941/1800800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5047/1024 : ℝ)) (lo := (2529/50000 : ℝ)) (hi := (11533/50000 : ℝ)) (c := (9003258222282058681/9004000000000000000 : ℝ)) (alpha := (1469501811941/1800800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1525374969/10000000000 : ℝ)*X 0 0+(5518798897/10000000000 : ℝ)*X 0 1+(2554933481/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1679_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((42890703/80000000 : ℝ)*X 1 0+(-869595209/5000000000 : ℝ)*X 1 1+(2554933451/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1679_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1072267479/2000000000 : ℝ)*X 2 0+(5109867353/10000000000 : ℝ)*X 2 1+(-347838093/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1679_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2070597997/5000000000 : ℝ)*X 0 0+(3615338147/10000000000 : ℝ)*X 0 1+(4717451701/10000000000 : ℝ)*X 0 2+(2070597997/5000000000 : ℝ)*X 1 0+(3615338147/10000000000 : ℝ)*X 1 1+(4717451701/10000000000 : ℝ)*X 1 2+(2070597997/5000000000 : ℝ)*X 2 0+(3615338147/10000000000 : ℝ)*X 2 1+(4717451701/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1679_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-95351777/625000000 : ℝ)*X 0 0+(5114901049/10000000000 : ℝ)*X 0 1+(5513678251/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1679_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5252059433/10000000000 : ℝ)*X 1 0+(-333845107/2500000000 : ℝ)*X 1 1+(1102735797/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1679_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1313015049/2500000000 : ℝ)*X 2 0+(2756839377/5000000000 : ℝ)*X 2 1+(-1335379679/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1679_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2070939181/5000000000 : ℝ)*X 0 0+(4703882451/10000000000 : ℝ)*X 0 1+(3629137973/10000000000 : ℝ)*X 0 2+(2070939181/5000000000 : ℝ)*X 1 0+(4703882451/10000000000 : ℝ)*X 1 1+(3629137973/10000000000 : ℝ)*X 1 2+(2070939181/5000000000 : ℝ)*X 2 0+(4703882451/10000000000 : ℝ)*X 2 1+(3629137973/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1679_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1110431534774782374340614651/450200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (40522377/12500000000000 : ℝ)*(base19) + (105088627/100000000000000 : ℝ)*(base23) + (23534843/100000000000000 : ℝ)*(upper2) + (12069799/20000000000000 : ℝ)*(upper3) + (2361739/10000000000000 : ℝ)*(upper4) + (1676374889176181/100000000000000 : ℝ)*(major0) + (1676374889176181/100000000000000 : ℝ)*(major1) + (1676374889176181/100000000000000 : ℝ)*(major2) + (97815932095261/4000000000000 : ℝ)*(sp0) + (2445400046159957/100000000000000 : ℝ)*(sp1) + (2445400265250347/100000000000000 : ℝ)*(sp2) + (45367418108223/5000000000000 : ℝ)*(sp3) + (2067957449/100000000000000 : ℝ)*(sp4) + (963631269/100000000000000 : ℝ)*(sp7) + (90734932579573/10000000000000 : ℝ)*(f.failure) + (1222700185169487/50000000000000 : ℝ)*(f.sum) + (449946745850321/90040000000000000000000000000 : ℝ)*base65 + (7988122268030082261/900400000000000000000000000000000 : ℝ)*base67 + (8749153781097682261/900400000000000000000000000000000 : ℝ)*base69 + (13019658197578882261/900400000000000000000000000000000 : ℝ)*base71 + (355883129450801/90040000000000000000000000000 : ℝ)*base73 + (12881427512811682261/900400000000000000000000000000000 : ℝ)*base75 + (5244384834702882261/900400000000000000000000000000000 : ℝ)*base77 + (7369926027704082261/900400000000000000000000000000000 : ℝ)*base79 + (578591763483641/90040000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (3482287/1000000000000000000000 : ℝ)*base90 + (3482287/1000000000000000000000 : ℝ)*base92 + (3482287/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2866793363550617656396192929/225100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1163282231/100000000000000 : ℝ)*(base19) + (874401749/50000000000000 : ℝ)*(base23) + (65412131/100000000000000 : ℝ)*(upper2) + (380072647/100000000000000 : ℝ)*(upper3) + (484628093/100000000000000 : ℝ)*(upper5) + (1719061008848897/100000000000000 : ℝ)*(major0) + (1719061008848897/100000000000000 : ℝ)*(major1) + (1719061008848897/100000000000000 : ℝ)*(major2) + (8069989929/100000000000000 : ℝ)*(sp1) + (12716263691/100000000000000 : ℝ)*(sp2) + (313458514298993/12500000000000 : ℝ)*(sp4) + (313457360139973/12500000000000 : ℝ)*(sp5) + (1253826824662377/50000000000000 : ℝ)*(sp6) + (93045347878439/10000000000000 : ℝ)*(sp7) + (93045347878439/10000000000000 : ℝ)*(f.failure) + (313458514298993/12500000000000 : ℝ)*(f.sum) + (128502767104197/90040000000000000000000000000 : ℝ)*base65 + (182188427446890143/900400000000000000000000000000000 : ℝ)*base68 + (7313135306445909857/900400000000000000000000000000000 : ℝ)*base69 + (4302646904300709857/900400000000000000000000000000000 : ℝ)*base71 + (225987832241563/90040000000000000000000000000 : ℝ)*base74 + (5281329354144309857/900400000000000000000000000000000 : ℝ)*base75 + (4641617447147909857/900400000000000000000000000000000 : ℝ)*base77 + (6126457704979909857/900400000000000000000000000000000 : ℝ)*base79 + (452084573821517/90040000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (6557541/1000000000000000000000 : ℝ)*base90 + (6557541/1000000000000000000000 : ℝ)*base92 + (6557541/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1679_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (184755181/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (11533/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2529/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1151/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8949/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1679_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1679_s2_0 (p : ℝ) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-766034993/5000000000 : ℝ)*x 0 + (5492376171/10000000000 : ℝ)*x 1 + (1026371141/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (766034993/5000000000 : ℝ)^5055 ≤ (237823032483/2500000000000 : ℝ)^4031 := by
    have hnat : (766034993 : ℕ)^5055*2500000000000^4031 ≤ 237823032483^4031*5000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      766034993 5000000000 237823032483 2500000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5492376171/10000000000 : ℝ)^5055 ≤ (47168411364383/100000000000000 : ℝ)^4031 := by
    have hnat : (5492376171 : ℕ)^5055*100000000000000^4031 ≤ 47168411364383^4031*10000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5492376171 10000000000 47168411364383 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1026371141/2000000000 : ℝ)^5055 ≤ (21659333662157/50000000000000 : ℝ)^4031 := by
    have hnat : (1026371141 : ℕ)^5055*50000000000000^4031 ≤ 21659333662157^4031*2000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026371141 2000000000 21659333662157 50000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5055/1024 : ℝ)) 5055 4031 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-766034993/5000000000 : ℝ), (5492376171/10000000000 : ℝ), (1026371141/2000000000 : ℝ)] ![(237823032483/2500000000000 : ℝ), (47168411364383/100000000000000 : ℝ), (21659333662157/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-766034993/5000000000 : ℝ)|^5055 ≤ (237823032483/2500000000000 : ℝ)^4031
        have hw : |(-766034993/5000000000 : ℝ)|=(766034993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5492376171/10000000000 : ℝ)|^5055 ≤ (47168411364383/100000000000000 : ℝ)^4031
        have hw : |(5492376171/10000000000 : ℝ)|=(5492376171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1026371141/2000000000 : ℝ)|^5055 ≤ (21659333662157/50000000000000 : ℝ)^4031
        have hw : |(1026371141/2000000000 : ℝ)|=(1026371141/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1679_s2_1 (p : ℝ) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354302193/10000000000 : ℝ)*x 0 + (-859798091/5000000000 : ℝ)*x 1 + (641481969/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354302193/10000000000 : ℝ)^5055 ≤ (45686188771137/100000000000000 : ℝ)^4031 := by
    have hnat : (5354302193 : ℕ)^5055*100000000000000^4031 ≤ 45686188771137^4031*10000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354302193 10000000000 45686188771137 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (859798091/5000000000 : ℝ)^5055 ≤ (5497571692621/50000000000000 : ℝ)^4031 := by
    have hnat : (859798091 : ℕ)^5055*50000000000000^4031 ≤ 5497571692621^4031*5000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      859798091 5000000000 5497571692621 50000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (641481969/1250000000 : ℝ)^5055 ≤ (4331866782183/10000000000000 : ℝ)^4031 := by
    have hnat : (641481969 : ℕ)^5055*10000000000000^4031 ≤ 4331866782183^4031*1250000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      641481969 1250000000 4331866782183 10000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5055/1024 : ℝ)) 5055 4031 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354302193/10000000000 : ℝ), (-859798091/5000000000 : ℝ), (641481969/1250000000 : ℝ)] ![(45686188771137/100000000000000 : ℝ), (5497571692621/50000000000000 : ℝ), (4331866782183/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354302193/10000000000 : ℝ)|^5055 ≤ (45686188771137/100000000000000 : ℝ)^4031
        have hw : |(5354302193/10000000000 : ℝ)|=(5354302193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-859798091/5000000000 : ℝ)|^5055 ≤ (5497571692621/50000000000000 : ℝ)^4031
        have hw : |(-859798091/5000000000 : ℝ)|=(859798091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(641481969/1250000000 : ℝ)|^5055 ≤ (4331866782183/10000000000000 : ℝ)^4031
        have hw : |(641481969/1250000000 : ℝ)|=(641481969/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1679_s2_2 (p : ℝ) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338575551/2500000000 : ℝ)*x 0 + (128296393/250000000 : ℝ)*x 1 + (-171959621/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338575551/2500000000 : ℝ)^5055 ≤ (45686188888839/100000000000000 : ℝ)^4031 := by
    have hnat : (1338575551 : ℕ)^5055*100000000000000^4031 ≤ 45686188888839^4031*2500000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338575551 2500000000 45686188888839 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (128296393/250000000 : ℝ)^5055 ≤ (5414833435387/12500000000000 : ℝ)^4031 := by
    have hnat : (128296393 : ℕ)^5055*12500000000000^4031 ≤ 5414833435387^4031*250000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128296393 250000000 5414833435387 12500000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (171959621/1000000000 : ℝ)^5055 ≤ (5497571804877/50000000000000 : ℝ)^4031 := by
    have hnat : (171959621 : ℕ)^5055*50000000000000^4031 ≤ 5497571804877^4031*1000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171959621 1000000000 5497571804877 50000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5055/1024 : ℝ)) 5055 4031 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338575551/2500000000 : ℝ), (128296393/250000000 : ℝ), (-171959621/1000000000 : ℝ)] ![(45686188888839/100000000000000 : ℝ), (5414833435387/12500000000000 : ℝ), (5497571804877/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338575551/2500000000 : ℝ)|^5055 ≤ (45686188888839/100000000000000 : ℝ)^4031
        have hw : |(1338575551/2500000000 : ℝ)|=(1338575551/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(128296393/250000000 : ℝ)|^5055 ≤ (5414833435387/12500000000000 : ℝ)^4031
        have hw : |(128296393/250000000 : ℝ)|=(128296393/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-171959621/1000000000 : ℝ)|^5055 ≤ (5497571804877/50000000000000 : ℝ)^4031
        have hw : |(-171959621/1000000000 : ℝ)|=(171959621/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1679_s2_3 (p : ℝ) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4146321513/10000000000 : ℝ)*x 0 + (46001053/125000000 : ℝ)*x 1 + (2325862093/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4146321513/10000000000 : ℝ)^5055 ≤ (16577056741101/50000000000000 : ℝ)^4031 := by
    have hnat : (4146321513 : ℕ)^5055*50000000000000^4031 ≤ 16577056741101^4031*10000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4146321513 10000000000 16577056741101 50000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (46001053/125000000 : ℝ)^5055 ≤ (892117549067/3125000000000 : ℝ)^4031 := by
    have hnat : (46001053 : ℕ)^5055*3125000000000^4031 ≤ 892117549067^4031*125000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46001053 125000000 892117549067 3125000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2325862093/5000000000 : ℝ)^5055 ≤ (1531924997231/4000000000000 : ℝ)^4031 := by
    have hnat : (2325862093 : ℕ)^5055*4000000000000^4031 ≤ 1531924997231^4031*5000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2325862093 5000000000 1531924997231 4000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5055/1024 : ℝ)) 5055 4031 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4146321513/10000000000 : ℝ), (46001053/125000000 : ℝ), (2325862093/5000000000 : ℝ)] ![(16577056741101/50000000000000 : ℝ), (892117549067/3125000000000 : ℝ), (1531924997231/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4146321513/10000000000 : ℝ)|^5055 ≤ (16577056741101/50000000000000 : ℝ)^4031
        have hw : |(4146321513/10000000000 : ℝ)|=(4146321513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(46001053/125000000 : ℝ)|^5055 ≤ (892117549067/3125000000000 : ℝ)^4031
        have hw : |(46001053/125000000 : ℝ)|=(46001053/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2325862093/5000000000 : ℝ)|^5055 ≤ (1531924997231/4000000000000 : ℝ)^4031
        have hw : |(2325862093/5000000000 : ℝ)|=(2325862093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1679_s2_4 (p : ℝ) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-191530399/1250000000 : ℝ)*x 0 + (2567886551/5000000000 : ℝ)*x 1 + (1372099947/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (191530399/1250000000 : ℝ)^5055 ≤ (9514269991469/100000000000000 : ℝ)^4031 := by
    have hnat : (191530399 : ℕ)^5055*100000000000000^4031 ≤ 9514269991469^4031*1250000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      191530399 1250000000 9514269991469 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2567886551/5000000000 : ℝ)^5055 ≤ (43360138724339/100000000000000 : ℝ)^4031 := by
    have hnat : (2567886551 : ℕ)^5055*100000000000000^4031 ≤ 43360138724339^4031*5000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2567886551 5000000000 43360138724339 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1372099947/2500000000 : ℝ)^5055 ≤ (47125591272007/100000000000000 : ℝ)^4031 := by
    have hnat : (1372099947 : ℕ)^5055*100000000000000^4031 ≤ 47125591272007^4031*2500000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1372099947 2500000000 47125591272007 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5055/1024 : ℝ)) 5055 4031 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-191530399/1250000000 : ℝ), (2567886551/5000000000 : ℝ), (1372099947/2500000000 : ℝ)] ![(9514269991469/100000000000000 : ℝ), (43360138724339/100000000000000 : ℝ), (47125591272007/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-191530399/1250000000 : ℝ)|^5055 ≤ (9514269991469/100000000000000 : ℝ)^4031
        have hw : |(-191530399/1250000000 : ℝ)|=(191530399/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2567886551/5000000000 : ℝ)|^5055 ≤ (43360138724339/100000000000000 : ℝ)^4031
        have hw : |(2567886551/5000000000 : ℝ)|=(2567886551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1372099947/2500000000 : ℝ)|^5055 ≤ (47125591272007/100000000000000 : ℝ)^4031
        have hw : |(1372099947/2500000000 : ℝ)|=(1372099947/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1679_s2_5 (p : ℝ) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5258044311/10000000000 : ℝ)*x 0 + (-10904417/80000000 : ℝ)*x 1 + (548839979/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5258044311/10000000000 : ℝ)^5055 ≤ (44658576186341/100000000000000 : ℝ)^4031 := by
    have hnat : (5258044311 : ℕ)^5055*100000000000000^4031 ≤ 44658576186341^4031*10000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258044311 10000000000 44658576186341 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (10904417/80000000 : ℝ)^5055 ≤ (4107916253441/50000000000000 : ℝ)^4031 := by
    have hnat : (10904417 : ℕ)^5055*50000000000000^4031 ≤ 4107916253441^4031*80000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10904417 80000000 4107916253441 50000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (548839979/1000000000 : ℝ)^5055 ≤ (23562795646771/50000000000000 : ℝ)^4031 := by
    have hnat : (548839979 : ℕ)^5055*50000000000000^4031 ≤ 23562795646771^4031*1000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548839979 1000000000 23562795646771 50000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5055/1024 : ℝ)) 5055 4031 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5258044311/10000000000 : ℝ), (-10904417/80000000 : ℝ), (548839979/1000000000 : ℝ)] ![(44658576186341/100000000000000 : ℝ), (4107916253441/50000000000000 : ℝ), (23562795646771/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5258044311/10000000000 : ℝ)|^5055 ≤ (44658576186341/100000000000000 : ℝ)^4031
        have hw : |(5258044311/10000000000 : ℝ)|=(5258044311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-10904417/80000000 : ℝ)|^5055 ≤ (4107916253441/50000000000000 : ℝ)^4031
        have hw : |(-10904417/80000000 : ℝ)|=(10904417/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(548839979/1000000000 : ℝ)|^5055 ≤ (23562795646771/50000000000000 : ℝ)^4031
        have hw : |(548839979/1000000000 : ℝ)|=(548839979/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1679_s2_6 (p : ℝ) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5258044311/10000000000 : ℝ)*x 0 + (5488399787/10000000000 : ℝ)*x 1 + (-1363052129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5258044311/10000000000 : ℝ)^5055 ≤ (44658576186341/100000000000000 : ℝ)^4031 := by
    have hnat : (5258044311 : ℕ)^5055*100000000000000^4031 ≤ 44658576186341^4031*10000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258044311 10000000000 44658576186341 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5488399787/10000000000 : ℝ)^5055 ≤ (47125591261239/100000000000000 : ℝ)^4031 := by
    have hnat : (5488399787 : ℕ)^5055*100000000000000^4031 ≤ 47125591261239^4031*10000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5488399787 10000000000 47125591261239 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1363052129/10000000000 : ℝ)^5055 ≤ (8215832537117/100000000000000 : ℝ)^4031 := by
    have hnat : (1363052129 : ℕ)^5055*100000000000000^4031 ≤ 8215832537117^4031*10000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1363052129 10000000000 8215832537117 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5055/1024 : ℝ)) 5055 4031 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5258044311/10000000000 : ℝ), (5488399787/10000000000 : ℝ), (-1363052129/10000000000 : ℝ)] ![(44658576186341/100000000000000 : ℝ), (47125591261239/100000000000000 : ℝ), (8215832537117/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5258044311/10000000000 : ℝ)|^5055 ≤ (44658576186341/100000000000000 : ℝ)^4031
        have hw : |(5258044311/10000000000 : ℝ)|=(5258044311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5488399787/10000000000 : ℝ)|^5055 ≤ (47125591261239/100000000000000 : ℝ)^4031
        have hw : |(5488399787/10000000000 : ℝ)|=(5488399787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1363052129/10000000000 : ℝ)|^5055 ≤ (8215832537117/100000000000000 : ℝ)^4031
        have hw : |(-1363052129/10000000000 : ℝ)|=(1363052129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1679_s2_7 (p : ℝ) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4146788423/10000000000 : ℝ)*x 0 + (4641166443/10000000000 : ℝ)*x 1 + (3690800983/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4146788423/10000000000 : ℝ)^5055 ≤ (33158795382849/100000000000000 : ℝ)^4031 := by
    have hnat : (4146788423 : ℕ)^5055*100000000000000^4031 ≤ 33158795382849^4031*10000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4146788423 10000000000 33158795382849 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4641166443/10000000000 : ℝ)^5055 ≤ (38189152229657/100000000000000 : ℝ)^4031 := by
    have hnat : (4641166443 : ℕ)^5055*100000000000000^4031 ≤ 38189152229657^4031*10000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4641166443 10000000000 38189152229657 100000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3690800983/10000000000 : ℝ)^5055 ≤ (2865205236321/10000000000000 : ℝ)^4031 := by
    have hnat : (3690800983 : ℕ)^5055*10000000000000^4031 ≤ 2865205236321^4031*10000000000^5055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3690800983 10000000000 2865205236321 10000000000000 5055 4031 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5055/1024 : ℝ)) 5055 4031 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4146788423/10000000000 : ℝ), (4641166443/10000000000 : ℝ), (3690800983/10000000000 : ℝ)] ![(33158795382849/100000000000000 : ℝ), (38189152229657/100000000000000 : ℝ), (2865205236321/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4146788423/10000000000 : ℝ)|^5055 ≤ (33158795382849/100000000000000 : ℝ)^4031
        have hw : |(4146788423/10000000000 : ℝ)|=(4146788423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4641166443/10000000000 : ℝ)|^5055 ≤ (38189152229657/100000000000000 : ℝ)^4031
        have hw : |(4641166443/10000000000 : ℝ)|=(4641166443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3690800983/10000000000 : ℝ)|^5055 ≤ (2865205236321/10000000000000 : ℝ)^4031
        have hw : |(3690800983/10000000000 : ℝ)|=(3690800983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1679_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (184755181/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8949/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1151/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (1937/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8673/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8949/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1151/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8949/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1151/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8949/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1151/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8949/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1151/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8949/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1151/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8949/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1151/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1151/12500 : ℝ) ^ (5047/1024 : ℝ) ≤ (784639625747797/100000000000000000000 : ℝ) := by
    have hpowers : (1151/12500 : ℝ)^5047 ≤ (784639625747797/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1151 : ℕ)^5047*100000000000000000000^1024 ≤ 784639625747797^1024*12500^5047 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1151 12500 784639625747797 100000000000000000000 5047 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1151/12500 : ℝ)) (X := (784639625747797/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5047 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8949/50000 : ℝ) ^ (5047/1024 : ℝ) ≤ (2595370704404973/12500000000000000000 : ℝ) := by
    have hpowers : (8949/50000 : ℝ)^5047 ≤ (2595370704404973/12500000000000000000 : ℝ)^1024 := by
      have hnat : (8949 : ℕ)^5047*12500000000000000000^1024 ≤ 2595370704404973^1024*50000^5047 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8949 50000 2595370704404973 12500000000000000000 5047 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8949/50000 : ℝ)) (X := (2595370704404973/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 5047 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000784639625747797/50000000000000000000 : ℝ) ≤ (1000003183934819/1000000000000000 : ℝ) ^ (5047/1024 : ℝ) := by
    have hpowers : (50000784639625747797/50000000000000000000 : ℝ)^1024 ≤ (1000003183934819/1000000000000000 : ℝ)^5047 := by
      have hnat : (50000784639625747797 : ℕ)^1024*1000000000000000^5047 ≤ 1000003183934819^5047*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000784639625747797 50000000000000000000 1000003183934819 1000000000000000 1024 5047 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000003183934819/1000000000000000 : ℝ)) (X := (50000784639625747797/50000000000000000000 : ℝ)) (by norm_num) 5047 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100021547605260987581/100000000000000000000 : ℝ) ≤ (10000437147872771/10000000000000000 : ℝ) ^ (5047/1024 : ℝ) := by
    have hpowers : (100021547605260987581/100000000000000000000 : ℝ)^1024 ≤ (10000437147872771/10000000000000000 : ℝ)^5047 := by
      have hnat : (100021547605260987581 : ℕ)^1024*10000000000000000^5047 ≤ 10000437147872771^5047*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100021547605260987581 100000000000000000000 10000437147872771 10000000000000000 1024 5047 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000437147872771/10000000000000000 : ℝ)) (X := (100021547605260987581/100000000000000000000 : ℝ)) (by norm_num) 5047 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6252595370704404973/6250000000000000000 : ℝ) ≤ (1250105307049669/1250000000000000 : ℝ) ^ (5047/1024 : ℝ) := by
    have hpowers : (6252595370704404973/6250000000000000000 : ℝ)^1024 ≤ (1250105307049669/1250000000000000 : ℝ)^5047 := by
      have hnat : (6252595370704404973 : ℕ)^1024*1250000000000000^5047 ≤ 1250105307049669^5047*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252595370704404973 6250000000000000000 1250105307049669 1250000000000000 1024 5047 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250105307049669/1250000000000000 : ℝ)) (X := (6252595370704404973/6250000000000000000 : ℝ)) (by norm_num) 5047 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(784639625747797/100000000000000000000 : ℝ) ≤ ((21723203130536771851/21725000000000000000 : ℝ)+2*(405308524581/869000000000000 : ℝ)*(1151/12500 : ℝ))^(5047/1024 : ℝ) := by
    rw [show (21723203130536771851/21725000000000000000 : ℝ)+2*(405308524581/869000000000000 : ℝ)*(1151/12500 : ℝ)=(1000003183934819/1000000000000000 : ℝ) by norm_num, show 1+2*(784639625747797/100000000000000000000 : ℝ)=(50000784639625747797/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2595370704404973/12500000000000000000 : ℝ)+(784639625747797/100000000000000000000 : ℝ) ≤ ((21723203130536771851/21725000000000000000 : ℝ)+(405308524581/869000000000000 : ℝ)*((8949/50000 : ℝ)+(1151/12500 : ℝ)))^(5047/1024 : ℝ) := by
    rw [show (21723203130536771851/21725000000000000000 : ℝ)+(405308524581/869000000000000 : ℝ)*((8949/50000 : ℝ)+(1151/12500 : ℝ))=(10000437147872771/10000000000000000 : ℝ) by norm_num, show 1+(2595370704404973/12500000000000000000 : ℝ)+(784639625747797/100000000000000000000 : ℝ)=(100021547605260987581/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2595370704404973/12500000000000000000 : ℝ) ≤ ((21723203130536771851/21725000000000000000 : ℝ)+2*(405308524581/869000000000000 : ℝ)*(8949/50000 : ℝ))^(5047/1024 : ℝ) := by
    rw [show (21723203130536771851/21725000000000000000 : ℝ)+2*(405308524581/869000000000000 : ℝ)*(8949/50000 : ℝ)=(1250105307049669/1250000000000000 : ℝ) by norm_num, show 1+2*(2595370704404973/12500000000000000000 : ℝ)=(6252595370704404973/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (21723203130536771851/21725000000000000000 : ℝ)*(X 1 0+X 2 0)+(405308524581/869000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5047/1024 : ℝ)) (lo := (1151/12500 : ℝ)) (hi := (8949/50000 : ℝ)) (c := (21723203130536771851/21725000000000000000 : ℝ)) (alpha := (405308524581/869000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (21723203130536771851/21725000000000000000 : ℝ)*(X 0 1+X 2 1)+(405308524581/869000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5047/1024 : ℝ)) (lo := (1151/12500 : ℝ)) (hi := (8949/50000 : ℝ)) (c := (21723203130536771851/21725000000000000000 : ℝ)) (alpha := (405308524581/869000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (21723203130536771851/21725000000000000000 : ℝ)*(X 0 2+X 1 2)+(405308524581/869000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5047/1024 : ℝ)) (lo := (1151/12500 : ℝ)) (hi := (8949/50000 : ℝ)) (c := (21723203130536771851/21725000000000000000 : ℝ)) (alpha := (405308524581/869000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-766034993/5000000000 : ℝ)*X 0 0+(5492376171/10000000000 : ℝ)*X 0 1+(1026371141/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1679_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5354302193/10000000000 : ℝ)*X 1 0+(-859798091/5000000000 : ℝ)*X 1 1+(641481969/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1679_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338575551/2500000000 : ℝ)*X 2 0+(128296393/250000000 : ℝ)*X 2 1+(-171959621/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1679_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4146321513/10000000000 : ℝ)*X 0 0+(46001053/125000000 : ℝ)*X 0 1+(2325862093/5000000000 : ℝ)*X 0 2+(4146321513/10000000000 : ℝ)*X 1 0+(46001053/125000000 : ℝ)*X 1 1+(2325862093/5000000000 : ℝ)*X 1 2+(4146321513/10000000000 : ℝ)*X 2 0+(46001053/125000000 : ℝ)*X 2 1+(2325862093/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1679_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-191530399/1250000000 : ℝ)*X 0 0+(2567886551/5000000000 : ℝ)*X 0 1+(1372099947/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1679_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5258044311/10000000000 : ℝ)*X 1 0+(-10904417/80000000 : ℝ)*X 1 1+(548839979/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1679_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5258044311/10000000000 : ℝ)*X 2 0+(5488399787/10000000000 : ℝ)*X 2 1+(-1363052129/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1679_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4146788423/10000000000 : ℝ)*X 0 0+(4641166443/10000000000 : ℝ)*X 0 1+(3690800983/10000000000 : ℝ)*X 0 2+(4146788423/10000000000 : ℝ)*X 1 0+(4641166443/10000000000 : ℝ)*X 1 1+(3690800983/10000000000 : ℝ)*X 1 2+(4146788423/10000000000 : ℝ)*X 2 0+(4641166443/10000000000 : ℝ)*X 2 1+(3690800983/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1679_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (230981217835861614593846607/19750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1812738023/100000000000000 : ℝ)*(base19) + (864001701/50000000000000 : ℝ)*(base23) + (48420657/100000000000000 : ℝ)*(lower2) + (146460109/50000000000000 : ℝ)*(upper3) + (52522521/25000000000000 : ℝ)*(upper5) + (380300299925909/20000000000000 : ℝ)*(major0) + (380300299925909/20000000000000 : ℝ)*(major1) + (380300299925909/20000000000000 : ℝ)*(major2) + (346723133975079/12500000000000 : ℝ)*(sp0) + (8668125499189/312500000000 : ℝ)*(sp1) + (1386900122237551/50000000000000 : ℝ)*(sp2) + (514596921958681/50000000000000 : ℝ)*(sp3) + (16900677871/100000000000000 : ℝ)*(sp4) + (6793021499/100000000000000 : ℝ)*(sp7) + (1029200636938861/100000000000000 : ℝ)*(f.failure) + (346725246559813/12500000000000 : ℝ)*(f.sum) + (2396992973471/790000000000000000000000000 : ℝ)*base66 + (361021323972226131/39500000000000000000000000000000 : ℝ)*base68 + (5568344240773869/39500000000000000000000000000000 : ℝ)*base69 + (237816422566226131/39500000000000000000000000000000 : ℝ)*base72 + (3791979854091/790000000000000000000000000 : ℝ)*base74 + (48593954186773869/39500000000000000000000000000000 : ℝ)*base75 + (438747083202226131/39500000000000000000000000000000 : ℝ)*base78 + (356609866249226131/39500000000000000000000000000000 : ℝ)*base80 + (1449947317171/790000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (49988841/10000000000000000000000 : ℝ)*base89 + (49988841/10000000000000000000000 : ℝ)*base91 + (49988841/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (194756780027337998718705381/27156250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1050003767/100000000000000 : ℝ)*(base19) + (225927401/20000000000000 : ℝ)*(base23) + (77634003/50000000000000 : ℝ)*(upper3) + (17882967/50000000000000 : ℝ)*(lower4) + (4710253/3125000000000 : ℝ)*(upper5) + (48601083830177/2500000000000 : ℝ)*(major0) + (48601083830177/2500000000000 : ℝ)*(major1) + (48601083830177/2500000000000 : ℝ)*(major2) + (1789506233/20000000000000 : ℝ)*(sp1) + (9581823551/100000000000000 : ℝ)*(sp2) + (2835859762436143/100000000000000 : ℝ)*(sp4) + (2835849764901211/100000000000000 : ℝ)*(sp5) + (708962262743897/25000000000000 : ℝ)*(sp6) + (1052226704920973/100000000000000 : ℝ)*(sp7) + (1052226704920973/100000000000000 : ℝ)*(f.failure) + (2835859762436143/100000000000000 : ℝ)*(f.sum) + (6263625626087/4345000000000000000000000000 : ℝ)*base66 + (73975405478560127/54312500000000000000000000000000 : ℝ)*base67 + (65559898342814873/54312500000000000000000000000000 : ℝ)*base70 + (344744989457689873/54312500000000000000000000000000 : ℝ)*base72 + (4241507691809/2172500000000000000000000000 : ℝ)*base73 + (829351558798810127/54312500000000000000000000000000 : ℝ)*base75 + (250826771983564873/54312500000000000000000000000000 : ℝ)*base78 + (161710206297064873/54312500000000000000000000000000 : ℝ)*base80 + (4643552289117/4345000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (42688887/10000000000000000000000 : ℝ)*base90 + (42688887/10000000000000000000000 : ℝ)*base92 + (42688887/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1679_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (184755181/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8949/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1151/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1937/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8673/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1679_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1679_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (184755181/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1937/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8673/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1679_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1679_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1679_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5047/1024 : ℝ) ≤ p) (hpb : p ≤ (5055/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (184755181/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1937/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8673/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1679_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
