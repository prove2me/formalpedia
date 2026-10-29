-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1757_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:24:22.388116+00:00
-- url     : https://prove2.me/submissions/1ecc0313-5bc6-4505-b29b-68beae3c9718

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
theorem support_rectangle_w1757_s0_0 (p : ℝ) (hpa : (5871/1024 : ℝ) ≤ p) (hpb : p ≤ (5887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-572210719/5000000000 : ℝ)*x 0 + (5609434383/10000000000 : ℝ)*x 1 + (2494029709/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (572210719/5000000000 : ℝ)^5887 ≤ (1450049409819/20000000000000 : ℝ)^4863 := by
    have hnat : (572210719 : ℕ)^5887*20000000000000^4863 ≤ 1450049409819^4863*5000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      572210719 5000000000 1450049409819 20000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5609434383/10000000000 : ℝ)^5887 ≤ (9932968437599/20000000000000 : ℝ)^4863 := by
    have hnat : (5609434383 : ℕ)^5887*20000000000000^4863 ≤ 9932968437599^4863*10000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5609434383 10000000000 9932968437599 20000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2494029709/5000000000 : ℝ)^5887 ≤ (10771227687699/25000000000000 : ℝ)^4863 := by
    have hnat : (2494029709 : ℕ)^5887*25000000000000^4863 ≤ 10771227687699^4863*5000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2494029709 5000000000 10771227687699 25000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5887/1024 : ℝ)) 5887 4863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-572210719/5000000000 : ℝ), (5609434383/10000000000 : ℝ), (2494029709/5000000000 : ℝ)] ![(1450049409819/20000000000000 : ℝ), (9932968437599/20000000000000 : ℝ), (10771227687699/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-572210719/5000000000 : ℝ)|^5887 ≤ (1450049409819/20000000000000 : ℝ)^4863
        have hw : |(-572210719/5000000000 : ℝ)|=(572210719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5609434383/10000000000 : ℝ)|^5887 ≤ (9932968437599/20000000000000 : ℝ)^4863
        have hw : |(5609434383/10000000000 : ℝ)|=(5609434383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2494029709/5000000000 : ℝ)|^5887 ≤ (10771227687699/25000000000000 : ℝ)^4863
        have hw : |(2494029709/5000000000 : ℝ)|=(2494029709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1757_s0_1 (p : ℝ) (hpa : (5871/1024 : ℝ) ≤ p) (hpb : p ≤ (5887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (10476121/19531250 : ℝ)*x 0 + (-369167903/2500000000 : ℝ)*x 1 + (4988060041/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10476121/19531250 : ℝ)^5887 ≤ (47044100530049/100000000000000 : ℝ)^4863 := by
    have hnat : (10476121 : ℕ)^5887*100000000000000^4863 ≤ 47044100530049^4863*19531250^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10476121 19531250 47044100530049 100000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (369167903/2500000000 : ℝ)^5887 ≤ (4935491097111/50000000000000 : ℝ)^4863 := by
    have hnat : (369167903 : ℕ)^5887*50000000000000^4863 ≤ 4935491097111^4863*2500000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      369167903 2500000000 4935491097111 50000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4988060041/10000000000 : ℝ)^5887 ≤ (43084917265151/100000000000000 : ℝ)^4863 := by
    have hnat : (4988060041 : ℕ)^5887*100000000000000^4863 ≤ 43084917265151^4863*10000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4988060041 10000000000 43084917265151 100000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5887/1024 : ℝ)) 5887 4863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(10476121/19531250 : ℝ), (-369167903/2500000000 : ℝ), (4988060041/10000000000 : ℝ)] ![(47044100530049/100000000000000 : ℝ), (4935491097111/50000000000000 : ℝ), (43084917265151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(10476121/19531250 : ℝ)|^5887 ≤ (47044100530049/100000000000000 : ℝ)^4863
        have hw : |(10476121/19531250 : ℝ)|=(10476121/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-369167903/2500000000 : ℝ)|^5887 ≤ (4935491097111/50000000000000 : ℝ)^4863
        have hw : |(-369167903/2500000000 : ℝ)|=(369167903/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4988060041/10000000000 : ℝ)|^5887 ≤ (43084917265151/100000000000000 : ℝ)^4863
        have hw : |(4988060041/10000000000 : ℝ)|=(4988060041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1757_s0_2 (p : ℝ) (hpa : (5871/1024 : ℝ) ≤ p) (hpb : p ≤ (5887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1340944267/2500000000 : ℝ)*x 0 + (4988058343/10000000000 : ℝ)*x 1 + (-1476669717/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1340944267/2500000000 : ℝ)^5887 ≤ (11761033403587/25000000000000 : ℝ)^4863 := by
    have hnat : (1340944267 : ℕ)^5887*25000000000000^4863 ≤ 11761033403587^4863*2500000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1340944267 2500000000 11761033403587 25000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4988058343/10000000000 : ℝ)^5887 ≤ (5385612438767/12500000000000 : ℝ)^4863 := by
    have hnat : (4988058343 : ℕ)^5887*12500000000000^4863 ≤ 5385612438767^4863*10000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4988058343 10000000000 5385612438767 12500000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1476669717/10000000000 : ℝ)^5887 ≤ (9870966859519/100000000000000 : ℝ)^4863 := by
    have hnat : (1476669717 : ℕ)^5887*100000000000000^4863 ≤ 9870966859519^4863*10000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1476669717 10000000000 9870966859519 100000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5887/1024 : ℝ)) 5887 4863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1340944267/2500000000 : ℝ), (4988058343/10000000000 : ℝ), (-1476669717/10000000000 : ℝ)] ![(11761033403587/25000000000000 : ℝ), (5385612438767/12500000000000 : ℝ), (9870966859519/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1340944267/2500000000 : ℝ)|^5887 ≤ (11761033403587/25000000000000 : ℝ)^4863
        have hw : |(1340944267/2500000000 : ℝ)|=(1340944267/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4988058343/10000000000 : ℝ)|^5887 ≤ (5385612438767/12500000000000 : ℝ)^4863
        have hw : |(4988058343/10000000000 : ℝ)|=(4988058343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1476669717/10000000000 : ℝ)|^5887 ≤ (9870966859519/100000000000000 : ℝ)^4863
        have hw : |(-1476669717/10000000000 : ℝ)|=(1476669717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1757_s0_3 (p : ℝ) (hpa : (5871/1024 : ℝ) ≤ p) (hpb : p ≤ (5887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3967312379/10000000000 : ℝ)*x 0 + (747547527/2500000000 : ℝ)*x 1 + (2545090917/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3967312379/10000000000 : ℝ)^5887 ≤ (32655169433967/100000000000000 : ℝ)^4863 := by
    have hnat : (3967312379 : ℕ)^5887*100000000000000^4863 ≤ 32655169433967^4863*10000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3967312379 10000000000 32655169433967 100000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (747547527/2500000000 : ℝ)^5887 ≤ (185518357149/800000000000 : ℝ)^4863 := by
    have hnat : (747547527 : ℕ)^5887*800000000000^4863 ≤ 185518357149^4863*2500000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      747547527 2500000000 185518357149 800000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2545090917/5000000000 : ℝ)^5887 ≤ (44155035896291/100000000000000 : ℝ)^4863 := by
    have hnat : (2545090917 : ℕ)^5887*100000000000000^4863 ≤ 44155035896291^4863*5000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2545090917 5000000000 44155035896291 100000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5887/1024 : ℝ)) 5887 4863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3967312379/10000000000 : ℝ), (747547527/2500000000 : ℝ), (2545090917/5000000000 : ℝ)] ![(32655169433967/100000000000000 : ℝ), (185518357149/800000000000 : ℝ), (44155035896291/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3967312379/10000000000 : ℝ)|^5887 ≤ (32655169433967/100000000000000 : ℝ)^4863
        have hw : |(3967312379/10000000000 : ℝ)|=(3967312379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(747547527/2500000000 : ℝ)|^5887 ≤ (185518357149/800000000000 : ℝ)^4863
        have hw : |(747547527/2500000000 : ℝ)|=(747547527/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2545090917/5000000000 : ℝ)|^5887 ≤ (44155035896291/100000000000000 : ℝ)^4863
        have hw : |(2545090917/5000000000 : ℝ)|=(2545090917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1757_s0_4 (p : ℝ) (hpa : (5871/1024 : ℝ) ≤ p) (hpb : p ≤ (5887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1145647151/10000000000 : ℝ)*x 0 + (5003714271/10000000000 : ℝ)*x 1 + (5593274697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1145647151/10000000000 : ℝ)^5887 ≤ (145192969763/2000000000000 : ℝ)^4863 := by
    have hnat : (1145647151 : ℕ)^5887*2000000000000^4863 ≤ 145192969763^4863*10000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1145647151 10000000000 145192969763 2000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5003714271/10000000000 : ℝ)^5887 ≤ (43248658637107/100000000000000 : ℝ)^4863 := by
    have hnat : (5003714271 : ℕ)^5887*100000000000000^4863 ≤ 43248658637107^4863*10000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5003714271 10000000000 43248658637107 100000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5593274697/10000000000 : ℝ)^5887 ≤ (9898338570599/20000000000000 : ℝ)^4863 := by
    have hnat : (5593274697 : ℕ)^5887*20000000000000^4863 ≤ 9898338570599^4863*10000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5593274697 10000000000 9898338570599 20000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5887/1024 : ℝ)) 5887 4863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1145647151/10000000000 : ℝ), (5003714271/10000000000 : ℝ), (5593274697/10000000000 : ℝ)] ![(145192969763/2000000000000 : ℝ), (43248658637107/100000000000000 : ℝ), (9898338570599/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1145647151/10000000000 : ℝ)|^5887 ≤ (145192969763/2000000000000 : ℝ)^4863
        have hw : |(-1145647151/10000000000 : ℝ)|=(1145647151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5003714271/10000000000 : ℝ)|^5887 ≤ (43248658637107/100000000000000 : ℝ)^4863
        have hw : |(5003714271/10000000000 : ℝ)|=(5003714271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5593274697/10000000000 : ℝ)|^5887 ≤ (9898338570599/20000000000000 : ℝ)^4863
        have hw : |(5593274697/10000000000 : ℝ)|=(5593274697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1757_s0_5 (p : ℝ) (hpa : (5871/1024 : ℝ) ≤ p) (hpb : p ≤ (5887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (25992601/50000000 : ℝ)*x 0 + (-871454753/10000000000 : ℝ)*x 1 + (5593274721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (25992601/50000000 : ℝ)^5887 ≤ (5661906020671/12500000000000 : ℝ)^4863 := by
    have hnat : (25992601 : ℕ)^5887*12500000000000^4863 ≤ 5661906020671^4863*50000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25992601 50000000 5661906020671 12500000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (871454753/10000000000 : ℝ)^5887 ≤ (1303264676637/25000000000000 : ℝ)^4863 := by
    have hnat : (871454753 : ℕ)^5887*25000000000000^4863 ≤ 1303264676637^4863*10000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      871454753 10000000000 1303264676637 25000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5593274721/10000000000 : ℝ)^5887 ≤ (1979667724403/4000000000000 : ℝ)^4863 := by
    have hnat : (5593274721 : ℕ)^5887*4000000000000^4863 ≤ 1979667724403^4863*10000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5593274721 10000000000 1979667724403 4000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5887/1024 : ℝ)) 5887 4863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(25992601/50000000 : ℝ), (-871454753/10000000000 : ℝ), (5593274721/10000000000 : ℝ)] ![(5661906020671/12500000000000 : ℝ), (1303264676637/25000000000000 : ℝ), (1979667724403/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(25992601/50000000 : ℝ)|^5887 ≤ (5661906020671/12500000000000 : ℝ)^4863
        have hw : |(25992601/50000000 : ℝ)|=(25992601/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-871454753/10000000000 : ℝ)|^5887 ≤ (1303264676637/25000000000000 : ℝ)^4863
        have hw : |(-871454753/10000000000 : ℝ)|=(871454753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5593274721/10000000000 : ℝ)|^5887 ≤ (1979667724403/4000000000000 : ℝ)^4863
        have hw : |(5593274721/10000000000 : ℝ)|=(5593274721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1757_s0_6 (p : ℝ) (hpa : (5871/1024 : ℝ) ≤ p) (hpb : p ≤ (5887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5198519549/10000000000 : ℝ)*x 0 + (5593274903/10000000000 : ℝ)*x 1 + (-871455433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5198519549/10000000000 : ℝ)^5887 ≤ (22647620649369/50000000000000 : ℝ)^4863 := by
    have hnat : (5198519549 : ℕ)^5887*50000000000000^4863 ≤ 22647620649369^4863*10000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5198519549 10000000000 22647620649369 50000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5593274903/10000000000 : ℝ)^5887 ≤ (49491695059593/100000000000000 : ℝ)^4863 := by
    have hnat : (5593274903 : ℕ)^5887*100000000000000^4863 ≤ 49491695059593^4863*10000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5593274903 10000000000 49491695059593 100000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (871455433/10000000000 : ℝ)^5887 ≤ (5213063630871/100000000000000 : ℝ)^4863 := by
    have hnat : (871455433 : ℕ)^5887*100000000000000^4863 ≤ 5213063630871^4863*10000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      871455433 10000000000 5213063630871 100000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5887/1024 : ℝ)) 5887 4863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5198519549/10000000000 : ℝ), (5593274903/10000000000 : ℝ), (-871455433/10000000000 : ℝ)] ![(22647620649369/50000000000000 : ℝ), (49491695059593/100000000000000 : ℝ), (5213063630871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5198519549/10000000000 : ℝ)|^5887 ≤ (22647620649369/50000000000000 : ℝ)^4863
        have hw : |(5198519549/10000000000 : ℝ)|=(5198519549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5593274903/10000000000 : ℝ)|^5887 ≤ (49491695059593/100000000000000 : ℝ)^4863
        have hw : |(5593274903/10000000000 : ℝ)|=(5593274903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-871455433/10000000000 : ℝ)|^5887 ≤ (5213063630871/100000000000000 : ℝ)^4863
        have hw : |(-871455433/10000000000 : ℝ)|=(871455433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1757_s0_7 (p : ℝ) (hpa : (5871/1024 : ℝ) ≤ p) (hpb : p ≤ (5887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1985728131/5000000000 : ℝ)*x 0 + (5037272141/10000000000 : ℝ)*x 1 + (761200827/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1985728131/5000000000 : ℝ)^5887 ≤ (4087058090719/12500000000000 : ℝ)^4863 := by
    have hnat : (1985728131 : ℕ)^5887*12500000000000^4863 ≤ 4087058090719^4863*5000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1985728131 5000000000 4087058090719 12500000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5037272141/10000000000 : ℝ)^5887 ≤ (43600033187333/100000000000000 : ℝ)^4863 := by
    have hnat : (5037272141 : ℕ)^5887*100000000000000^4863 ≤ 43600033187333^4863*10000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5037272141 10000000000 43600033187333 100000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (761200827/2500000000 : ℝ)^5887 ≤ (237035020619/1000000000000 : ℝ)^4863 := by
    have hnat : (761200827 : ℕ)^5887*1000000000000^4863 ≤ 237035020619^4863*2500000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      761200827 2500000000 237035020619 1000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5887/1024 : ℝ)) 5887 4863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1985728131/5000000000 : ℝ), (5037272141/10000000000 : ℝ), (761200827/2500000000 : ℝ)] ![(4087058090719/12500000000000 : ℝ), (43600033187333/100000000000000 : ℝ), (237035020619/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1985728131/5000000000 : ℝ)|^5887 ≤ (4087058090719/12500000000000 : ℝ)^4863
        have hw : |(1985728131/5000000000 : ℝ)|=(1985728131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5037272141/10000000000 : ℝ)|^5887 ≤ (43600033187333/100000000000000 : ℝ)^4863
        have hw : |(5037272141/10000000000 : ℝ)|=(5037272141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(761200827/2500000000 : ℝ)|^5887 ≤ (237035020619/1000000000000 : ℝ)^4863
        have hw : |(761200827/2500000000 : ℝ)|=(761200827/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1757_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5871/1024 : ℝ) ≤ p) (hpb : p ≤ (5887/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (218979081/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (3497/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (409/2000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (5871/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5871 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5871*1^1024 ≤ 0^1024*1^5871 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5871 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5871 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5871/1024 : ℝ) ≤ (522939414211724397/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5871 ≤ (522939414211724397/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5871*100000000000000000000^1024 ≤ 522939414211724397^1024*5^5871 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 522939414211724397 100000000000000000000 5871 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (522939414211724397/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5871 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5871/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5871 := by
      have hnat : (1 : ℕ)^1024*1^5871 ≤ 1^5871*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5871 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5871 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100522939414211724397/100000000000000000000 : ℝ) ≤ (10009101306241497/10000000000000000 : ℝ) ^ (5871/1024 : ℝ) := by
    have hpowers : (100522939414211724397/100000000000000000000 : ℝ)^1024 ≤ (10009101306241497/10000000000000000 : ℝ)^5871 := by
      have hnat : (100522939414211724397 : ℕ)^1024*10000000000000000^5871 ≤ 10009101306241497^5871*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100522939414211724397 100000000000000000000 10009101306241497 10000000000000000 1024 5871 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10009101306241497/10000000000000000 : ℝ)) (X := (100522939414211724397/100000000000000000000 : ℝ)) (by norm_num) 5871 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50522939414211724397/50000000000000000000 : ℝ) ≤ (5009101306241497/5000000000000000 : ℝ) ^ (5871/1024 : ℝ) := by
    have hpowers : (50522939414211724397/50000000000000000000 : ℝ)^1024 ≤ (5009101306241497/5000000000000000 : ℝ)^5871 := by
      have hnat : (50522939414211724397 : ℕ)^1024*5000000000000000^5871 ≤ 5009101306241497^5871*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50522939414211724397 50000000000000000000 5009101306241497 5000000000000000 1024 5871 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5009101306241497/5000000000000000 : ℝ)) (X := (50522939414211724397/50000000000000000000 : ℝ)) (by norm_num) 5871 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(9101306241497/4000000000000000 : ℝ)*(0 : ℝ))^(5871/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(9101306241497/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(522939414211724397/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(9101306241497/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5871/1024 : ℝ) := by
    rw [show (1 : ℝ)+(9101306241497/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10009101306241497/10000000000000000 : ℝ) by norm_num, show 1+(522939414211724397/100000000000000000000 : ℝ)+(0 : ℝ)=(100522939414211724397/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(522939414211724397/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(9101306241497/4000000000000000 : ℝ)*(2/5 : ℝ))^(5871/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(9101306241497/4000000000000000 : ℝ)*(2/5 : ℝ)=(5009101306241497/5000000000000000 : ℝ) by norm_num, show 1+2*(522939414211724397/100000000000000000000 : ℝ)=(50522939414211724397/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(9101306241497/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5871/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (9101306241497/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(9101306241497/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5871/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (9101306241497/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(9101306241497/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5871/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (9101306241497/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-572210719/5000000000 : ℝ)*X 0 0+(5609434383/10000000000 : ℝ)*X 0 1+(2494029709/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1757_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((10476121/19531250 : ℝ)*X 1 0+(-369167903/2500000000 : ℝ)*X 1 1+(4988060041/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1757_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1340944267/2500000000 : ℝ)*X 2 0+(4988058343/10000000000 : ℝ)*X 2 1+(-1476669717/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1757_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((3967312379/10000000000 : ℝ)*X 0 0+(747547527/2500000000 : ℝ)*X 0 1+(2545090917/5000000000 : ℝ)*X 0 2+(3967312379/10000000000 : ℝ)*X 1 0+(747547527/2500000000 : ℝ)*X 1 1+(2545090917/5000000000 : ℝ)*X 1 2+(3967312379/10000000000 : ℝ)*X 2 0+(747547527/2500000000 : ℝ)*X 2 1+(2545090917/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1757_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1145647151/10000000000 : ℝ)*X 0 0+(5003714271/10000000000 : ℝ)*X 0 1+(5593274697/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1757_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((25992601/50000000 : ℝ)*X 1 0+(-871454753/10000000000 : ℝ)*X 1 1+(5593274721/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1757_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5198519549/10000000000 : ℝ)*X 2 0+(5593274903/10000000000 : ℝ)*X 2 1+(-871455433/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1757_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1985728131/5000000000 : ℝ)*X 0 0+(5037272141/10000000000 : ℝ)*X 0 1+(761200827/2500000000 : ℝ)*X 0 2+(1985728131/5000000000 : ℝ)*X 1 0+(5037272141/10000000000 : ℝ)*X 1 1+(761200827/2500000000 : ℝ)*X 1 2+(1985728131/5000000000 : ℝ)*X 2 0+(5037272141/10000000000 : ℝ)*X 2 1+(761200827/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1757_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1042547957474468078559249/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (406964217/25000000000000 : ℝ)*(base19) + (2264305677/100000000000000 : ℝ)*(base23) + (49776719/50000000000000 : ℝ)*(base24) + (13337383/12500000000000 : ℝ)*(upper4) + (147016771/25000000000000 : ℝ)*(upper5) + (1042776945905139/100000000000000 : ℝ)*(major0) + (1042776945905139/100000000000000 : ℝ)*(major1) + (1042776945905139/100000000000000 : ℝ)*(major2) + (40233476588897/2500000000000 : ℝ)*(sp0) + (1609352573037519/100000000000000 : ℝ)*(sp1) + (1609351837035271/100000000000000 : ℝ)*(sp2) + (238098212746787/50000000000000 : ℝ)*(sp3) + (7568669253/50000000000000 : ℝ)*(sp4) + (364738291/12500000000000 : ℝ)*(sp7) + (238099671699951/50000000000000 : ℝ)*(f.failure) + (804677100447193/50000000000000 : ℝ)*(f.sum) + (154028539846917/200000000000000000000000000000 : ℝ)*base66 + (2413830624953083/400000000000000000000000000000 : ℝ)*base67 + (1171545482553083/400000000000000000000000000000 : ℝ)*base69 + (616683359353083/400000000000000000000000000000 : ℝ)*base71 + (210115935046917/200000000000000000000000000000 : ℝ)*base74 + (2500781620246917/400000000000000000000000000000 : ℝ)*base76 + (1510259223353083/400000000000000000000000000000 : ℝ)*base77 + (367359289846917/400000000000000000000000000000 : ℝ)*base80 + (586979099246917/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (27725031/5000000000000000000000 : ℝ)*base89 + (27725031/5000000000000000000000 : ℝ)*base91 + (27725031/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (88713156588682013123133/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (704366637/100000000000000 : ℝ)*(base19) + (74549139/12500000000000 : ℝ)*(base23) + (15145601/20000000000000 : ℝ)*(upper2) + (12181497/10000000000000 : ℝ)*(upper3) + (9727239/10000000000000 : ℝ)*(upper5) + (549516835267421/50000000000000 : ℝ)*(major0) + (549516835267421/50000000000000 : ℝ)*(major1) + (549516835267421/50000000000000 : ℝ)*(major2) + (3183182587/100000000000000 : ℝ)*(sp1) + (117869613/6250000000000 : ℝ)*(sp2) + (848088756009131/50000000000000 : ℝ)*(sp4) + (1696173624469037/100000000000000 : ℝ)*(sp5) + (848087514855671/50000000000000 : ℝ)*(sp6) + (501889799480363/100000000000000 : ℝ)*(sp7) + (501889799480363/100000000000000 : ℝ)*(f.failure) + (848088756009131/50000000000000 : ℝ)*(f.sum) + (128692752030763/100000000000000000000000000000 : ℝ)*base66 + (1022178434630763/200000000000000000000000000000 : ℝ)*base68 + (1780473081230763/200000000000000000000000000000 : ℝ)*base70 + (884882463630763/200000000000000000000000000000 : ℝ)*base72 + (318931994569237/100000000000000000000000000000 : ℝ)*base73 + (444626292769237/200000000000000000000000000000 : ℝ)*base75 + (1896754159230763/200000000000000000000000000000 : ℝ)*base78 + (1249045028230763/200000000000000000000000000000 : ℝ)*base80 + (81488335830763/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (32713597/10000000000000000000000 : ℝ)*base90 + (32713597/10000000000000000000000 : ℝ)*base92 + (32713597/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1757_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5871/1024 : ℝ) ≤ p) (hpb : p ≤ (5887/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (218979081/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3497/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (409/2000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1757_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1757_s1_0 (p : ℝ) (hpa : (5871/1024 : ℝ) ≤ p) (hpb : p ≤ (5887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-147933683/1250000000 : ℝ)*x 0 + (549018577/1000000000 : ℝ)*x 1 + (2540546957/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (147933683/1250000000 : ℝ)^5887 ≤ (1510156992187/20000000000000 : ℝ)^4863 := by
    have hnat : (147933683 : ℕ)^5887*20000000000000^4863 ≤ 1510156992187^4863*1250000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      147933683 1250000000 1510156992187 20000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (549018577/1000000000 : ℝ)^5887 ≤ (48389594754343/100000000000000 : ℝ)^4863 := by
    have hnat : (549018577 : ℕ)^5887*100000000000000^4863 ≤ 48389594754343^4863*1000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549018577 1000000000 48389594754343 100000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2540546957/5000000000 : ℝ)^5887 ≤ (2753726266603/6250000000000 : ℝ)^4863 := by
    have hnat : (2540546957 : ℕ)^5887*6250000000000^4863 ≤ 2753726266603^4863*5000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2540546957 5000000000 2753726266603 6250000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5887/1024 : ℝ)) 5887 4863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-147933683/1250000000 : ℝ), (549018577/1000000000 : ℝ), (2540546957/5000000000 : ℝ)] ![(1510156992187/20000000000000 : ℝ), (48389594754343/100000000000000 : ℝ), (2753726266603/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-147933683/1250000000 : ℝ)|^5887 ≤ (1510156992187/20000000000000 : ℝ)^4863
        have hw : |(-147933683/1250000000 : ℝ)|=(147933683/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(549018577/1000000000 : ℝ)|^5887 ≤ (48389594754343/100000000000000 : ℝ)^4863
        have hw : |(549018577/1000000000 : ℝ)|=(549018577/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2540546957/5000000000 : ℝ)|^5887 ≤ (2753726266603/6250000000000 : ℝ)^4863
        have hw : |(2540546957/5000000000 : ℝ)|=(2540546957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1757_s1_1 (p : ℝ) (hpa : (5871/1024 : ℝ) ≤ p) (hpb : p ≤ (5887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5332090021/10000000000 : ℝ)*x 0 + (-1397312917/10000000000 : ℝ)*x 1 + (1016218647/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5332090021/10000000000 : ℝ)^5887 ≤ (5838488029093/12500000000000 : ℝ)^4863 := by
    have hnat : (5332090021 : ℕ)^5887*12500000000000^4863 ≤ 5838488029093^4863*10000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5332090021 10000000000 5838488029093 12500000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1397312917/10000000000 : ℝ)^5887 ≤ (2308120652739/25000000000000 : ℝ)^4863 := by
    have hnat : (1397312917 : ℕ)^5887*25000000000000^4863 ≤ 2308120652739^4863*10000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1397312917 10000000000 2308120652739 25000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1016218647/2000000000 : ℝ)^5887 ≤ (44059613138053/100000000000000 : ℝ)^4863 := by
    have hnat : (1016218647 : ℕ)^5887*100000000000000^4863 ≤ 44059613138053^4863*2000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1016218647 2000000000 44059613138053 100000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5887/1024 : ℝ)) 5887 4863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5332090021/10000000000 : ℝ), (-1397312917/10000000000 : ℝ), (1016218647/2000000000 : ℝ)] ![(5838488029093/12500000000000 : ℝ), (2308120652739/25000000000000 : ℝ), (44059613138053/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5332090021/10000000000 : ℝ)|^5887 ≤ (5838488029093/12500000000000 : ℝ)^4863
        have hw : |(5332090021/10000000000 : ℝ)|=(5332090021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1397312917/10000000000 : ℝ)|^5887 ≤ (2308120652739/25000000000000 : ℝ)^4863
        have hw : |(-1397312917/10000000000 : ℝ)|=(1397312917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1016218647/2000000000 : ℝ)|^5887 ≤ (44059613138053/100000000000000 : ℝ)^4863
        have hw : |(1016218647/2000000000 : ℝ)|=(1016218647/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1757_s1_2 (p : ℝ) (hpa : (5871/1024 : ℝ) ≤ p) (hpb : p ≤ (5887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2666044047/5000000000 : ℝ)*x 0 + (1016218949/2000000000 : ℝ)*x 1 + (-139731349/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2666044047/5000000000 : ℝ)^5887 ≤ (46707883798227/100000000000000 : ℝ)^4863 := by
    have hnat : (2666044047 : ℕ)^5887*100000000000000^4863 ≤ 46707883798227^4863*5000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2666044047 5000000000 46707883798227 100000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1016218949/2000000000 : ℝ)^5887 ≤ (22029814494409/50000000000000 : ℝ)^4863 := by
    have hnat : (1016218949 : ℕ)^5887*50000000000000^4863 ≤ 22029814494409^4863*2000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1016218949 2000000000 22029814494409 50000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (139731349/1000000000 : ℝ)^5887 ≤ (115406089927/1250000000000 : ℝ)^4863 := by
    have hnat : (139731349 : ℕ)^5887*1250000000000^4863 ≤ 115406089927^4863*1000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      139731349 1000000000 115406089927 1250000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5887/1024 : ℝ)) 5887 4863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2666044047/5000000000 : ℝ), (1016218949/2000000000 : ℝ), (-139731349/1000000000 : ℝ)] ![(46707883798227/100000000000000 : ℝ), (22029814494409/50000000000000 : ℝ), (115406089927/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2666044047/5000000000 : ℝ)|^5887 ≤ (46707883798227/100000000000000 : ℝ)^4863
        have hw : |(2666044047/5000000000 : ℝ)|=(2666044047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1016218949/2000000000 : ℝ)|^5887 ≤ (22029814494409/50000000000000 : ℝ)^4863
        have hw : |(1016218949/2000000000 : ℝ)|=(1016218949/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-139731349/1000000000 : ℝ)|^5887 ≤ (115406089927/1250000000000 : ℝ)^4863
        have hw : |(-139731349/1000000000 : ℝ)|=(139731349/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1757_s1_3 (p : ℝ) (hpa : (5871/1024 : ℝ) ≤ p) (hpb : p ≤ (5887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1001489113/2500000000 : ℝ)*x 0 + (1673049273/5000000000 : ℝ)*x 1 + (4728659489/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1001489113/2500000000 : ℝ)^5887 ≤ (6608124628131/20000000000000 : ℝ)^4863 := by
    have hnat : (1001489113 : ℕ)^5887*20000000000000^4863 ≤ 6608124628131^4863*2500000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1001489113 2500000000 6608124628131 20000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1673049273/5000000000 : ℝ)^5887 ≤ (3321475449849/12500000000000 : ℝ)^4863 := by
    have hnat : (1673049273 : ℕ)^5887*12500000000000^4863 ≤ 3321475449849^4863*5000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1673049273 5000000000 3321475449849 12500000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4728659489/10000000000 : ℝ)^5887 ≤ (40387573254017/100000000000000 : ℝ)^4863 := by
    have hnat : (4728659489 : ℕ)^5887*100000000000000^4863 ≤ 40387573254017^4863*10000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4728659489 10000000000 40387573254017 100000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5887/1024 : ℝ)) 5887 4863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1001489113/2500000000 : ℝ), (1673049273/5000000000 : ℝ), (4728659489/10000000000 : ℝ)] ![(6608124628131/20000000000000 : ℝ), (3321475449849/12500000000000 : ℝ), (40387573254017/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1001489113/2500000000 : ℝ)|^5887 ≤ (6608124628131/20000000000000 : ℝ)^4863
        have hw : |(1001489113/2500000000 : ℝ)|=(1001489113/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1673049273/5000000000 : ℝ)|^5887 ≤ (3321475449849/12500000000000 : ℝ)^4863
        have hw : |(1673049273/5000000000 : ℝ)|=(1673049273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4728659489/10000000000 : ℝ)|^5887 ≤ (40387573254017/100000000000000 : ℝ)^4863
        have hw : |(4728659489/10000000000 : ℝ)|=(4728659489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1757_s1_4 (p : ℝ) (hpa : (5871/1024 : ℝ) ≤ p) (hpb : p ≤ (5887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1183817711/10000000000 : ℝ)*x 0 + (5087895319/10000000000 : ℝ)*x 1 + (13708101/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1183817711/10000000000 : ℝ)^5887 ≤ (755347479599/10000000000000 : ℝ)^4863 := by
    have hnat : (1183817711 : ℕ)^5887*10000000000000^4863 ≤ 755347479599^4863*10000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1183817711 10000000000 755347479599 10000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5087895319/10000000000 : ℝ)^5887 ≤ (11032756500831/25000000000000 : ℝ)^4863 := by
    have hnat : (5087895319 : ℕ)^5887*25000000000000^4863 ≤ 11032756500831^4863*10000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5087895319 10000000000 11032756500831 25000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13708101/25000000 : ℝ)^5887 ≤ (48315499186411/100000000000000 : ℝ)^4863 := by
    have hnat : (13708101 : ℕ)^5887*100000000000000^4863 ≤ 48315499186411^4863*25000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13708101 25000000 48315499186411 100000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5887/1024 : ℝ)) 5887 4863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1183817711/10000000000 : ℝ), (5087895319/10000000000 : ℝ), (13708101/25000000 : ℝ)] ![(755347479599/10000000000000 : ℝ), (11032756500831/25000000000000 : ℝ), (48315499186411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1183817711/10000000000 : ℝ)|^5887 ≤ (755347479599/10000000000000 : ℝ)^4863
        have hw : |(-1183817711/10000000000 : ℝ)|=(1183817711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5087895319/10000000000 : ℝ)|^5887 ≤ (11032756500831/25000000000000 : ℝ)^4863
        have hw : |(5087895319/10000000000 : ℝ)|=(5087895319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(13708101/25000000 : ℝ)|^5887 ≤ (48315499186411/100000000000000 : ℝ)^4863
        have hw : |(13708101/25000000 : ℝ)|=(13708101/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1757_s1_5 (p : ℝ) (hpa : (5871/1024 : ℝ) ≤ p) (hpb : p ≤ (5887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (326491141/625000000 : ℝ)*x 0 + (-995166473/10000000000 : ℝ)*x 1 + (171351261/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (326491141/625000000 : ℝ)^5887 ≤ (45562646371293/100000000000000 : ℝ)^4863 := by
    have hnat : (326491141 : ℕ)^5887*100000000000000^4863 ≤ 45562646371293^4863*625000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326491141 625000000 45562646371293 100000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (995166473/10000000000 : ℝ)^5887 ≤ (765231868329/12500000000000 : ℝ)^4863 := by
    have hnat : (995166473 : ℕ)^5887*12500000000000^4863 ≤ 765231868329^4863*10000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      995166473 10000000000 765231868329 12500000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (171351261/312500000 : ℝ)^5887 ≤ (48315498674399/100000000000000 : ℝ)^4863 := by
    have hnat : (171351261 : ℕ)^5887*100000000000000^4863 ≤ 48315498674399^4863*312500000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171351261 312500000 48315498674399 100000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5887/1024 : ℝ)) 5887 4863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(326491141/625000000 : ℝ), (-995166473/10000000000 : ℝ), (171351261/312500000 : ℝ)] ![(45562646371293/100000000000000 : ℝ), (765231868329/12500000000000 : ℝ), (48315498674399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(326491141/625000000 : ℝ)|^5887 ≤ (45562646371293/100000000000000 : ℝ)^4863
        have hw : |(326491141/625000000 : ℝ)|=(326491141/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-995166473/10000000000 : ℝ)|^5887 ≤ (765231868329/12500000000000 : ℝ)^4863
        have hw : |(-995166473/10000000000 : ℝ)|=(995166473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(171351261/312500000 : ℝ)|^5887 ≤ (48315498674399/100000000000000 : ℝ)^4863
        have hw : |(171351261/312500000 : ℝ)|=(171351261/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1757_s1_6 (p : ℝ) (hpa : (5871/1024 : ℝ) ≤ p) (hpb : p ≤ (5887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5223857479/10000000000 : ℝ)*x 0 + (274162059/500000000 : ℝ)*x 1 + (-995166387/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5223857479/10000000000 : ℝ)^5887 ≤ (22781319083621/50000000000000 : ℝ)^4863 := by
    have hnat : (5223857479 : ℕ)^5887*50000000000000^4863 ≤ 22781319083621^4863*10000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5223857479 10000000000 22781319083621 50000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (274162059/500000000 : ℝ)^5887 ≤ (48315507506607/100000000000000 : ℝ)^4863 := by
    have hnat : (274162059 : ℕ)^5887*100000000000000^4863 ≤ 48315507506607^4863*500000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274162059 500000000 48315507506607 100000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (995166387/10000000000 : ℝ)^5887 ≤ (6121854306197/100000000000000 : ℝ)^4863 := by
    have hnat : (995166387 : ℕ)^5887*100000000000000^4863 ≤ 6121854306197^4863*10000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      995166387 10000000000 6121854306197 100000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5887/1024 : ℝ)) 5887 4863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5223857479/10000000000 : ℝ), (274162059/500000000 : ℝ), (-995166387/10000000000 : ℝ)] ![(22781319083621/50000000000000 : ℝ), (48315507506607/100000000000000 : ℝ), (6121854306197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5223857479/10000000000 : ℝ)|^5887 ≤ (22781319083621/50000000000000 : ℝ)^4863
        have hw : |(5223857479/10000000000 : ℝ)|=(5223857479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(274162059/500000000 : ℝ)|^5887 ≤ (48315507506607/100000000000000 : ℝ)^4863
        have hw : |(274162059/500000000 : ℝ)|=(274162059/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-995166387/10000000000 : ℝ)|^5887 ≤ (6121854306197/100000000000000 : ℝ)^4863
        have hw : |(-995166387/10000000000 : ℝ)|=(995166387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1757_s1_7 (p : ℝ) (hpa : (5871/1024 : ℝ) ≤ p) (hpb : p ≤ (5887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (500891433/1250000000 : ℝ)*x 0 + (4705672531/10000000000 : ℝ)*x 1 + (134782863/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (500891433/1250000000 : ℝ)^5887 ≤ (2065772222343/6250000000000 : ℝ)^4863 := by
    have hnat : (500891433 : ℕ)^5887*6250000000000^4863 ≤ 2065772222343^4863*1250000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      500891433 1250000000 2065772222343 6250000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4705672531/10000000000 : ℝ)^5887 ≤ (10037505357799/25000000000000 : ℝ)^4863 := by
    have hnat : (4705672531 : ℕ)^5887*25000000000000^4863 ≤ 10037505357799^4863*10000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4705672531 10000000000 10037505357799 25000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (134782863/400000000 : ℝ)^5887 ≤ (535952460089/2000000000000 : ℝ)^4863 := by
    have hnat : (134782863 : ℕ)^5887*2000000000000^4863 ≤ 535952460089^4863*400000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134782863 400000000 535952460089 2000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5887/1024 : ℝ)) 5887 4863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(500891433/1250000000 : ℝ), (4705672531/10000000000 : ℝ), (134782863/400000000 : ℝ)] ![(2065772222343/6250000000000 : ℝ), (10037505357799/25000000000000 : ℝ), (535952460089/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(500891433/1250000000 : ℝ)|^5887 ≤ (2065772222343/6250000000000 : ℝ)^4863
        have hw : |(500891433/1250000000 : ℝ)|=(500891433/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4705672531/10000000000 : ℝ)|^5887 ≤ (10037505357799/25000000000000 : ℝ)^4863
        have hw : |(4705672531/10000000000 : ℝ)|=(4705672531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(134782863/400000000 : ℝ)|^5887 ≤ (535952460089/2000000000000 : ℝ)^4863
        have hw : |(134782863/400000000 : ℝ)|=(134782863/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1757_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5871/1024 : ℝ) ≤ p) (hpb : p ≤ (5887/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (218979081/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (409/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3497/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (9081/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4473/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (409/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3497/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (409/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3497/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (409/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3497/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (409/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3497/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (409/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3497/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (409/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3497/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3497/50000 : ℝ) ^ (5871/1024 : ℝ) ≤ (951506395819/4000000000000000000 : ℝ) := by
    have hpowers : (3497/50000 : ℝ)^5871 ≤ (951506395819/4000000000000000000 : ℝ)^1024 := by
      have hnat : (3497 : ℕ)^5871*4000000000000000000^1024 ≤ 951506395819^1024*50000^5871 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3497 50000 951506395819 4000000000000000000 5871 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3497/50000 : ℝ)) (X := (951506395819/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5871 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (409/2000 : ℝ) ^ (5871/1024 : ℝ) ≤ (2233367076808751/20000000000000000000 : ℝ) := by
    have hpowers : (409/2000 : ℝ)^5871 ≤ (2233367076808751/20000000000000000000 : ℝ)^1024 := by
      have hnat : (409 : ℕ)^5871*20000000000000000000^1024 ≤ 2233367076808751^1024*2000^5871 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        409 2000 2233367076808751 20000000000000000000 5871 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (409/2000 : ℝ)) (X := (2233367076808751/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5871 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000000951506395819/2000000000000000000 : ℝ) ≤ (1250000103724063/1250000000000000 : ℝ) ^ (5871/1024 : ℝ) := by
    have hpowers : (2000000951506395819/2000000000000000000 : ℝ)^1024 ≤ (1250000103724063/1250000000000000 : ℝ)^5871 := by
      have hnat : (2000000951506395819 : ℕ)^1024*1250000000000000^5871 ≤ 1250000103724063^5871*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000000951506395819 2000000000000000000 1250000103724063 1250000000000000 1024 5871 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250000103724063/1250000000000000 : ℝ)) (X := (2000000951506395819/2000000000000000000 : ℝ)) (by norm_num) 5871 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10001119062304393923/10000000000000000000 : ℝ) ≤ (1250024396756701/1250000000000000 : ℝ) ^ (5871/1024 : ℝ) := by
    have hpowers : (10001119062304393923/10000000000000000000 : ℝ)^1024 ≤ (1250024396756701/1250000000000000 : ℝ)^5871 := by
      have hnat : (10001119062304393923 : ℕ)^1024*1250000000000000^5871 ≤ 1250024396756701^5871*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001119062304393923 10000000000000000000 1250024396756701 1250000000000000 1024 5871 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250024396756701/1250000000000000 : ℝ)) (X := (10001119062304393923/10000000000000000000 : ℝ)) (by norm_num) 5871 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10002233367076808751/10000000000000000000 : ℝ) ≤ (1250048689789339/1250000000000000 : ℝ) ^ (5871/1024 : ℝ) := by
    have hpowers : (10002233367076808751/10000000000000000000 : ℝ)^1024 ≤ (1250048689789339/1250000000000000 : ℝ)^5871 := by
      have hnat : (10002233367076808751 : ℕ)^1024*1250000000000000^5871 ≤ 1250048689789339^5871*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002233367076808751 10000000000000000000 1250048689789339 1250000000000000 1024 5871 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250048689789339/1250000000000000 : ℝ)) (X := (10002233367076808751/10000000000000000000 : ℝ)) (by norm_num) 5871 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(951506395819/4000000000000000000 : ℝ) ≤ ((2102457698096306423/2102500000000000000 : ℝ)+2*(12146516319/84100000000000 : ℝ)*(3497/50000 : ℝ))^(5871/1024 : ℝ) := by
    rw [show (2102457698096306423/2102500000000000000 : ℝ)+2*(12146516319/84100000000000 : ℝ)*(3497/50000 : ℝ)=(1250000103724063/1250000000000000 : ℝ) by norm_num, show 1+2*(951506395819/4000000000000000000 : ℝ)=(2000000951506395819/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2233367076808751/20000000000000000000 : ℝ)+(951506395819/4000000000000000000 : ℝ) ≤ ((2102457698096306423/2102500000000000000 : ℝ)+(12146516319/84100000000000 : ℝ)*((409/2000 : ℝ)+(3497/50000 : ℝ)))^(5871/1024 : ℝ) := by
    rw [show (2102457698096306423/2102500000000000000 : ℝ)+(12146516319/84100000000000 : ℝ)*((409/2000 : ℝ)+(3497/50000 : ℝ))=(1250024396756701/1250000000000000 : ℝ) by norm_num, show 1+(2233367076808751/20000000000000000000 : ℝ)+(951506395819/4000000000000000000 : ℝ)=(10001119062304393923/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2233367076808751/20000000000000000000 : ℝ) ≤ ((2102457698096306423/2102500000000000000 : ℝ)+2*(12146516319/84100000000000 : ℝ)*(409/2000 : ℝ))^(5871/1024 : ℝ) := by
    rw [show (2102457698096306423/2102500000000000000 : ℝ)+2*(12146516319/84100000000000 : ℝ)*(409/2000 : ℝ)=(1250048689789339/1250000000000000 : ℝ) by norm_num, show 1+2*(2233367076808751/20000000000000000000 : ℝ)=(10002233367076808751/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2102457698096306423/2102500000000000000 : ℝ)*(X 1 0+X 2 0)+(12146516319/84100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5871/1024 : ℝ)) (lo := (3497/50000 : ℝ)) (hi := (409/2000 : ℝ)) (c := (2102457698096306423/2102500000000000000 : ℝ)) (alpha := (12146516319/84100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2102457698096306423/2102500000000000000 : ℝ)*(X 0 1+X 2 1)+(12146516319/84100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5871/1024 : ℝ)) (lo := (3497/50000 : ℝ)) (hi := (409/2000 : ℝ)) (c := (2102457698096306423/2102500000000000000 : ℝ)) (alpha := (12146516319/84100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2102457698096306423/2102500000000000000 : ℝ)*(X 0 2+X 1 2)+(12146516319/84100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5871/1024 : ℝ)) (lo := (3497/50000 : ℝ)) (hi := (409/2000 : ℝ)) (c := (2102457698096306423/2102500000000000000 : ℝ)) (alpha := (12146516319/84100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-147933683/1250000000 : ℝ)*X 0 0+(549018577/1000000000 : ℝ)*X 0 1+(2540546957/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1757_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5332090021/10000000000 : ℝ)*X 1 0+(-1397312917/10000000000 : ℝ)*X 1 1+(1016218647/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1757_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2666044047/5000000000 : ℝ)*X 2 0+(1016218949/2000000000 : ℝ)*X 2 1+(-139731349/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1757_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1001489113/2500000000 : ℝ)*X 0 0+(1673049273/5000000000 : ℝ)*X 0 1+(4728659489/10000000000 : ℝ)*X 0 2+(1001489113/2500000000 : ℝ)*X 1 0+(1673049273/5000000000 : ℝ)*X 1 1+(4728659489/10000000000 : ℝ)*X 1 2+(1001489113/2500000000 : ℝ)*X 2 0+(1673049273/5000000000 : ℝ)*X 2 1+(4728659489/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1757_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1183817711/10000000000 : ℝ)*X 0 0+(5087895319/10000000000 : ℝ)*X 0 1+(13708101/25000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1757_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((326491141/625000000 : ℝ)*X 1 0+(-995166473/10000000000 : ℝ)*X 1 1+(171351261/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1757_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5223857479/10000000000 : ℝ)*X 2 0+(274162059/500000000 : ℝ)*X 2 1+(-995166387/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1757_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((500891433/1250000000 : ℝ)*X 0 0+(4705672531/10000000000 : ℝ)*X 0 1+(134782863/400000000 : ℝ)*X 0 2+(500891433/1250000000 : ℝ)*X 1 0+(4705672531/10000000000 : ℝ)*X 1 1+(134782863/400000000 : ℝ)*X 1 2+(500891433/1250000000 : ℝ)*X 2 0+(4705672531/10000000000 : ℝ)*X 2 1+(134782863/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1757_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (355375041866577384942011373/52562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (570453581/50000000000000 : ℝ)*(base19) + (132460141/50000000000000 : ℝ)*(base23) + (16647137/100000000000000 : ℝ)*(upper2) + (73344151/25000000000000 : ℝ)*(upper3) + (1583875316770217/100000000000000 : ℝ)*(major0) + (1583875316770217/100000000000000 : ℝ)*(major1) + (1583875316770217/100000000000000 : ℝ)*(major2) + (2444448047347043/100000000000000 : ℝ)*(sp0) + (2444449439019447/100000000000000 : ℝ)*(sp1) + (2444449142911697/100000000000000 : ℝ)*(sp2) + (144659460030413/20000000000000 : ℝ)*(sp3) + (1266289783/50000000000000 : ℝ)*(sp4) + (117209463/10000000000000 : ℝ)*(sp6) + (2528095099/100000000000000 : ℝ)*(sp7) + (180824957061791/25000000000000 : ℝ)*(f.failure) + (152778161245413/6250000000000 : ℝ)*(f.sum) + (2397756531933/4205000000000000000000000000 : ℝ)*base65 + (1499192145717971209/210250000000000000000000000000000 : ℝ)*base68 + (1647253494330221209/210250000000000000000000000000000 : ℝ)*base70 + (1142093870012971209/210250000000000000000000000000000 : ℝ)*base72 + (6356406831577/4205000000000000000000000000 : ℝ)*base74 + (1783133515945971209/210250000000000000000000000000000 : ℝ)*base76 + (599904142051778791/210250000000000000000000000000000 : ℝ)*base77 + (1314585497428221209/210250000000000000000000000000000 : ℝ)*base80 + (11605025639627/4205000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (28394071/2500000000000000000000 : ℝ)*base89 + (28394071/2500000000000000000000 : ℝ)*base91 + (28394071/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1205040356191678927615271901/105125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (384088101/25000000000000 : ℝ)*(base19) + (737582637/50000000000000 : ℝ)*(base23) + (143296401/100000000000000 : ℝ)*(upper2) + (282802937/100000000000000 : ℝ)*(upper3) + (295417201/100000000000000 : ℝ)*(upper5) + (1638939883715071/100000000000000 : ℝ)*(major0) + (1638939883715071/100000000000000 : ℝ)*(major1) + (1638939883715071/100000000000000 : ℝ)*(major2) + (4960737251/50000000000000 : ℝ)*(sp1) + (11887491249/100000000000000 : ℝ)*(sp2) + (632358379311873/25000000000000 : ℝ)*(sp4) + (1264711029710293/50000000000000 : ℝ)*(sp5) + (316177519323871/12500000000000 : ℝ)*(sp6) + (74844586808503/10000000000000 : ℝ)*(sp7) + (74844586808503/10000000000000 : ℝ)*(f.failure) + (632358379311873/25000000000000 : ℝ)*(f.sum) + (3471642424509/4205000000000000000000000000 : ℝ)*base65 + (1100116948569073967/210250000000000000000000000000000 : ℝ)*base68 + (325240189232073967/210250000000000000000000000000000 : ℝ)*base70 + (104954979030926033/210250000000000000000000000000000 : ℝ)*base71 + (16623641789041/4205000000000000000000000000 : ℝ)*base74 + (242686387087426033/210250000000000000000000000000000 : ℝ)*base75 + (1319750775700926033/210250000000000000000000000000000 : ℝ)*base77 + (1420831264361676033/210250000000000000000000000000000 : ℝ)*base79 + (17799465780271/4205000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (74257/1000000000000000000000 : ℝ)*base90 + (74257/1000000000000000000000 : ℝ)*base92 + (74257/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1757_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5871/1024 : ℝ) ≤ p) (hpb : p ≤ (5887/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (218979081/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (409/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3497/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9081/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4473/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1757_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1757_s2_0 (p : ℝ) (hpa : (5871/1024 : ℝ) ≤ p) (hpb : p ≤ (5887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-592109681/5000000000 : ℝ)*x 0 + (137194311/250000000 : ℝ)*x 1 + (317687183/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (592109681/5000000000 : ℝ)^5887 ≤ (7556577326651/100000000000000 : ℝ)^4863 := by
    have hnat : (592109681 : ℕ)^5887*100000000000000^4863 ≤ 7556577326651^4863*5000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      592109681 5000000000 7556577326651 100000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (137194311/250000000 : ℝ)^5887 ≤ (24181923145339/50000000000000 : ℝ)^4863 := by
    have hnat : (137194311 : ℕ)^5887*50000000000000^4863 ≤ 24181923145339^4863*250000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137194311 250000000 24181923145339 50000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (317687183/625000000 : ℝ)^5887 ≤ (44079576367617/100000000000000 : ℝ)^4863 := by
    have hnat : (317687183 : ℕ)^5887*100000000000000^4863 ≤ 44079576367617^4863*625000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      317687183 625000000 44079576367617 100000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5887/1024 : ℝ)) 5887 4863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-592109681/5000000000 : ℝ), (137194311/250000000 : ℝ), (317687183/625000000 : ℝ)] ![(7556577326651/100000000000000 : ℝ), (24181923145339/50000000000000 : ℝ), (44079576367617/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-592109681/5000000000 : ℝ)|^5887 ≤ (7556577326651/100000000000000 : ℝ)^4863
        have hw : |(-592109681/5000000000 : ℝ)|=(592109681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(137194311/250000000 : ℝ)|^5887 ≤ (24181923145339/50000000000000 : ℝ)^4863
        have hw : |(137194311/250000000 : ℝ)|=(137194311/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(317687183/625000000 : ℝ)|^5887 ≤ (44079576367617/100000000000000 : ℝ)^4863
        have hw : |(317687183/625000000 : ℝ)|=(317687183/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1757_s2_1 (p : ℝ) (hpa : (5871/1024 : ℝ) ≤ p) (hpb : p ≤ (5887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5331416327/10000000000 : ℝ)*x 0 + (-1395710039/10000000000 : ℝ)*x 1 + (317687183/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5331416327/10000000000 : ℝ)^5887 ≤ (9340152052699/20000000000000 : ℝ)^4863 := by
    have hnat : (5331416327 : ℕ)^5887*20000000000000^4863 ≤ 9340152052699^4863*10000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5331416327 10000000000 9340152052699 20000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1395710039/10000000000 : ℝ)^5887 ≤ (9219663361801/100000000000000 : ℝ)^4863 := by
    have hnat : (1395710039 : ℕ)^5887*100000000000000^4863 ≤ 9219663361801^4863*10000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1395710039 10000000000 9219663361801 100000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (317687183/625000000 : ℝ)^5887 ≤ (44079576367617/100000000000000 : ℝ)^4863 := by
    have hnat : (317687183 : ℕ)^5887*100000000000000^4863 ≤ 44079576367617^4863*625000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      317687183 625000000 44079576367617 100000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5887/1024 : ℝ)) 5887 4863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5331416327/10000000000 : ℝ), (-1395710039/10000000000 : ℝ), (317687183/625000000 : ℝ)] ![(9340152052699/20000000000000 : ℝ), (9219663361801/100000000000000 : ℝ), (44079576367617/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5331416327/10000000000 : ℝ)|^5887 ≤ (9340152052699/20000000000000 : ℝ)^4863
        have hw : |(5331416327/10000000000 : ℝ)|=(5331416327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1395710039/10000000000 : ℝ)|^5887 ≤ (9219663361801/100000000000000 : ℝ)^4863
        have hw : |(-1395710039/10000000000 : ℝ)|=(1395710039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(317687183/625000000 : ℝ)|^5887 ≤ (44079576367617/100000000000000 : ℝ)^4863
        have hw : |(317687183/625000000 : ℝ)|=(317687183/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1757_s2_2 (p : ℝ) (hpa : (5871/1024 : ℝ) ≤ p) (hpb : p ≤ (5887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (666427041/1250000000 : ℝ)*x 0 + (203319797/400000000 : ℝ)*x 1 + (-1395710041/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (666427041/1250000000 : ℝ)^5887 ≤ (46700760274099/100000000000000 : ℝ)^4863 := by
    have hnat : (666427041 : ℕ)^5887*100000000000000^4863 ≤ 46700760274099^4863*1250000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      666427041 1250000000 46700760274099 100000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (203319797/400000000 : ℝ)^5887 ≤ (44079576336123/100000000000000 : ℝ)^4863 := by
    have hnat : (203319797 : ℕ)^5887*100000000000000^4863 ≤ 44079576336123^4863*400000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      203319797 400000000 44079576336123 100000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1395710041/10000000000 : ℝ)^5887 ≤ (4609831688897/50000000000000 : ℝ)^4863 := by
    have hnat : (1395710041 : ℕ)^5887*50000000000000^4863 ≤ 4609831688897^4863*10000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1395710041 10000000000 4609831688897 50000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5887/1024 : ℝ)) 5887 4863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(666427041/1250000000 : ℝ), (203319797/400000000 : ℝ), (-1395710041/10000000000 : ℝ)] ![(46700760274099/100000000000000 : ℝ), (44079576336123/100000000000000 : ℝ), (4609831688897/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(666427041/1250000000 : ℝ)|^5887 ≤ (46700760274099/100000000000000 : ℝ)^4863
        have hw : |(666427041/1250000000 : ℝ)|=(666427041/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(203319797/400000000 : ℝ)|^5887 ≤ (44079576336123/100000000000000 : ℝ)^4863
        have hw : |(203319797/400000000 : ℝ)|=(203319797/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1395710041/10000000000 : ℝ)|^5887 ≤ (4609831688897/50000000000000 : ℝ)^4863
        have hw : |(-1395710041/10000000000 : ℝ)|=(1395710041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1757_s2_3 (p : ℝ) (hpa : (5871/1024 : ℝ) ≤ p) (hpb : p ≤ (5887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2003286759/5000000000 : ℝ)*x 0 + (3353344859/10000000000 : ℝ)*x 1 + (2360661749/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2003286759/5000000000 : ℝ)^5887 ≤ (33046784413373/100000000000000 : ℝ)^4863 := by
    have hnat : (2003286759 : ℕ)^5887*100000000000000^4863 ≤ 33046784413373^4863*5000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2003286759 5000000000 33046784413373 100000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3353344859/10000000000 : ℝ)^5887 ≤ (26641480385741/100000000000000 : ℝ)^4863 := by
    have hnat : (3353344859 : ℕ)^5887*100000000000000^4863 ≤ 26641480385741^4863*10000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3353344859 10000000000 26641480385741 100000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2360661749/5000000000 : ℝ)^5887 ≤ (40311735178831/100000000000000 : ℝ)^4863 := by
    have hnat : (2360661749 : ℕ)^5887*100000000000000^4863 ≤ 40311735178831^4863*5000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2360661749 5000000000 40311735178831 100000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5887/1024 : ℝ)) 5887 4863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2003286759/5000000000 : ℝ), (3353344859/10000000000 : ℝ), (2360661749/5000000000 : ℝ)] ![(33046784413373/100000000000000 : ℝ), (26641480385741/100000000000000 : ℝ), (40311735178831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2003286759/5000000000 : ℝ)|^5887 ≤ (33046784413373/100000000000000 : ℝ)^4863
        have hw : |(2003286759/5000000000 : ℝ)|=(2003286759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3353344859/10000000000 : ℝ)|^5887 ≤ (26641480385741/100000000000000 : ℝ)^4863
        have hw : |(3353344859/10000000000 : ℝ)|=(3353344859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2360661749/5000000000 : ℝ)|^5887 ≤ (40311735178831/100000000000000 : ℝ)^4863
        have hw : |(2360661749/5000000000 : ℝ)|=(2360661749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1757_s2_4 (p : ℝ) (hpa : (5871/1024 : ℝ) ≤ p) (hpb : p ≤ (5887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1184556239/10000000000 : ℝ)*x 0 + (2544827071/5000000000 : ℝ)*x 1 + (1370243523/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1184556239/10000000000 : ℝ)^5887 ≤ (7559179685043/100000000000000 : ℝ)^4863 := by
    have hnat : (1184556239 : ℕ)^5887*100000000000000^4863 ≤ 7559179685043^4863*10000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1184556239 10000000000 7559179685043 100000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2544827071/5000000000 : ℝ)^5887 ≤ (5518686823231/12500000000000 : ℝ)^4863 := by
    have hnat : (2544827071 : ℕ)^5887*12500000000000^4863 ≤ 5518686823231^4863*5000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2544827071 5000000000 5518686823231 12500000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1370243523/2500000000 : ℝ)^5887 ≤ (12072831429313/25000000000000 : ℝ)^4863 := by
    have hnat : (1370243523 : ℕ)^5887*25000000000000^4863 ≤ 12072831429313^4863*2500000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1370243523 2500000000 12072831429313 25000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5887/1024 : ℝ)) 5887 4863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1184556239/10000000000 : ℝ), (2544827071/5000000000 : ℝ), (1370243523/2500000000 : ℝ)] ![(7559179685043/100000000000000 : ℝ), (5518686823231/12500000000000 : ℝ), (12072831429313/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1184556239/10000000000 : ℝ)|^5887 ≤ (7559179685043/100000000000000 : ℝ)^4863
        have hw : |(-1184556239/10000000000 : ℝ)|=(1184556239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2544827071/5000000000 : ℝ)|^5887 ≤ (5518686823231/12500000000000 : ℝ)^4863
        have hw : |(2544827071/5000000000 : ℝ)|=(2544827071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1370243523/2500000000 : ℝ)|^5887 ≤ (12072831429313/25000000000000 : ℝ)^4863
        have hw : |(1370243523/2500000000 : ℝ)|=(1370243523/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1757_s2_5 (p : ℝ) (hpa : (5871/1024 : ℝ) ≤ p) (hpb : p ≤ (5887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5224338463/10000000000 : ℝ)*x 0 + (-199546163/2000000000 : ℝ)*x 1 + (5480974179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5224338463/10000000000 : ℝ)^5887 ≤ (22783858372749/50000000000000 : ℝ)^4863 := by
    have hnat : (5224338463 : ℕ)^5887*50000000000000^4863 ≤ 22783858372749^4863*10000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5224338463 10000000000 22783858372749 50000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (199546163/2000000000 : ℝ)^5887 ≤ (1535239147559/25000000000000 : ℝ)^4863 := by
    have hnat : (199546163 : ℕ)^5887*25000000000000^4863 ≤ 1535239147559^4863*2000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      199546163 2000000000 1535239147559 25000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5480974179/10000000000 : ℝ)^5887 ≤ (48291326645193/100000000000000 : ℝ)^4863 := by
    have hnat : (5480974179 : ℕ)^5887*100000000000000^4863 ≤ 48291326645193^4863*10000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5480974179 10000000000 48291326645193 100000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5887/1024 : ℝ)) 5887 4863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5224338463/10000000000 : ℝ), (-199546163/2000000000 : ℝ), (5480974179/10000000000 : ℝ)] ![(22783858372749/50000000000000 : ℝ), (1535239147559/25000000000000 : ℝ), (48291326645193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5224338463/10000000000 : ℝ)|^5887 ≤ (22783858372749/50000000000000 : ℝ)^4863
        have hw : |(5224338463/10000000000 : ℝ)|=(5224338463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-199546163/2000000000 : ℝ)|^5887 ≤ (1535239147559/25000000000000 : ℝ)^4863
        have hw : |(-199546163/2000000000 : ℝ)|=(199546163/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5480974179/10000000000 : ℝ)|^5887 ≤ (48291326645193/100000000000000 : ℝ)^4863
        have hw : |(5480974179/10000000000 : ℝ)|=(5480974179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1757_s2_6 (p : ℝ) (hpa : (5871/1024 : ℝ) ≤ p) (hpb : p ≤ (5887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2612169253/5000000000 : ℝ)*x 0 + (5480974167/10000000000 : ℝ)*x 1 + (-249432693/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2612169253/5000000000 : ℝ)^5887 ≤ (5695964649941/12500000000000 : ℝ)^4863 := by
    have hnat : (2612169253 : ℕ)^5887*12500000000000^4863 ≤ 5695964649941^4863*5000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2612169253 5000000000 5695964649941 12500000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5480974167/10000000000 : ℝ)^5887 ≤ (48291326517201/100000000000000 : ℝ)^4863 := by
    have hnat : (5480974167 : ℕ)^5887*100000000000000^4863 ≤ 48291326517201^4863*10000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5480974167 10000000000 48291326517201 100000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (249432693/2500000000 : ℝ)^5887 ≤ (1228191253969/20000000000000 : ℝ)^4863 := by
    have hnat : (249432693 : ℕ)^5887*20000000000000^4863 ≤ 1228191253969^4863*2500000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249432693 2500000000 1228191253969 20000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5887/1024 : ℝ)) 5887 4863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2612169253/5000000000 : ℝ), (5480974167/10000000000 : ℝ), (-249432693/2500000000 : ℝ)] ![(5695964649941/12500000000000 : ℝ), (48291326517201/100000000000000 : ℝ), (1228191253969/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2612169253/5000000000 : ℝ)|^5887 ≤ (5695964649941/12500000000000 : ℝ)^4863
        have hw : |(2612169253/5000000000 : ℝ)|=(2612169253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5480974167/10000000000 : ℝ)|^5887 ≤ (48291326517201/100000000000000 : ℝ)^4863
        have hw : |(5480974167/10000000000 : ℝ)|=(5480974167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-249432693/2500000000 : ℝ)|^5887 ≤ (1228191253969/20000000000000 : ℝ)^4863
        have hw : |(-249432693/2500000000 : ℝ)|=(249432693/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1757_s2_7 (p : ℝ) (hpa : (5871/1024 : ℝ) ≤ p) (hpb : p ≤ (5887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4007712107/10000000000 : ℝ)*x 0 + (293676141/625000000 : ℝ)*x 1 + (3376320461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4007712107/10000000000 : ℝ)^5887 ≤ (16529076753381/50000000000000 : ℝ)^4863 := by
    have hnat : (4007712107 : ℕ)^5887*50000000000000^4863 ≤ 16529076753381^4863*10000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4007712107 10000000000 16529076753381 50000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (293676141/625000000 : ℝ)^5887 ≤ (20039617604243/50000000000000 : ℝ)^4863 := by
    have hnat : (293676141 : ℕ)^5887*50000000000000^4863 ≤ 20039617604243^4863*625000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      293676141 625000000 20039617604243 50000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3376320461/10000000000 : ℝ)^5887 ≤ (5372522254683/20000000000000 : ℝ)^4863 := by
    have hnat : (3376320461 : ℕ)^5887*20000000000000^4863 ≤ 5372522254683^4863*10000000000^5887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3376320461 10000000000 5372522254683 20000000000000 5887 4863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5887/1024 : ℝ)) 5887 4863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4007712107/10000000000 : ℝ), (293676141/625000000 : ℝ), (3376320461/10000000000 : ℝ)] ![(16529076753381/50000000000000 : ℝ), (20039617604243/50000000000000 : ℝ), (5372522254683/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4007712107/10000000000 : ℝ)|^5887 ≤ (16529076753381/50000000000000 : ℝ)^4863
        have hw : |(4007712107/10000000000 : ℝ)|=(4007712107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(293676141/625000000 : ℝ)|^5887 ≤ (20039617604243/50000000000000 : ℝ)^4863
        have hw : |(293676141/625000000 : ℝ)|=(293676141/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3376320461/10000000000 : ℝ)|^5887 ≤ (5372522254683/20000000000000 : ℝ)^4863
        have hw : |(3376320461/10000000000 : ℝ)|=(3376320461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1757_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5871/1024 : ℝ) ≤ p) (hpb : p ≤ (5887/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (218979081/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4473/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9081/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9123/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (223/1250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4473/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9081/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4473/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9081/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4473/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9081/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4473/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9081/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4473/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9081/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4473/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9081/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9081/100000 : ℝ) ^ (5871/1024 : ℝ) ≤ (53153913873817/50000000000000000000 : ℝ) := by
    have hpowers : (9081/100000 : ℝ)^5871 ≤ (53153913873817/50000000000000000000 : ℝ)^1024 := by
      have hnat : (9081 : ℕ)^5871*50000000000000000000^1024 ≤ 53153913873817^1024*100000^5871 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9081 100000 53153913873817 50000000000000000000 5871 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9081/100000 : ℝ)) (X := (53153913873817/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5871 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4473/25000 : ℝ) ^ (5871/1024 : ℝ) ≤ (5190338051666111/100000000000000000000 : ℝ) := by
    have hpowers : (4473/25000 : ℝ)^5871 ≤ (5190338051666111/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4473 : ℕ)^5871*100000000000000000000^1024 ≤ 5190338051666111^1024*25000^5871 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4473 25000 5190338051666111 100000000000000000000 5871 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4473/25000 : ℝ)) (X := (5190338051666111/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5871 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000053153913873817/25000000000000000000 : ℝ) ≤ (78125028971619/78125000000000 : ℝ) ^ (5871/1024 : ℝ) := by
    have hpowers : (25000053153913873817/25000000000000000000 : ℝ)^1024 ≤ (78125028971619/78125000000000 : ℝ)^5871 := by
      have hnat : (25000053153913873817 : ℕ)^1024*78125000000000^5871 ≤ 78125028971619^5871*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000053153913873817 25000000000000000000 78125028971619 78125000000000 1024 5871 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (78125028971619/78125000000000 : ℝ)) (X := (25000053153913873817/25000000000000000000 : ℝ)) (by norm_num) 5871 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20001059329175882749/20000000000000000000 : ℝ) ≤ (5000046190144767/5000000000000000 : ℝ) ^ (5871/1024 : ℝ) := by
    have hpowers : (20001059329175882749/20000000000000000000 : ℝ)^1024 ≤ (5000046190144767/5000000000000000 : ℝ)^5871 := by
      have hnat : (20001059329175882749 : ℕ)^1024*5000000000000000^5871 ≤ 5000046190144767^5871*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20001059329175882749 20000000000000000000 5000046190144767 5000000000000000 1024 5871 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000046190144767/5000000000000000 : ℝ)) (X := (20001059329175882749/20000000000000000000 : ℝ)) (by norm_num) 5871 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50005190338051666111/50000000000000000000 : ℝ) ≤ (2500045263052959/2500000000000000 : ℝ) ^ (5871/1024 : ℝ) := by
    have hpowers : (50005190338051666111/50000000000000000000 : ℝ)^1024 ≤ (2500045263052959/2500000000000000 : ℝ)^5871 := by
      have hnat : (50005190338051666111 : ℕ)^1024*2500000000000000^5871 ≤ 2500045263052959^5871*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005190338051666111 50000000000000000000 2500045263052959 2500000000000000 1024 5871 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500045263052959/2500000000000000 : ℝ)) (X := (50005190338051666111/50000000000000000000 : ℝ)) (by norm_num) 5871 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(53153913873817/50000000000000000000 : ℝ) ≤ ((2447456172638078673/2447500000000000000 : ℝ)+2*(14778653717/146850000000000 : ℝ)*(9081/100000 : ℝ))^(5871/1024 : ℝ) := by
    rw [show (2447456172638078673/2447500000000000000 : ℝ)+2*(14778653717/146850000000000 : ℝ)*(9081/100000 : ℝ)=(78125028971619/78125000000000 : ℝ) by norm_num, show 1+2*(53153913873817/50000000000000000000 : ℝ)=(25000053153913873817/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5190338051666111/100000000000000000000 : ℝ)+(53153913873817/50000000000000000000 : ℝ) ≤ ((2447456172638078673/2447500000000000000 : ℝ)+(14778653717/146850000000000 : ℝ)*((4473/25000 : ℝ)+(9081/100000 : ℝ)))^(5871/1024 : ℝ) := by
    rw [show (2447456172638078673/2447500000000000000 : ℝ)+(14778653717/146850000000000 : ℝ)*((4473/25000 : ℝ)+(9081/100000 : ℝ))=(5000046190144767/5000000000000000 : ℝ) by norm_num, show 1+(5190338051666111/100000000000000000000 : ℝ)+(53153913873817/50000000000000000000 : ℝ)=(20001059329175882749/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5190338051666111/100000000000000000000 : ℝ) ≤ ((2447456172638078673/2447500000000000000 : ℝ)+2*(14778653717/146850000000000 : ℝ)*(4473/25000 : ℝ))^(5871/1024 : ℝ) := by
    rw [show (2447456172638078673/2447500000000000000 : ℝ)+2*(14778653717/146850000000000 : ℝ)*(4473/25000 : ℝ)=(2500045263052959/2500000000000000 : ℝ) by norm_num, show 1+2*(5190338051666111/100000000000000000000 : ℝ)=(50005190338051666111/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2447456172638078673/2447500000000000000 : ℝ)*(X 1 0+X 2 0)+(14778653717/146850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5871/1024 : ℝ)) (lo := (9081/100000 : ℝ)) (hi := (4473/25000 : ℝ)) (c := (2447456172638078673/2447500000000000000 : ℝ)) (alpha := (14778653717/146850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2447456172638078673/2447500000000000000 : ℝ)*(X 0 1+X 2 1)+(14778653717/146850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5871/1024 : ℝ)) (lo := (9081/100000 : ℝ)) (hi := (4473/25000 : ℝ)) (c := (2447456172638078673/2447500000000000000 : ℝ)) (alpha := (14778653717/146850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2447456172638078673/2447500000000000000 : ℝ)*(X 0 2+X 1 2)+(14778653717/146850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5871/1024 : ℝ)) (lo := (9081/100000 : ℝ)) (hi := (4473/25000 : ℝ)) (c := (2447456172638078673/2447500000000000000 : ℝ)) (alpha := (14778653717/146850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-592109681/5000000000 : ℝ)*X 0 0+(137194311/250000000 : ℝ)*X 0 1+(317687183/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1757_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5331416327/10000000000 : ℝ)*X 1 0+(-1395710039/10000000000 : ℝ)*X 1 1+(317687183/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1757_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((666427041/1250000000 : ℝ)*X 2 0+(203319797/400000000 : ℝ)*X 2 1+(-1395710041/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1757_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2003286759/5000000000 : ℝ)*X 0 0+(3353344859/10000000000 : ℝ)*X 0 1+(2360661749/5000000000 : ℝ)*X 0 2+(2003286759/5000000000 : ℝ)*X 1 0+(3353344859/10000000000 : ℝ)*X 1 1+(2360661749/5000000000 : ℝ)*X 1 2+(2003286759/5000000000 : ℝ)*X 2 0+(3353344859/10000000000 : ℝ)*X 2 1+(2360661749/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1757_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1184556239/10000000000 : ℝ)*X 0 0+(2544827071/5000000000 : ℝ)*X 0 1+(1370243523/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1757_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5224338463/10000000000 : ℝ)*X 1 0+(-199546163/2000000000 : ℝ)*X 1 1+(5480974179/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1757_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2612169253/5000000000 : ℝ)*X 2 0+(5480974167/10000000000 : ℝ)*X 2 1+(-249432693/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1757_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4007712107/10000000000 : ℝ)*X 0 0+(293676141/625000000 : ℝ)*X 0 1+(3376320461/10000000000 : ℝ)*X 0 2+(4007712107/10000000000 : ℝ)*X 1 0+(293676141/625000000 : ℝ)*X 1 1+(3376320461/10000000000 : ℝ)*X 1 2+(4007712107/10000000000 : ℝ)*X 2 0+(293676141/625000000 : ℝ)*X 2 1+(3376320461/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1757_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2655401876396121869884657/305937500000000000000000000000 : ℝ) := by norm_num
    linear_combination (587846567/50000000000000 : ℝ)*(base19) + (554844327/50000000000000 : ℝ)*(base23) + (35436787/100000000000000 : ℝ)*(lower2) + (104172489/50000000000000 : ℝ)*(upper3) + (6400541/4000000000000 : ℝ)*(upper5) + (8003807699681/500000000000 : ℝ)*(major0) + (8003807699681/500000000000 : ℝ)*(major1) + (8003807699681/500000000000 : ℝ)*(major2) + (77203197843589/3125000000000 : ℝ)*(sp0) + (123525522291833/5000000000000 : ℝ)*(sp1) + (1235255255920571/50000000000000 : ℝ)*(sp2) + (91376022107553/12500000000000 : ℝ)*(sp3) + (9290534947/100000000000000 : ℝ)*(sp4) + (93505113/3125000000000 : ℝ)*(sp7) + (18275279225601/2500000000000 : ℝ)*(f.failure) + (494102324305959/20000000000000 : ℝ)*(f.sum) + (775138370207/587400000000000000000000000 : ℝ)*base66 + (1067848802542561/3671250000000000000000000000000 : ℝ)*base68 + (19369730123205061/3671250000000000000000000000000 : ℝ)*base70 + (23164696250024939/3671250000000000000000000000000 : ℝ)*base71 + (202354902751/734250000000000000000000000 : ℝ)*base74 + (29859028824239939/3671250000000000000000000000000 : ℝ)*base75 + (26403855857940061/3671250000000000000000000000000 : ℝ)*base78 + (31030809850507561/3671250000000000000000000000000 : ℝ)*base80 + (1149502363781/1468500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (1347319/250000000000000000000 : ℝ)*base90 + (1347319/250000000000000000000 : ℝ)*base92 + (1347319/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4245752302786544433717/979000000000000000000000000 : ℝ) := by norm_num
    linear_combination (100699299/20000000000000 : ℝ)*(base19) + (587068143/100000000000000 : ℝ)*(base23) + (2511139/1562500000000 : ℝ)*(lower1) + (89050879/100000000000000 : ℝ)*(upper3) + (24789747/100000000000000 : ℝ)*(lower4) + (20186513/25000000000000 : ℝ)*(upper5) + (165579652573311/10000000000000 : ℝ)*(major0) + (165579652573311/10000000000000 : ℝ)*(major1) + (165579652573311/10000000000000 : ℝ)*(major2) + (368072601/50000000000000 : ℝ)*(sp2) + (79857787709603/3125000000000 : ℝ)*(sp4) + (2555448703210801/100000000000000 : ℝ)*(sp5) + (39928873179593/1562500000000 : ℝ)*(sp6) + (378071850099031/50000000000000 : ℝ)*(sp7) + (378071850099031/50000000000000 : ℝ)*(f.failure) + (79857787709603/3125000000000 : ℝ)*(f.sum) + (1004101347003/489500000000000000000000000 : ℝ)*base65 + (11701421215853697/24475000000000000000000000000000 : ℝ)*base68 + (76502026536896303/24475000000000000000000000000000 : ℝ)*base69 + (321363297645471303/24475000000000000000000000000000 : ℝ)*base71 + (3563452899487/979000000000000000000000000 : ℝ)*base74 + (255866277239071303/24475000000000000000000000000000 : ℝ)*base75 + (63188761549403697/24475000000000000000000000000000 : ℝ)*base78 + (236230611919803697/24475000000000000000000000000000 : ℝ)*base80 + (529698462151/122375000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (67370511/5000000000000000000000 : ℝ)*base89 + (67370511/5000000000000000000000 : ℝ)*base91 + (67370511/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1757_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5871/1024 : ℝ) ≤ p) (hpb : p ≤ (5887/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (218979081/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4473/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9081/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9123/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (223/1250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1757_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1757_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5871/1024 : ℝ) ≤ p) (hpb : p ≤ (5887/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (218979081/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9123/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (223/1250 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1757_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1757_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1757_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5871/1024 : ℝ) ≤ p) (hpb : p ≤ (5887/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (218979081/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9123/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (223/1250 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1757_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
