-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1402_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:46:05.388034+00:00
-- url     : https://prove2.me/submissions/46fd5796-0907-446c-a8af-22eed9028c2c

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
theorem support_rectangle_w1402_s6_0 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1993246363/10000000000 : ℝ)*x 0 + (1352404913/2500000000 : ℝ)*x 1 + (5246264451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1993246363/10000000000 : ℝ)^2181 ≤ (12153096241693/100000000000000 : ℝ)^1669 := by
    have hnat : (1993246363 : ℕ)^2181*100000000000000^1669 ≤ 12153096241693^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1993246363 10000000000 12153096241693 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352404913/2500000000 : ℝ)^2181 ≤ (44803315152361/100000000000000 : ℝ)^1669 := by
    have hnat : (1352404913 : ℕ)^2181*100000000000000^1669 ≤ 44803315152361^1669*2500000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352404913 2500000000 44803315152361 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246264451/10000000000 : ℝ)^2181 ≤ (43043588586067/100000000000000 : ℝ)^1669 := by
    have hnat : (5246264451 : ℕ)^2181*100000000000000^1669 ≤ 43043588586067^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246264451 10000000000 43043588586067 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1993246363/10000000000 : ℝ), (1352404913/2500000000 : ℝ), (5246264451/10000000000 : ℝ)] ![(12153096241693/100000000000000 : ℝ), (44803315152361/100000000000000 : ℝ), (43043588586067/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1993246363/10000000000 : ℝ)|^2181 ≤ (12153096241693/100000000000000 : ℝ)^1669
        have hw : |(-1993246363/10000000000 : ℝ)|=(1993246363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352404913/2500000000 : ℝ)|^2181 ≤ (44803315152361/100000000000000 : ℝ)^1669
        have hw : |(1352404913/2500000000 : ℝ)|=(1352404913/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246264451/10000000000 : ℝ)|^2181 ≤ (43043588586067/100000000000000 : ℝ)^1669
        have hw : |(5246264451/10000000000 : ℝ)|=(5246264451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_s6_1 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (668485427/1250000000 : ℝ)*x 0 + (-2076432249/10000000000 : ℝ)*x 1 + (1049252891/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668485427/1250000000 : ℝ)^2181 ≤ (2206816206569/5000000000000 : ℝ)^1669 := by
    have hnat : (668485427 : ℕ)^2181*5000000000000^1669 ≤ 2206816206569^1669*1250000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668485427 1250000000 2206816206569 5000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2076432249/10000000000 : ℝ)^2181 ≤ (512803489269/4000000000000 : ℝ)^1669 := by
    have hnat : (2076432249 : ℕ)^2181*4000000000000^1669 ≤ 512803489269^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2076432249 10000000000 512803489269 4000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1049252891/2000000000 : ℝ)^2181 ≤ (43043588628953/100000000000000 : ℝ)^1669 := by
    have hnat : (1049252891 : ℕ)^2181*100000000000000^1669 ≤ 43043588628953^1669*2000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049252891 2000000000 43043588628953 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668485427/1250000000 : ℝ), (-2076432249/10000000000 : ℝ), (1049252891/2000000000 : ℝ)] ![(2206816206569/5000000000000 : ℝ), (512803489269/4000000000000 : ℝ), (43043588628953/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668485427/1250000000 : ℝ)|^2181 ≤ (2206816206569/5000000000000 : ℝ)^1669
        have hw : |(668485427/1250000000 : ℝ)|=(668485427/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2076432249/10000000000 : ℝ)|^2181 ≤ (512803489269/4000000000000 : ℝ)^1669
        have hw : |(-2076432249/10000000000 : ℝ)|=(2076432249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1049252891/2000000000 : ℝ)|^2181 ≤ (43043588628953/100000000000000 : ℝ)^1669
        have hw : |(1049252891/2000000000 : ℝ)|=(1049252891/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_s6_2 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5347883371/10000000000 : ℝ)*x 0 + (5246264483/10000000000 : ℝ)*x 1 + (-207643227/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347883371/10000000000 : ℝ)^2181 ≤ (44136323646063/100000000000000 : ℝ)^1669 := by
    have hnat : (5347883371 : ℕ)^2181*100000000000000^1669 ≤ 44136323646063^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347883371 10000000000 44136323646063 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246264483/10000000000 : ℝ)^2181 ≤ (43043588929157/100000000000000 : ℝ)^1669 := by
    have hnat : (5246264483 : ℕ)^2181*100000000000000^1669 ≤ 43043588929157^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246264483 10000000000 43043588929157 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (207643227/1000000000 : ℝ)^2181 ≤ (3205021850289/25000000000000 : ℝ)^1669 := by
    have hnat : (207643227 : ℕ)^2181*25000000000000^1669 ≤ 3205021850289^1669*1000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207643227 1000000000 3205021850289 25000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347883371/10000000000 : ℝ), (5246264483/10000000000 : ℝ), (-207643227/1000000000 : ℝ)] ![(44136323646063/100000000000000 : ℝ), (43043588929157/100000000000000 : ℝ), (3205021850289/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347883371/10000000000 : ℝ)|^2181 ≤ (44136323646063/100000000000000 : ℝ)^1669
        have hw : |(5347883371/10000000000 : ℝ)|=(5347883371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246264483/10000000000 : ℝ)|^2181 ≤ (43043588929157/100000000000000 : ℝ)^1669
        have hw : |(5246264483/10000000000 : ℝ)|=(5246264483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-207643227/1000000000 : ℝ)|^2181 ≤ (3205021850289/25000000000000 : ℝ)^1669
        have hw : |(-207643227/1000000000 : ℝ)|=(207643227/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_s6_3 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2155585387/5000000000 : ℝ)*x 0 + (4139451997/10000000000 : ℝ)*x 1 + (4489351051/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2155585387/5000000000 : ℝ)^2181 ≤ (33304261936909/100000000000000 : ℝ)^1669 := by
    have hnat : (2155585387 : ℕ)^2181*100000000000000^1669 ≤ 33304261936909^1669*5000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155585387 5000000000 33304261936909 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4139451997/10000000000 : ℝ)^2181 ≤ (246730159593/781250000000 : ℝ)^1669 := by
    have hnat : (4139451997 : ℕ)^2181*781250000000^1669 ≤ 246730159593^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4139451997 10000000000 246730159593 781250000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4489351051/10000000000 : ℝ)^2181 ≤ (35114277627911/100000000000000 : ℝ)^1669 := by
    have hnat : (4489351051 : ℕ)^2181*100000000000000^1669 ≤ 35114277627911^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4489351051 10000000000 35114277627911 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2155585387/5000000000 : ℝ), (4139451997/10000000000 : ℝ), (4489351051/10000000000 : ℝ)] ![(33304261936909/100000000000000 : ℝ), (246730159593/781250000000 : ℝ), (35114277627911/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2155585387/5000000000 : ℝ)|^2181 ≤ (33304261936909/100000000000000 : ℝ)^1669
        have hw : |(2155585387/5000000000 : ℝ)|=(2155585387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4139451997/10000000000 : ℝ)|^2181 ≤ (246730159593/781250000000 : ℝ)^1669
        have hw : |(4139451997/10000000000 : ℝ)|=(4139451997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4489351051/10000000000 : ℝ)|^2181 ≤ (35114277627911/100000000000000 : ℝ)^1669
        have hw : |(4489351051/10000000000 : ℝ)|=(4489351051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_s6_4 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-398651583/2000000000 : ℝ)*x 0 + (2623426151/5000000000 : ℝ)*x 1 + (5409028781/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (398651583/2000000000 : ℝ)^2181 ≤ (1519148535377/12500000000000 : ℝ)^1669 := by
    have hnat : (398651583 : ℕ)^2181*12500000000000^1669 ≤ 1519148535377^1669*2000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      398651583 2000000000 1519148535377 12500000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623426151/5000000000 : ℝ)^2181 ≤ (21524945684479/50000000000000 : ℝ)^1669 := by
    have hnat : (2623426151 : ℕ)^2181*50000000000000^1669 ≤ 21524945684479^1669*5000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623426151 5000000000 21524945684479 50000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5409028781/10000000000 : ℝ)^2181 ≤ (349975940117/781250000000 : ℝ)^1669 := by
    have hnat : (5409028781 : ℕ)^2181*781250000000^1669 ≤ 349975940117^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409028781 10000000000 349975940117 781250000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-398651583/2000000000 : ℝ), (2623426151/5000000000 : ℝ), (5409028781/10000000000 : ℝ)] ![(1519148535377/12500000000000 : ℝ), (21524945684479/50000000000000 : ℝ), (349975940117/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-398651583/2000000000 : ℝ)|^2181 ≤ (1519148535377/12500000000000 : ℝ)^1669
        have hw : |(-398651583/2000000000 : ℝ)|=(398651583/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623426151/5000000000 : ℝ)|^2181 ≤ (21524945684479/50000000000000 : ℝ)^1669
        have hw : |(2623426151/5000000000 : ℝ)|=(2623426151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5409028781/10000000000 : ℝ)|^2181 ≤ (349975940117/781250000000 : ℝ)^1669
        have hw : |(5409028781/10000000000 : ℝ)|=(5409028781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_s6_5 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305530457/10000000000 : ℝ)*x 0 + (-1913667913/10000000000 : ℝ)*x 1 + (676128597/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305530457/10000000000 : ℝ)^2181 ≤ (43680110278961/100000000000000 : ℝ)^1669 := by
    have hnat : (5305530457 : ℕ)^2181*100000000000000^1669 ≤ 43680110278961^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305530457 10000000000 43680110278961 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1913667913/10000000000 : ℝ)^2181 ≤ (11522969433859/100000000000000 : ℝ)^1669 := by
    have hnat : (1913667913 : ℕ)^2181*100000000000000^1669 ≤ 11522969433859^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1913667913 10000000000 11522969433859 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676128597/1250000000 : ℝ)^2181 ≤ (1399903758777/3125000000000 : ℝ)^1669 := by
    have hnat : (676128597 : ℕ)^2181*3125000000000^1669 ≤ 1399903758777^1669*1250000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676128597 1250000000 1399903758777 3125000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305530457/10000000000 : ℝ), (-1913667913/10000000000 : ℝ), (676128597/1250000000 : ℝ)] ![(43680110278961/100000000000000 : ℝ), (11522969433859/100000000000000 : ℝ), (1399903758777/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305530457/10000000000 : ℝ)|^2181 ≤ (43680110278961/100000000000000 : ℝ)^1669
        have hw : |(5305530457/10000000000 : ℝ)|=(5305530457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1913667913/10000000000 : ℝ)|^2181 ≤ (11522969433859/100000000000000 : ℝ)^1669
        have hw : |(-1913667913/10000000000 : ℝ)|=(1913667913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(676128597/1250000000 : ℝ)|^2181 ≤ (1399903758777/3125000000000 : ℝ)^1669
        have hw : |(676128597/1250000000 : ℝ)|=(676128597/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_s6_6 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (265276521/500000000 : ℝ)*x 0 + (1352257201/2500000000 : ℝ)*x 1 + (-478416981/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265276521/500000000 : ℝ)^2181 ≤ (21840054940447/50000000000000 : ℝ)^1669 := by
    have hnat : (265276521 : ℕ)^2181*50000000000000^1669 ≤ 21840054940447^1669*500000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265276521 500000000 21840054940447 50000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352257201/2500000000 : ℝ)^2181 ≤ (22398460291947/50000000000000 : ℝ)^1669 := by
    have hnat : (1352257201 : ℕ)^2181*50000000000000^1669 ≤ 22398460291947^1669*2500000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352257201 2500000000 22398460291947 50000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (478416981/2500000000 : ℝ)^2181 ≤ (11522969520413/100000000000000 : ℝ)^1669 := by
    have hnat : (478416981 : ℕ)^2181*100000000000000^1669 ≤ 11522969520413^1669*2500000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      478416981 2500000000 11522969520413 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265276521/500000000 : ℝ), (1352257201/2500000000 : ℝ), (-478416981/2500000000 : ℝ)] ![(21840054940447/50000000000000 : ℝ), (22398460291947/50000000000000 : ℝ), (11522969520413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265276521/500000000 : ℝ)|^2181 ≤ (21840054940447/50000000000000 : ℝ)^1669
        have hw : |(265276521/500000000 : ℝ)|=(265276521/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352257201/2500000000 : ℝ)|^2181 ≤ (22398460291947/50000000000000 : ℝ)^1669
        have hw : |(1352257201/2500000000 : ℝ)|=(1352257201/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-478416981/2500000000 : ℝ)|^2181 ≤ (11522969520413/100000000000000 : ℝ)^1669
        have hw : |(-478416981/2500000000 : ℝ)|=(478416981/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_s6_7 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4311195579/10000000000 : ℝ)*x 0 + (2244045969/5000000000 : ℝ)*x 1 + (828143523/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4311195579/10000000000 : ℝ)^2181 ≤ (33304512342217/100000000000000 : ℝ)^1669 := by
    have hnat : (4311195579 : ℕ)^2181*100000000000000^1669 ≤ 33304512342217^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4311195579 10000000000 33304512342217 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2244045969/5000000000 : ℝ)^2181 ≤ (17550704303247/50000000000000 : ℝ)^1669 := by
    have hnat : (2244045969 : ℕ)^2181*50000000000000^1669 ≤ 17550704303247^1669*5000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2244045969 5000000000 17550704303247 50000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (828143523/2000000000 : ℝ)^2181 ≤ (31594079043063/100000000000000 : ℝ)^1669 := by
    have hnat : (828143523 : ℕ)^2181*100000000000000^1669 ≤ 31594079043063^1669*2000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      828143523 2000000000 31594079043063 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4311195579/10000000000 : ℝ), (2244045969/5000000000 : ℝ), (828143523/2000000000 : ℝ)] ![(33304512342217/100000000000000 : ℝ), (17550704303247/50000000000000 : ℝ), (31594079043063/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4311195579/10000000000 : ℝ)|^2181 ≤ (33304512342217/100000000000000 : ℝ)^1669
        have hw : |(4311195579/10000000000 : ℝ)|=(4311195579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2244045969/5000000000 : ℝ)|^2181 ≤ (17550704303247/50000000000000 : ℝ)^1669
        have hw : |(2244045969/5000000000 : ℝ)|=(2244045969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(828143523/2000000000 : ℝ)|^2181 ≤ (31594079043063/100000000000000 : ℝ)^1669
        have hw : |(828143523/2000000000 : ℝ)|=(828143523/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1402_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157097619/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3687/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11279/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11283/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14743/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3687/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11279/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3687/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11279/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3687/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11279/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3687/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11279/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3687/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11279/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3687/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11279/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11279/100000 : ℝ) ^ (4361/1024 : ℝ) ≤ (4600344837103613/50000000000000000000 : ℝ) := by
    have hpowers : (11279/100000 : ℝ)^4361 ≤ (4600344837103613/50000000000000000000 : ℝ)^1024 := by
      have hnat : (11279 : ℕ)^4361*50000000000000000000^1024 ≤ 4600344837103613^1024*100000^4361 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11279 100000 4600344837103613 50000000000000000000 4361 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11279/100000 : ℝ)) (X := (4600344837103613/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4361 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3687/25000 : ℝ) ^ (4361/1024 : ℝ) ≤ (28827683248054547/100000000000000000000 : ℝ) := by
    have hpowers : (3687/25000 : ℝ)^4361 ≤ (28827683248054547/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3687 : ℕ)^4361*100000000000000000000^1024 ≤ 28827683248054547^1024*25000^4361 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3687 25000 28827683248054547 100000000000000000000 4361 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3687/25000 : ℝ)) (X := (28827683248054547/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4361 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004600344837103613/25000000000000000000 : ℝ) ≤ (5000216024833683/5000000000000000 : ℝ) ^ (4361/1024 : ℝ) := by
    have hpowers : (25004600344837103613/25000000000000000000 : ℝ)^1024 ≤ (5000216024833683/5000000000000000 : ℝ)^4361 := by
      have hnat : (25004600344837103613 : ℕ)^1024*5000000000000000^4361 ≤ 5000216024833683^4361*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004600344837103613 25000000000000000000 5000216024833683 5000000000000000 1024 4361 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000216024833683/5000000000000000 : ℝ)) (X := (25004600344837103613/25000000000000000000 : ℝ)) (by norm_num) 4361 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100038028372922261773/100000000000000000000 : ℝ) ≤ (10000892808746017/10000000000000000 : ℝ) ^ (4361/1024 : ℝ) := by
    have hpowers : (100038028372922261773/100000000000000000000 : ℝ)^1024 ≤ (10000892808746017/10000000000000000 : ℝ)^4361 := by
      have hnat : (100038028372922261773 : ℕ)^1024*10000000000000000^4361 ≤ 10000892808746017^4361*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100038028372922261773 100000000000000000000 10000892808746017 10000000000000000 1024 4361 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000892808746017/10000000000000000 : ℝ)) (X := (100038028372922261773/100000000000000000000 : ℝ)) (by norm_num) 4361 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50028827683248054547/50000000000000000000 : ℝ) ≤ (2500338391956167/2500000000000000 : ℝ) ^ (4361/1024 : ℝ) := by
    have hpowers : (50028827683248054547/50000000000000000000 : ℝ)^1024 ≤ (2500338391956167/2500000000000000 : ℝ)^4361 := by
      have hnat : (50028827683248054547 : ℕ)^1024*2500000000000000^4361 ≤ 2500338391956167^4361*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028827683248054547 50000000000000000000 2500338391956167 2500000000000000 1024 4361 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500338391956167/2500000000000000 : ℝ)) (X := (50028827683248054547/50000000000000000000 : ℝ)) (by norm_num) 4361 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4600344837103613/50000000000000000000 : ℝ) ≤ ((8670276244249970849/8672500000000000000 : ℝ)+2*(460759078651/346900000000000 : ℝ)*(11279/100000 : ℝ))^(4361/1024 : ℝ) := by
    rw [show (8670276244249970849/8672500000000000000 : ℝ)+2*(460759078651/346900000000000 : ℝ)*(11279/100000 : ℝ)=(5000216024833683/5000000000000000 : ℝ) by norm_num, show 1+2*(4600344837103613/50000000000000000000 : ℝ)=(25004600344837103613/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(28827683248054547/100000000000000000000 : ℝ)+(4600344837103613/50000000000000000000 : ℝ) ≤ ((8670276244249970849/8672500000000000000 : ℝ)+(460759078651/346900000000000 : ℝ)*((3687/25000 : ℝ)+(11279/100000 : ℝ)))^(4361/1024 : ℝ) := by
    rw [show (8670276244249970849/8672500000000000000 : ℝ)+(460759078651/346900000000000 : ℝ)*((3687/25000 : ℝ)+(11279/100000 : ℝ))=(10000892808746017/10000000000000000 : ℝ) by norm_num, show 1+(28827683248054547/100000000000000000000 : ℝ)+(4600344837103613/50000000000000000000 : ℝ)=(100038028372922261773/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(28827683248054547/100000000000000000000 : ℝ) ≤ ((8670276244249970849/8672500000000000000 : ℝ)+2*(460759078651/346900000000000 : ℝ)*(3687/25000 : ℝ))^(4361/1024 : ℝ) := by
    rw [show (8670276244249970849/8672500000000000000 : ℝ)+2*(460759078651/346900000000000 : ℝ)*(3687/25000 : ℝ)=(2500338391956167/2500000000000000 : ℝ) by norm_num, show 1+2*(28827683248054547/100000000000000000000 : ℝ)=(50028827683248054547/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8670276244249970849/8672500000000000000 : ℝ)*(X 1 0+X 2 0)+(460759078651/346900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4361/1024 : ℝ)) (lo := (11279/100000 : ℝ)) (hi := (3687/25000 : ℝ)) (c := (8670276244249970849/8672500000000000000 : ℝ)) (alpha := (460759078651/346900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8670276244249970849/8672500000000000000 : ℝ)*(X 0 1+X 2 1)+(460759078651/346900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4361/1024 : ℝ)) (lo := (11279/100000 : ℝ)) (hi := (3687/25000 : ℝ)) (c := (8670276244249970849/8672500000000000000 : ℝ)) (alpha := (460759078651/346900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8670276244249970849/8672500000000000000 : ℝ)*(X 0 2+X 1 2)+(460759078651/346900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4361/1024 : ℝ)) (lo := (11279/100000 : ℝ)) (hi := (3687/25000 : ℝ)) (c := (8670276244249970849/8672500000000000000 : ℝ)) (alpha := (460759078651/346900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1993246363/10000000000 : ℝ)*X 0 0+(1352404913/2500000000 : ℝ)*X 0 1+(5246264451/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668485427/1250000000 : ℝ)*X 1 0+(-2076432249/10000000000 : ℝ)*X 1 1+(1049252891/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347883371/10000000000 : ℝ)*X 2 0+(5246264483/10000000000 : ℝ)*X 2 1+(-207643227/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2155585387/5000000000 : ℝ)*X 0 0+(4139451997/10000000000 : ℝ)*X 0 1+(4489351051/10000000000 : ℝ)*X 0 2+(2155585387/5000000000 : ℝ)*X 1 0+(4139451997/10000000000 : ℝ)*X 1 1+(4489351051/10000000000 : ℝ)*X 1 2+(2155585387/5000000000 : ℝ)*X 2 0+(4139451997/10000000000 : ℝ)*X 2 1+(4489351051/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-398651583/2000000000 : ℝ)*X 0 0+(2623426151/5000000000 : ℝ)*X 0 1+(5409028781/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305530457/10000000000 : ℝ)*X 1 0+(-1913667913/10000000000 : ℝ)*X 1 1+(676128597/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((265276521/500000000 : ℝ)*X 2 0+(1352257201/2500000000 : ℝ)*X 2 1+(-478416981/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4311195579/10000000000 : ℝ)*X 0 0+(2244045969/5000000000 : ℝ)*X 0 1+(828143523/2000000000 : ℝ)*X 0 2+(4311195579/10000000000 : ℝ)*X 1 0+(2244045969/5000000000 : ℝ)*X 1 1+(828143523/2000000000 : ℝ)*X 1 2+(4311195579/10000000000 : ℝ)*X 2 0+(2244045969/5000000000 : ℝ)*X 2 1+(828143523/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1079721252330306069285510117/108406250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1860281977/100000000000000 : ℝ)*(base19) + (1694245709/100000000000000 : ℝ)*(base23) + (30623289/50000000000000 : ℝ)*(lower2) + (66330747/25000000000000 : ℝ)*(upper3) + (36357151/25000000000000 : ℝ)*(upper5) + (2244928447335689/50000000000000 : ℝ)*(major0) + (2244928447335689/50000000000000 : ℝ)*(major1) + (2244928447335689/50000000000000 : ℝ)*(major2) + (3060835428067503/50000000000000 : ℝ)*(sp0) + (6121707177102653/100000000000000 : ℝ)*(sp1) + (3060853671569461/50000000000000 : ℝ)*(sp2) + (1428992336881929/50000000000000 : ℝ)*(sp3) + (4772656203/12500000000000 : ℝ)*(sp4) + (4936548949/25000000000000 : ℝ)*(sp7) + (1429002209979827/50000000000000 : ℝ)*(f.failure) + (612170903738463/10000000000000 : ℝ)*(f.sum) + (2155014386623/1084062500000000000000000000 : ℝ)*base65 + (627221641462445039/433625000000000000000000000000000 : ℝ)*base68 + (3656225012329304961/433625000000000000000000000000000 : ℝ)*base69 + (495960255523804961/433625000000000000000000000000000 : ℝ)*base71 + (65119381077513/17345000000000000000000000000 : ℝ)*base73 + (3515644192768679961/433625000000000000000000000000000 : ℝ)*base75 + (930294920128054961/433625000000000000000000000000000 : ℝ)*base77 + (1939953283905804961/433625000000000000000000000000000 : ℝ)*base79 + (1448001934087/271015625000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (40268087/5000000000000000000000 : ℝ)*base90 + (40268087/5000000000000000000000 : ℝ)*base92 + (40268087/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1754437913242525060665124671/216812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (140765287/10000000000000 : ℝ)*(base19) + (753667933/50000000000000 : ℝ)*(base23) + (481027551/100000000000000 : ℝ)*(lower1) + (40534697/25000000000000 : ℝ)*(upper3) + (66403043/100000000000000 : ℝ)*(lower4) + (78936399/50000000000000 : ℝ)*(upper5) + (4522407754149993/100000000000000 : ℝ)*(major0) + (4522407754149993/100000000000000 : ℝ)*(major1) + (4522407754149993/100000000000000 : ℝ)*(major2) + (2195498871/100000000000000 : ℝ)*(sp2) + (6166090670406331/100000000000000 : ℝ)*(sp4) + (6166089262753461/100000000000000 : ℝ)*(sp5) + (3083043483785797/50000000000000 : ℝ)*(sp6) + (359840571020207/12500000000000 : ℝ)*(sp7) + (359840571020207/12500000000000 : ℝ)*(f.failure) + (6166090670406331/100000000000000 : ℝ)*(f.sum) + (19855142113897/4336250000000000000000000000 : ℝ)*base65 + (519979264242870943/867250000000000000000000000000000 : ℝ)*base68 + (437616237745120943/867250000000000000000000000000000 : ℝ)*base70 + (162678754762982620943/867250000000000000000000000000000 : ℝ)*base72 + (475577968301/542031250000000000000000000 : ℝ)*base74 + (20203817294873629057/867250000000000000000000000000000 : ℝ)*base75 + (2885689098916620943/867250000000000000000000000000000 : ℝ)*base78 + (12825708928488620943/867250000000000000000000000000000 : ℝ)*base80 + (8861899021387/17345000000000000000000000000 : ℝ)*base82 + (8087133/1250000000000000000000 : ℝ)*base89 + (8087133/1250000000000000000000 : ℝ)*base91 + (8087133/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1402_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157097619/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3687/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11279/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11283/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14743/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1402_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1402_s7_0 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1993252007/10000000000 : ℝ)*x 0 + (27047923/50000000 : ℝ)*x 1 + (131157391/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1993252007/10000000000 : ℝ)^2181 ≤ (1519142651327/12500000000000 : ℝ)^1669 := by
    have hnat : (1993252007 : ℕ)^2181*12500000000000^1669 ≤ 1519142651327^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1993252007 10000000000 1519142651327 12500000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (27047923/50000000 : ℝ)^2181 ≤ (44802935789231/100000000000000 : ℝ)^1669 := by
    have hnat : (27047923 : ℕ)^2181*100000000000000^1669 ≤ 44802935789231^1669*50000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27047923 50000000 44802935789231 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131157391/250000000 : ℝ)^2181 ≤ (43043922980831/100000000000000 : ℝ)^1669 := by
    have hnat : (131157391 : ℕ)^2181*100000000000000^1669 ≤ 43043922980831^1669*250000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131157391 250000000 43043922980831 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1993252007/10000000000 : ℝ), (27047923/50000000 : ℝ), (131157391/250000000 : ℝ)] ![(1519142651327/12500000000000 : ℝ), (44802935789231/100000000000000 : ℝ), (43043922980831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1993252007/10000000000 : ℝ)|^2181 ≤ (1519142651327/12500000000000 : ℝ)^1669
        have hw : |(-1993252007/10000000000 : ℝ)|=(1993252007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(27047923/50000000 : ℝ)|^2181 ≤ (44802935789231/100000000000000 : ℝ)^1669
        have hw : |(27047923/50000000 : ℝ)|=(27047923/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(131157391/250000000 : ℝ)|^2181 ≤ (43043922980831/100000000000000 : ℝ)^1669
        have hw : |(131157391/250000000 : ℝ)|=(131157391/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_s7_1 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2673936929/5000000000 : ℝ)*x 0 + (-16221903/78125000 : ℝ)*x 1 + (5246295639/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673936929/5000000000 : ℝ)^2181 ≤ (44136221049943/100000000000000 : ℝ)^1669 := by
    have hnat : (2673936929 : ℕ)^2181*100000000000000^1669 ≤ 44136221049943^1669*5000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673936929 5000000000 44136221049943 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16221903/78125000 : ℝ)^2181 ≤ (12819855959451/100000000000000 : ℝ)^1669 := by
    have hnat : (16221903 : ℕ)^2181*100000000000000^1669 ≤ 12819855959451^1669*78125000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16221903 78125000 12819855959451 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246295639/10000000000 : ℝ)^2181 ≤ (43043922970109/100000000000000 : ℝ)^1669 := by
    have hnat : (5246295639 : ℕ)^2181*100000000000000^1669 ≤ 43043922970109^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246295639 10000000000 43043922970109 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673936929/5000000000 : ℝ), (-16221903/78125000 : ℝ), (5246295639/10000000000 : ℝ)] ![(44136221049943/100000000000000 : ℝ), (12819855959451/100000000000000 : ℝ), (43043922970109/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673936929/5000000000 : ℝ)|^2181 ≤ (44136221049943/100000000000000 : ℝ)^1669
        have hw : |(2673936929/5000000000 : ℝ)|=(2673936929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-16221903/78125000 : ℝ)|^2181 ≤ (12819855959451/100000000000000 : ℝ)^1669
        have hw : |(-16221903/78125000 : ℝ)|=(16221903/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246295639/10000000000 : ℝ)|^2181 ≤ (43043922970109/100000000000000 : ℝ)^1669
        have hw : |(5246295639/10000000000 : ℝ)|=(5246295639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_s7_2 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2673936929/5000000000 : ℝ)*x 0 + (131157391/250000000 : ℝ)*x 1 + (-16221903/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673936929/5000000000 : ℝ)^2181 ≤ (44136221049943/100000000000000 : ℝ)^1669 := by
    have hnat : (2673936929 : ℕ)^2181*100000000000000^1669 ≤ 44136221049943^1669*5000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673936929 5000000000 44136221049943 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131157391/250000000 : ℝ)^2181 ≤ (43043922980831/100000000000000 : ℝ)^1669 := by
    have hnat : (131157391 : ℕ)^2181*100000000000000^1669 ≤ 43043922980831^1669*250000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131157391 250000000 43043922980831 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (16221903/78125000 : ℝ)^2181 ≤ (12819855959451/100000000000000 : ℝ)^1669 := by
    have hnat : (16221903 : ℕ)^2181*100000000000000^1669 ≤ 12819855959451^1669*78125000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16221903 78125000 12819855959451 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673936929/5000000000 : ℝ), (131157391/250000000 : ℝ), (-16221903/78125000 : ℝ)] ![(44136221049943/100000000000000 : ℝ), (43043922980831/100000000000000 : ℝ), (12819855959451/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673936929/5000000000 : ℝ)|^2181 ≤ (44136221049943/100000000000000 : ℝ)^1669
        have hw : |(2673936929/5000000000 : ℝ)|=(2673936929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(131157391/250000000 : ℝ)|^2181 ≤ (43043922980831/100000000000000 : ℝ)^1669
        have hw : |(131157391/250000000 : ℝ)|=(131157391/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-16221903/78125000 : ℝ)|^2181 ≤ (12819855959451/100000000000000 : ℝ)^1669
        have hw : |(-16221903/78125000 : ℝ)|=(16221903/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_s7_3 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (431117311/1000000000 : ℝ)*x 0 + (4139522649/10000000000 : ℝ)*x 1 + (1122319957/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (431117311/1000000000 : ℝ)^2181 ≤ (33304285518701/100000000000000 : ℝ)^1669 := by
    have hnat : (431117311 : ℕ)^2181*100000000000000^1669 ≤ 33304285518701^1669*1000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431117311 1000000000 33304285518701 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4139522649/10000000000 : ℝ)^2181 ≤ (31582164819693/100000000000000 : ℝ)^1669 := by
    have hnat : (4139522649 : ℕ)^2181*100000000000000^1669 ≤ 31582164819693^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4139522649 10000000000 31582164819693 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1122319957/2500000000 : ℝ)^2181 ≤ (17556774824577/50000000000000 : ℝ)^1669 := by
    have hnat : (1122319957 : ℕ)^2181*50000000000000^1669 ≤ 17556774824577^1669*2500000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122319957 2500000000 17556774824577 50000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(431117311/1000000000 : ℝ), (4139522649/10000000000 : ℝ), (1122319957/2500000000 : ℝ)] ![(33304285518701/100000000000000 : ℝ), (31582164819693/100000000000000 : ℝ), (17556774824577/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(431117311/1000000000 : ℝ)|^2181 ≤ (33304285518701/100000000000000 : ℝ)^1669
        have hw : |(431117311/1000000000 : ℝ)|=(431117311/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4139522649/10000000000 : ℝ)|^2181 ≤ (31582164819693/100000000000000 : ℝ)^1669
        have hw : |(4139522649/10000000000 : ℝ)|=(4139522649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1122319957/2500000000 : ℝ)|^2181 ≤ (17556774824577/50000000000000 : ℝ)^1669
        have hw : |(1122319957/2500000000 : ℝ)|=(1122319957/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_s7_4 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-996631781/5000000000 : ℝ)*x 0 + (209875319/400000000 : ℝ)*x 1 + (1352248559/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (996631781/5000000000 : ℝ)^2181 ≤ (12153233275921/100000000000000 : ℝ)^1669 := by
    have hnat : (996631781 : ℕ)^2181*100000000000000^1669 ≤ 12153233275921^1669*5000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      996631781 5000000000 12153233275921 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209875319/400000000 : ℝ)^2181 ≤ (8610044048539/20000000000000 : ℝ)^1669 := by
    have hnat : (209875319 : ℕ)^2181*20000000000000^1669 ≤ 8610044048539^1669*400000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209875319 400000000 8610044048539 20000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1352248559/2500000000 : ℝ)^2181 ≤ (44796546471563/100000000000000 : ℝ)^1669 := by
    have hnat : (1352248559 : ℕ)^2181*100000000000000^1669 ≤ 44796546471563^1669*2500000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352248559 2500000000 44796546471563 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-996631781/5000000000 : ℝ), (209875319/400000000 : ℝ), (1352248559/2500000000 : ℝ)] ![(12153233275921/100000000000000 : ℝ), (8610044048539/20000000000000 : ℝ), (44796546471563/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-996631781/5000000000 : ℝ)|^2181 ≤ (12153233275921/100000000000000 : ℝ)^1669
        have hw : |(-996631781/5000000000 : ℝ)|=(996631781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(209875319/400000000 : ℝ)|^2181 ≤ (8610044048539/20000000000000 : ℝ)^1669
        have hw : |(209875319/400000000 : ℝ)|=(209875319/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1352248559/2500000000 : ℝ)|^2181 ≤ (44796546471563/100000000000000 : ℝ)^1669
        have hw : |(1352248559/2500000000 : ℝ)|=(1352248559/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_s7_5 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305538093/10000000000 : ℝ)*x 0 + (-478426247/2500000000 : ℝ)*x 1 + (5408994229/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305538093/10000000000 : ℝ)^2181 ≤ (43680192431361/100000000000000 : ℝ)^1669 := by
    have hnat : (5305538093 : ℕ)^2181*100000000000000^1669 ≤ 43680192431361^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305538093 10000000000 43680192431361 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (478426247/2500000000 : ℝ)^2181 ≤ (5761630581433/50000000000000 : ℝ)^1669 := by
    have hnat : (478426247 : ℕ)^2181*50000000000000^1669 ≤ 5761630581433^1669*2500000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      478426247 2500000000 5761630581433 50000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5408994229/10000000000 : ℝ)^2181 ≤ (8959309279161/20000000000000 : ℝ)^1669 := by
    have hnat : (5408994229 : ℕ)^2181*20000000000000^1669 ≤ 8959309279161^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408994229 10000000000 8959309279161 20000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305538093/10000000000 : ℝ), (-478426247/2500000000 : ℝ), (5408994229/10000000000 : ℝ)] ![(43680192431361/100000000000000 : ℝ), (5761630581433/50000000000000 : ℝ), (8959309279161/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305538093/10000000000 : ℝ)|^2181 ≤ (43680192431361/100000000000000 : ℝ)^1669
        have hw : |(5305538093/10000000000 : ℝ)|=(5305538093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-478426247/2500000000 : ℝ)|^2181 ≤ (5761630581433/50000000000000 : ℝ)^1669
        have hw : |(-478426247/2500000000 : ℝ)|=(478426247/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5408994229/10000000000 : ℝ)|^2181 ≤ (8959309279161/20000000000000 : ℝ)^1669
        have hw : |(5408994229/10000000000 : ℝ)|=(5408994229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_s7_6 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1326384523/2500000000 : ℝ)*x 0 + (5408994223/10000000000 : ℝ)*x 1 + (-478426249/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326384523/2500000000 : ℝ)^2181 ≤ (43680192420603/100000000000000 : ℝ)^1669 := by
    have hnat : (1326384523 : ℕ)^2181*100000000000000^1669 ≤ 43680192420603^1669*2500000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326384523 2500000000 43680192420603 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5408994223/10000000000 : ℝ)^2181 ≤ (4479654633087/10000000000000 : ℝ)^1669 := by
    have hnat : (5408994223 : ℕ)^2181*10000000000000^1669 ≤ 4479654633087^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408994223 10000000000 4479654633087 10000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (478426249/2500000000 : ℝ)^2181 ≤ (2304652245163/20000000000000 : ℝ)^1669 := by
    have hnat : (478426249 : ℕ)^2181*20000000000000^1669 ≤ 2304652245163^1669*2500000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      478426249 2500000000 2304652245163 20000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326384523/2500000000 : ℝ), (5408994223/10000000000 : ℝ), (-478426249/2500000000 : ℝ)] ![(43680192420603/100000000000000 : ℝ), (4479654633087/10000000000000 : ℝ), (2304652245163/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326384523/2500000000 : ℝ)|^2181 ≤ (43680192420603/100000000000000 : ℝ)^1669
        have hw : |(1326384523/2500000000 : ℝ)|=(1326384523/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5408994223/10000000000 : ℝ)|^2181 ≤ (4479654633087/10000000000000 : ℝ)^1669
        have hw : |(5408994223/10000000000 : ℝ)|=(5408994223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-478426249/2500000000 : ℝ)|^2181 ≤ (2304652245163/20000000000000 : ℝ)^1669
        have hw : |(-478426249/2500000000 : ℝ)|=(478426249/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_s7_7 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2155598951/5000000000 : ℝ)*x 0 + (448802177/1000000000 : ℝ)*x 1 + (2070393593/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2155598951/5000000000 : ℝ)^2181 ≤ (2081533487051/6250000000000 : ℝ)^1669 := by
    have hnat : (2155598951 : ℕ)^2181*6250000000000^1669 ≤ 2081533487051^1669*5000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155598951 5000000000 2081533487051 6250000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (448802177/1000000000 : ℝ)^2181 ≤ (7020138294541/20000000000000 : ℝ)^1669 := by
    have hnat : (448802177 : ℕ)^2181*20000000000000^1669 ≤ 7020138294541^1669*1000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448802177 1000000000 7020138294541 20000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2070393593/5000000000 : ℝ)^2181 ≤ (7898693180609/25000000000000 : ℝ)^1669 := by
    have hnat : (2070393593 : ℕ)^2181*25000000000000^1669 ≤ 7898693180609^1669*5000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2070393593 5000000000 7898693180609 25000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2155598951/5000000000 : ℝ), (448802177/1000000000 : ℝ), (2070393593/5000000000 : ℝ)] ![(2081533487051/6250000000000 : ℝ), (7020138294541/20000000000000 : ℝ), (7898693180609/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2155598951/5000000000 : ℝ)|^2181 ≤ (2081533487051/6250000000000 : ℝ)^1669
        have hw : |(2155598951/5000000000 : ℝ)|=(2155598951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(448802177/1000000000 : ℝ)|^2181 ≤ (7020138294541/20000000000000 : ℝ)^1669
        have hw : |(448802177/1000000000 : ℝ)|=(448802177/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2070393593/5000000000 : ℝ)|^2181 ≤ (7898693180609/25000000000000 : ℝ)^1669
        have hw : |(2070393593/5000000000 : ℝ)|=(2070393593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1402_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157097619/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14743/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11283/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2821/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7371/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14743/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11283/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14743/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11283/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14743/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11283/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14743/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11283/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14743/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11283/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14743/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11283/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11283/100000 : ℝ) ^ (4361/1024 : ℝ) ≤ (9214593901526371/100000000000000000000 : ℝ) := by
    have hpowers : (11283/100000 : ℝ)^4361 ≤ (9214593901526371/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11283 : ℕ)^4361*100000000000000000000^1024 ≤ 9214593901526371^1024*100000^4361 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11283 100000 9214593901526371 100000000000000000000 4361 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11283/100000 : ℝ)) (X := (9214593901526371/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4361 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14743/100000 : ℝ) ^ (4361/1024 : ℝ) ≤ (14393041647889079/50000000000000000000 : ℝ) := by
    have hpowers : (14743/100000 : ℝ)^4361 ≤ (14393041647889079/50000000000000000000 : ℝ)^1024 := by
      have hnat : (14743 : ℕ)^4361*50000000000000000000^1024 ≤ 14393041647889079^1024*100000^4361 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14743 100000 14393041647889079 50000000000000000000 4361 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14743/100000 : ℝ)) (X := (14393041647889079/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4361 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009214593901526371/50000000000000000000 : ℝ) ≤ (5000216351270803/5000000000000000 : ℝ) ^ (4361/1024 : ℝ) := by
    have hpowers : (50009214593901526371/50000000000000000000 : ℝ)^1024 ≤ (5000216351270803/5000000000000000 : ℝ)^4361 := by
      have hnat : (50009214593901526371 : ℕ)^1024*5000000000000000^4361 ≤ 5000216351270803^4361*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009214593901526371 50000000000000000000 5000216351270803 5000000000000000 1024 4361 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000216351270803/5000000000000000 : ℝ)) (X := (50009214593901526371/50000000000000000000 : ℝ)) (by norm_num) 4361 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100038000677197304529/100000000000000000000 : ℝ) ≤ (5000446079307937/5000000000000000 : ℝ) ^ (4361/1024 : ℝ) := by
    have hpowers : (100038000677197304529/100000000000000000000 : ℝ)^1024 ≤ (5000446079307937/5000000000000000 : ℝ)^4361 := by
      have hnat : (100038000677197304529 : ℕ)^1024*5000000000000000^4361 ≤ 5000446079307937^4361*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100038000677197304529 100000000000000000000 5000446079307937 5000000000000000 1024 4361 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000446079307937/5000000000000000 : ℝ)) (X := (100038000677197304529/100000000000000000000 : ℝ)) (by norm_num) 4361 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25014393041647889079/25000000000000000000 : ℝ) ≤ (5000675807345071/5000000000000000 : ℝ) ^ (4361/1024 : ℝ) := by
    have hpowers : (25014393041647889079/25000000000000000000 : ℝ)^1024 ≤ (5000675807345071/5000000000000000 : ℝ)^4361 := by
      have hnat : (25014393041647889079 : ℕ)^1024*5000000000000000^4361 ≤ 5000675807345071^4361*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014393041647889079 25000000000000000000 5000675807345071 5000000000000000 1024 4361 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000675807345071/5000000000000000 : ℝ)) (X := (25014393041647889079/25000000000000000000 : ℝ)) (by norm_num) 4361 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9214593901526371/100000000000000000000 : ℝ) ≤ ((2161945566563876567/2162500000000000000 : ℝ)+2*(114864018567/86500000000000 : ℝ)*(11283/100000 : ℝ))^(4361/1024 : ℝ) := by
    rw [show (2161945566563876567/2162500000000000000 : ℝ)+2*(114864018567/86500000000000 : ℝ)*(11283/100000 : ℝ)=(5000216351270803/5000000000000000 : ℝ) by norm_num, show 1+2*(9214593901526371/100000000000000000000 : ℝ)=(50009214593901526371/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14393041647889079/50000000000000000000 : ℝ)+(9214593901526371/100000000000000000000 : ℝ) ≤ ((2161945566563876567/2162500000000000000 : ℝ)+(114864018567/86500000000000 : ℝ)*((14743/100000 : ℝ)+(11283/100000 : ℝ)))^(4361/1024 : ℝ) := by
    rw [show (2161945566563876567/2162500000000000000 : ℝ)+(114864018567/86500000000000 : ℝ)*((14743/100000 : ℝ)+(11283/100000 : ℝ))=(5000446079307937/5000000000000000 : ℝ) by norm_num, show 1+(14393041647889079/50000000000000000000 : ℝ)+(9214593901526371/100000000000000000000 : ℝ)=(100038000677197304529/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14393041647889079/50000000000000000000 : ℝ) ≤ ((2161945566563876567/2162500000000000000 : ℝ)+2*(114864018567/86500000000000 : ℝ)*(14743/100000 : ℝ))^(4361/1024 : ℝ) := by
    rw [show (2161945566563876567/2162500000000000000 : ℝ)+2*(114864018567/86500000000000 : ℝ)*(14743/100000 : ℝ)=(5000675807345071/5000000000000000 : ℝ) by norm_num, show 1+2*(14393041647889079/50000000000000000000 : ℝ)=(25014393041647889079/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2161945566563876567/2162500000000000000 : ℝ)*(X 1 0+X 2 0)+(114864018567/86500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4361/1024 : ℝ)) (lo := (11283/100000 : ℝ)) (hi := (14743/100000 : ℝ)) (c := (2161945566563876567/2162500000000000000 : ℝ)) (alpha := (114864018567/86500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2161945566563876567/2162500000000000000 : ℝ)*(X 0 1+X 2 1)+(114864018567/86500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4361/1024 : ℝ)) (lo := (11283/100000 : ℝ)) (hi := (14743/100000 : ℝ)) (c := (2161945566563876567/2162500000000000000 : ℝ)) (alpha := (114864018567/86500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2161945566563876567/2162500000000000000 : ℝ)*(X 0 2+X 1 2)+(114864018567/86500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4361/1024 : ℝ)) (lo := (11283/100000 : ℝ)) (hi := (14743/100000 : ℝ)) (c := (2161945566563876567/2162500000000000000 : ℝ)) (alpha := (114864018567/86500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1993252007/10000000000 : ℝ)*X 0 0+(27047923/50000000 : ℝ)*X 0 1+(131157391/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673936929/5000000000 : ℝ)*X 1 0+(-16221903/78125000 : ℝ)*X 1 1+(5246295639/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673936929/5000000000 : ℝ)*X 2 0+(131157391/250000000 : ℝ)*X 2 1+(-16221903/78125000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((431117311/1000000000 : ℝ)*X 0 0+(4139522649/10000000000 : ℝ)*X 0 1+(1122319957/2500000000 : ℝ)*X 0 2+(431117311/1000000000 : ℝ)*X 1 0+(4139522649/10000000000 : ℝ)*X 1 1+(1122319957/2500000000 : ℝ)*X 1 2+(431117311/1000000000 : ℝ)*X 2 0+(4139522649/10000000000 : ℝ)*X 2 1+(1122319957/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-996631781/5000000000 : ℝ)*X 0 0+(209875319/400000000 : ℝ)*X 0 1+(1352248559/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305538093/10000000000 : ℝ)*X 1 0+(-478426247/2500000000 : ℝ)*X 1 1+(5408994229/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326384523/2500000000 : ℝ)*X 2 0+(5408994223/10000000000 : ℝ)*X 2 1+(-478426249/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2155598951/5000000000 : ℝ)*X 0 0+(448802177/1000000000 : ℝ)*X 0 1+(2070393593/5000000000 : ℝ)*X 0 2+(2155598951/5000000000 : ℝ)*X 1 0+(448802177/1000000000 : ℝ)*X 1 1+(2070393593/5000000000 : ℝ)*X 1 2+(2155598951/5000000000 : ℝ)*X 2 0+(448802177/1000000000 : ℝ)*X 2 1+(2070393593/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (181338244539294360622161111/27031250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1235014681/100000000000000 : ℝ)*(base19) + (143879987/12500000000000 : ℝ)*(base23) + (2806791/6250000000000 : ℝ)*(lower2) + (83801451/50000000000000 : ℝ)*(upper3) + (53495303/50000000000000 : ℝ)*(upper5) + (1122914588014339/25000000000000 : ℝ)*(major0) + (1122914588014339/25000000000000 : ℝ)*(major1) + (1122914588014339/25000000000000 : ℝ)*(major2) + (1531034900761411/25000000000000 : ℝ)*(sp0) + (6124164113437483/100000000000000 : ℝ)*(sp1) + (1531041049353067/25000000000000 : ℝ)*(sp2) + (178696132791677/6250000000000 : ℝ)*(sp3) + (643635163/2500000000000 : ℝ)*(sp4) + (13007380151/100000000000000 : ℝ)*(sp7) + (2859151132046983/100000000000000 : ℝ)*(f.failure) + (1531041337113041/25000000000000 : ℝ)*(f.sum) + (4178427433151/2162500000000000000000000000 : ℝ)*base65 + (53226223885544213/54062500000000000000000000000000 : ℝ)*base67 + (209230259275544213/54062500000000000000000000000000 : ℝ)*base69 + (321064979600080787/54062500000000000000000000000000 : ℝ)*base72 + (4589892380451/2162500000000000000000000000 : ℝ)*base73 + (459700429287731713/54062500000000000000000000000000 : ℝ)*base75 + (182268730128205787/54062500000000000000000000000000 : ℝ)*base78 + (173816299898044213/54062500000000000000000000000000 : ℝ)*base79 + (1836564285551/2162500000000000000000000000 : ℝ)*base81 + (25433477/10000000000000000000000 : ℝ)*base89 + (25433477/10000000000000000000000 : ℝ)*base91 + (25433477/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (583098088450369849833493107/108125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (230682971/25000000000000 : ℝ)*(base19) + (1023677417/100000000000000 : ℝ)*(base23) + (311388831/100000000000000 : ℝ)*(lower1) + (53959959/50000000000000 : ℝ)*(upper3) + (9637619/20000000000000 : ℝ)*(lower4) + (11446671/10000000000000 : ℝ)*(upper5) + (4524235580979793/100000000000000 : ℝ)*(major0) + (4524235580979793/100000000000000 : ℝ)*(major1) + (4524235580979793/100000000000000 : ℝ)*(major2) + (1413886243/100000000000000 : ℝ)*(sp2) + (3084291458281381/50000000000000 : ℝ)*(sp4) + (3084290996915439/50000000000000 : ℝ)*(sp5) + (6168580478999103/100000000000000 : ℝ)*(sp6) + (575977613127261/20000000000000 : ℝ)*(sp7) + (575977613127261/20000000000000 : ℝ)*(f.failure) + (3084291458281381/50000000000000 : ℝ)*(f.sum) + (10298923346181/4325000000000000000000000000 : ℝ)*base65 + (6799191986588985631/216250000000000000000000000000000 : ℝ)*base67 + (167170015693514369/216250000000000000000000000000000 : ℝ)*base70 + (7595539209376014369/216250000000000000000000000000000 : ℝ)*base72 + (1183893352819/4325000000000000000000000000 : ℝ)*base74 + (35705728685818985631/216250000000000000000000000000000 : ℝ)*base75 + (1076684518538985631/216250000000000000000000000000000 : ℝ)*base77 + (2128346488780235631/216250000000000000000000000000000 : ℝ)*base79 + (3653182228119/4325000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (12908441/2000000000000000000000 : ℝ)*base90 + (12908441/2000000000000000000000 : ℝ)*base92 + (12908441/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1402_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157097619/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14743/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11283/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2821/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7371/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1402_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1402_box_0 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-366122123/2000000000 : ℝ)*x 0 + (538740987/1000000000 : ℝ)*x 1 + (2693704641/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (366122123/2000000000 : ℝ)^2181 ≤ (2174764100103/20000000000000 : ℝ)^1669 := by
    have hnat : (366122123 : ℕ)^2181*20000000000000^1669 ≤ 2174764100103^1669*2000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      366122123 2000000000 2174764100103 20000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (538740987/1000000000 : ℝ)^2181 ≤ (44563092916473/100000000000000 : ℝ)^1669 := by
    have hnat : (538740987 : ℕ)^2181*100000000000000^1669 ≤ 44563092916473^1669*1000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538740987 1000000000 44563092916473 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2693704641/5000000000 : ℝ)^2181 ≤ (44563086560647/100000000000000 : ℝ)^1669 := by
    have hnat : (2693704641 : ℕ)^2181*100000000000000^1669 ≤ 44563086560647^1669*5000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693704641 5000000000 44563086560647 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-366122123/2000000000 : ℝ), (538740987/1000000000 : ℝ), (2693704641/5000000000 : ℝ)] ![(2174764100103/20000000000000 : ℝ), (44563092916473/100000000000000 : ℝ), (44563086560647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-366122123/2000000000 : ℝ)|^2181 ≤ (2174764100103/20000000000000 : ℝ)^1669
        have hw : |(-366122123/2000000000 : ℝ)|=(366122123/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(538740987/1000000000 : ℝ)|^2181 ≤ (44563092916473/100000000000000 : ℝ)^1669
        have hw : |(538740987/1000000000 : ℝ)|=(538740987/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2693704641/5000000000 : ℝ)|^2181 ≤ (44563086560647/100000000000000 : ℝ)^1669
        have hw : |(2693704641/5000000000 : ℝ)|=(2693704641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_box_1 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5285845979/10000000000 : ℝ)*x 0 + (-197003143/1000000000 : ℝ)*x 1 + (673426137/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285845979/10000000000 : ℝ)^2181 ≤ (43468454216979/100000000000000 : ℝ)^1669 := by
    have hnat : (5285845979 : ℕ)^2181*100000000000000^1669 ≤ 43468454216979^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285845979 10000000000 43468454216979 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (197003143/1000000000 : ℝ)^2181 ≤ (59842306103/500000000000 : ℝ)^1669 := by
    have hnat : (197003143 : ℕ)^2181*500000000000^1669 ≤ 59842306103^1669*1000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197003143 1000000000 59842306103 500000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (673426137/1250000000 : ℝ)^2181 ≤ (44563084550131/100000000000000 : ℝ)^1669 := by
    have hnat : (673426137 : ℕ)^2181*100000000000000^1669 ≤ 44563084550131^1669*1250000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673426137 1250000000 44563084550131 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285845979/10000000000 : ℝ), (-197003143/1000000000 : ℝ), (673426137/1250000000 : ℝ)] ![(43468454216979/100000000000000 : ℝ), (59842306103/500000000000 : ℝ), (44563084550131/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285845979/10000000000 : ℝ)|^2181 ≤ (43468454216979/100000000000000 : ℝ)^1669
        have hw : |(5285845979/10000000000 : ℝ)|=(5285845979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-197003143/1000000000 : ℝ)|^2181 ≤ (59842306103/500000000000 : ℝ)^1669
        have hw : |(-197003143/1000000000 : ℝ)|=(197003143/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(673426137/1250000000 : ℝ)|^2181 ≤ (44563084550131/100000000000000 : ℝ)^1669
        have hw : |(673426137/1250000000 : ℝ)|=(673426137/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_box_2 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2642923153/5000000000 : ℝ)*x 0 + (5387409313/10000000000 : ℝ)*x 1 + (-492507673/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642923153/5000000000 : ℝ)^2181 ≤ (43468457731019/100000000000000 : ℝ)^1669 := by
    have hnat : (2642923153 : ℕ)^2181*100000000000000^1669 ≤ 43468457731019^1669*5000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642923153 5000000000 43468457731019 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5387409313/10000000000 : ℝ)^2181 ≤ (44563086895733/100000000000000 : ℝ)^1669 := by
    have hnat : (5387409313 : ℕ)^2181*100000000000000^1669 ≤ 44563086895733^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387409313 10000000000 44563086895733 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (492507673/2500000000 : ℝ)^2181 ≤ (2992113840409/25000000000000 : ℝ)^1669 := by
    have hnat : (492507673 : ℕ)^2181*25000000000000^1669 ≤ 2992113840409^1669*2500000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      492507673 2500000000 2992113840409 25000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642923153/5000000000 : ℝ), (5387409313/10000000000 : ℝ), (-492507673/2500000000 : ℝ)] ![(43468457731019/100000000000000 : ℝ), (44563086895733/100000000000000 : ℝ), (2992113840409/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642923153/5000000000 : ℝ)|^2181 ≤ (43468457731019/100000000000000 : ℝ)^1669
        have hw : |(2642923153/5000000000 : ℝ)|=(2642923153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5387409313/10000000000 : ℝ)|^2181 ≤ (44563086895733/100000000000000 : ℝ)^1669
        have hw : |(5387409313/10000000000 : ℝ)|=(5387409313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-492507673/2500000000 : ℝ)|^2181 ≤ (2992113840409/25000000000000 : ℝ)^1669
        have hw : |(-492507673/2500000000 : ℝ)|=(492507673/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_box_3 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4458025679/10000000000 : ℝ)*x 0 + (2120754489/5000000000 : ℝ)*x 1 + (848301821/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4458025679/10000000000 : ℝ)^2181 ≤ (2174652483209/6250000000000 : ℝ)^1669 := by
    have hnat : (4458025679 : ℕ)^2181*6250000000000^1669 ≤ 2174652483209^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4458025679 10000000000 2174652483209 6250000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2120754489/5000000000 : ℝ)^2181 ≤ (16301389746907/50000000000000 : ℝ)^1669 := by
    have hnat : (2120754489 : ℕ)^2181*50000000000000^1669 ≤ 16301389746907^1669*5000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2120754489 5000000000 16301389746907 50000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (848301821/2000000000 : ℝ)^2181 ≤ (32602780769481/100000000000000 : ℝ)^1669 := by
    have hnat : (848301821 : ℕ)^2181*100000000000000^1669 ≤ 32602780769481^1669*2000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848301821 2000000000 32602780769481 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4458025679/10000000000 : ℝ), (2120754489/5000000000 : ℝ), (848301821/2000000000 : ℝ)] ![(2174652483209/6250000000000 : ℝ), (16301389746907/50000000000000 : ℝ), (32602780769481/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4458025679/10000000000 : ℝ)|^2181 ≤ (2174652483209/6250000000000 : ℝ)^1669
        have hw : |(4458025679/10000000000 : ℝ)|=(4458025679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2120754489/5000000000 : ℝ)|^2181 ≤ (16301389746907/50000000000000 : ℝ)^1669
        have hw : |(2120754489/5000000000 : ℝ)|=(2120754489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(848301821/2000000000 : ℝ)|^2181 ≤ (32602780769481/100000000000000 : ℝ)^1669
        have hw : |(848301821/2000000000 : ℝ)|=(848301821/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_box_4 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2158633427/10000000000 : ℝ)*x 0 + (5266097713/10000000000 : ℝ)*x 1 + (5266097933/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2158633427/10000000000 : ℝ)^2181 ≤ (3371821845523/25000000000000 : ℝ)^1669 := by
    have hnat : (2158633427 : ℕ)^2181*25000000000000^1669 ≤ 3371821845523^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158633427 10000000000 3371821845523 25000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266097713/10000000000 : ℝ)^2181 ≤ (4325635511629/10000000000000 : ℝ)^1669 := by
    have hnat : (5266097713 : ℕ)^2181*10000000000000^1669 ≤ 4325635511629^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266097713 10000000000 4325635511629 10000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266097933/10000000000 : ℝ)^2181 ≤ (10814089369441/25000000000000 : ℝ)^1669 := by
    have hnat : (5266097933 : ℕ)^2181*25000000000000^1669 ≤ 10814089369441^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266097933 10000000000 10814089369441 25000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2158633427/10000000000 : ℝ), (5266097713/10000000000 : ℝ), (5266097933/10000000000 : ℝ)] ![(3371821845523/25000000000000 : ℝ), (4325635511629/10000000000000 : ℝ), (10814089369441/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2158633427/10000000000 : ℝ)|^2181 ≤ (3371821845523/25000000000000 : ℝ)^1669
        have hw : |(-2158633427/10000000000 : ℝ)|=(2158633427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266097713/10000000000 : ℝ)|^2181 ≤ (4325635511629/10000000000000 : ℝ)^1669
        have hw : |(5266097713/10000000000 : ℝ)|=(5266097713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266097933/10000000000 : ℝ)|^2181 ≤ (10814089369441/25000000000000 : ℝ)^1669
        have hw : |(5266097933/10000000000 : ℝ)|=(5266097933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_box_5 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2685419973/5000000000 : ℝ)*x 0 + (-31548597/156250000 : ℝ)*x 1 + (2633048791/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2685419973/5000000000 : ℝ)^2181 ≤ (44384069403531/100000000000000 : ℝ)^1669 := by
    have hnat : (2685419973 : ℕ)^2181*100000000000000^1669 ≤ 44384069403531^1669*5000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2685419973 5000000000 44384069403531 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (31548597/156250000 : ℝ)^2181 ≤ (98876614963/800000000000 : ℝ)^1669 := by
    have hnat : (31548597 : ℕ)^2181*800000000000^1669 ≤ 98876614963^1669*156250000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31548597 156250000 98876614963 800000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633048791/5000000000 : ℝ)^2181 ≤ (2162817685507/5000000000000 : ℝ)^1669 := by
    have hnat : (2633048791 : ℕ)^2181*5000000000000^1669 ≤ 2162817685507^1669*5000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633048791 5000000000 2162817685507 5000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2685419973/5000000000 : ℝ), (-31548597/156250000 : ℝ), (2633048791/5000000000 : ℝ)] ![(44384069403531/100000000000000 : ℝ), (98876614963/800000000000 : ℝ), (2162817685507/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2685419973/5000000000 : ℝ)|^2181 ≤ (44384069403531/100000000000000 : ℝ)^1669
        have hw : |(2685419973/5000000000 : ℝ)|=(2685419973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-31548597/156250000 : ℝ)|^2181 ≤ (98876614963/800000000000 : ℝ)^1669
        have hw : |(-31548597/156250000 : ℝ)|=(31548597/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633048791/5000000000 : ℝ)|^2181 ≤ (2162817685507/5000000000000 : ℝ)^1669
        have hw : |(2633048791/5000000000 : ℝ)|=(2633048791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_box_6 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (268541991/500000000 : ℝ)*x 0 + (2633048941/5000000000 : ℝ)*x 1 + (-252388747/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268541991/500000000 : ℝ)^2181 ≤ (22192034021427/50000000000000 : ℝ)^1669 := by
    have hnat : (268541991 : ℕ)^2181*50000000000000^1669 ≤ 22192034021427^1669*500000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268541991 500000000 22192034021427 50000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633048941/5000000000 : ℝ)^2181 ≤ (43256356930331/100000000000000 : ℝ)^1669 := by
    have hnat : (2633048941 : ℕ)^2181*100000000000000^1669 ≤ 43256356930331^1669*5000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633048941 5000000000 43256356930331 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (252388747/1250000000 : ℝ)^2181 ≤ (772473438411/6250000000000 : ℝ)^1669 := by
    have hnat : (252388747 : ℕ)^2181*6250000000000^1669 ≤ 772473438411^1669*1250000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      252388747 1250000000 772473438411 6250000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268541991/500000000 : ℝ), (2633048941/5000000000 : ℝ), (-252388747/1250000000 : ℝ)] ![(22192034021427/50000000000000 : ℝ), (43256356930331/100000000000000 : ℝ), (772473438411/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268541991/500000000 : ℝ)|^2181 ≤ (22192034021427/50000000000000 : ℝ)^1669
        have hw : |(268541991/500000000 : ℝ)|=(268541991/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633048941/5000000000 : ℝ)|^2181 ≤ (43256356930331/100000000000000 : ℝ)^1669
        have hw : |(2633048941/5000000000 : ℝ)|=(2633048941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-252388747/1250000000 : ℝ)|^2181 ≤ (772473438411/6250000000000 : ℝ)^1669
        have hw : |(-252388747/1250000000 : ℝ)|=(252388747/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_box_7 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1040827241/2500000000 : ℝ)*x 0 + (4388815697/10000000000 : ℝ)*x 1 + (4388815723/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1040827241/2500000000 : ℝ)^2181 ≤ (31819520827249/100000000000000 : ℝ)^1669 := by
    have hnat : (1040827241 : ℕ)^2181*100000000000000^1669 ≤ 31819520827249^1669*2500000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040827241 2500000000 31819520827249 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4388815697/10000000000 : ℝ)^2181 ≤ (34090239448459/100000000000000 : ℝ)^1669 := by
    have hnat : (4388815697 : ℕ)^2181*100000000000000^1669 ≤ 34090239448459^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4388815697 10000000000 34090239448459 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4388815723/10000000000 : ℝ)^2181 ≤ (34090239712369/100000000000000 : ℝ)^1669 := by
    have hnat : (4388815723 : ℕ)^2181*100000000000000^1669 ≤ 34090239712369^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4388815723 10000000000 34090239712369 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1040827241/2500000000 : ℝ), (4388815697/10000000000 : ℝ), (4388815723/10000000000 : ℝ)] ![(31819520827249/100000000000000 : ℝ), (34090239448459/100000000000000 : ℝ), (34090239712369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1040827241/2500000000 : ℝ)|^2181 ≤ (31819520827249/100000000000000 : ℝ)^1669
        have hw : |(1040827241/2500000000 : ℝ)|=(1040827241/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4388815697/10000000000 : ℝ)|^2181 ≤ (34090239448459/100000000000000 : ℝ)^1669
        have hw : |(4388815697/10000000000 : ℝ)|=(4388815697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4388815723/10000000000 : ℝ)|^2181 ≤ (34090239712369/100000000000000 : ℝ)^1669
        have hw : |(4388815723/10000000000 : ℝ)|=(4388815723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_box_8 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2089603287/10000000000 : ℝ)*x 0 + (5182310027/10000000000 : ℝ)*x 1 + (5401398579/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2089603287/10000000000 : ℝ)^2181 ≤ (12926456033353/100000000000000 : ℝ)^1669 := by
    have hnat : (2089603287 : ℕ)^2181*100000000000000^1669 ≤ 12926456033353^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2089603287 10000000000 12926456033353 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5182310027/10000000000 : ℝ)^2181 ≤ (2647448982403/6250000000000 : ℝ)^1669 := by
    have hnat : (5182310027 : ℕ)^2181*6250000000000^1669 ≤ 2647448982403^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182310027 10000000000 2647448982403 6250000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5401398579/10000000000 : ℝ)^2181 ≤ (22357180116497/50000000000000 : ℝ)^1669 := by
    have hnat : (5401398579 : ℕ)^2181*50000000000000^1669 ≤ 22357180116497^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401398579 10000000000 22357180116497 50000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2089603287/10000000000 : ℝ), (5182310027/10000000000 : ℝ), (5401398579/10000000000 : ℝ)] ![(12926456033353/100000000000000 : ℝ), (2647448982403/6250000000000 : ℝ), (22357180116497/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2089603287/10000000000 : ℝ)|^2181 ≤ (12926456033353/100000000000000 : ℝ)^1669
        have hw : |(-2089603287/10000000000 : ℝ)|=(2089603287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5182310027/10000000000 : ℝ)|^2181 ≤ (2647448982403/6250000000000 : ℝ)^1669
        have hw : |(5182310027/10000000000 : ℝ)|=(5182310027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5401398579/10000000000 : ℝ)|^2181 ≤ (22357180116497/50000000000000 : ℝ)^1669
        have hw : |(5401398579/10000000000 : ℝ)|=(5401398579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_box_9 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2638019773/5000000000 : ℝ)*x 0 + (-1964243501/10000000000 : ℝ)*x 1 + (5401399199/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638019773/5000000000 : ℝ)^2181 ≤ (43363101332373/100000000000000 : ℝ)^1669 := by
    have hnat : (2638019773 : ℕ)^2181*100000000000000^1669 ≤ 43363101332373^1669*5000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638019773 5000000000 43363101332373 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1964243501/10000000000 : ℝ)^2181 ≤ (596126585613/5000000000000 : ℝ)^1669 := by
    have hnat : (1964243501 : ℕ)^2181*5000000000000^1669 ≤ 596126585613^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1964243501 10000000000 596126585613 5000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5401399199/10000000000 : ℝ)^2181 ≤ (2794647933753/6250000000000 : ℝ)^1669 := by
    have hnat : (5401399199 : ℕ)^2181*6250000000000^1669 ≤ 2794647933753^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401399199 10000000000 2794647933753 6250000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638019773/5000000000 : ℝ), (-1964243501/10000000000 : ℝ), (5401399199/10000000000 : ℝ)] ![(43363101332373/100000000000000 : ℝ), (596126585613/5000000000000 : ℝ), (2794647933753/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638019773/5000000000 : ℝ)|^2181 ≤ (43363101332373/100000000000000 : ℝ)^1669
        have hw : |(2638019773/5000000000 : ℝ)|=(2638019773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1964243501/10000000000 : ℝ)|^2181 ≤ (596126585613/5000000000000 : ℝ)^1669
        have hw : |(-1964243501/10000000000 : ℝ)|=(1964243501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5401399199/10000000000 : ℝ)|^2181 ≤ (2794647933753/6250000000000 : ℝ)^1669
        have hw : |(5401399199/10000000000 : ℝ)|=(5401399199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_box_10 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5276039193/10000000000 : ℝ)*x 0 + (2700700239/5000000000 : ℝ)*x 1 + (-392848447/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276039193/10000000000 : ℝ)^2181 ≤ (43363097541089/100000000000000 : ℝ)^1669 := by
    have hnat : (5276039193 : ℕ)^2181*100000000000000^1669 ≤ 43363097541089^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276039193 10000000000 43363097541089 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2700700239/5000000000 : ℝ)^2181 ≤ (44714380776053/100000000000000 : ℝ)^1669 := by
    have hnat : (2700700239 : ℕ)^2181*100000000000000^1669 ≤ 44714380776053^1669*5000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700700239 5000000000 44714380776053 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (392848447/2000000000 : ℝ)^2181 ≤ (2384504334117/20000000000000 : ℝ)^1669 := by
    have hnat : (392848447 : ℕ)^2181*20000000000000^1669 ≤ 2384504334117^1669*2000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      392848447 2000000000 2384504334117 20000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276039193/10000000000 : ℝ), (2700700239/5000000000 : ℝ), (-392848447/2000000000 : ℝ)] ![(43363097541089/100000000000000 : ℝ), (44714380776053/100000000000000 : ℝ), (2384504334117/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276039193/10000000000 : ℝ)|^2181 ≤ (43363097541089/100000000000000 : ℝ)^1669
        have hw : |(5276039193/10000000000 : ℝ)|=(5276039193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2700700239/5000000000 : ℝ)|^2181 ≤ (44714380776053/100000000000000 : ℝ)^1669
        have hw : |(2700700239/5000000000 : ℝ)|=(2700700239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-392848447/2000000000 : ℝ)|^2181 ≤ (2384504334117/20000000000000 : ℝ)^1669
        have hw : |(-392848447/2000000000 : ℝ)|=(392848447/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_box_11 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2245728061/5000000000 : ℝ)*x 0 + (132015849/312500000 : ℝ)*x 1 + (4224506059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2245728061/5000000000 : ℝ)^2181 ≤ (7027159081751/20000000000000 : ℝ)^1669 := by
    have hnat : (2245728061 : ℕ)^2181*20000000000000^1669 ≤ 7027159081751^1669*5000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245728061 5000000000 7027159081751 20000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (132015849/312500000 : ℝ)^2181 ≤ (32432107848929/100000000000000 : ℝ)^1669 := by
    have hnat : (132015849 : ℕ)^2181*100000000000000^1669 ≤ 32432107848929^1669*312500000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132015849 312500000 32432107848929 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4224506059/10000000000 : ℝ)^2181 ≤ (32432096723161/100000000000000 : ℝ)^1669 := by
    have hnat : (4224506059 : ℕ)^2181*100000000000000^1669 ≤ 32432096723161^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4224506059 10000000000 32432096723161 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2245728061/5000000000 : ℝ), (132015849/312500000 : ℝ), (4224506059/10000000000 : ℝ)] ![(7027159081751/20000000000000 : ℝ), (32432107848929/100000000000000 : ℝ), (32432096723161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2245728061/5000000000 : ℝ)|^2181 ≤ (7027159081751/20000000000000 : ℝ)^1669
        have hw : |(2245728061/5000000000 : ℝ)|=(2245728061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(132015849/312500000 : ℝ)|^2181 ≤ (32432107848929/100000000000000 : ℝ)^1669
        have hw : |(132015849/312500000 : ℝ)|=(132015849/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4224506059/10000000000 : ℝ)|^2181 ≤ (32432096723161/100000000000000 : ℝ)^1669
        have hw : |(4224506059/10000000000 : ℝ)|=(4224506059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_box_12 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1899867851/10000000000 : ℝ)*x 0 + (5469120597/10000000000 : ℝ)*x 1 + (656873321/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1899867851/10000000000 : ℝ)^2181 ≤ (11414502652169/100000000000000 : ℝ)^1669 := by
    have hnat : (1899867851 : ℕ)^2181*100000000000000^1669 ≤ 11414502652169^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1899867851 10000000000 11414502652169 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5469120597/10000000000 : ℝ)^2181 ≤ (22724185147113/50000000000000 : ℝ)^1669 := by
    have hnat : (5469120597 : ℕ)^2181*50000000000000^1669 ≤ 22724185147113^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5469120597 10000000000 22724185147113 50000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (656873321/1250000000 : ℝ)^2181 ≤ (21568563523793/50000000000000 : ℝ)^1669 := by
    have hnat : (656873321 : ℕ)^2181*50000000000000^1669 ≤ 21568563523793^1669*1250000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656873321 1250000000 21568563523793 50000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1899867851/10000000000 : ℝ), (5469120597/10000000000 : ℝ), (656873321/1250000000 : ℝ)] ![(11414502652169/100000000000000 : ℝ), (22724185147113/50000000000000 : ℝ), (21568563523793/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1899867851/10000000000 : ℝ)|^2181 ≤ (11414502652169/100000000000000 : ℝ)^1669
        have hw : |(-1899867851/10000000000 : ℝ)|=(1899867851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5469120597/10000000000 : ℝ)|^2181 ≤ (22724185147113/50000000000000 : ℝ)^1669
        have hw : |(5469120597/10000000000 : ℝ)|=(5469120597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(656873321/1250000000 : ℝ)|^2181 ≤ (21568563523793/50000000000000 : ℝ)^1669
        have hw : |(656873321/1250000000 : ℝ)|=(656873321/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_box_13 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5378623137/10000000000 : ℝ)*x 0 + (-252938081/1250000000 : ℝ)*x 1 + (20527289/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5378623137/10000000000 : ℝ)^2181 ≤ (44468138894323/100000000000000 : ℝ)^1669 := by
    have hnat : (5378623137 : ℕ)^2181*100000000000000^1669 ≤ 44468138894323^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378623137 10000000000 44468138894323 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (252938081/1250000000 : ℝ)^2181 ≤ (6197370154201/50000000000000 : ℝ)^1669 := by
    have hnat : (252938081 : ℕ)^2181*50000000000000^1669 ≤ 6197370154201^1669*1250000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      252938081 1250000000 6197370154201 50000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (20527289/39062500 : ℝ)^2181 ≤ (43137120783009/100000000000000 : ℝ)^1669 := by
    have hnat : (20527289 : ℕ)^2181*100000000000000^1669 ≤ 43137120783009^1669*39062500^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20527289 39062500 43137120783009 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5378623137/10000000000 : ℝ), (-252938081/1250000000 : ℝ), (20527289/39062500 : ℝ)] ![(44468138894323/100000000000000 : ℝ), (6197370154201/50000000000000 : ℝ), (43137120783009/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5378623137/10000000000 : ℝ)|^2181 ≤ (44468138894323/100000000000000 : ℝ)^1669
        have hw : |(5378623137/10000000000 : ℝ)|=(5378623137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-252938081/1250000000 : ℝ)|^2181 ≤ (6197370154201/50000000000000 : ℝ)^1669
        have hw : |(-252938081/1250000000 : ℝ)|=(252938081/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(20527289/39062500 : ℝ)|^2181 ≤ (43137120783009/100000000000000 : ℝ)^1669
        have hw : |(20527289/39062500 : ℝ)|=(20527289/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_box_14 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1075724607/2000000000 : ℝ)*x 0 + (5254986161/10000000000 : ℝ)*x 1 + (-505876137/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075724607/2000000000 : ℝ)^2181 ≤ (44468137792333/100000000000000 : ℝ)^1669 := by
    have hnat : (1075724607 : ℕ)^2181*100000000000000^1669 ≤ 44468137792333^1669*2000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075724607 2000000000 44468137792333 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5254986161/10000000000 : ℝ)^2181 ≤ (43137122681691/100000000000000 : ℝ)^1669 := by
    have hnat : (5254986161 : ℕ)^2181*100000000000000^1669 ≤ 43137122681691^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254986161 10000000000 43137122681691 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (505876137/2500000000 : ℝ)^2181 ≤ (2478947901591/20000000000000 : ℝ)^1669 := by
    have hnat : (505876137 : ℕ)^2181*20000000000000^1669 ≤ 2478947901591^1669*2500000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      505876137 2500000000 2478947901591 20000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075724607/2000000000 : ℝ), (5254986161/10000000000 : ℝ), (-505876137/2500000000 : ℝ)] ![(44468137792333/100000000000000 : ℝ), (43137122681691/100000000000000 : ℝ), (2478947901591/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075724607/2000000000 : ℝ)|^2181 ≤ (44468137792333/100000000000000 : ℝ)^1669
        have hw : |(1075724607/2000000000 : ℝ)|=(1075724607/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5254986161/10000000000 : ℝ)|^2181 ≤ (43137122681691/100000000000000 : ℝ)^1669
        have hw : |(5254986161/10000000000 : ℝ)|=(5254986161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-505876137/2500000000 : ℝ)|^2181 ≤ (2478947901591/20000000000000 : ℝ)^1669
        have hw : |(-505876137/2500000000 : ℝ)|=(505876137/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1402_box_15 (p : ℝ) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4135865427/10000000000 : ℝ)*x 0 + (4402297421/10000000000 : ℝ)*x 1 + (2201148491/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4135865427/10000000000 : ℝ)^2181 ≤ (15772853805429/50000000000000 : ℝ)^1669 := by
    have hnat : (4135865427 : ℕ)^2181*50000000000000^1669 ≤ 15772853805429^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4135865427 10000000000 15772853805429 50000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4402297421/10000000000 : ℝ)^2181 ≤ (17113574209403/50000000000000 : ℝ)^1669 := by
    have hnat : (4402297421 : ℕ)^2181*50000000000000^1669 ≤ 17113574209403^1669*10000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4402297421 10000000000 17113574209403 50000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2201148491/5000000000 : ℝ)^2181 ≤ (34227143958597/100000000000000 : ℝ)^1669 := by
    have hnat : (2201148491 : ℕ)^2181*100000000000000^1669 ≤ 34227143958597^1669*5000000000^2181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2201148491 5000000000 34227143958597 100000000000000 2181 1669 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2181/512 : ℝ)) 2181 1669 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4135865427/10000000000 : ℝ), (4402297421/10000000000 : ℝ), (2201148491/5000000000 : ℝ)] ![(15772853805429/50000000000000 : ℝ), (17113574209403/50000000000000 : ℝ), (34227143958597/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4135865427/10000000000 : ℝ)|^2181 ≤ (15772853805429/50000000000000 : ℝ)^1669
        have hw : |(4135865427/10000000000 : ℝ)|=(4135865427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4402297421/10000000000 : ℝ)|^2181 ≤ (17113574209403/50000000000000 : ℝ)^1669
        have hw : |(4402297421/10000000000 : ℝ)|=(4402297421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2201148491/5000000000 : ℝ)|^2181 ≤ (34227143958597/100000000000000 : ℝ)^1669
        have hw : |(2201148491/5000000000 : ℝ)|=(2201148491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1402_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157097619/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7371/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2821/25000 : ℝ)*pair X i i ≤ pair X i h) :
    -(15721/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59059/100000 : ℝ) ∧ (40149/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84583/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7371/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2821/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7371/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2821/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7371/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2821/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7371/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2821/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7371/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2821/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7371/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2821/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2821/25000 : ℝ) ^ (4361/1024 : ℝ) ≤ (9218072469216001/100000000000000000000 : ℝ) := by
    have hpowers : (2821/25000 : ℝ)^4361 ≤ (9218072469216001/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2821 : ℕ)^4361*100000000000000000000^1024 ≤ 9218072469216001^1024*25000^4361 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2821 25000 9218072469216001 100000000000000000000 4361 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2821/25000 : ℝ)) (X := (9218072469216001/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4361 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7371/50000 : ℝ) ^ (4361/1024 : ℝ) ≤ (14388884410273723/50000000000000000000 : ℝ) := by
    have hpowers : (7371/50000 : ℝ)^4361 ≤ (14388884410273723/50000000000000000000 : ℝ)^1024 := by
      have hnat : (7371 : ℕ)^4361*50000000000000000000^1024 ≤ 14388884410273723^1024*50000^4361 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7371 50000 14388884410273723 50000000000000000000 4361 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7371/50000 : ℝ)) (X := (14388884410273723/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4361 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009218072469216001/50000000000000000000 : ℝ) ≤ (5000216432939021/5000000000000000 : ℝ) ^ (4361/1024 : ℝ) := by
    have hpowers : (50009218072469216001/50000000000000000000 : ℝ)^1024 ≤ (5000216432939021/5000000000000000 : ℝ)^4361 := by
      have hnat : (50009218072469216001 : ℕ)^1024*5000000000000000^4361 ≤ 5000216432939021^4361*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009218072469216001 50000000000000000000 5000216432939021 5000000000000000 1024 4361 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000216432939021/5000000000000000 : ℝ)) (X := (50009218072469216001/50000000000000000000 : ℝ)) (by norm_num) 4361 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100037995841289763447/100000000000000000000 : ℝ) ≤ (2000178409019529/2000000000000000 : ℝ) ^ (4361/1024 : ℝ) := by
    have hpowers : (100037995841289763447/100000000000000000000 : ℝ)^1024 ≤ (2000178409019529/2000000000000000 : ℝ)^4361 := by
      have hnat : (100037995841289763447 : ℕ)^1024*2000000000000000^4361 ≤ 2000178409019529^4361*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100037995841289763447 100000000000000000000 2000178409019529 2000000000000000 1024 4361 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000178409019529/2000000000000000 : ℝ)) (X := (100037995841289763447/100000000000000000000 : ℝ)) (by norm_num) 4361 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25014388884410273723/25000000000000000000 : ℝ) ≤ (156271112879957/156250000000000 : ℝ) ^ (4361/1024 : ℝ) := by
    have hpowers : (25014388884410273723/25000000000000000000 : ℝ)^1024 ≤ (156271112879957/156250000000000 : ℝ)^4361 := by
      have hnat : (25014388884410273723 : ℕ)^1024*156250000000000^4361 ≤ 156271112879957^4361*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014388884410273723 25000000000000000000 156271112879957 156250000000000 1024 4361 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156271112879957/156250000000000 : ℝ)) (X := (25014388884410273723/25000000000000000000 : ℝ)) (by norm_num) 4361 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9218072469216001/100000000000000000000 : ℝ) ≤ ((94975643114226013/95000000000000000 : ℝ)+2*(35321478431/26600000000000 : ℝ)*(2821/25000 : ℝ))^(4361/1024 : ℝ) := by
    rw [show (94975643114226013/95000000000000000 : ℝ)+2*(35321478431/26600000000000 : ℝ)*(2821/25000 : ℝ)=(5000216432939021/5000000000000000 : ℝ) by norm_num, show 1+2*(9218072469216001/100000000000000000000 : ℝ)=(50009218072469216001/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14388884410273723/50000000000000000000 : ℝ)+(9218072469216001/100000000000000000000 : ℝ) ≤ ((94975643114226013/95000000000000000 : ℝ)+(35321478431/26600000000000 : ℝ)*((7371/50000 : ℝ)+(2821/25000 : ℝ)))^(4361/1024 : ℝ) := by
    rw [show (94975643114226013/95000000000000000 : ℝ)+(35321478431/26600000000000 : ℝ)*((7371/50000 : ℝ)+(2821/25000 : ℝ))=(2000178409019529/2000000000000000 : ℝ) by norm_num, show 1+(14388884410273723/50000000000000000000 : ℝ)+(9218072469216001/100000000000000000000 : ℝ)=(100037995841289763447/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14388884410273723/50000000000000000000 : ℝ) ≤ ((94975643114226013/95000000000000000 : ℝ)+2*(35321478431/26600000000000 : ℝ)*(7371/50000 : ℝ))^(4361/1024 : ℝ) := by
    rw [show (94975643114226013/95000000000000000 : ℝ)+2*(35321478431/26600000000000 : ℝ)*(7371/50000 : ℝ)=(156271112879957/156250000000000 : ℝ) by norm_num, show 1+2*(14388884410273723/50000000000000000000 : ℝ)=(25014388884410273723/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (94975643114226013/95000000000000000 : ℝ)*(X 1 0+X 2 0)+(35321478431/26600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4361/1024 : ℝ)) (lo := (2821/25000 : ℝ)) (hi := (7371/50000 : ℝ)) (c := (94975643114226013/95000000000000000 : ℝ)) (alpha := (35321478431/26600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (94975643114226013/95000000000000000 : ℝ)*(X 0 1+X 2 1)+(35321478431/26600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4361/1024 : ℝ)) (lo := (2821/25000 : ℝ)) (hi := (7371/50000 : ℝ)) (c := (94975643114226013/95000000000000000 : ℝ)) (alpha := (35321478431/26600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (94975643114226013/95000000000000000 : ℝ)*(X 0 2+X 1 2)+(35321478431/26600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4361/1024 : ℝ)) (lo := (2821/25000 : ℝ)) (hi := (7371/50000 : ℝ)) (c := (94975643114226013/95000000000000000 : ℝ)) (alpha := (35321478431/26600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-366122123/2000000000 : ℝ)*X 0 0+(538740987/1000000000 : ℝ)*X 0 1+(2693704641/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5285845979/10000000000 : ℝ)*X 1 0+(-197003143/1000000000 : ℝ)*X 1 1+(673426137/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2642923153/5000000000 : ℝ)*X 2 0+(5387409313/10000000000 : ℝ)*X 2 1+(-492507673/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4458025679/10000000000 : ℝ)*X 0 0+(2120754489/5000000000 : ℝ)*X 0 1+(848301821/2000000000 : ℝ)*X 0 2+(4458025679/10000000000 : ℝ)*X 1 0+(2120754489/5000000000 : ℝ)*X 1 1+(848301821/2000000000 : ℝ)*X 1 2+(4458025679/10000000000 : ℝ)*X 2 0+(2120754489/5000000000 : ℝ)*X 2 1+(848301821/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2158633427/10000000000 : ℝ)*X 0 0+(5266097713/10000000000 : ℝ)*X 0 1+(5266097933/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2685419973/5000000000 : ℝ)*X 1 0+(-31548597/156250000 : ℝ)*X 1 1+(2633048791/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((268541991/500000000 : ℝ)*X 2 0+(2633048941/5000000000 : ℝ)*X 2 1+(-252388747/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1040827241/2500000000 : ℝ)*X 0 0+(4388815697/10000000000 : ℝ)*X 0 1+(4388815723/10000000000 : ℝ)*X 0 2+(1040827241/2500000000 : ℝ)*X 1 0+(4388815697/10000000000 : ℝ)*X 1 1+(4388815723/10000000000 : ℝ)*X 1 2+(1040827241/2500000000 : ℝ)*X 2 0+(4388815697/10000000000 : ℝ)*X 2 1+(4388815723/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2089603287/10000000000 : ℝ)*X 0 0+(5182310027/10000000000 : ℝ)*X 0 1+(5401398579/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2638019773/5000000000 : ℝ)*X 1 0+(-1964243501/10000000000 : ℝ)*X 1 1+(5401399199/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5276039193/10000000000 : ℝ)*X 2 0+(2700700239/5000000000 : ℝ)*X 2 1+(-392848447/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2245728061/5000000000 : ℝ)*X 0 0+(132015849/312500000 : ℝ)*X 0 1+(4224506059/10000000000 : ℝ)*X 0 2+(2245728061/5000000000 : ℝ)*X 1 0+(132015849/312500000 : ℝ)*X 1 1+(4224506059/10000000000 : ℝ)*X 1 2+(2245728061/5000000000 : ℝ)*X 2 0+(132015849/312500000 : ℝ)*X 2 1+(4224506059/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1899867851/10000000000 : ℝ)*X 0 0+(5469120597/10000000000 : ℝ)*X 0 1+(656873321/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5378623137/10000000000 : ℝ)*X 1 0+(-252938081/1250000000 : ℝ)*X 1 1+(20527289/39062500 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1075724607/2000000000 : ℝ)*X 2 0+(5254986161/10000000000 : ℝ)*X 2 1+(-505876137/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4135865427/10000000000 : ℝ)*X 0 0+(4402297421/10000000000 : ℝ)*X 0 1+(2201148491/5000000000 : ℝ)*X 0 2+(4135865427/10000000000 : ℝ)*X 1 0+(4402297421/10000000000 : ℝ)*X 1 1+(2201148491/5000000000 : ℝ)*X 1 2+(4135865427/10000000000 : ℝ)*X 2 0+(4402297421/10000000000 : ℝ)*X 2 1+(2201148491/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1402_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-15721/25000 : ℝ) ≤ (-20907994345769471436538030985583/33250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (25154879/100000000000000 : ℝ)*(lower0) + (38764011/100000000000000 : ℝ)*(lower2) + (5198701/6250000000000 : ℝ)*(lower3) + (17105159/100000000000000 : ℝ)*(lower4) + (2987229266417471/100000000000000 : ℝ)*(major0) + (2987229266417471/100000000000000 : ℝ)*(major1) + (2987229266417471/100000000000000 : ℝ)*(major2) + (623569573/12500000000000 : ℝ)*(sp1) + (127934607629449/3125000000000 : ℝ)*(sp4) + (511737806948223/12500000000000 : ℝ)*(sp5) + (51173347717191/1250000000000 : ℝ)*(sp6) + (475373835570059/25000000000000 : ℝ)*(sp7) + (2476672943/6250000000000 : ℝ)*(sp14) + (16141746439/100000000000000 : ℝ)*(sp15) + (76060459361067/4000000000000 : ℝ)*(f.failure) + (127934607629449/3125000000000 : ℝ)*(f.sum) + (3712106856071/1330000000000000000000000000 : ℝ)*base65 + (273589978976363139/66500000000000000000000000000000 : ℝ)*base68 + (95304116086136861/66500000000000000000000000000000 : ℝ)*base69 + (15226127000636861/66500000000000000000000000000000 : ℝ)*base71 + (3472420509731/1330000000000000000000000000 : ℝ)*base73 + (162752605054136861/66500000000000000000000000000000 : ℝ)*base75 + (231955588619363139/66500000000000000000000000000000 : ℝ)*base78 + (521336275047636861/66500000000000000000000000000000 : ℝ)*base79 + (6491418267259/1330000000000000000000000000 : ℝ)*base82 + (2999473/400000000000000000000 : ℝ)*base89 + (2999473/400000000000000000000 : ℝ)*base91 + (2999473/400000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (59059/100000 : ℝ) ≤ (2454749653794928724739461929377/4156250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (25139631/12500000000000 : ℝ)*(lower1) + (6715199/5000000000000 : ℝ)*(lower2) + (221679151/100000000000000 : ℝ)*(upper4) + (382242149202183/12500000000000 : ℝ)*(major0) + (382242149202183/12500000000000 : ℝ)*(major1) + (382242149202183/12500000000000 : ℝ)*(major2) + (2074827292550043/50000000000000 : ℝ)*(sp0) + (2074727829427051/50000000000000 : ℝ)*(sp1) + (20748326086711/500000000000 : ℝ)*(sp2) + (243314881791583/12500000000000 : ℝ)*(sp3) + (1559800471/100000000000000 : ℝ)*(sp6) + (1340491057/100000000000000 : ℝ)*(sp7) + (1524005323/12500000000000 : ℝ)*(sp8) + (211118288569/100000000000000 : ℝ)*(sp9) + (1946520394823721/100000000000000 : ℝ)*(f.failure) + (4149666777142671/100000000000000 : ℝ)*(f.sum) + (1653081349499/332500000000000000000000000 : ℝ)*base66 + (33537133369332847/8312500000000000000000000000000 : ℝ)*base68 + (24633312127457847/8312500000000000000000000000000 : ℝ)*base70 + (25032628143770347/8312500000000000000000000000000 : ℝ)*base72 + (16584953297/166250000000000000000000000 : ℝ)*base74 + (44239853218395347/8312500000000000000000000000000 : ℝ)*base76 + (35185207150270347/8312500000000000000000000000000 : ℝ)*base78 + (59598254226957847/8312500000000000000000000000000 : ℝ)*base80 + (828350440783/665000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (93820299/10000000000000000000000 : ℝ)*base89 + (93820299/10000000000000000000000 : ℝ)*base91 + (93820299/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (40149/50000 : ℝ) ≤ (13350003395874346094702363889639/16625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (59858343/100000000000000 : ℝ)*(lower3) + (230064643/50000000000000 : ℝ)*(upper4) + (86364623/100000000000000 : ℝ)*(lower5) + (3367313075753843/100000000000000 : ℝ)*(major0) + (3367313075753843/100000000000000 : ℝ)*(major1) + (3367313075753843/100000000000000 : ℝ)*(major2) + (29521952801/100000000000000 : ℝ)*(sp0) + (68646865459/25000000000000 : ℝ)*(sp1) + (227010026573/25000000000000 : ℝ)*(sp2) + (1398991641/500000000000 : ℝ)*(sp3) + (4564377056591377/100000000000000 : ℝ)*(sp8) + (2282065995541171/50000000000000 : ℝ)*(sp9) + (4563498538437887/100000000000000 : ℝ)*(sp10) + (1071586425266649/50000000000000 : ℝ)*(sp11) + (1071726324430749/50000000000000 : ℝ)*(f.failure) + (2282203289272089/50000000000000 : ℝ)*(f.sum) + (2669282064527/1330000000000000000000000000 : ℝ)*base66 + (125361448281050713/66500000000000000000000000000000 : ℝ)*base67 + (141398183479949287/66500000000000000000000000000000 : ℝ)*base70 + (493208891382449287/66500000000000000000000000000000 : ℝ)*base72 + (1255805279527/1330000000000000000000000000 : ℝ)*base74 + (198345601388449287/66500000000000000000000000000000 : ℝ)*base76 + (948920647787949287/66500000000000000000000000000000 : ℝ)*base78 + (406334269863449287/66500000000000000000000000000000 : ℝ)*base80 + (7430095903243/1330000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (48286631/5000000000000000000000 : ℝ)*base89 + (48286631/5000000000000000000000 : ℝ)*base91 + (48286631/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-84583/100000 : ℝ) ≤ (-7030747493987033532726801458727/8312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (99221561/100000000000000 : ℝ)*(lower0) + (9622853/100000000000000 : ℝ)*(lower2) + (923069/5000000000000 : ℝ)*(lower3) + (1702214579284999/50000000000000 : ℝ)*(major0) + (1702214579284999/50000000000000 : ℝ)*(major1) + (1702214579284999/50000000000000 : ℝ)*(major2) + (243712567/4000000000000 : ℝ)*(sp4) + (234921198831/100000000000000 : ℝ)*(sp5) + (161356299871/100000000000000 : ℝ)*(sp6) + (7982713047/100000000000000 : ℝ)*(sp7) + (4669966922228019/100000000000000 : ℝ)*(sp12) + (2334869046921681/50000000000000 : ℝ)*(sp13) + (4669811658742323/100000000000000 : ℝ)*(sp14) + (433414158608969/20000000000000 : ℝ)*(sp15) + (541769693939473/25000000000000 : ℝ)*(f.failure) + (2334986507521097/50000000000000 : ℝ)*(f.sum) + (466240706429/166250000000000000000000000 : ℝ)*base66 + (315627908018077909/33250000000000000000000000000000 : ℝ)*base67 + (118102551836077909/33250000000000000000000000000000 : ℝ)*base69 + (278039972669827909/33250000000000000000000000000000 : ℝ)*base71 + (2209194353369/665000000000000000000000000 : ℝ)*base73 + (288578102051327909/33250000000000000000000000000000 : ℝ)*base75 + (213877278846422091/33250000000000000000000000000000 : ℝ)*base78 + (265251627460327909/33250000000000000000000000000000 : ℝ)*base79 + (2750047323/332500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (11585213/2500000000000000000000 : ℝ)*base90 + (11585213/2500000000000000000000 : ℝ)*base92 + (11585213/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1402_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157097619/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7371/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2821/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15721/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(59059/100000 : ℝ) else (40149/50000 : ℝ) ≤ X j i ∧ X j i ≤ (84583/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1402_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1402_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157097619/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3687/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11279/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15721/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(59059/100000 : ℝ) else (40149/50000 : ℝ) ≤ X j i ∧ X j i ≤ (84583/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1402_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1402_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1402_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4361/1024 : ℝ) ≤ p) (hpb : p ≤ (2181/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157097619/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3687/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11279/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15721/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(59059/100000 : ℝ) else (40149/50000 : ℝ) ≤ X j i ∧ X j i ≤ (84583/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1402_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
