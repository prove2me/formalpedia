-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1400_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:44:50.574488+00:00
-- url     : https://prove2.me/submissions/3bfc5326-4b2c-4f22-b42e-d25a1cee8d29

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
theorem support_rectangle_w1400_s3_0 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1993653481/10000000000 : ℝ)*x 0 + (1355079709/2500000000 : ℝ)*x 1 + (2618220039/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1993653481/10000000000 : ℝ)^545 ≤ (151909190391/1250000000000 : ℝ)^417 := by
    have hnat : (1993653481 : ℕ)^545*1250000000000^417 ≤ 151909190391^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1993653481 10000000000 151909190391 1250000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1355079709/2500000000 : ℝ)^545 ≤ (8982817405877/20000000000000 : ℝ)^417 := by
    have hnat : (1355079709 : ℕ)^545*20000000000000^417 ≤ 8982817405877^417*2500000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355079709 2500000000 8982817405877 20000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2618220039/5000000000 : ℝ)^545 ≤ (10733294432113/25000000000000 : ℝ)^417 := by
    have hnat : (2618220039 : ℕ)^545*25000000000000^417 ≤ 10733294432113^417*5000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2618220039 5000000000 10733294432113 25000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1993653481/10000000000 : ℝ), (1355079709/2500000000 : ℝ), (2618220039/5000000000 : ℝ)] ![(151909190391/1250000000000 : ℝ), (8982817405877/20000000000000 : ℝ), (10733294432113/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1993653481/10000000000 : ℝ)|^545 ≤ (151909190391/1250000000000 : ℝ)^417
        have hw : |(-1993653481/10000000000 : ℝ)|=(1993653481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1355079709/2500000000 : ℝ)|^545 ≤ (8982817405877/20000000000000 : ℝ)^417
        have hw : |(1355079709/2500000000 : ℝ)|=(1355079709/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2618220039/5000000000 : ℝ)|^545 ≤ (10733294432113/25000000000000 : ℝ)^417
        have hw : |(2618220039/5000000000 : ℝ)|=(2618220039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_s3_1 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5350647399/10000000000 : ℝ)*x 0 + (-417500719/2000000000 : ℝ)*x 1 + (5236440071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350647399/10000000000 : ℝ)^545 ≤ (5520132017617/12500000000000 : ℝ)^417 := by
    have hnat : (5350647399 : ℕ)^545*12500000000000^417 ≤ 5520132017617^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350647399 10000000000 5520132017617 12500000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (417500719/2000000000 : ℝ)^545 ≤ (3226441545031/25000000000000 : ℝ)^417 := by
    have hnat : (417500719 : ℕ)^545*25000000000000^417 ≤ 3226441545031^417*2000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417500719 2000000000 3226441545031 25000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5236440071/10000000000 : ℝ)^545 ≤ (42933177653443/100000000000000 : ℝ)^417 := by
    have hnat : (5236440071 : ℕ)^545*100000000000000^417 ≤ 42933177653443^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5236440071 10000000000 42933177653443 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350647399/10000000000 : ℝ), (-417500719/2000000000 : ℝ), (5236440071/10000000000 : ℝ)] ![(5520132017617/12500000000000 : ℝ), (3226441545031/25000000000000 : ℝ), (42933177653443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350647399/10000000000 : ℝ)|^545 ≤ (5520132017617/12500000000000 : ℝ)^417
        have hw : |(5350647399/10000000000 : ℝ)|=(5350647399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-417500719/2000000000 : ℝ)|^545 ≤ (3226441545031/25000000000000 : ℝ)^417
        have hw : |(-417500719/2000000000 : ℝ)|=(417500719/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5236440071/10000000000 : ℝ)|^545 ≤ (42933177653443/100000000000000 : ℝ)^417
        have hw : |(5236440071/10000000000 : ℝ)|=(5236440071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_s3_2 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2675323733/5000000000 : ℝ)*x 0 + (5236440049/10000000000 : ℝ)*x 1 + (-2087503537/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675323733/5000000000 : ℝ)^545 ≤ (44161056863653/100000000000000 : ℝ)^417 := by
    have hnat : (2675323733 : ℕ)^545*100000000000000^417 ≤ 44161056863653^417*5000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675323733 5000000000 44161056863653 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5236440049/10000000000 : ℝ)^545 ≤ (42933177417699/100000000000000 : ℝ)^417 := by
    have hnat : (5236440049 : ℕ)^545*100000000000000^417 ≤ 42933177417699^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5236440049 10000000000 42933177417699 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2087503537/10000000000 : ℝ)^545 ≤ (6452882855739/50000000000000 : ℝ)^417 := by
    have hnat : (2087503537 : ℕ)^545*50000000000000^417 ≤ 6452882855739^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2087503537 10000000000 6452882855739 50000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675323733/5000000000 : ℝ), (5236440049/10000000000 : ℝ), (-2087503537/10000000000 : ℝ)] ![(44161056863653/100000000000000 : ℝ), (42933177417699/100000000000000 : ℝ), (6452882855739/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675323733/5000000000 : ℝ)|^545 ≤ (44161056863653/100000000000000 : ℝ)^417
        have hw : |(2675323733/5000000000 : ℝ)|=(2675323733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5236440049/10000000000 : ℝ)|^545 ≤ (42933177417699/100000000000000 : ℝ)^417
        have hw : |(5236440049/10000000000 : ℝ)|=(5236440049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2087503537/10000000000 : ℝ)|^545 ≤ (6452882855739/50000000000000 : ℝ)^417
        have hw : |(-2087503537/10000000000 : ℝ)|=(2087503537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_s3_3 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (862183147/2000000000 : ℝ)*x 0 + (2059110499/5000000000 : ℝ)*x 1 + (2255894739/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (862183147/2000000000 : ℝ)^545 ≤ (4162066778889/12500000000000 : ℝ)^417 := by
    have hnat : (862183147 : ℕ)^545*12500000000000^417 ≤ 4162066778889^417*2000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      862183147 2000000000 4162066778889 12500000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2059110499/5000000000 : ℝ)^545 ≤ (15682419622753/50000000000000 : ℝ)^417 := by
    have hnat : (2059110499 : ℕ)^545*50000000000000^417 ≤ 15682419622753^417*5000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2059110499 5000000000 15682419622753 50000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2255894739/5000000000 : ℝ)^545 ≤ (7067725303901/20000000000000 : ℝ)^417 := by
    have hnat : (2255894739 : ℕ)^545*20000000000000^417 ≤ 7067725303901^417*5000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2255894739 5000000000 7067725303901 20000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(862183147/2000000000 : ℝ), (2059110499/5000000000 : ℝ), (2255894739/5000000000 : ℝ)] ![(4162066778889/12500000000000 : ℝ), (15682419622753/50000000000000 : ℝ), (7067725303901/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(862183147/2000000000 : ℝ)|^545 ≤ (4162066778889/12500000000000 : ℝ)^417
        have hw : |(862183147/2000000000 : ℝ)|=(862183147/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2059110499/5000000000 : ℝ)|^545 ≤ (15682419622753/50000000000000 : ℝ)^417
        have hw : |(2059110499/5000000000 : ℝ)|=(2059110499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2255894739/5000000000 : ℝ)|^545 ≤ (7067725303901/20000000000000 : ℝ)^417
        have hw : |(2255894739/5000000000 : ℝ)|=(2255894739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_s3_4 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-249208791/1250000000 : ℝ)*x 0 + (5237183517/10000000000 : ℝ)*x 1 + (2709785403/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (249208791/1250000000 : ℝ)^545 ≤ (1215286944841/10000000000000 : ℝ)^417 := by
    have hnat : (249208791 : ℕ)^545*10000000000000^417 ≤ 1215286944841^417*1250000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249208791 1250000000 1215286944841 10000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5237183517/10000000000 : ℝ)^545 ≤ (4294114431257/10000000000000 : ℝ)^417 := by
    have hnat : (5237183517 : ℕ)^545*10000000000000^417 ≤ 4294114431257^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5237183517 10000000000 4294114431257 10000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2709785403/5000000000 : ℝ)^545 ≤ (22452993113791/50000000000000 : ℝ)^417 := by
    have hnat : (2709785403 : ℕ)^545*50000000000000^417 ≤ 22452993113791^417*5000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709785403 5000000000 22452993113791 50000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-249208791/1250000000 : ℝ), (5237183517/10000000000 : ℝ), (2709785403/5000000000 : ℝ)] ![(1215286944841/10000000000000 : ℝ), (4294114431257/10000000000000 : ℝ), (22452993113791/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-249208791/1250000000 : ℝ)|^545 ≤ (1215286944841/10000000000000 : ℝ)^417
        have hw : |(-249208791/1250000000 : ℝ)|=(249208791/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5237183517/10000000000 : ℝ)|^545 ≤ (4294114431257/10000000000000 : ℝ)^417
        have hw : |(5237183517/10000000000 : ℝ)|=(5237183517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2709785403/5000000000 : ℝ)|^545 ≤ (22452993113791/50000000000000 : ℝ)^417
        have hw : |(2709785403/5000000000 : ℝ)|=(2709785403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_s3_5 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5302983621/10000000000 : ℝ)*x 0 + (-1904372307/10000000000 : ℝ)*x 1 + (5419571283/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302983621/10000000000 : ℝ)^545 ≤ (43647619763533/100000000000000 : ℝ)^417 := by
    have hnat : (5302983621 : ℕ)^545*100000000000000^417 ≤ 43647619763533^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302983621 10000000000 43647619763533 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1904372307/10000000000 : ℝ)^545 ≤ (11446388831453/100000000000000 : ℝ)^417 := by
    have hnat : (1904372307 : ℕ)^545*100000000000000^417 ≤ 11446388831453^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1904372307 10000000000 11446388831453 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5419571283/10000000000 : ℝ)^545 ≤ (44905991393151/100000000000000 : ℝ)^417 := by
    have hnat : (5419571283 : ℕ)^545*100000000000000^417 ≤ 44905991393151^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419571283 10000000000 44905991393151 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302983621/10000000000 : ℝ), (-1904372307/10000000000 : ℝ), (5419571283/10000000000 : ℝ)] ![(43647619763533/100000000000000 : ℝ), (11446388831453/100000000000000 : ℝ), (44905991393151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302983621/10000000000 : ℝ)|^545 ≤ (43647619763533/100000000000000 : ℝ)^417
        have hw : |(5302983621/10000000000 : ℝ)|=(5302983621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1904372307/10000000000 : ℝ)|^545 ≤ (11446388831453/100000000000000 : ℝ)^417
        have hw : |(-1904372307/10000000000 : ℝ)|=(1904372307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5419571283/10000000000 : ℝ)|^545 ≤ (44905991393151/100000000000000 : ℝ)^417
        have hw : |(5419571283/10000000000 : ℝ)|=(5419571283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_s3_6 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5302984609/10000000000 : ℝ)*x 0 + (1083914109/2000000000 : ℝ)*x 1 + (-1904371971/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302984609/10000000000 : ℝ)^545 ≤ (43647630391683/100000000000000 : ℝ)^417 := by
    have hnat : (5302984609 : ℕ)^545*100000000000000^417 ≤ 43647630391683^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302984609 10000000000 43647630391683 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1083914109/2000000000 : ℝ)^545 ≤ (44905983401139/100000000000000 : ℝ)^417 := by
    have hnat : (1083914109 : ℕ)^545*100000000000000^417 ≤ 44905983401139^417*2000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083914109 2000000000 44905983401139 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1904371971/10000000000 : ℝ)^545 ≤ (2289277238397/20000000000000 : ℝ)^417 := by
    have hnat : (1904371971 : ℕ)^545*20000000000000^417 ≤ 2289277238397^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1904371971 10000000000 2289277238397 20000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302984609/10000000000 : ℝ), (1083914109/2000000000 : ℝ), (-1904371971/10000000000 : ℝ)] ![(43647630391683/100000000000000 : ℝ), (44905983401139/100000000000000 : ℝ), (2289277238397/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302984609/10000000000 : ℝ)|^545 ≤ (43647630391683/100000000000000 : ℝ)^417
        have hw : |(5302984609/10000000000 : ℝ)|=(5302984609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1083914109/2000000000 : ℝ)|^545 ≤ (44905983401139/100000000000000 : ℝ)^417
        have hw : |(1083914109/2000000000 : ℝ)|=(1083914109/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1904371971/10000000000 : ℝ)|^545 ≤ (2289277238397/20000000000000 : ℝ)^417
        have hw : |(-1904371971/10000000000 : ℝ)|=(1904371971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_s3_7 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4310952083/10000000000 : ℝ)*x 0 + (451019791/1000000000 : ℝ)*x 1 + (205991037/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4310952083/10000000000 : ℝ)^545 ≤ (4162112643851/12500000000000 : ℝ)^417 := by
    have hnat : (4310952083 : ℕ)^545*12500000000000^417 ≤ 4162112643851^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4310952083 10000000000 4162112643851 12500000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (451019791/1000000000 : ℝ)^545 ≤ (35322334948349/100000000000000 : ℝ)^417 := by
    have hnat : (451019791 : ℕ)^545*100000000000000^417 ≤ 35322334948349^417*1000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451019791 1000000000 35322334948349 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (205991037/500000000 : ℝ)^545 ≤ (31380763888347/100000000000000 : ℝ)^417 := by
    have hnat : (205991037 : ℕ)^545*100000000000000^417 ≤ 31380763888347^417*500000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205991037 500000000 31380763888347 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4310952083/10000000000 : ℝ), (451019791/1000000000 : ℝ), (205991037/500000000 : ℝ)] ![(4162112643851/12500000000000 : ℝ), (35322334948349/100000000000000 : ℝ), (31380763888347/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4310952083/10000000000 : ℝ)|^545 ≤ (4162112643851/12500000000000 : ℝ)^417
        have hw : |(4310952083/10000000000 : ℝ)|=(4310952083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(451019791/1000000000 : ℝ)|^545 ≤ (35322334948349/100000000000000 : ℝ)^417
        have hw : |(451019791/1000000000 : ℝ)|=(451019791/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(205991037/500000000 : ℝ)|^545 ≤ (31380763888347/100000000000000 : ℝ)^417
        have hw : |(205991037/500000000 : ℝ)|=(205991037/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_s3_8 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-205483/25000000 : ℝ)*x 0 + (5712345691/10000000000 : ℝ)*x 1 + (1207452817/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (205483/25000000 : ℝ)^545 ≤ (23533987987/12500000000000 : ℝ)^417 := by
    have hnat : (205483 : ℕ)^545*12500000000000^417 ≤ 23533987987^417*25000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205483 25000000 23533987987 12500000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5712345691/10000000000 : ℝ)^545 ≤ (48102495513437/100000000000000 : ℝ)^417 := by
    have hnat : (5712345691 : ℕ)^545*100000000000000^417 ≤ 48102495513437^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5712345691 10000000000 48102495513437 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1207452817/2000000000 : ℝ)^545 ≤ (2585461628387/5000000000000 : ℝ)^417 := by
    have hnat : (1207452817 : ℕ)^545*5000000000000^417 ≤ 2585461628387^417*2000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1207452817 2000000000 2585461628387 5000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-205483/25000000 : ℝ), (5712345691/10000000000 : ℝ), (1207452817/2000000000 : ℝ)] ![(23533987987/12500000000000 : ℝ), (48102495513437/100000000000000 : ℝ), (2585461628387/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-205483/25000000 : ℝ)|^545 ≤ (23533987987/12500000000000 : ℝ)^417
        have hw : |(-205483/25000000 : ℝ)|=(205483/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5712345691/10000000000 : ℝ)|^545 ≤ (48102495513437/100000000000000 : ℝ)^417
        have hw : |(5712345691/10000000000 : ℝ)|=(5712345691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1207452817/2000000000 : ℝ)|^545 ≤ (2585461628387/5000000000000 : ℝ)^417
        have hw : |(1207452817/2000000000 : ℝ)|=(1207452817/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_s3_9 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (518542961/5000000000 : ℝ)*x 0 + (-2099672593/5000000000 : ℝ)*x 1 + (6992464071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (518542961/5000000000 : ℝ)^545 ≤ (2586334607489/50000000000000 : ℝ)^417 := by
    have hnat : (518542961 : ℕ)^545*50000000000000^417 ≤ 2586334607489^417*5000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518542961 5000000000 2586334607489 50000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2099672593/5000000000 : ℝ)^545 ≤ (32174772724901/100000000000000 : ℝ)^417 := by
    have hnat : (2099672593 : ℕ)^545*100000000000000^417 ≤ 32174772724901^417*5000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2099672593 5000000000 32174772724901 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6992464071/10000000000 : ℝ)^545 ≤ (7831569755151/12500000000000 : ℝ)^417 := by
    have hnat : (6992464071 : ℕ)^545*12500000000000^417 ≤ 7831569755151^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6992464071 10000000000 7831569755151 12500000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(518542961/5000000000 : ℝ), (-2099672593/5000000000 : ℝ), (6992464071/10000000000 : ℝ)] ![(2586334607489/50000000000000 : ℝ), (32174772724901/100000000000000 : ℝ), (7831569755151/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(518542961/5000000000 : ℝ)|^545 ≤ (2586334607489/50000000000000 : ℝ)^417
        have hw : |(518542961/5000000000 : ℝ)|=(518542961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2099672593/5000000000 : ℝ)|^545 ≤ (32174772724901/100000000000000 : ℝ)^417
        have hw : |(-2099672593/5000000000 : ℝ)|=(2099672593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6992464071/10000000000 : ℝ)|^545 ≤ (7831569755151/12500000000000 : ℝ)^417
        have hw : |(6992464071/10000000000 : ℝ)|=(6992464071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_s3_10 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (32409231/312500000 : ℝ)*x 0 + (6992484833/10000000000 : ℝ)*x 1 + (-2099657371/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (32409231/312500000 : ℝ)^545 ≤ (5172730947071/100000000000000 : ℝ)^417 := by
    have hnat : (32409231 : ℕ)^545*100000000000000^417 ≤ 5172730947071^417*312500000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32409231 312500000 5172730947071 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6992484833/10000000000 : ℝ)^545 ≤ (31326400585561/50000000000000 : ℝ)^417 := by
    have hnat : (6992484833 : ℕ)^545*50000000000000^417 ≤ 31326400585561^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6992484833 10000000000 31326400585561 50000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2099657371/5000000000 : ℝ)^545 ≤ (32174467868309/100000000000000 : ℝ)^417 := by
    have hnat : (2099657371 : ℕ)^545*100000000000000^417 ≤ 32174467868309^417*5000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2099657371 5000000000 32174467868309 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(32409231/312500000 : ℝ), (6992484833/10000000000 : ℝ), (-2099657371/5000000000 : ℝ)] ![(5172730947071/100000000000000 : ℝ), (31326400585561/50000000000000 : ℝ), (32174467868309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(32409231/312500000 : ℝ)|^545 ≤ (5172730947071/100000000000000 : ℝ)^417
        have hw : |(32409231/312500000 : ℝ)|=(32409231/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6992484833/10000000000 : ℝ)|^545 ≤ (31326400585561/50000000000000 : ℝ)^417
        have hw : |(6992484833/10000000000 : ℝ)|=(6992484833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2099657371/5000000000 : ℝ)|^545 ≤ (32174467868309/100000000000000 : ℝ)^417
        have hw : |(-2099657371/5000000000 : ℝ)|=(2099657371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_s3_11 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (979900243/10000000000 : ℝ)*x 0 + (2911260387/5000000000 : ℝ)*x 1 + (1101826009/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (979900243/10000000000 : ℝ)^545 ≤ (2401544661967/50000000000000 : ℝ)^417 := by
    have hnat : (979900243 : ℕ)^545*50000000000000^417 ≤ 2401544661967^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      979900243 10000000000 2401544661967 50000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2911260387/5000000000 : ℝ)^545 ≤ (49318611422847/100000000000000 : ℝ)^417 := by
    have hnat : (2911260387 : ℕ)^545*100000000000000^417 ≤ 49318611422847^417*5000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2911260387 5000000000 49318611422847 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1101826009/2000000000 : ℝ)^545 ≤ (5734787405331/12500000000000 : ℝ)^417 := by
    have hnat : (1101826009 : ℕ)^545*12500000000000^417 ≤ 5734787405331^417*2000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101826009 2000000000 5734787405331 12500000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(979900243/10000000000 : ℝ), (2911260387/5000000000 : ℝ), (1101826009/2000000000 : ℝ)] ![(2401544661967/50000000000000 : ℝ), (49318611422847/100000000000000 : ℝ), (5734787405331/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(979900243/10000000000 : ℝ)|^545 ≤ (2401544661967/50000000000000 : ℝ)^417
        have hw : |(979900243/10000000000 : ℝ)|=(979900243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2911260387/5000000000 : ℝ)|^545 ≤ (49318611422847/100000000000000 : ℝ)^417
        have hw : |(2911260387/5000000000 : ℝ)|=(2911260387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1101826009/2000000000 : ℝ)|^545 ≤ (5734787405331/12500000000000 : ℝ)^417
        have hw : |(1101826009/2000000000 : ℝ)|=(1101826009/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1400_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157018501/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3973/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10207/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1107/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14963/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3973/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10207/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3973/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10207/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3973/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10207/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3973/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10207/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3973/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10207/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3973/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10207/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10207/100000 : ℝ) ^ (4359/1024 : ℝ) ≤ (1208013736939399/20000000000000000000 : ℝ) := by
    have hpowers : (10207/100000 : ℝ)^4359 ≤ (1208013736939399/20000000000000000000 : ℝ)^1024 := by
      have hnat : (10207 : ℕ)^4359*20000000000000000000^1024 ≤ 1208013736939399^1024*100000^4359 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10207 100000 1208013736939399 20000000000000000000 4359 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10207/100000 : ℝ)) (X := (1208013736939399/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4359 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3973/25000 : ℝ) ^ (4359/1024 : ℝ) ≤ (39769320544708623/100000000000000000000 : ℝ) := by
    have hpowers : (3973/25000 : ℝ)^4359 ≤ (39769320544708623/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3973 : ℕ)^4359*100000000000000000000^1024 ≤ 39769320544708623^1024*25000^4359 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3973 25000 39769320544708623 100000000000000000000 4359 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3973/25000 : ℝ)) (X := (39769320544708623/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4359 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001208013736939399/10000000000000000000 : ℝ) ≤ (39063608472509/39062500000000 : ℝ) ^ (4359/1024 : ℝ) := by
    have hpowers : (10001208013736939399/10000000000000000000 : ℝ)^1024 ≤ (39063608472509/39062500000000 : ℝ)^4359 := by
      have hnat : (10001208013736939399 : ℕ)^1024*39062500000000^4359 ≤ 39063608472509^4359*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001208013736939399 10000000000000000000 39063608472509 39062500000000 1024 4359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (39063608472509/39062500000000 : ℝ)) (X := (10001208013736939399/10000000000000000000 : ℝ)) (by norm_num) 4359 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022904694614702809/50000000000000000000 : ℝ) ≤ (2500268987132833/2500000000000000 : ℝ) ^ (4359/1024 : ℝ) := by
    have hpowers : (50022904694614702809/50000000000000000000 : ℝ)^1024 ≤ (2500268987132833/2500000000000000 : ℝ)^4359 := by
      have hnat : (50022904694614702809 : ℕ)^1024*2500000000000000^4359 ≤ 2500268987132833^4359*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022904694614702809 50000000000000000000 2500268987132833 2500000000000000 1024 4359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500268987132833/2500000000000000 : ℝ)) (X := (50022904694614702809/50000000000000000000 : ℝ)) (by norm_num) 4359 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50039769320544708623/50000000000000000000 : ℝ) ≤ (250046703202509/250000000000000 : ℝ) ^ (4359/1024 : ℝ) := by
    have hpowers : (50039769320544708623/50000000000000000000 : ℝ)^1024 ≤ (250046703202509/250000000000000 : ℝ)^4359 := by
      have hnat : (50039769320544708623 : ℕ)^1024*250000000000000^4359 ≤ 250046703202509^4359*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50039769320544708623 50000000000000000000 250046703202509 250000000000000 1024 4359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250046703202509/250000000000000 : ℝ)) (X := (50039769320544708623/50000000000000000000 : ℝ)) (by norm_num) 4359 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1208013736939399/20000000000000000000 : ℝ) ≤ ((7104430209103570081/7106250000000000000 : ℝ)+2*(198044892257/142125000000000 : ℝ)*(10207/100000 : ℝ))^(4359/1024 : ℝ) := by
    rw [show (7104430209103570081/7106250000000000000 : ℝ)+2*(198044892257/142125000000000 : ℝ)*(10207/100000 : ℝ)=(39063608472509/39062500000000 : ℝ) by norm_num, show 1+2*(1208013736939399/20000000000000000000 : ℝ)=(10001208013736939399/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(39769320544708623/100000000000000000000 : ℝ)+(1208013736939399/20000000000000000000 : ℝ) ≤ ((7104430209103570081/7106250000000000000 : ℝ)+(198044892257/142125000000000 : ℝ)*((3973/25000 : ℝ)+(10207/100000 : ℝ)))^(4359/1024 : ℝ) := by
    rw [show (7104430209103570081/7106250000000000000 : ℝ)+(198044892257/142125000000000 : ℝ)*((3973/25000 : ℝ)+(10207/100000 : ℝ))=(2500268987132833/2500000000000000 : ℝ) by norm_num, show 1+(39769320544708623/100000000000000000000 : ℝ)+(1208013736939399/20000000000000000000 : ℝ)=(50022904694614702809/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(39769320544708623/100000000000000000000 : ℝ) ≤ ((7104430209103570081/7106250000000000000 : ℝ)+2*(198044892257/142125000000000 : ℝ)*(3973/25000 : ℝ))^(4359/1024 : ℝ) := by
    rw [show (7104430209103570081/7106250000000000000 : ℝ)+2*(198044892257/142125000000000 : ℝ)*(3973/25000 : ℝ)=(250046703202509/250000000000000 : ℝ) by norm_num, show 1+2*(39769320544708623/100000000000000000000 : ℝ)=(50039769320544708623/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7104430209103570081/7106250000000000000 : ℝ)*(X 1 0+X 2 0)+(198044892257/142125000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4359/1024 : ℝ)) (lo := (10207/100000 : ℝ)) (hi := (3973/25000 : ℝ)) (c := (7104430209103570081/7106250000000000000 : ℝ)) (alpha := (198044892257/142125000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7104430209103570081/7106250000000000000 : ℝ)*(X 0 1+X 2 1)+(198044892257/142125000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4359/1024 : ℝ)) (lo := (10207/100000 : ℝ)) (hi := (3973/25000 : ℝ)) (c := (7104430209103570081/7106250000000000000 : ℝ)) (alpha := (198044892257/142125000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7104430209103570081/7106250000000000000 : ℝ)*(X 0 2+X 1 2)+(198044892257/142125000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4359/1024 : ℝ)) (lo := (10207/100000 : ℝ)) (hi := (3973/25000 : ℝ)) (c := (7104430209103570081/7106250000000000000 : ℝ)) (alpha := (198044892257/142125000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1993653481/10000000000 : ℝ)*X 0 0+(1355079709/2500000000 : ℝ)*X 0 1+(2618220039/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350647399/10000000000 : ℝ)*X 1 0+(-417500719/2000000000 : ℝ)*X 1 1+(5236440071/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675323733/5000000000 : ℝ)*X 2 0+(5236440049/10000000000 : ℝ)*X 2 1+(-2087503537/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((862183147/2000000000 : ℝ)*X 0 0+(2059110499/5000000000 : ℝ)*X 0 1+(2255894739/5000000000 : ℝ)*X 0 2+(862183147/2000000000 : ℝ)*X 1 0+(2059110499/5000000000 : ℝ)*X 1 1+(2255894739/5000000000 : ℝ)*X 1 2+(862183147/2000000000 : ℝ)*X 2 0+(2059110499/5000000000 : ℝ)*X 2 1+(2255894739/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-249208791/1250000000 : ℝ)*X 0 0+(5237183517/10000000000 : ℝ)*X 0 1+(2709785403/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5302983621/10000000000 : ℝ)*X 1 0+(-1904372307/10000000000 : ℝ)*X 1 1+(5419571283/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5302984609/10000000000 : ℝ)*X 2 0+(1083914109/2000000000 : ℝ)*X 2 1+(-1904371971/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4310952083/10000000000 : ℝ)*X 0 0+(451019791/1000000000 : ℝ)*X 0 1+(205991037/500000000 : ℝ)*X 0 2+(4310952083/10000000000 : ℝ)*X 1 0+(451019791/1000000000 : ℝ)*X 1 1+(205991037/500000000 : ℝ)*X 1 2+(4310952083/10000000000 : ℝ)*X 2 0+(451019791/1000000000 : ℝ)*X 2 1+(205991037/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-205483/25000000 : ℝ)*X 0 0+(5712345691/10000000000 : ℝ)*X 0 1+(1207452817/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s3_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((518542961/5000000000 : ℝ)*X 1 0+(-2099672593/5000000000 : ℝ)*X 1 1+(6992464071/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s3_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((32409231/312500000 : ℝ)*X 2 0+(6992484833/10000000000 : ℝ)*X 2 1+(-2099657371/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s3_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((979900243/10000000000 : ℝ)*X 0 0+(2911260387/5000000000 : ℝ)*X 0 1+(1101826009/2000000000 : ℝ)*X 0 2+(979900243/10000000000 : ℝ)*X 1 0+(2911260387/5000000000 : ℝ)*X 1 1+(1101826009/2000000000 : ℝ)*X 1 2+(979900243/10000000000 : ℝ)*X 2 0+(2911260387/5000000000 : ℝ)*X 2 1+(1101826009/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s3_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10649302082175879829999773/740234375000000000000000000000 : ℝ) := by norm_num
    linear_combination (38752393/5000000000000 : ℝ)*(lower2) + (3862879/5000000000000 : ℝ)*(lower4) + (199480228986311/5000000000000 : ℝ)*(major0) + (199480228986311/5000000000000 : ℝ)*(major1) + (199480228986311/5000000000000 : ℝ)*(major2) + (339897160287639/6250000000000 : ℝ)*(sp0) + (1087670653100543/20000000000000 : ℝ)*(sp1) + (679794835221687/12500000000000 : ℝ)*(sp2) + (50816968912119/2000000000000 : ℝ)*(sp3) + (3926461761/100000000000000 : ℝ)*(sp5) + (1515948999/100000000000000 : ℝ)*(sp7) + (514646409/12500000000000 : ℝ)*(sp8) + (74490451/5000000000000 : ℝ)*(sp9) + (4572197/12500000000000 : ℝ)*(sp11) + (1270424999066263/50000000000000 : ℝ)*(f.failure) + (679794835221687/12500000000000 : ℝ)*(f.sum) + (16801699091003/5685000000000000000000000000 : ℝ)*base66 + (209059029885176309/35531250000000000000000000000000 : ℝ)*base68 + (520070602488809/35531250000000000000000000000000 : ℝ)*base70 + (1480905420992729941/35531250000000000000000000000000 : ℝ)*base71 + (6282919186031/2842500000000000000000000000 : ℝ)*base73 + (376845860617136191/35531250000000000000000000000000 : ℝ)*base75 + (410002790158042441/35531250000000000000000000000000 : ℝ)*base77 + (57842443331823691/35531250000000000000000000000000 : ℝ)*base79 + (1435606071697/355312500000000000000000000 : ℝ)*base81 + (15931763/5000000000000000000000 : ℝ)*base89 + (15931763/5000000000000000000000 : ℝ)*base91 + (15931763/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (41544309992681373656892693/14804687500000000000000000000000 : ℝ) := by norm_num
    linear_combination (19049331/20000000000000 : ℝ)*(lower4) + (125694821179791/3125000000000 : ℝ)*(major0) + (125694821179791/3125000000000 : ℝ)*(major1) + (125694821179791/3125000000000 : ℝ)*(major2) + (9027830957/100000000000000 : ℝ)*(sp1) + (571055769/25000000000000 : ℝ)*(sp3) + (2741417761717543/50000000000000 : ℝ)*(sp4) + (2741414204047929/50000000000000 : ℝ)*(sp5) + (685354505458801/12500000000000 : ℝ)*(sp6) + (51232546908227/2000000000000 : ℝ)*(sp7) + (2142074509/100000000000000 : ℝ)*(sp8) + (11479139/5000000000000 : ℝ)*(sp9) + (1621839187/100000000000000 : ℝ)*(sp10) + (291705989/25000000000000 : ℝ)*(sp11) + (1280815398229191/50000000000000 : ℝ)*(f.failure) + (1096567533101919/20000000000000 : ℝ)*(f.sum) + (17282014821081/4737500000000000000000000000 : ℝ)*base65 + (179095326545606947/29609375000000000000000000000000 : ℝ)*base68 + (120788380343143053/29609375000000000000000000000000 : ℝ)*base69 + (653630021351388197/29609375000000000000000000000000 : ℝ)*base72 + (21558633452187/9475000000000000000000000000 : ℝ)*base73 + (268456835300606947/29609375000000000000000000000000 : ℝ)*base76 + (125000189657920661/14804687500000000000000000000000 : ℝ)*base78 + (257314855143263197/29609375000000000000000000000000 : ℝ)*base80 + (7055527860281/4737500000000000000000000000 : ℝ)*base81 + (25262691/5000000000000000000000 : ℝ)*base89 + (25262691/5000000000000000000000 : ℝ)*base91 + (25262691/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1400_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157018501/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3973/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10207/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1107/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14963/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1400_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1400_s4_0 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-79788527/400000000 : ℝ)*x 0 + (2705703263/5000000000 : ℝ)*x 1 + (5244655131/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (79788527/400000000 : ℝ)^545 ≤ (6080589153719/50000000000000 : ℝ)^417 := by
    have hnat : (79788527 : ℕ)^545*50000000000000^417 ≤ 6080589153719^417*400000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79788527 400000000 6080589153719 50000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2705703263/5000000000 : ℝ)^545 ≤ (44817593359709/100000000000000 : ℝ)^417 := by
    have hnat : (2705703263 : ℕ)^545*100000000000000^417 ≤ 44817593359709^417*5000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705703263 5000000000 44817593359709 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244655131/10000000000 : ℝ)^545 ≤ (10755307077643/25000000000000 : ℝ)^417 := by
    have hnat : (5244655131 : ℕ)^545*25000000000000^417 ≤ 10755307077643^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244655131 10000000000 10755307077643 25000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-79788527/400000000 : ℝ), (2705703263/5000000000 : ℝ), (5244655131/10000000000 : ℝ)] ![(6080589153719/50000000000000 : ℝ), (44817593359709/100000000000000 : ℝ), (10755307077643/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-79788527/400000000 : ℝ)|^545 ≤ (6080589153719/50000000000000 : ℝ)^417
        have hw : |(-79788527/400000000 : ℝ)|=(79788527/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2705703263/5000000000 : ℝ)|^545 ≤ (44817593359709/100000000000000 : ℝ)^417
        have hw : |(2705703263/5000000000 : ℝ)|=(2705703263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244655131/10000000000 : ℝ)|^545 ≤ (10755307077643/25000000000000 : ℝ)^417
        have hw : |(5244655131/10000000000 : ℝ)|=(5244655131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_s4_1 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5348355833/10000000000 : ℝ)*x 0 + (-2079660389/10000000000 : ℝ)*x 1 + (1048931097/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348355833/10000000000 : ℝ)^545 ≤ (44136339048271/100000000000000 : ℝ)^417 := by
    have hnat : (5348355833 : ℕ)^545*100000000000000^417 ≤ 44136339048271^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348355833 10000000000 44136339048271 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2079660389/10000000000 : ℝ)^545 ≤ (64212144139/500000000000 : ℝ)^417 := by
    have hnat : (2079660389 : ℕ)^545*500000000000^417 ≤ 64212144139^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079660389 10000000000 64212144139 500000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048931097/2000000000 : ℝ)^545 ≤ (43021232105727/100000000000000 : ℝ)^417 := by
    have hnat : (1048931097 : ℕ)^545*100000000000000^417 ≤ 43021232105727^417*2000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048931097 2000000000 43021232105727 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348355833/10000000000 : ℝ), (-2079660389/10000000000 : ℝ), (1048931097/2000000000 : ℝ)] ![(44136339048271/100000000000000 : ℝ), (64212144139/500000000000 : ℝ), (43021232105727/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348355833/10000000000 : ℝ)|^545 ≤ (44136339048271/100000000000000 : ℝ)^417
        have hw : |(5348355833/10000000000 : ℝ)|=(5348355833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2079660389/10000000000 : ℝ)|^545 ≤ (64212144139/500000000000 : ℝ)^417
        have hw : |(-2079660389/10000000000 : ℝ)|=(2079660389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048931097/2000000000 : ℝ)|^545 ≤ (43021232105727/100000000000000 : ℝ)^417
        have hw : |(1048931097/2000000000 : ℝ)|=(1048931097/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_s4_2 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5348355989/10000000000 : ℝ)*x 0 + (2622327683/5000000000 : ℝ)*x 1 + (-2079660339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348355989/10000000000 : ℝ)^545 ≤ (22068170365397/50000000000000 : ℝ)^417 := by
    have hnat : (5348355989 : ℕ)^545*50000000000000^417 ≤ 22068170365397^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348355989 10000000000 22068170365397 50000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622327683/5000000000 : ℝ)^545 ≤ (21510615414977/50000000000000 : ℝ)^417 := by
    have hnat : (2622327683 : ℕ)^545*50000000000000^417 ≤ 21510615414977^417*5000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622327683 5000000000 21510615414977 50000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2079660339/10000000000 : ℝ)^545 ≤ (12842428424261/100000000000000 : ℝ)^417 := by
    have hnat : (2079660339 : ℕ)^545*100000000000000^417 ≤ 12842428424261^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079660339 10000000000 12842428424261 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348355989/10000000000 : ℝ), (2622327683/5000000000 : ℝ), (-2079660339/10000000000 : ℝ)] ![(22068170365397/50000000000000 : ℝ), (21510615414977/50000000000000 : ℝ), (12842428424261/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348355989/10000000000 : ℝ)|^545 ≤ (22068170365397/50000000000000 : ℝ)^417
        have hw : |(5348355989/10000000000 : ℝ)|=(5348355989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622327683/5000000000 : ℝ)|^545 ≤ (21510615414977/50000000000000 : ℝ)^417
        have hw : |(2622327683/5000000000 : ℝ)|=(2622327683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2079660339/10000000000 : ℝ)|^545 ≤ (12842428424261/100000000000000 : ℝ)^417
        have hw : |(-2079660339/10000000000 : ℝ)|=(2079660339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_s4_3 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4311562719/10000000000 : ℝ)*x 0 + (2068235903/5000000000 : ℝ)*x 1 + (1123345321/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4311562719/10000000000 : ℝ)^545 ≤ (8325766359677/25000000000000 : ℝ)^417 := by
    have hnat : (4311562719 : ℕ)^545*25000000000000^417 ≤ 8325766359677^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4311562719 10000000000 8325766359677 25000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2068235903/5000000000 : ℝ)^545 ≤ (15773314824211/50000000000000 : ℝ)^417 := by
    have hnat : (2068235903 : ℕ)^545*50000000000000^417 ≤ 15773314824211^417*5000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2068235903 5000000000 15773314824211 50000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1123345321/2500000000 : ℝ)^545 ≤ (17575152450963/50000000000000 : ℝ)^417 := by
    have hnat : (1123345321 : ℕ)^545*50000000000000^417 ≤ 17575152450963^417*2500000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123345321 2500000000 17575152450963 50000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4311562719/10000000000 : ℝ), (2068235903/5000000000 : ℝ), (1123345321/2500000000 : ℝ)] ![(8325766359677/25000000000000 : ℝ), (15773314824211/50000000000000 : ℝ), (17575152450963/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4311562719/10000000000 : ℝ)|^545 ≤ (8325766359677/25000000000000 : ℝ)^417
        have hw : |(4311562719/10000000000 : ℝ)|=(4311562719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2068235903/5000000000 : ℝ)|^545 ≤ (15773314824211/50000000000000 : ℝ)^417
        have hw : |(2068235903/5000000000 : ℝ)|=(2068235903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1123345321/2500000000 : ℝ)|^545 ≤ (17575152450963/50000000000000 : ℝ)^417
        have hw : |(1123345321/2500000000 : ℝ)|=(1123345321/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_s4_4 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1994725421/10000000000 : ℝ)*x 0 + (5245266931/10000000000 : ℝ)*x 1 + (270539577/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1994725421/10000000000 : ℝ)^545 ≤ (6080637942539/50000000000000 : ℝ)^417 := by
    have hnat : (1994725421 : ℕ)^545*50000000000000^417 ≤ 6080637942539^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1994725421 10000000000 6080637942539 50000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245266931/10000000000 : ℝ)^545 ≤ (43027787400193/100000000000000 : ℝ)^417 := by
    have hnat : (5245266931 : ℕ)^545*100000000000000^417 ≤ 43027787400193^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245266931 10000000000 43027787400193 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270539577/500000000 : ℝ)^545 ≤ (2800683543639/6250000000000 : ℝ)^417 := by
    have hnat : (270539577 : ℕ)^545*6250000000000^417 ≤ 2800683543639^417*500000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270539577 500000000 2800683543639 6250000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1994725421/10000000000 : ℝ), (5245266931/10000000000 : ℝ), (270539577/500000000 : ℝ)] ![(6080637942539/50000000000000 : ℝ), (43027787400193/100000000000000 : ℝ), (2800683543639/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1994725421/10000000000 : ℝ)|^545 ≤ (6080637942539/50000000000000 : ℝ)^417
        have hw : |(-1994725421/10000000000 : ℝ)|=(1994725421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245266931/10000000000 : ℝ)|^545 ≤ (43027787400193/100000000000000 : ℝ)^417
        have hw : |(5245266931/10000000000 : ℝ)|=(5245266931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(270539577/500000000 : ℝ)|^545 ≤ (2800683543639/6250000000000 : ℝ)^417
        have hw : |(270539577/500000000 : ℝ)|=(270539577/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_s4_5 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5305131699/10000000000 : ℝ)*x 0 + (-1913523929/10000000000 : ℝ)*x 1 + (2705395853/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305131699/10000000000 : ℝ)^545 ≤ (10917682145891/25000000000000 : ℝ)^417 := by
    have hnat : (5305131699 : ℕ)^545*25000000000000^417 ≤ 10917682145891^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305131699 10000000000 10917682145891 25000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1913523929/10000000000 : ℝ)^545 ≤ (1151833290071/10000000000000 : ℝ)^417 := by
    have hnat : (1913523929 : ℕ)^545*10000000000000^417 ≤ 1151833290071^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1913523929 10000000000 1151833290071 10000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2705395853/5000000000 : ℝ)^545 ≤ (44810938494991/100000000000000 : ℝ)^417 := by
    have hnat : (2705395853 : ℕ)^545*100000000000000^417 ≤ 44810938494991^417*5000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705395853 5000000000 44810938494991 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305131699/10000000000 : ℝ), (-1913523929/10000000000 : ℝ), (2705395853/5000000000 : ℝ)] ![(10917682145891/25000000000000 : ℝ), (1151833290071/10000000000000 : ℝ), (44810938494991/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305131699/10000000000 : ℝ)|^545 ≤ (10917682145891/25000000000000 : ℝ)^417
        have hw : |(5305131699/10000000000 : ℝ)|=(5305131699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1913523929/10000000000 : ℝ)|^545 ≤ (1151833290071/10000000000000 : ℝ)^417
        have hw : |(-1913523929/10000000000 : ℝ)|=(1913523929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2705395853/5000000000 : ℝ)|^545 ≤ (44810938494991/100000000000000 : ℝ)^417
        have hw : |(2705395853/5000000000 : ℝ)|=(2705395853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_s4_6 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5305131657/10000000000 : ℝ)*x 0 + (5410791623/10000000000 : ℝ)*x 1 + (-1913524101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305131657/10000000000 : ℝ)^545 ≤ (5458841016463/12500000000000 : ℝ)^417 := by
    have hnat : (5305131657 : ℕ)^545*12500000000000^417 ≤ 5458841016463^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305131657 10000000000 5458841016463 12500000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5410791623/10000000000 : ℝ)^545 ≤ (700170899947/1562500000000 : ℝ)^417 := by
    have hnat : (5410791623 : ℕ)^545*1562500000000^417 ≤ 700170899947^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410791623 10000000000 700170899947 1562500000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1913524101/10000000000 : ℝ)^545 ≤ (359947945433/3125000000000 : ℝ)^417 := by
    have hnat : (1913524101 : ℕ)^545*3125000000000^417 ≤ 359947945433^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1913524101 10000000000 359947945433 3125000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305131657/10000000000 : ℝ), (5410791623/10000000000 : ℝ), (-1913524101/10000000000 : ℝ)] ![(5458841016463/12500000000000 : ℝ), (700170899947/1562500000000 : ℝ), (359947945433/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305131657/10000000000 : ℝ)|^545 ≤ (5458841016463/12500000000000 : ℝ)^417
        have hw : |(5305131657/10000000000 : ℝ)|=(5305131657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5410791623/10000000000 : ℝ)|^545 ≤ (700170899947/1562500000000 : ℝ)^417
        have hw : |(5410791623/10000000000 : ℝ)|=(5410791623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1913524101/10000000000 : ℝ)|^545 ≤ (359947945433/3125000000000 : ℝ)^417
        have hw : |(-1913524101/10000000000 : ℝ)|=(1913524101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_s4_7 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (862317789/2000000000 : ℝ)*x 0 + (4492071857/10000000000 : ℝ)*x 1 + (4137788237/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (862317789/2000000000 : ℝ)^545 ≤ (33303330192637/100000000000000 : ℝ)^417 := by
    have hnat : (862317789 : ℕ)^545*100000000000000^417 ≤ 33303330192637^417*2000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      862317789 2000000000 33303330192637 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4492071857/10000000000 : ℝ)^545 ≤ (35136918059917/100000000000000 : ℝ)^417 := by
    have hnat : (4492071857 : ℕ)^545*100000000000000^417 ≤ 35136918059917^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4492071857 10000000000 35136918059917 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4137788237/10000000000 : ℝ)^545 ≤ (6311950345541/20000000000000 : ℝ)^417 := by
    have hnat : (4137788237 : ℕ)^545*20000000000000^417 ≤ 6311950345541^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4137788237 10000000000 6311950345541 20000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(862317789/2000000000 : ℝ), (4492071857/10000000000 : ℝ), (4137788237/10000000000 : ℝ)] ![(33303330192637/100000000000000 : ℝ), (35136918059917/100000000000000 : ℝ), (6311950345541/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(862317789/2000000000 : ℝ)|^545 ≤ (33303330192637/100000000000000 : ℝ)^417
        have hw : |(862317789/2000000000 : ℝ)|=(862317789/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4492071857/10000000000 : ℝ)|^545 ≤ (35136918059917/100000000000000 : ℝ)^417
        have hw : |(4492071857/10000000000 : ℝ)|=(4492071857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4137788237/10000000000 : ℝ)|^545 ≤ (6311950345541/20000000000000 : ℝ)^417
        have hw : |(4137788237/10000000000 : ℝ)|=(4137788237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1400_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157018501/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14963/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1107/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (5623/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14777/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14963/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1107/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14963/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1107/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14963/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1107/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14963/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1107/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14963/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1107/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14963/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1107/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1107/10000 : ℝ) ^ (4359/1024 : ℝ) ≤ (8532832914984007/100000000000000000000 : ℝ) := by
    have hpowers : (1107/10000 : ℝ)^4359 ≤ (8532832914984007/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1107 : ℕ)^4359*100000000000000000000^1024 ≤ 8532832914984007^1024*10000^4359 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1107 10000 8532832914984007 100000000000000000000 4359 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1107/10000 : ℝ)) (X := (8532832914984007/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4359 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14963/100000 : ℝ) ^ (4359/1024 : ℝ) ≤ (1538720912666979/5000000000000000000 : ℝ) := by
    have hpowers : (14963/100000 : ℝ)^4359 ≤ (1538720912666979/5000000000000000000 : ℝ)^1024 := by
      have hnat : (14963 : ℕ)^4359*5000000000000000000^1024 ≤ 1538720912666979^1024*100000^4359 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14963 100000 1538720912666979 5000000000000000000 4359 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14963/100000 : ℝ)) (X := (1538720912666979/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4359 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008532832914984007/50000000000000000000 : ℝ) ≤ (250010021851963/250000000000000 : ℝ) ^ (4359/1024 : ℝ) := by
    have hpowers : (50008532832914984007/50000000000000000000 : ℝ)^1024 ≤ (250010021851963/250000000000000 : ℝ)^4359 := by
      have hnat : (50008532832914984007 : ℕ)^1024*250000000000000^4359 ≤ 250010021851963^4359*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008532832914984007 50000000000000000000 250010021851963 250000000000000 1024 4359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250010021851963/250000000000000 : ℝ)) (X := (50008532832914984007/50000000000000000000 : ℝ)) (by norm_num) 4359 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100039307251168323587/100000000000000000000 : ℝ) ≤ (500046162622439/500000000000000 : ℝ) ^ (4359/1024 : ℝ) := by
    have hpowers : (100039307251168323587/100000000000000000000 : ℝ)^1024 ≤ (500046162622439/500000000000000 : ℝ)^4359 := by
      have hnat : (100039307251168323587 : ℕ)^1024*500000000000000^4359 ≤ 500046162622439^4359*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100039307251168323587 100000000000000000000 500046162622439 500000000000000 1024 4359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500046162622439/500000000000000 : ℝ)) (X := (100039307251168323587/100000000000000000000 : ℝ)) (by norm_num) 4359 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501538720912666979/2500000000000000000 : ℝ) ≤ (62509035192619/62500000000000 : ℝ) ^ (4359/1024 : ℝ) := by
    have hpowers : (2501538720912666979/2500000000000000000 : ℝ)^1024 ≤ (62509035192619/62500000000000 : ℝ)^4359 := by
      have hnat : (2501538720912666979 : ℕ)^1024*62500000000000^4359 ≤ 62509035192619^4359*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501538720912666979 2500000000000000000 62509035192619 62500000000000 1024 4359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (62509035192619/62500000000000 : ℝ)) (X := (2501538720912666979/2500000000000000000 : ℝ)) (by norm_num) 4359 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8532832914984007/100000000000000000000 : ℝ) ≤ ((972999878641753049/973250000000000000 : ℝ)+2*(26118918513/19465000000000 : ℝ)*(1107/10000 : ℝ))^(4359/1024 : ℝ) := by
    rw [show (972999878641753049/973250000000000000 : ℝ)+2*(26118918513/19465000000000 : ℝ)*(1107/10000 : ℝ)=(250010021851963/250000000000000 : ℝ) by norm_num, show 1+2*(8532832914984007/100000000000000000000 : ℝ)=(50008532832914984007/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1538720912666979/5000000000000000000 : ℝ)+(8532832914984007/100000000000000000000 : ℝ) ≤ ((972999878641753049/973250000000000000 : ℝ)+(26118918513/19465000000000 : ℝ)*((14963/100000 : ℝ)+(1107/10000 : ℝ)))^(4359/1024 : ℝ) := by
    rw [show (972999878641753049/973250000000000000 : ℝ)+(26118918513/19465000000000 : ℝ)*((14963/100000 : ℝ)+(1107/10000 : ℝ))=(500046162622439/500000000000000 : ℝ) by norm_num, show 1+(1538720912666979/5000000000000000000 : ℝ)+(8532832914984007/100000000000000000000 : ℝ)=(100039307251168323587/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1538720912666979/5000000000000000000 : ℝ) ≤ ((972999878641753049/973250000000000000 : ℝ)+2*(26118918513/19465000000000 : ℝ)*(14963/100000 : ℝ))^(4359/1024 : ℝ) := by
    rw [show (972999878641753049/973250000000000000 : ℝ)+2*(26118918513/19465000000000 : ℝ)*(14963/100000 : ℝ)=(62509035192619/62500000000000 : ℝ) by norm_num, show 1+2*(1538720912666979/5000000000000000000 : ℝ)=(2501538720912666979/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (972999878641753049/973250000000000000 : ℝ)*(X 1 0+X 2 0)+(26118918513/19465000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4359/1024 : ℝ)) (lo := (1107/10000 : ℝ)) (hi := (14963/100000 : ℝ)) (c := (972999878641753049/973250000000000000 : ℝ)) (alpha := (26118918513/19465000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (972999878641753049/973250000000000000 : ℝ)*(X 0 1+X 2 1)+(26118918513/19465000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4359/1024 : ℝ)) (lo := (1107/10000 : ℝ)) (hi := (14963/100000 : ℝ)) (c := (972999878641753049/973250000000000000 : ℝ)) (alpha := (26118918513/19465000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (972999878641753049/973250000000000000 : ℝ)*(X 0 2+X 1 2)+(26118918513/19465000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4359/1024 : ℝ)) (lo := (1107/10000 : ℝ)) (hi := (14963/100000 : ℝ)) (c := (972999878641753049/973250000000000000 : ℝ)) (alpha := (26118918513/19465000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-79788527/400000000 : ℝ)*X 0 0+(2705703263/5000000000 : ℝ)*X 0 1+(5244655131/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348355833/10000000000 : ℝ)*X 1 0+(-2079660389/10000000000 : ℝ)*X 1 1+(1048931097/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348355989/10000000000 : ℝ)*X 2 0+(2622327683/5000000000 : ℝ)*X 2 1+(-2079660339/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4311562719/10000000000 : ℝ)*X 0 0+(2068235903/5000000000 : ℝ)*X 0 1+(1123345321/2500000000 : ℝ)*X 0 2+(4311562719/10000000000 : ℝ)*X 1 0+(2068235903/5000000000 : ℝ)*X 1 1+(1123345321/2500000000 : ℝ)*X 1 2+(4311562719/10000000000 : ℝ)*X 2 0+(2068235903/5000000000 : ℝ)*X 2 1+(1123345321/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1994725421/10000000000 : ℝ)*X 0 0+(5245266931/10000000000 : ℝ)*X 0 1+(270539577/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305131699/10000000000 : ℝ)*X 1 0+(-1913523929/10000000000 : ℝ)*X 1 1+(2705395853/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305131657/10000000000 : ℝ)*X 2 0+(5410791623/10000000000 : ℝ)*X 2 1+(-1913524101/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((862317789/2000000000 : ℝ)*X 0 0+(4492071857/10000000000 : ℝ)*X 0 1+(4137788237/10000000000 : ℝ)*X 0 2+(862317789/2000000000 : ℝ)*X 1 0+(4492071857/10000000000 : ℝ)*X 1 1+(4137788237/10000000000 : ℝ)*X 1 2+(862317789/2000000000 : ℝ)*X 2 0+(4492071857/10000000000 : ℝ)*X 2 1+(4137788237/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3739291333500281441173323/760351562500000000000000000000 : ℝ) := by norm_num
    linear_combination (57624743/10000000000000 : ℝ)*(base19) + (326247371/50000000000000 : ℝ)*(base23) + (15051339/10000000000000 : ℝ)*(upper3) + (52773231/100000000000000 : ℝ)*(upper4) + (172424229/100000000000000 : ℝ)*(upper5) + (549927181166553/12500000000000 : ℝ)*(major0) + (549927181166553/12500000000000 : ℝ)*(major1) + (549927181166553/12500000000000 : ℝ)*(major2) + (749620996814761/12500000000000 : ℝ)*(sp0) + (1499246902726981/25000000000000 : ℝ)*(sp1) + (1499246883665153/25000000000000 : ℝ)*(sp2) + (56036767056817/2000000000000 : ℝ)*(sp3) + (10106318633/50000000000000 : ℝ)*(sp4) + (409737023/5000000000000 : ℝ)*(sp7) + (280184654758131/10000000000000 : ℝ)*(f.failure) + (1199397637431071/20000000000000 : ℝ)*(f.sum) + (1097616810663/486625000000000000000000000 : ℝ)*base66 + (1203561906679/3125000000000000000000000000 : ℝ)*base67 + (22431507737929/3125000000000000000000000000 : ℝ)*base69 + (35412701493321/3125000000000000000000000000 : ℝ)*base72 + (3380018944341/973250000000000000000000000 : ℝ)*base74 + (16201745325429/3125000000000000000000000000 : ℝ)*base75 + (2666715793321/3125000000000000000000000000 : ℝ)*base78 + (10708714850429/3125000000000000000000000000 : ℝ)*base79 + (1361875727489/486625000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (7181631/1000000000000000000000 : ℝ)*base89 + (7181631/1000000000000000000000 : ℝ)*base91 + (7181631/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (173867373469199283888167811/24331250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1141921529/100000000000000 : ℝ)*(base19) + (137205071/12500000000000 : ℝ)*(base23) + (17173269/50000000000000 : ℝ)*(upper2) + (69954599/50000000000000 : ℝ)*(upper3) + (53079339/25000000000000 : ℝ)*(upper5) + (4431997357681213/100000000000000 : ℝ)*(major0) + (4431997357681213/100000000000000 : ℝ)*(major1) + (4431997357681213/100000000000000 : ℝ)*(major2) + (29158578153/100000000000000 : ℝ)*(sp1) + (10823895137/50000000000000 : ℝ)*(sp2) + (3020699420347303/50000000000000 : ℝ)*(sp4) + (1510342135048731/25000000000000 : ℝ)*(sp5) + (1208275219052753/20000000000000 : ℝ)*(sp6) + (352824454559117/12500000000000 : ℝ)*(sp7) + (352824454559117/12500000000000 : ℝ)*(f.failure) + (3020699420347303/50000000000000 : ℝ)*(f.sum) + (6339277171117/1946500000000000000000000000 : ℝ)*base65 + (40126503783809/25000000000000000000000000000 : ℝ)*base67 + (213434764566191/25000000000000000000000000000 : ℝ)*base70 + (172165208891191/25000000000000000000000000000 : ℝ)*base72 + (16450751262649/3893000000000000000000000000 : ℝ)*base73 + (100101922291191/25000000000000000000000000000 : ℝ)*base76 + (34543890541191/25000000000000000000000000000 : ℝ)*base78 + (417180413541191/25000000000000000000000000000 : ℝ)*base80 + (14100992796057/3893000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (4723617/1250000000000000000000 : ℝ)*base89 + (4723617/1250000000000000000000 : ℝ)*base91 + (4723617/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1400_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157018501/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14963/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1107/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5623/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14777/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1400_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1400_s5_0 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-398975383/2000000000 : ℝ)*x 0 + (1352487187/2500000000 : ℝ)*x 1 + (5246005169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (398975383/2000000000 : ℝ)^545 ≤ (6081241511593/50000000000000 : ℝ)^417 := by
    have hnat : (398975383 : ℕ)^545*50000000000000^417 ≤ 6081241511593^417*2000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      398975383 2000000000 6081241511593 50000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352487187/2500000000 : ℝ)^545 ≤ (11200453655541/25000000000000 : ℝ)^417 := by
    have hnat : (1352487187 : ℕ)^545*25000000000000^417 ≤ 11200453655541^417*2500000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352487187 2500000000 11200453655541 25000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246005169/10000000000 : ℝ)^545 ≤ (21517851170253/50000000000000 : ℝ)^417 := by
    have hnat : (5246005169 : ℕ)^545*50000000000000^417 ≤ 21517851170253^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246005169 10000000000 21517851170253 50000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-398975383/2000000000 : ℝ), (1352487187/2500000000 : ℝ), (5246005169/10000000000 : ℝ)] ![(6081241511593/50000000000000 : ℝ), (11200453655541/25000000000000 : ℝ), (21517851170253/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-398975383/2000000000 : ℝ)|^545 ≤ (6081241511593/50000000000000 : ℝ)^417
        have hw : |(-398975383/2000000000 : ℝ)|=(398975383/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352487187/2500000000 : ℝ)|^545 ≤ (11200453655541/25000000000000 : ℝ)^417
        have hw : |(1352487187/2500000000 : ℝ)|=(1352487187/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246005169/10000000000 : ℝ)|^545 ≤ (21517851170253/50000000000000 : ℝ)^417
        have hw : |(5246005169/10000000000 : ℝ)|=(5246005169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_s5_1 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (334248757/625000000 : ℝ)*x 0 + (-2078365597/10000000000 : ℝ)*x 1 + (262300403/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334248757/625000000 : ℝ)^545 ≤ (44132286788783/100000000000000 : ℝ)^417 := by
    have hnat : (334248757 : ℕ)^545*100000000000000^417 ≤ 44132286788783^417*625000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334248757 625000000 44132286788783 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2078365597/10000000000 : ℝ)^545 ≤ (12831979852669/100000000000000 : ℝ)^417 := by
    have hnat : (2078365597 : ℕ)^545*100000000000000^417 ≤ 12831979852669^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2078365597 10000000000 12831979852669 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262300403/500000000 : ℝ)^545 ≤ (5379466667091/12500000000000 : ℝ)^417 := by
    have hnat : (262300403 : ℕ)^545*12500000000000^417 ≤ 5379466667091^417*500000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262300403 500000000 5379466667091 12500000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334248757/625000000 : ℝ), (-2078365597/10000000000 : ℝ), (262300403/500000000 : ℝ)] ![(44132286788783/100000000000000 : ℝ), (12831979852669/100000000000000 : ℝ), (5379466667091/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334248757/625000000 : ℝ)|^545 ≤ (44132286788783/100000000000000 : ℝ)^417
        have hw : |(334248757/625000000 : ℝ)|=(334248757/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2078365597/10000000000 : ℝ)|^545 ≤ (12831979852669/100000000000000 : ℝ)^417
        have hw : |(-2078365597/10000000000 : ℝ)|=(2078365597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(262300403/500000000 : ℝ)|^545 ≤ (5379466667091/12500000000000 : ℝ)^417
        have hw : |(262300403/500000000 : ℝ)|=(262300403/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_s5_2 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1336995271/2500000000 : ℝ)*x 0 + (655750751/1250000000 : ℝ)*x 1 + (-83134681/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336995271/2500000000 : ℝ)^545 ≤ (44132297271971/100000000000000 : ℝ)^417 := by
    have hnat : (1336995271 : ℕ)^545*100000000000000^417 ≤ 44132297271971^417*2500000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336995271 2500000000 44132297271971 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655750751/1250000000 : ℝ)^545 ≤ (860714226719/2000000000000 : ℝ)^417 := by
    have hnat : (655750751 : ℕ)^545*2000000000000^417 ≤ 860714226719^417*1250000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655750751 1250000000 860714226719 2000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (83134681/400000000 : ℝ)^545 ≤ (3207997843883/25000000000000 : ℝ)^417 := by
    have hnat : (83134681 : ℕ)^545*25000000000000^417 ≤ 3207997843883^417*400000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83134681 400000000 3207997843883 25000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336995271/2500000000 : ℝ), (655750751/1250000000 : ℝ), (-83134681/400000000 : ℝ)] ![(44132297271971/100000000000000 : ℝ), (860714226719/2000000000000 : ℝ), (3207997843883/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336995271/2500000000 : ℝ)|^545 ≤ (44132297271971/100000000000000 : ℝ)^417
        have hw : |(1336995271/2500000000 : ℝ)|=(1336995271/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655750751/1250000000 : ℝ)|^545 ≤ (860714226719/2000000000000 : ℝ)^417
        have hw : |(655750751/1250000000 : ℝ)|=(655750751/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-83134681/400000000 : ℝ)|^545 ≤ (3207997843883/25000000000000 : ℝ)^417
        have hw : |(-83134681/400000000 : ℝ)|=(83134681/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_s5_3 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2155831773/5000000000 : ℝ)*x 0 + (2069733929/5000000000 : ℝ)*x 1 + (35080939/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2155831773/5000000000 : ℝ)^545 ≤ (33304083299427/100000000000000 : ℝ)^417 := by
    have hnat : (2155831773 : ℕ)^545*100000000000000^417 ≤ 33304083299427^417*5000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155831773 5000000000 33304083299427 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2069733929/5000000000 : ℝ)^545 ≤ (31576495916561/100000000000000 : ℝ)^417 := by
    have hnat : (2069733929 : ℕ)^545*100000000000000^417 ≤ 31576495916561^417*5000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069733929 5000000000 31576495916561 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (35080939/78125000 : ℝ)^545 ≤ (17559710385003/50000000000000 : ℝ)^417 := by
    have hnat : (35080939 : ℕ)^545*50000000000000^417 ≤ 17559710385003^417*78125000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35080939 78125000 17559710385003 50000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2155831773/5000000000 : ℝ), (2069733929/5000000000 : ℝ), (35080939/78125000 : ℝ)] ![(33304083299427/100000000000000 : ℝ), (31576495916561/100000000000000 : ℝ), (17559710385003/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2155831773/5000000000 : ℝ)|^545 ≤ (33304083299427/100000000000000 : ℝ)^417
        have hw : |(2155831773/5000000000 : ℝ)|=(2155831773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2069733929/5000000000 : ℝ)|^545 ≤ (31576495916561/100000000000000 : ℝ)^417
        have hw : |(2069733929/5000000000 : ℝ)|=(2069733929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(35080939/78125000 : ℝ)|^545 ≤ (17559710385003/50000000000000 : ℝ)^417
        have hw : |(35080939/78125000 : ℝ)|=(35080939/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_s5_4 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1994888813/10000000000 : ℝ)*x 0 + (1049319603/2000000000 : ℝ)*x 1 + (676169087/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1994888813/10000000000 : ℝ)^545 ≤ (6081288915153/50000000000000 : ℝ)^417 := by
    have hnat : (1994888813 : ℕ)^545*50000000000000^417 ≤ 6081288915153^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1994888813 10000000000 6081288915153 50000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049319603/2000000000 : ℝ)^545 ≤ (43042058723461/100000000000000 : ℝ)^417 := by
    have hnat : (1049319603 : ℕ)^545*100000000000000^417 ≤ 43042058723461^417*2000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049319603 2000000000 43042058723461 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676169087/1250000000 : ℝ)^545 ≤ (22397681717019/50000000000000 : ℝ)^417 := by
    have hnat : (676169087 : ℕ)^545*50000000000000^417 ≤ 22397681717019^417*1250000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676169087 1250000000 22397681717019 50000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1994888813/10000000000 : ℝ), (1049319603/2000000000 : ℝ), (676169087/1250000000 : ℝ)] ![(6081288915153/50000000000000 : ℝ), (43042058723461/100000000000000 : ℝ), (22397681717019/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1994888813/10000000000 : ℝ)|^545 ≤ (6081288915153/50000000000000 : ℝ)^417
        have hw : |(-1994888813/10000000000 : ℝ)|=(1994888813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1049319603/2000000000 : ℝ)|^545 ≤ (43042058723461/100000000000000 : ℝ)^417
        have hw : |(1049319603/2000000000 : ℝ)|=(1049319603/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(676169087/1250000000 : ℝ)|^545 ≤ (22397681717019/50000000000000 : ℝ)^417
        have hw : |(676169087/1250000000 : ℝ)|=(676169087/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_s5_5 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (20724551/39062500 : ℝ)*x 0 + (-239377563/1250000000 : ℝ)*x 1 + (1081870507/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20724551/39062500 : ℝ)^545 ≤ (10918632559973/25000000000000 : ℝ)^417 := by
    have hnat : (20724551 : ℕ)^545*25000000000000^417 ≤ 10918632559973^417*39062500^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20724551 39062500 10918632559973 25000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (239377563/1250000000 : ℝ)^545 ≤ (11530108059713/100000000000000 : ℝ)^417 := by
    have hnat : (239377563 : ℕ)^545*100000000000000^417 ≤ 11530108059713^417*1250000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      239377563 1250000000 11530108059713 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081870507/2000000000 : ℝ)^545 ≤ (44795361691533/100000000000000 : ℝ)^417 := by
    have hnat : (1081870507 : ℕ)^545*100000000000000^417 ≤ 44795361691533^417*2000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081870507 2000000000 44795361691533 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(20724551/39062500 : ℝ), (-239377563/1250000000 : ℝ), (1081870507/2000000000 : ℝ)] ![(10918632559973/25000000000000 : ℝ), (11530108059713/100000000000000 : ℝ), (44795361691533/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(20724551/39062500 : ℝ)|^545 ≤ (10918632559973/25000000000000 : ℝ)^417
        have hw : |(20724551/39062500 : ℝ)|=(20724551/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-239377563/1250000000 : ℝ)|^545 ≤ (11530108059713/100000000000000 : ℝ)^417
        have hw : |(-239377563/1250000000 : ℝ)|=(239377563/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081870507/2000000000 : ℝ)|^545 ≤ (44795361691533/100000000000000 : ℝ)^417
        have hw : |(1081870507/2000000000 : ℝ)|=(1081870507/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_s5_6 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5305484887/10000000000 : ℝ)*x 0 + (5409352761/10000000000 : ℝ)*x 1 + (-1915020423/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305484887/10000000000 : ℝ)^545 ≤ (5459316052707/12500000000000 : ℝ)^417 := by
    have hnat : (5305484887 : ℕ)^545*12500000000000^417 ≤ 5459316052707^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305484887 10000000000 5459316052707 12500000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5409352761/10000000000 : ℝ)^545 ≤ (22397682068767/50000000000000 : ℝ)^417 := by
    have hnat : (5409352761 : ℕ)^545*50000000000000^417 ≤ 22397682068767^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409352761 10000000000 22397682068767 50000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1915020423/10000000000 : ℝ)^545 ≤ (11530107422323/100000000000000 : ℝ)^417 := by
    have hnat : (1915020423 : ℕ)^545*100000000000000^417 ≤ 11530107422323^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1915020423 10000000000 11530107422323 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305484887/10000000000 : ℝ), (5409352761/10000000000 : ℝ), (-1915020423/10000000000 : ℝ)] ![(5459316052707/12500000000000 : ℝ), (22397682068767/50000000000000 : ℝ), (11530107422323/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305484887/10000000000 : ℝ)|^545 ≤ (5459316052707/12500000000000 : ℝ)^417
        have hw : |(5305484887/10000000000 : ℝ)|=(5305484887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5409352761/10000000000 : ℝ)|^545 ≤ (22397682068767/50000000000000 : ℝ)^417
        have hw : |(5409352761/10000000000 : ℝ)|=(5409352761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1915020423/10000000000 : ℝ)|^545 ≤ (11530107422323/100000000000000 : ℝ)^417
        have hw : |(-1915020423/10000000000 : ℝ)|=(1915020423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_s5_7 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (269480469/625000000 : ℝ)*x 0 + (2244547701/5000000000 : ℝ)*x 1 + (2070370129/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (269480469/625000000 : ℝ)^545 ≤ (33304325159399/100000000000000 : ℝ)^417 := by
    have hnat : (269480469 : ℕ)^545*100000000000000^417 ≤ 33304325159399^417*625000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269480469 625000000 33304325159399 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2244547701/5000000000 : ℝ)^545 ≤ (35106492921333/100000000000000 : ℝ)^417 := by
    have hnat : (2244547701 : ℕ)^545*100000000000000^417 ≤ 35106492921333^417*5000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2244547701 5000000000 35106492921333 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2070370129/5000000000 : ℝ)^545 ≤ (1974323868519/6250000000000 : ℝ)^417 := by
    have hnat : (2070370129 : ℕ)^545*6250000000000^417 ≤ 1974323868519^417*5000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2070370129 5000000000 1974323868519 6250000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(269480469/625000000 : ℝ), (2244547701/5000000000 : ℝ), (2070370129/5000000000 : ℝ)] ![(33304325159399/100000000000000 : ℝ), (35106492921333/100000000000000 : ℝ), (1974323868519/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(269480469/625000000 : ℝ)|^545 ≤ (33304325159399/100000000000000 : ℝ)^417
        have hw : |(269480469/625000000 : ℝ)|=(269480469/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2244547701/5000000000 : ℝ)|^545 ≤ (35106492921333/100000000000000 : ℝ)^417
        have hw : |(2244547701/5000000000 : ℝ)|=(2244547701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2070370129/5000000000 : ℝ)|^545 ≤ (1974323868519/6250000000000 : ℝ)^417
        have hw : |(2070370129/5000000000 : ℝ)|=(2070370129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1400_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157018501/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14777/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5623/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (451/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7373/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14777/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5623/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14777/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5623/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14777/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5623/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14777/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5623/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14777/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5623/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14777/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5623/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5623/50000 : ℝ) ^ (4359/1024 : ℝ) ≤ (4562727403852651/50000000000000000000 : ℝ) := by
    have hpowers : (5623/50000 : ℝ)^4359 ≤ (4562727403852651/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5623 : ℕ)^4359*50000000000000000000^1024 ≤ 4562727403852651^1024*50000^4359 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5623 50000 4562727403852651 50000000000000000000 4359 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5623/50000 : ℝ)) (X := (4562727403852651/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4359 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14777/100000 : ℝ) ^ (4359/1024 : ℝ) ≤ (29178637277329651/100000000000000000000 : ℝ) := by
    have hpowers : (14777/100000 : ℝ)^4359 ≤ (29178637277329651/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14777 : ℕ)^4359*100000000000000000000^1024 ≤ 29178637277329651^1024*100000^4359 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14777 100000 29178637277329651 100000000000000000000 4359 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14777/100000 : ℝ)) (X := (29178637277329651/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4359 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004562727403852651/25000000000000000000 : ℝ) ≤ (50002143568109/50000000000000 : ℝ) ^ (4359/1024 : ℝ) := by
    have hpowers : (25004562727403852651/25000000000000000000 : ℝ)^1024 ≤ (50002143568109/50000000000000 : ℝ)^4359 := by
      have hnat : (25004562727403852651 : ℕ)^1024*50000000000000^4359 ≤ 50002143568109^4359*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004562727403852651 25000000000000000000 50002143568109 50000000000000 1024 4359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (50002143568109/50000000000000 : ℝ)) (X := (25004562727403852651/25000000000000000000 : ℝ)) (by norm_num) 4359 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100038304092085034953/100000000000000000000 : ℝ) ≤ (10000899693604461/10000000000000000 : ℝ) ^ (4359/1024 : ℝ) := by
    have hpowers : (100038304092085034953/100000000000000000000 : ℝ)^1024 ≤ (10000899693604461/10000000000000000 : ℝ)^4359 := by
      have hnat : (100038304092085034953 : ℕ)^1024*10000000000000000^4359 ≤ 10000899693604461^4359*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100038304092085034953 100000000000000000000 10000899693604461 10000000000000000 1024 4359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000899693604461/10000000000000000 : ℝ)) (X := (100038304092085034953/100000000000000000000 : ℝ)) (by norm_num) 4359 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50029178637277329651/50000000000000000000 : ℝ) ≤ (5000685336793561/5000000000000000 : ℝ) ^ (4359/1024 : ℝ) := by
    have hpowers : (50029178637277329651/50000000000000000000 : ℝ)^1024 ≤ (5000685336793561/5000000000000000 : ℝ)^4359 := by
      have hnat : (50029178637277329651 : ℕ)^1024*5000000000000000^4359 ≤ 5000685336793561^4359*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50029178637277329651 50000000000000000000 5000685336793561 5000000000000000 1024 4359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000685336793561/5000000000000000 : ℝ)) (X := (50029178637277329651/50000000000000000000 : ℝ)) (by norm_num) 4359 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4562727403852651/50000000000000000000 : ℝ) ≤ ((8825230126507141147/8827500000000000000 : ℝ)+2*(470979982661/353100000000000 : ℝ)*(5623/50000 : ℝ))^(4359/1024 : ℝ) := by
    rw [show (8825230126507141147/8827500000000000000 : ℝ)+2*(470979982661/353100000000000 : ℝ)*(5623/50000 : ℝ)=(50002143568109/50000000000000 : ℝ) by norm_num, show 1+2*(4562727403852651/50000000000000000000 : ℝ)=(25004562727403852651/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(29178637277329651/100000000000000000000 : ℝ)+(4562727403852651/50000000000000000000 : ℝ) ≤ ((8825230126507141147/8827500000000000000 : ℝ)+(470979982661/353100000000000 : ℝ)*((14777/100000 : ℝ)+(5623/50000 : ℝ)))^(4359/1024 : ℝ) := by
    rw [show (8825230126507141147/8827500000000000000 : ℝ)+(470979982661/353100000000000 : ℝ)*((14777/100000 : ℝ)+(5623/50000 : ℝ))=(10000899693604461/10000000000000000 : ℝ) by norm_num, show 1+(29178637277329651/100000000000000000000 : ℝ)+(4562727403852651/50000000000000000000 : ℝ)=(100038304092085034953/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(29178637277329651/100000000000000000000 : ℝ) ≤ ((8825230126507141147/8827500000000000000 : ℝ)+2*(470979982661/353100000000000 : ℝ)*(14777/100000 : ℝ))^(4359/1024 : ℝ) := by
    rw [show (8825230126507141147/8827500000000000000 : ℝ)+2*(470979982661/353100000000000 : ℝ)*(14777/100000 : ℝ)=(5000685336793561/5000000000000000 : ℝ) by norm_num, show 1+2*(29178637277329651/100000000000000000000 : ℝ)=(50029178637277329651/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8825230126507141147/8827500000000000000 : ℝ)*(X 1 0+X 2 0)+(470979982661/353100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4359/1024 : ℝ)) (lo := (5623/50000 : ℝ)) (hi := (14777/100000 : ℝ)) (c := (8825230126507141147/8827500000000000000 : ℝ)) (alpha := (470979982661/353100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8825230126507141147/8827500000000000000 : ℝ)*(X 0 1+X 2 1)+(470979982661/353100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4359/1024 : ℝ)) (lo := (5623/50000 : ℝ)) (hi := (14777/100000 : ℝ)) (c := (8825230126507141147/8827500000000000000 : ℝ)) (alpha := (470979982661/353100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8825230126507141147/8827500000000000000 : ℝ)*(X 0 2+X 1 2)+(470979982661/353100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4359/1024 : ℝ)) (lo := (5623/50000 : ℝ)) (hi := (14777/100000 : ℝ)) (c := (8825230126507141147/8827500000000000000 : ℝ)) (alpha := (470979982661/353100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-398975383/2000000000 : ℝ)*X 0 0+(1352487187/2500000000 : ℝ)*X 0 1+(5246005169/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334248757/625000000 : ℝ)*X 1 0+(-2078365597/10000000000 : ℝ)*X 1 1+(262300403/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336995271/2500000000 : ℝ)*X 2 0+(655750751/1250000000 : ℝ)*X 2 1+(-83134681/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2155831773/5000000000 : ℝ)*X 0 0+(2069733929/5000000000 : ℝ)*X 0 1+(35080939/78125000 : ℝ)*X 0 2+(2155831773/5000000000 : ℝ)*X 1 0+(2069733929/5000000000 : ℝ)*X 1 1+(35080939/78125000 : ℝ)*X 1 2+(2155831773/5000000000 : ℝ)*X 2 0+(2069733929/5000000000 : ℝ)*X 2 1+(35080939/78125000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1994888813/10000000000 : ℝ)*X 0 0+(1049319603/2000000000 : ℝ)*X 0 1+(676169087/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((20724551/39062500 : ℝ)*X 1 0+(-239377563/1250000000 : ℝ)*X 1 1+(1081870507/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305484887/10000000000 : ℝ)*X 2 0+(5409352761/10000000000 : ℝ)*X 2 1+(-1915020423/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((269480469/625000000 : ℝ)*X 0 0+(2244547701/5000000000 : ℝ)*X 0 1+(2070370129/5000000000 : ℝ)*X 0 2+(269480469/625000000 : ℝ)*X 1 0+(2244547701/5000000000 : ℝ)*X 1 1+(2070370129/5000000000 : ℝ)*X 1 2+(269480469/625000000 : ℝ)*X 2 0+(2244547701/5000000000 : ℝ)*X 2 1+(2070370129/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9195096569032472609726473/2942500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (126372491/20000000000000 : ℝ)*(base23) + (211066549/100000000000000 : ℝ)*(lower2) + (5555771/2500000000000 : ℝ)*(upper3) + (75264027/50000000000000 : ℝ)*(lower4) + (178995050135459/4000000000000 : ℝ)*(major0) + (178995050135459/4000000000000 : ℝ)*(major1) + (178995050135459/4000000000000 : ℝ)*(major2) + (1219950846492667/20000000000000 : ℝ)*(sp0) + (6099848585614271/100000000000000 : ℝ)*(sp1) + (6099802197200667/100000000000000 : ℝ)*(sp2) + (1424943541527793/50000000000000 : ℝ)*(sp3) + (11794143867/12500000000000 : ℝ)*(sp4) + (45756551149/100000000000000 : ℝ)*(sp6) + (4183484717/25000000000000 : ℝ)*(sp7) + (1424951908497227/50000000000000 : ℝ)*(f.failure) + (6099848585614271/100000000000000 : ℝ)*(f.sum) + (638241746149/353100000000000000000000000 : ℝ)*base66 + (7016563571344509/11770000000000000000000000000000 : ℝ)*base68 + (100850489645254509/11770000000000000000000000000000 : ℝ)*base70 + (28943666753064509/11770000000000000000000000000000 : ℝ)*base72 + (1761059668681/441375000000000000000000000 : ℝ)*base73 + (5579474190215491/11770000000000000000000000000000 : ℝ)*base75 + (105669823158094509/11770000000000000000000000000000 : ℝ)*base78 + (143458324217194509/11770000000000000000000000000000 : ℝ)*base80 + (5781256721621/3531000000000000000000000000 : ℝ)*base81 + (3803273/5000000000000000000000 : ℝ)*base90 + (3803273/5000000000000000000000 : ℝ)*base92 + (3803273/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (80675098148323516494217577/36781250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (189081741/50000000000000 : ℝ)*(base19) + (181765509/50000000000000 : ℝ)*(base23) + (74973587/100000000000000 : ℝ)*(upper2) + (3279137/50000000000000 : ℝ)*(lower3) + (2253712049381809/50000000000000 : ℝ)*(major0) + (2253712049381809/50000000000000 : ℝ)*(major1) + (2253712049381809/50000000000000 : ℝ)*(major2) + (921385879/100000000000000 : ℝ)*(sp0) + (5894814371/100000000000000 : ℝ)*(sp1) + (1357488097/12500000000000 : ℝ)*(sp2) + (6144214717011389/100000000000000 : ℝ)*(sp4) + (1228841873083883/20000000000000 : ℝ)*(sp5) + (3072102207480737/50000000000000 : ℝ)*(sp6) + (2870632486017439/100000000000000 : ℝ)*(sp7) + (2870632486017439/100000000000000 : ℝ)*(f.failure) + (1536053909599317/25000000000000 : ℝ)*(f.sum) + (13659402109207/4413750000000000000000000000 : ℝ)*base65 + (1281156355639681641/147125000000000000000000000000000 : ℝ)*base67 + (270865936501681641/147125000000000000000000000000000 : ℝ)*base69 + (637205966611693359/147125000000000000000000000000000 : ℝ)*base72 + (35114213031193/17655000000000000000000000000 : ℝ)*base73 + (519384485722931641/147125000000000000000000000000000 : ℝ)*base75 + (306019936774556641/147125000000000000000000000000000 : ℝ)*base77 + (1646953008475306641/147125000000000000000000000000000 : ℝ)*base79 + (19309433574151/8827500000000000000000000000 : ℝ)*base82 + (68361061/10000000000000000000000 : ℝ)*base90 + (68361061/10000000000000000000000 : ℝ)*base92 + (68361061/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1400_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157018501/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14777/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5623/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (451/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7373/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1400_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1400_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157018501/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3973/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10207/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (451/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7373/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1400_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1400_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1400_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157018501/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3973/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10207/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (451/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7373/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1400_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
