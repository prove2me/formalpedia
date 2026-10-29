-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1506_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:54:15.289738+00:00
-- url     : https://prove2.me/submissions/b25d9df1-4da5-4725-aac8-148b8fb21501

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
theorem support_rectangle_w1506_s0_0 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1692216103/10000000000 : ℝ)*x 0 + (1479365763/2500000000 : ℝ)*x 1 + (2426371259/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1692216103/10000000000 : ℝ)^4509 ≤ (10040433305387/100000000000000 : ℝ)^3485 := by
    have hnat : (1692216103 : ℕ)^4509*100000000000000^3485 ≤ 10040433305387^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1692216103 10000000000 10040433305387 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1479365763/2500000000 : ℝ)^4509 ≤ (50720319992931/100000000000000 : ℝ)^3485 := by
    have hnat : (1479365763 : ℕ)^4509*100000000000000^3485 ≤ 50720319992931^3485*2500000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1479365763 2500000000 50720319992931 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2426371259/5000000000 : ℝ)^4509 ≤ (39239246683467/100000000000000 : ℝ)^3485 := by
    have hnat : (2426371259 : ℕ)^4509*100000000000000^3485 ≤ 39239246683467^3485*5000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2426371259 5000000000 39239246683467 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1692216103/10000000000 : ℝ), (1479365763/2500000000 : ℝ), (2426371259/5000000000 : ℝ)] ![(10040433305387/100000000000000 : ℝ), (50720319992931/100000000000000 : ℝ), (39239246683467/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1692216103/10000000000 : ℝ)|^4509 ≤ (10040433305387/100000000000000 : ℝ)^3485
        have hw : |(-1692216103/10000000000 : ℝ)|=(1692216103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1479365763/2500000000 : ℝ)|^4509 ≤ (50720319992931/100000000000000 : ℝ)^3485
        have hw : |(1479365763/2500000000 : ℝ)|=(1479365763/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2426371259/5000000000 : ℝ)|^4509 ≤ (39239246683467/100000000000000 : ℝ)^3485
        have hw : |(2426371259/5000000000 : ℝ)|=(2426371259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_s0_1 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (547928697/1000000000 : ℝ)*x 0 + (-2289475193/10000000000 : ℝ)*x 1 + (4852742473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (547928697/1000000000 : ℝ)^4509 ≤ (45914847851397/100000000000000 : ℝ)^3485 := by
    have hnat : (547928697 : ℕ)^4509*100000000000000^3485 ≤ 45914847851397^3485*1000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547928697 1000000000 45914847851397 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2289475193/10000000000 : ℝ)^4509 ≤ (7422952958871/50000000000000 : ℝ)^3485 := by
    have hnat : (2289475193 : ℕ)^4509*50000000000000^3485 ≤ 7422952958871^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2289475193 10000000000 7422952958871 50000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4852742473/10000000000 : ℝ)^4509 ≤ (39239246212681/100000000000000 : ℝ)^3485 := by
    have hnat : (4852742473 : ℕ)^4509*100000000000000^3485 ≤ 39239246212681^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4852742473 10000000000 39239246212681 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(547928697/1000000000 : ℝ), (-2289475193/10000000000 : ℝ), (4852742473/10000000000 : ℝ)] ![(45914847851397/100000000000000 : ℝ), (7422952958871/50000000000000 : ℝ), (39239246212681/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(547928697/1000000000 : ℝ)|^4509 ≤ (45914847851397/100000000000000 : ℝ)^3485
        have hw : |(547928697/1000000000 : ℝ)|=(547928697/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2289475193/10000000000 : ℝ)|^4509 ≤ (7422952958871/50000000000000 : ℝ)^3485
        have hw : |(-2289475193/10000000000 : ℝ)|=(2289475193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4852742473/10000000000 : ℝ)|^4509 ≤ (39239246212681/100000000000000 : ℝ)^3485
        have hw : |(4852742473/10000000000 : ℝ)|=(4852742473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_s0_2 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5479287007/10000000000 : ℝ)*x 0 + (60659281/125000000 : ℝ)*x 1 + (-1144737569/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5479287007/10000000000 : ℝ)^4509 ≤ (11478712063137/25000000000000 : ℝ)^3485 := by
    have hnat : (5479287007 : ℕ)^4509*25000000000000^3485 ≤ 11478712063137^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5479287007 10000000000 11478712063137 25000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (60659281/125000000 : ℝ)^4509 ≤ (7847849257183/20000000000000 : ℝ)^3485 := by
    have hnat : (60659281 : ℕ)^4509*20000000000000^3485 ≤ 7847849257183^3485*125000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      60659281 125000000 7847849257183 20000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1144737569/5000000000 : ℝ)^4509 ≤ (14845905456307/100000000000000 : ℝ)^3485 := by
    have hnat : (1144737569 : ℕ)^4509*100000000000000^3485 ≤ 14845905456307^3485*5000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1144737569 5000000000 14845905456307 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5479287007/10000000000 : ℝ), (60659281/125000000 : ℝ), (-1144737569/5000000000 : ℝ)] ![(11478712063137/25000000000000 : ℝ), (7847849257183/20000000000000 : ℝ), (14845905456307/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5479287007/10000000000 : ℝ)|^4509 ≤ (11478712063137/25000000000000 : ℝ)^3485
        have hw : |(5479287007/10000000000 : ℝ)|=(5479287007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(60659281/125000000 : ℝ)|^4509 ≤ (7847849257183/20000000000000 : ℝ)^3485
        have hw : |(60659281/125000000 : ℝ)|=(60659281/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1144737569/5000000000 : ℝ)|^4509 ≤ (14845905456307/100000000000000 : ℝ)^3485
        have hw : |(-1144737569/5000000000 : ℝ)|=(1144737569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_s0_3 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1036691379/2500000000 : ℝ)*x 0 + (772809199/2500000000 : ℝ)*x 1 + (2747688669/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1036691379/2500000000 : ℝ)^4509 ≤ (8004252757247/25000000000000 : ℝ)^3485 := by
    have hnat : (1036691379 : ℕ)^4509*25000000000000^3485 ≤ 8004252757247^3485*2500000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036691379 2500000000 8004252757247 25000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (772809199/2500000000 : ℝ)^4509 ≤ (10946807633641/50000000000000 : ℝ)^3485 := by
    have hnat : (772809199 : ℕ)^4509*50000000000000^3485 ≤ 10946807633641^3485*2500000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      772809199 2500000000 10946807633641 50000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2747688669/5000000000 : ℝ)^4509 ≤ (46089373688649/100000000000000 : ℝ)^3485 := by
    have hnat : (2747688669 : ℕ)^4509*100000000000000^3485 ≤ 46089373688649^3485*5000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2747688669 5000000000 46089373688649 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1036691379/2500000000 : ℝ), (772809199/2500000000 : ℝ), (2747688669/5000000000 : ℝ)] ![(8004252757247/25000000000000 : ℝ), (10946807633641/50000000000000 : ℝ), (46089373688649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1036691379/2500000000 : ℝ)|^4509 ≤ (8004252757247/25000000000000 : ℝ)^3485
        have hw : |(1036691379/2500000000 : ℝ)|=(1036691379/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(772809199/2500000000 : ℝ)|^4509 ≤ (10946807633641/50000000000000 : ℝ)^3485
        have hw : |(772809199/2500000000 : ℝ)|=(772809199/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2747688669/5000000000 : ℝ)|^4509 ≤ (46089373688649/100000000000000 : ℝ)^3485
        have hw : |(2747688669/5000000000 : ℝ)|=(2747688669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_s0_4 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-339157571/2000000000 : ℝ)*x 0 + (243996567/500000000 : ℝ)*x 1 + (1472324901/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (339157571/2000000000 : ℝ)^4509 ≤ (5033930520859/50000000000000 : ℝ)^3485 := by
    have hnat : (339157571 : ℕ)^4509*50000000000000^3485 ≤ 5033930520859^3485*2000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339157571 2000000000 5033930520859 50000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (243996567/500000000 : ℝ)^4509 ≤ (19761963723593/50000000000000 : ℝ)^3485 := by
    have hnat : (243996567 : ℕ)^4509*50000000000000^3485 ≤ 19761963723593^3485*500000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      243996567 500000000 19761963723593 50000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1472324901/2500000000 : ℝ)^4509 ≤ (50408211498189/100000000000000 : ℝ)^3485 := by
    have hnat : (1472324901 : ℕ)^4509*100000000000000^3485 ≤ 50408211498189^3485*2500000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1472324901 2500000000 50408211498189 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-339157571/2000000000 : ℝ), (243996567/500000000 : ℝ), (1472324901/2500000000 : ℝ)] ![(5033930520859/50000000000000 : ℝ), (19761963723593/50000000000000 : ℝ), (50408211498189/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-339157571/2000000000 : ℝ)|^4509 ≤ (5033930520859/50000000000000 : ℝ)^3485
        have hw : |(-339157571/2000000000 : ℝ)|=(339157571/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(243996567/500000000 : ℝ)|^4509 ≤ (19761963723593/50000000000000 : ℝ)^3485
        have hw : |(243996567/500000000 : ℝ)|=(243996567/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1472324901/2500000000 : ℝ)|^4509 ≤ (50408211498189/100000000000000 : ℝ)^3485
        have hw : |(1472324901/2500000000 : ℝ)|=(1472324901/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_s0_5 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5188421749/10000000000 : ℝ)*x 0 + (-1252918437/10000000000 : ℝ)*x 1 + (2944649667/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5188421749/10000000000 : ℝ)^4509 ≤ (171144866063/400000000000 : ℝ)^3485 := by
    have hnat : (5188421749 : ℕ)^4509*400000000000^3485 ≤ 171144866063^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5188421749 10000000000 171144866063 400000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1252918437/10000000000 : ℝ)^4509 ≤ (54444599719/800000000000 : ℝ)^3485 := by
    have hnat : (1252918437 : ℕ)^4509*800000000000^3485 ≤ 54444599719^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1252918437 10000000000 54444599719 800000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2944649667/5000000000 : ℝ)^4509 ≤ (50408208508137/100000000000000 : ℝ)^3485 := by
    have hnat : (2944649667 : ℕ)^4509*100000000000000^3485 ≤ 50408208508137^3485*5000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2944649667 5000000000 50408208508137 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5188421749/10000000000 : ℝ), (-1252918437/10000000000 : ℝ), (2944649667/5000000000 : ℝ)] ![(171144866063/400000000000 : ℝ), (54444599719/800000000000 : ℝ), (50408208508137/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5188421749/10000000000 : ℝ)|^4509 ≤ (171144866063/400000000000 : ℝ)^3485
        have hw : |(5188421749/10000000000 : ℝ)|=(5188421749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1252918437/10000000000 : ℝ)|^4509 ≤ (54444599719/800000000000 : ℝ)^3485
        have hw : |(-1252918437/10000000000 : ℝ)|=(1252918437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2944649667/5000000000 : ℝ)|^4509 ≤ (50408208508137/100000000000000 : ℝ)^3485
        have hw : |(2944649667/5000000000 : ℝ)|=(2944649667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_s0_6 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5188421857/10000000000 : ℝ)*x 0 + (588929929/1000000000 : ℝ)*x 1 + (-1252918341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5188421857/10000000000 : ℝ)^4509 ≤ (42786217668061/100000000000000 : ℝ)^3485 := by
    have hnat : (5188421857 : ℕ)^4509*100000000000000^3485 ≤ 42786217668061^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5188421857 10000000000 42786217668061 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (588929929/1000000000 : ℝ)^4509 ≤ (50408208020869/100000000000000 : ℝ)^3485 := by
    have hnat : (588929929 : ℕ)^4509*100000000000000^3485 ≤ 50408208020869^3485*1000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      588929929 1000000000 50408208020869 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1252918341/10000000000 : ℝ)^4509 ≤ (3402787145103/50000000000000 : ℝ)^3485 := by
    have hnat : (1252918341 : ℕ)^4509*50000000000000^3485 ≤ 3402787145103^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1252918341 10000000000 3402787145103 50000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5188421857/10000000000 : ℝ), (588929929/1000000000 : ℝ), (-1252918341/10000000000 : ℝ)] ![(42786217668061/100000000000000 : ℝ), (50408208020869/100000000000000 : ℝ), (3402787145103/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5188421857/10000000000 : ℝ)|^4509 ≤ (42786217668061/100000000000000 : ℝ)^3485
        have hw : |(5188421857/10000000000 : ℝ)|=(5188421857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(588929929/1000000000 : ℝ)|^4509 ≤ (50408208020869/100000000000000 : ℝ)^3485
        have hw : |(588929929/1000000000 : ℝ)|=(588929929/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1252918341/10000000000 : ℝ)|^4509 ≤ (3402787145103/50000000000000 : ℝ)^3485
        have hw : |(-1252918341/10000000000 : ℝ)|=(1252918341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_s0_7 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4154830751/10000000000 : ℝ)*x 0 + (5433985023/10000000000 : ℝ)*x 1 + (630966133/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4154830751/10000000000 : ℝ)^4509 ≤ (32097602634583/100000000000000 : ℝ)^3485 := by
    have hnat : (4154830751 : ℕ)^4509*100000000000000^3485 ≤ 32097602634583^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4154830751 10000000000 32097602634583 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5433985023/10000000000 : ℝ)^4509 ≤ (11356071281853/25000000000000 : ℝ)^3485 := by
    have hnat : (5433985023 : ℕ)^4509*25000000000000^3485 ≤ 11356071281853^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433985023 10000000000 11356071281853 25000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (630966133/2000000000 : ℝ)^4509 ≤ (22478112222181/100000000000000 : ℝ)^3485 := by
    have hnat : (630966133 : ℕ)^4509*100000000000000^3485 ≤ 22478112222181^3485*2000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      630966133 2000000000 22478112222181 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4154830751/10000000000 : ℝ), (5433985023/10000000000 : ℝ), (630966133/2000000000 : ℝ)] ![(32097602634583/100000000000000 : ℝ), (11356071281853/25000000000000 : ℝ), (22478112222181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4154830751/10000000000 : ℝ)|^4509 ≤ (32097602634583/100000000000000 : ℝ)^3485
        have hw : |(4154830751/10000000000 : ℝ)|=(4154830751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5433985023/10000000000 : ℝ)|^4509 ≤ (11356071281853/25000000000000 : ℝ)^3485
        have hw : |(5433985023/10000000000 : ℝ)|=(5433985023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(630966133/2000000000 : ℝ)|^4509 ≤ (22478112222181/100000000000000 : ℝ)^3485
        have hw : |(630966133/2000000000 : ℝ)|=(630966133/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1506_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32580013/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (11/400 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (12781/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4507/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4507 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4507*1^1024 ≤ 0^1024*1^4507 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4507 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4507 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4507/1024 : ℝ) ≤ (886114631293905573/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4507 ≤ (886114631293905573/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4507*50000000000000000000^1024 ≤ 886114631293905573^1024*5^4507 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 886114631293905573 50000000000000000000 4507 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (886114631293905573/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4507 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4507/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4507 := by
      have hnat : (1 : ℕ)^1024*1^4507 ≤ 1^4507*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4507 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4507 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50886114631293905573/50000000000000000000 : ℝ) ≤ (2509998136595103/2500000000000000 : ℝ) ^ (4507/1024 : ℝ) := by
    have hpowers : (50886114631293905573/50000000000000000000 : ℝ)^1024 ≤ (2509998136595103/2500000000000000 : ℝ)^4507 := by
      have hnat : (50886114631293905573 : ℕ)^1024*2500000000000000^4507 ≤ 2509998136595103^4507*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50886114631293905573 50000000000000000000 2509998136595103 2500000000000000 1024 4507 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2509998136595103/2500000000000000 : ℝ)) (X := (50886114631293905573/50000000000000000000 : ℝ)) (by norm_num) 4507 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25886114631293905573/25000000000000000000 : ℝ) ≤ (1259998136595103/1250000000000000 : ℝ) ^ (4507/1024 : ℝ) := by
    have hpowers : (25886114631293905573/25000000000000000000 : ℝ)^1024 ≤ (1259998136595103/1250000000000000 : ℝ)^4507 := by
      have hnat : (25886114631293905573 : ℕ)^1024*1250000000000000^4507 ≤ 1259998136595103^4507*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25886114631293905573 25000000000000000000 1259998136595103 1250000000000000 1024 4507 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1259998136595103/1250000000000000 : ℝ)) (X := (25886114631293905573/25000000000000000000 : ℝ)) (by norm_num) 4507 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(9998136595103/1000000000000000 : ℝ)*(0 : ℝ))^(4507/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(9998136595103/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(886114631293905573/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(9998136595103/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4507/1024 : ℝ) := by
    rw [show (1 : ℝ)+(9998136595103/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2509998136595103/2500000000000000 : ℝ) by norm_num, show 1+(886114631293905573/50000000000000000000 : ℝ)+(0 : ℝ)=(50886114631293905573/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(886114631293905573/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(9998136595103/1000000000000000 : ℝ)*(2/5 : ℝ))^(4507/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(9998136595103/1000000000000000 : ℝ)*(2/5 : ℝ)=(1259998136595103/1250000000000000 : ℝ) by norm_num, show 1+2*(886114631293905573/50000000000000000000 : ℝ)=(25886114631293905573/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(9998136595103/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4507/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (9998136595103/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(9998136595103/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4507/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (9998136595103/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(9998136595103/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4507/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (9998136595103/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1692216103/10000000000 : ℝ)*X 0 0+(1479365763/2500000000 : ℝ)*X 0 1+(2426371259/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((547928697/1000000000 : ℝ)*X 1 0+(-2289475193/10000000000 : ℝ)*X 1 1+(4852742473/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5479287007/10000000000 : ℝ)*X 2 0+(60659281/125000000 : ℝ)*X 2 1+(-1144737569/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1036691379/2500000000 : ℝ)*X 0 0+(772809199/2500000000 : ℝ)*X 0 1+(2747688669/5000000000 : ℝ)*X 0 2+(1036691379/2500000000 : ℝ)*X 1 0+(772809199/2500000000 : ℝ)*X 1 1+(2747688669/5000000000 : ℝ)*X 1 2+(1036691379/2500000000 : ℝ)*X 2 0+(772809199/2500000000 : ℝ)*X 2 1+(2747688669/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-339157571/2000000000 : ℝ)*X 0 0+(243996567/500000000 : ℝ)*X 0 1+(1472324901/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5188421749/10000000000 : ℝ)*X 1 0+(-1252918437/10000000000 : ℝ)*X 1 1+(2944649667/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5188421857/10000000000 : ℝ)*X 2 0+(588929929/1000000000 : ℝ)*X 2 1+(-1252918341/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4154830751/10000000000 : ℝ)*X 0 0+(5433985023/10000000000 : ℝ)*X 0 1+(630966133/2000000000 : ℝ)*X 0 2+(4154830751/10000000000 : ℝ)*X 1 0+(5433985023/10000000000 : ℝ)*X 1 1+(630966133/2000000000 : ℝ)*X 1 2+(4154830751/10000000000 : ℝ)*X 2 0+(5433985023/10000000000 : ℝ)*X 2 1+(630966133/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (91631521937269871927589/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7689271/25000000000000 : ℝ)*(base1) + (42019393/5000000000000 : ℝ)*(base19) + (6773841/800000000000 : ℝ)*(base23) + (4951041/5000000000000 : ℝ)*(upper3) + (116587031/100000000000000 : ℝ)*(upper5) + (677585580312921/100000000000000 : ℝ)*(major0) + (677585580312921/100000000000000 : ℝ)*(major1) + (677585580312921/100000000000000 : ℝ)*(major2) + (939216341867971/100000000000000 : ℝ)*(sp0) + (939218503805817/100000000000000 : ℝ)*(sp1) + (939218497463553/100000000000000 : ℝ)*(sp2) + (103987587673977/25000000000000 : ℝ)*(sp3) + (3033082791/100000000000000 : ℝ)*(sp4) + (1312803803/100000000000000 : ℝ)*(sp7) + (83190338851359/20000000000000 : ℝ)*(f.failure) + (939219344193677/100000000000000 : ℝ)*(f.sum) + (22554496924137/50000000000000000000000000000 : ℝ)*base66 + (85721149325863/100000000000000000000000000000 : ℝ)*base67 + (535199547874137/100000000000000000000000000000 : ℝ)*base70 + (5400309125863/100000000000000000000000000000 : ℝ)*base71 + (8937561574137/50000000000000000000000000000 : ℝ)*base74 + (69724482225863/100000000000000000000000000000 : ℝ)*base75 + (14335171025863/100000000000000000000000000000 : ℝ)*base77 + (736734251474137/100000000000000000000000000000 : ℝ)*base80 + (258229113024137/50000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (2712333/400000000000000000000 : ℝ)*base90 + (2712333/400000000000000000000 : ℝ)*base92 + (2712333/400000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (300395247864837181536681/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1164648579/100000000000000 : ℝ)*(base19) + (600203759/50000000000000 : ℝ)*(base23) + (19507943/20000000000000 : ℝ)*(base32) + (83795701/50000000000000 : ℝ)*(upper3) + (114851819/100000000000000 : ℝ)*(upper5) + (714738801532109/100000000000000 : ℝ)*(major0) + (714738801532109/100000000000000 : ℝ)*(major1) + (714738801532109/100000000000000 : ℝ)*(major2) + (548761737/20000000000000 : ℝ)*(sp1) + (1506907109/50000000000000 : ℝ)*(sp2) + (990718338136063/100000000000000 : ℝ)*(sp4) + (2476786074197/250000000000 : ℝ)*(sp5) + (990714123914327/100000000000000 : ℝ)*(sp6) + (54844870890617/12500000000000 : ℝ)*(sp7) + (438759064664651/100000000000000 : ℝ)*(f.failure) + (990718338136063/100000000000000 : ℝ)*(f.sum) + (80217383112227/50000000000000000000000000000 : ℝ)*base65 + (222017808137773/100000000000000000000000000000 : ℝ)*base68 + (51141162537773/100000000000000000000000000000 : ℝ)*base70 + (265769271937773/100000000000000000000000000000 : ℝ)*base72 + (17139650512227/50000000000000000000000000000 : ℝ)*base73 + (674708977837773/100000000000000000000000000000 : ℝ)*base76 + (343835216562227/100000000000000000000000000000 : ℝ)*base77 + (174077213137773/100000000000000000000000000000 : ℝ)*base80 + (26146955787773/50000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (9779537/2000000000000000000000 : ℝ)*base90 + (9779537/2000000000000000000000 : ℝ)*base92 + (9779537/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1506_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32580013/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11/400 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (12781/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1506_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1506_s1_0 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-369508017/2000000000 : ℝ)*x 0 + (2787265549/5000000000 : ℝ)*x 1 + (5095871269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (369508017/2000000000 : ℝ)^4509 ≤ (5624276137911/50000000000000 : ℝ)^3485 := by
    have hnat : (369508017 : ℕ)^4509*50000000000000^3485 ≤ 5624276137911^3485*2000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      369508017 2000000000 5624276137911 50000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2787265549/5000000000 : ℝ)^4509 ≤ (46950104303569/100000000000000 : ℝ)^3485 := by
    have hnat : (2787265549 : ℕ)^4509*100000000000000^3485 ≤ 46950104303569^3485*5000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2787265549 5000000000 46950104303569 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5095871269/10000000000 : ℝ)^4509 ≤ (20900671701109/50000000000000 : ℝ)^3485 := by
    have hnat : (5095871269 : ℕ)^4509*50000000000000^3485 ≤ 20900671701109^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5095871269 10000000000 20900671701109 50000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-369508017/2000000000 : ℝ), (2787265549/5000000000 : ℝ), (5095871269/10000000000 : ℝ)] ![(5624276137911/50000000000000 : ℝ), (46950104303569/100000000000000 : ℝ), (20900671701109/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-369508017/2000000000 : ℝ)|^4509 ≤ (5624276137911/50000000000000 : ℝ)^3485
        have hw : |(-369508017/2000000000 : ℝ)|=(369508017/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2787265549/5000000000 : ℝ)|^4509 ≤ (46950104303569/100000000000000 : ℝ)^3485
        have hw : |(2787265549/5000000000 : ℝ)|=(2787265549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5095871269/10000000000 : ℝ)|^4509 ≤ (20900671701109/50000000000000 : ℝ)^3485
        have hw : |(5095871269/10000000000 : ℝ)|=(5095871269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_s1_1 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2693859683/5000000000 : ℝ)*x 0 + (-2099778173/10000000000 : ℝ)*x 1 + (1019173647/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2693859683/5000000000 : ℝ)^4509 ≤ (2246226274569/5000000000000 : ℝ)^3485 := by
    have hnat : (2693859683 : ℕ)^4509*5000000000000^3485 ≤ 2246226274569^3485*5000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693859683 5000000000 2246226274569 5000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2099778173/10000000000 : ℝ)^4509 ≤ (1327416328383/10000000000000 : ℝ)^3485 := by
    have hnat : (2099778173 : ℕ)^4509*10000000000000^3485 ≤ 1327416328383^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2099778173 10000000000 1327416328383 10000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1019173647/2000000000 : ℝ)^4509 ≤ (41801311201557/100000000000000 : ℝ)^3485 := by
    have hnat : (1019173647 : ℕ)^4509*100000000000000^3485 ≤ 41801311201557^3485*2000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1019173647 2000000000 41801311201557 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2693859683/5000000000 : ℝ), (-2099778173/10000000000 : ℝ), (1019173647/2000000000 : ℝ)] ![(2246226274569/5000000000000 : ℝ), (1327416328383/10000000000000 : ℝ), (41801311201557/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2693859683/5000000000 : ℝ)|^4509 ≤ (2246226274569/5000000000000 : ℝ)^3485
        have hw : |(2693859683/5000000000 : ℝ)|=(2693859683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2099778173/10000000000 : ℝ)|^4509 ≤ (1327416328383/10000000000000 : ℝ)^3485
        have hw : |(-2099778173/10000000000 : ℝ)|=(2099778173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1019173647/2000000000 : ℝ)|^4509 ≤ (41801311201557/100000000000000 : ℝ)^3485
        have hw : |(1019173647/2000000000 : ℝ)|=(1019173647/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_s1_2 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5387718817/10000000000 : ℝ)*x 0 + (254793477/500000000 : ℝ)*x 1 + (-419955441/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5387718817/10000000000 : ℝ)^4509 ≤ (44924519568563/100000000000000 : ℝ)^3485 := by
    have hnat : (5387718817 : ℕ)^4509*100000000000000^3485 ≤ 44924519568563^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387718817 10000000000 44924519568563 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (254793477/500000000 : ℝ)^4509 ≤ (20900662525937/50000000000000 : ℝ)^3485 := by
    have hnat : (254793477 : ℕ)^4509*50000000000000^3485 ≤ 20900662525937^3485*500000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      254793477 500000000 20900662525937 50000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (419955441/2000000000 : ℝ)^4509 ≤ (6637077683179/50000000000000 : ℝ)^3485 := by
    have hnat : (419955441 : ℕ)^4509*50000000000000^3485 ≤ 6637077683179^3485*2000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419955441 2000000000 6637077683179 50000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5387718817/10000000000 : ℝ), (254793477/500000000 : ℝ), (-419955441/2000000000 : ℝ)] ![(44924519568563/100000000000000 : ℝ), (20900662525937/50000000000000 : ℝ), (6637077683179/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5387718817/10000000000 : ℝ)|^4509 ≤ (44924519568563/100000000000000 : ℝ)^3485
        have hw : |(5387718817/10000000000 : ℝ)|=(5387718817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(254793477/500000000 : ℝ)|^4509 ≤ (20900662525937/50000000000000 : ℝ)^3485
        have hw : |(254793477/500000000 : ℝ)|=(254793477/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-419955441/2000000000 : ℝ)|^4509 ≤ (6637077683179/50000000000000 : ℝ)^3485
        have hw : |(-419955441/2000000000 : ℝ)|=(419955441/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_s1_3 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4251801173/10000000000 : ℝ)*x 0 + (935132663/2500000000 : ℝ)*x 1 + (1205337837/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4251801173/10000000000 : ℝ)^4509 ≤ (33070158424451/100000000000000 : ℝ)^3485 := by
    have hnat : (4251801173 : ℕ)^4509*100000000000000^3485 ≤ 33070158424451^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4251801173 10000000000 33070158424451 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (935132663/2500000000 : ℝ)^4509 ≤ (7004673450647/25000000000000 : ℝ)^3485 := by
    have hnat : (935132663 : ℕ)^4509*25000000000000^3485 ≤ 7004673450647^3485*2500000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      935132663 2500000000 7004673450647 25000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1205337837/2500000000 : ℝ)^4509 ≤ (19455573879861/50000000000000 : ℝ)^3485 := by
    have hnat : (1205337837 : ℕ)^4509*50000000000000^3485 ≤ 19455573879861^3485*2500000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1205337837 2500000000 19455573879861 50000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4251801173/10000000000 : ℝ), (935132663/2500000000 : ℝ), (1205337837/2500000000 : ℝ)] ![(33070158424451/100000000000000 : ℝ), (7004673450647/25000000000000 : ℝ), (19455573879861/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4251801173/10000000000 : ℝ)|^4509 ≤ (33070158424451/100000000000000 : ℝ)^3485
        have hw : |(4251801173/10000000000 : ℝ)|=(4251801173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(935132663/2500000000 : ℝ)|^4509 ≤ (7004673450647/25000000000000 : ℝ)^3485
        have hw : |(935132663/2500000000 : ℝ)|=(935132663/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1205337837/2500000000 : ℝ)|^4509 ≤ (19455573879861/50000000000000 : ℝ)^3485
        have hw : |(1205337837/2500000000 : ℝ)|=(1205337837/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_s1_4 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1847854073/10000000000 : ℝ)*x 0 + (5101268199/10000000000 : ℝ)*x 1 + (2784523039/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1847854073/10000000000 : ℝ)^4509 ≤ (11251025731357/100000000000000 : ℝ)^3485 := by
    have hnat : (1847854073 : ℕ)^4509*100000000000000^3485 ≤ 11251025731357^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1847854073 10000000000 11251025731357 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5101268199/10000000000 : ℝ)^4509 ≤ (130808223099/312500000000 : ℝ)^3485 := by
    have hnat : (5101268199 : ℕ)^4509*312500000000^3485 ≤ 130808223099^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5101268199 10000000000 130808223099 312500000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2784523039/5000000000 : ℝ)^4509 ≤ (23445171429409/50000000000000 : ℝ)^3485 := by
    have hnat : (2784523039 : ℕ)^4509*50000000000000^3485 ≤ 23445171429409^3485*5000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2784523039 5000000000 23445171429409 50000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1847854073/10000000000 : ℝ), (5101268199/10000000000 : ℝ), (2784523039/5000000000 : ℝ)] ![(11251025731357/100000000000000 : ℝ), (130808223099/312500000000 : ℝ), (23445171429409/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1847854073/10000000000 : ℝ)|^4509 ≤ (11251025731357/100000000000000 : ℝ)^3485
        have hw : |(-1847854073/10000000000 : ℝ)|=(1847854073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5101268199/10000000000 : ℝ)|^4509 ≤ (130808223099/312500000000 : ℝ)^3485
        have hw : |(5101268199/10000000000 : ℝ)|=(5101268199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2784523039/5000000000 : ℝ)|^4509 ≤ (23445171429409/50000000000000 : ℝ)^3485
        have hw : |(2784523039/5000000000 : ℝ)|=(2784523039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_s1_5 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2630866669/5000000000 : ℝ)*x 0 + (-325320107/2000000000 : ℝ)*x 1 + (2784523117/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2630866669/5000000000 : ℝ)^4509 ≤ (1742801460437/4000000000000 : ℝ)^3485 := by
    have hnat : (2630866669 : ℕ)^4509*4000000000000^3485 ≤ 1742801460437^3485*5000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630866669 5000000000 1742801460437 4000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (325320107/2000000000 : ℝ)^4509 ≤ (4769809461083/50000000000000 : ℝ)^3485 := by
    have hnat : (325320107 : ℕ)^4509*50000000000000^3485 ≤ 4769809461083^3485*2000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      325320107 2000000000 4769809461083 50000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2784523117/5000000000 : ℝ)^4509 ≤ (23445172279127/50000000000000 : ℝ)^3485 := by
    have hnat : (2784523117 : ℕ)^4509*50000000000000^3485 ≤ 23445172279127^3485*5000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2784523117 5000000000 23445172279127 50000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2630866669/5000000000 : ℝ), (-325320107/2000000000 : ℝ), (2784523117/5000000000 : ℝ)] ![(1742801460437/4000000000000 : ℝ), (4769809461083/50000000000000 : ℝ), (23445172279127/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2630866669/5000000000 : ℝ)|^4509 ≤ (1742801460437/4000000000000 : ℝ)^3485
        have hw : |(2630866669/5000000000 : ℝ)|=(2630866669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-325320107/2000000000 : ℝ)|^4509 ≤ (4769809461083/50000000000000 : ℝ)^3485
        have hw : |(-325320107/2000000000 : ℝ)|=(325320107/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2784523117/5000000000 : ℝ)|^4509 ≤ (23445172279127/50000000000000 : ℝ)^3485
        have hw : |(2784523117/5000000000 : ℝ)|=(2784523117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_s1_6 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (526173317/1000000000 : ℝ)*x 0 + (5569046293/10000000000 : ℝ)*x 1 + (-813300343/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (526173317/1000000000 : ℝ)^4509 ≤ (10892508677759/25000000000000 : ℝ)^3485 := by
    have hnat : (526173317 : ℕ)^4509*25000000000000^3485 ≤ 10892508677759^3485*1000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526173317 1000000000 10892508677759 25000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5569046293/10000000000 : ℝ)^4509 ≤ (46890345200989/100000000000000 : ℝ)^3485 := by
    have hnat : (5569046293 : ℕ)^4509*100000000000000^3485 ≤ 46890345200989^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5569046293 10000000000 46890345200989 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (813300343/5000000000 : ℝ)^4509 ≤ (1907924013591/20000000000000 : ℝ)^3485 := by
    have hnat : (813300343 : ℕ)^4509*20000000000000^3485 ≤ 1907924013591^3485*5000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      813300343 5000000000 1907924013591 20000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(526173317/1000000000 : ℝ), (5569046293/10000000000 : ℝ), (-813300343/5000000000 : ℝ)] ![(10892508677759/25000000000000 : ℝ), (46890345200989/100000000000000 : ℝ), (1907924013591/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(526173317/1000000000 : ℝ)|^4509 ≤ (10892508677759/25000000000000 : ℝ)^3485
        have hw : |(526173317/1000000000 : ℝ)|=(526173317/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5569046293/10000000000 : ℝ)|^4509 ≤ (46890345200989/100000000000000 : ℝ)^3485
        have hw : |(5569046293/10000000000 : ℝ)|=(5569046293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-813300343/5000000000 : ℝ)|^4509 ≤ (1907924013591/20000000000000 : ℝ)^3485
        have hw : |(-813300343/5000000000 : ℝ)|=(813300343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_s1_7 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2126254229/5000000000 : ℝ)*x 0 + (4809162407/10000000000 : ℝ)*x 1 + (375291809/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2126254229/5000000000 : ℝ)^4509 ≤ (33077276225453/100000000000000 : ℝ)^3485 := by
    have hnat : (2126254229 : ℕ)^4509*100000000000000^3485 ≤ 33077276225453^3485*5000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126254229 5000000000 33077276225453 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4809162407/10000000000 : ℝ)^4509 ≤ (19391959212459/50000000000000 : ℝ)^3485 := by
    have hnat : (4809162407 : ℕ)^4509*50000000000000^3485 ≤ 19391959212459^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4809162407 10000000000 19391959212459 50000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (375291809/1000000000 : ℝ)^4509 ≤ (28138805332343/100000000000000 : ℝ)^3485 := by
    have hnat : (375291809 : ℕ)^4509*100000000000000^3485 ≤ 28138805332343^3485*1000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      375291809 1000000000 28138805332343 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2126254229/5000000000 : ℝ), (4809162407/10000000000 : ℝ), (375291809/1000000000 : ℝ)] ![(33077276225453/100000000000000 : ℝ), (19391959212459/50000000000000 : ℝ), (28138805332343/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2126254229/5000000000 : ℝ)|^4509 ≤ (33077276225453/100000000000000 : ℝ)^3485
        have hw : |(2126254229/5000000000 : ℝ)|=(2126254229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4809162407/10000000000 : ℝ)|^4509 ≤ (19391959212459/50000000000000 : ℝ)^3485
        have hw : |(4809162407/10000000000 : ℝ)|=(4809162407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(375291809/1000000000 : ℝ)|^4509 ≤ (28138805332343/100000000000000 : ℝ)^3485
        have hw : |(375291809/1000000000 : ℝ)|=(375291809/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1506_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32580013/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (12781/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11/400 : ℝ)*pair X i i ≤ pair X i h) :
    (331/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9199/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (12781/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11/400 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (12781/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11/400 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (12781/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11/400 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (12781/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11/400 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (12781/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11/400 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (12781/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11/400 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11/400 : ℝ) ^ (4507/1024 : ℝ) ≤ (2703710101809/20000000000000000000 : ℝ) := by
    have hpowers : (11/400 : ℝ)^4507 ≤ (2703710101809/20000000000000000000 : ℝ)^1024 := by
      have hnat : (11 : ℕ)^4507*20000000000000000000^1024 ≤ 2703710101809^1024*400^4507 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11 400 2703710101809 20000000000000000000 4507 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11/400 : ℝ)) (X := (2703710101809/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4507 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (12781/50000 : ℝ) ^ (4507/1024 : ℝ) ≤ (246949030389310779/100000000000000000000 : ℝ) := by
    have hpowers : (12781/50000 : ℝ)^4507 ≤ (246949030389310779/100000000000000000000 : ℝ)^1024 := by
      have hnat : (12781 : ℕ)^4507*100000000000000000000^1024 ≤ 246949030389310779^1024*50000^4507 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12781 50000 246949030389310779 100000000000000000000 4507 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (12781/50000 : ℝ)) (X := (246949030389310779/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4507 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000002703710101809/10000000000000000000 : ℝ) ≤ (1000000061428863/1000000000000000 : ℝ) ^ (4507/1024 : ℝ) := by
    have hpowers : (10000002703710101809/10000000000000000000 : ℝ)^1024 ≤ (1000000061428863/1000000000000000 : ℝ)^4507 := by
      have hnat : (10000002703710101809 : ℕ)^1024*1000000000000000^4507 ≤ 1000000061428863^4507*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000002703710101809 10000000000000000000 1000000061428863 1000000000000000 1024 4507 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000000061428863/1000000000000000 : ℝ)) (X := (10000002703710101809/10000000000000000000 : ℝ)) (by norm_num) 4507 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6265435159308738739/6250000000000000000 : ℝ) ≤ (10005605695119823/10000000000000000 : ℝ) ^ (4507/1024 : ℝ) := by
    have hpowers : (6265435159308738739/6250000000000000000 : ℝ)^1024 ≤ (10005605695119823/10000000000000000 : ℝ)^4507 := by
      have hnat : (6265435159308738739 : ℕ)^1024*10000000000000000^4507 ≤ 10005605695119823^4507*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6265435159308738739 6250000000000000000 10005605695119823 10000000000000000 1024 4507 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005605695119823/10000000000000000 : ℝ)) (X := (6265435159308738739/6250000000000000000 : ℝ)) (by norm_num) 4507 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50246949030389310779/50000000000000000000 : ℝ) ≤ (1251401346993877/1250000000000000 : ℝ) ^ (4507/1024 : ℝ) := by
    have hpowers : (50246949030389310779/50000000000000000000 : ℝ)^1024 ≤ (1251401346993877/1250000000000000 : ℝ)^4507 := by
      have hnat : (50246949030389310779 : ℕ)^1024*1250000000000000^4507 ≤ 1251401346993877^4507*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50246949030389310779 50000000000000000000 1251401346993877 1250000000000000 1024 4507 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1251401346993877/1250000000000000 : ℝ)) (X := (50246949030389310779/50000000000000000000 : ℝ)) (by norm_num) 4507 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2703710101809/20000000000000000000 : ℝ) ≤ ((11404459303429033303/11406000000000000000 : ℝ)+2*(5605080831193/2281200000000000 : ℝ)*(11/400 : ℝ))^(4507/1024 : ℝ) := by
    rw [show (11404459303429033303/11406000000000000000 : ℝ)+2*(5605080831193/2281200000000000 : ℝ)*(11/400 : ℝ)=(1000000061428863/1000000000000000 : ℝ) by norm_num, show 1+2*(2703710101809/20000000000000000000 : ℝ)=(10000002703710101809/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(246949030389310779/100000000000000000000 : ℝ)+(2703710101809/20000000000000000000 : ℝ) ≤ ((11404459303429033303/11406000000000000000 : ℝ)+(5605080831193/2281200000000000 : ℝ)*((12781/50000 : ℝ)+(11/400 : ℝ)))^(4507/1024 : ℝ) := by
    rw [show (11404459303429033303/11406000000000000000 : ℝ)+(5605080831193/2281200000000000 : ℝ)*((12781/50000 : ℝ)+(11/400 : ℝ))=(10005605695119823/10000000000000000 : ℝ) by norm_num, show 1+(246949030389310779/100000000000000000000 : ℝ)+(2703710101809/20000000000000000000 : ℝ)=(6265435159308738739/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(246949030389310779/100000000000000000000 : ℝ) ≤ ((11404459303429033303/11406000000000000000 : ℝ)+2*(5605080831193/2281200000000000 : ℝ)*(12781/50000 : ℝ))^(4507/1024 : ℝ) := by
    rw [show (11404459303429033303/11406000000000000000 : ℝ)+2*(5605080831193/2281200000000000 : ℝ)*(12781/50000 : ℝ)=(1251401346993877/1250000000000000 : ℝ) by norm_num, show 1+2*(246949030389310779/100000000000000000000 : ℝ)=(50246949030389310779/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11404459303429033303/11406000000000000000 : ℝ)*(X 1 0+X 2 0)+(5605080831193/2281200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4507/1024 : ℝ)) (lo := (11/400 : ℝ)) (hi := (12781/50000 : ℝ)) (c := (11404459303429033303/11406000000000000000 : ℝ)) (alpha := (5605080831193/2281200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11404459303429033303/11406000000000000000 : ℝ)*(X 0 1+X 2 1)+(5605080831193/2281200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4507/1024 : ℝ)) (lo := (11/400 : ℝ)) (hi := (12781/50000 : ℝ)) (c := (11404459303429033303/11406000000000000000 : ℝ)) (alpha := (5605080831193/2281200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11404459303429033303/11406000000000000000 : ℝ)*(X 0 2+X 1 2)+(5605080831193/2281200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4507/1024 : ℝ)) (lo := (11/400 : ℝ)) (hi := (12781/50000 : ℝ)) (c := (11404459303429033303/11406000000000000000 : ℝ)) (alpha := (5605080831193/2281200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-369508017/2000000000 : ℝ)*X 0 0+(2787265549/5000000000 : ℝ)*X 0 1+(5095871269/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2693859683/5000000000 : ℝ)*X 1 0+(-2099778173/10000000000 : ℝ)*X 1 1+(1019173647/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5387718817/10000000000 : ℝ)*X 2 0+(254793477/500000000 : ℝ)*X 2 1+(-419955441/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4251801173/10000000000 : ℝ)*X 0 0+(935132663/2500000000 : ℝ)*X 0 1+(1205337837/2500000000 : ℝ)*X 0 2+(4251801173/10000000000 : ℝ)*X 1 0+(935132663/2500000000 : ℝ)*X 1 1+(1205337837/2500000000 : ℝ)*X 1 2+(4251801173/10000000000 : ℝ)*X 2 0+(935132663/2500000000 : ℝ)*X 2 1+(1205337837/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1847854073/10000000000 : ℝ)*X 0 0+(5101268199/10000000000 : ℝ)*X 0 1+(2784523039/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2630866669/5000000000 : ℝ)*X 1 0+(-325320107/2000000000 : ℝ)*X 1 1+(2784523117/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((526173317/1000000000 : ℝ)*X 2 0+(5569046293/10000000000 : ℝ)*X 2 1+(-813300343/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2126254229/5000000000 : ℝ)*X 0 0+(4809162407/10000000000 : ℝ)*X 0 1+(375291809/1000000000 : ℝ)*X 0 2+(2126254229/5000000000 : ℝ)*X 1 0+(4809162407/10000000000 : ℝ)*X 1 1+(375291809/1000000000 : ℝ)*X 1 2+(2126254229/5000000000 : ℝ)*X 2 0+(4809162407/10000000000 : ℝ)*X 2 1+(375291809/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (252557904624645648109256201/47525000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3597633/5000000000000 : ℝ)*(base1) + (265139177/20000000000000 : ℝ)*(base19) + (850617707/100000000000000 : ℝ)*(base23) + (18336243/12500000000000 : ℝ)*(lower2) + (70797747/50000000000000 : ℝ)*(upper5) + (1507195466968469/100000000000000 : ℝ)*(major0) + (1507195466968469/100000000000000 : ℝ)*(major1) + (150719546696847/10000000000000 : ℝ)*(major2) + (6528636806441/312500000000 : ℝ)*(sp0) + (522290487428613/25000000000000 : ℝ)*(sp1) + (1044581427745377/50000000000000 : ℝ)*(sp2) + (925225166851381/100000000000000 : ℝ)*(sp3) + (430698123/100000000000000 : ℝ)*(sp5) + (905942021/50000000000000 : ℝ)*(sp7) + (462613525344041/50000000000000 : ℝ)*(f.failure) + (104458185305423/5000000000000 : ℝ)*(f.sum) + (17682797532347/228120000000000000000000000000 : ℝ)*base65 + (12539687338724126893/1140600000000000000000000000000000 : ℝ)*base68 + (191414993903974141/114060000000000000000000000000000 : ℝ)*base69 + (7763937982117526893/1140600000000000000000000000000000 : ℝ)*base72 + (1170454115502373/228120000000000000000000000000 : ℝ)*base74 + (280690928212654141/114060000000000000000000000000000 : ℝ)*base75 + (3921069556520230631/380200000000000000000000000000000 : ℝ)*base78 + (4750231577640030631/380200000000000000000000000000000 : ℝ)*base80 + (150675800446363/114060000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (4747467/1000000000000000000000 : ℝ)*base90 + (4747467/1000000000000000000000 : ℝ)*base92 + (14747467/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (411989260739814825242692149/95050000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (855966083/100000000000000 : ℝ)*(base19) + (426135771/50000000000000 : ℝ)*(base23) + (16840907/12500000000000 : ℝ)*(upper3) + (27110767/100000000000000 : ℝ)*(lower4) + (35075791/100000000000000 : ℝ)*(upper5) + (771129033206083/50000000000000 : ℝ)*(major0) + (771129033206083/50000000000000 : ℝ)*(major1) + (771129033206083/50000000000000 : ℝ)*(major2) + (587297997/10000000000000 : ℝ)*(sp1) + (3208740231/50000000000000 : ℝ)*(sp2) + (1068882472064557/50000000000000 : ℝ)*(sp4) + (2137758215183061/100000000000000 : ℝ)*(sp5) + (2137757674377111/100000000000000 : ℝ)*(sp6) + (47337552210681/5000000000000 : ℝ)*(sp7) + (47337552210681/5000000000000 : ℝ)*(f.failure) + (1068882472064557/50000000000000 : ℝ)*(f.sum) + (266628374881879/57030000000000000000000000000 : ℝ)*base65 + (183463332225492383/190100000000000000000000000000000 : ℝ)*base67 + (643105091481107617/190100000000000000000000000000000 : ℝ)*base70 + (952977567988292383/190100000000000000000000000000000 : ℝ)*base71 + (135594293205169/57030000000000000000000000000 : ℝ)*base73 + (633520312594307617/190100000000000000000000000000000 : ℝ)*base76 + (291994686220307617/190100000000000000000000000000000 : ℝ)*base78 + (1708275246136207617/190100000000000000000000000000000 : ℝ)*base80 + (93222825370699/57030000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (281147/100000000000000000000 : ℝ)*base90 + (281147/100000000000000000000 : ℝ)*base92 + (281147/100000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1506_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32580013/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (12781/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11/400 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (331/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9199/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1506_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1506_s2_0 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1872757833/10000000000 : ℝ)*x 0 + (5459862577/10000000000 : ℝ)*x 1 + (1298553839/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1872757833/10000000000 : ℝ)^4509 ≤ (228951968293/2000000000000 : ℝ)^3485 := by
    have hnat : (1872757833 : ℕ)^4509*2000000000000^3485 ≤ 228951968293^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1872757833 10000000000 228951968293 2000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5459862577/10000000000 : ℝ)^4509 ≤ (4570435973913/10000000000000 : ℝ)^3485 := by
    have hnat : (5459862577 : ℕ)^4509*10000000000000^3485 ≤ 4570435973913^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5459862577 10000000000 4570435973913 10000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1298553839/2500000000 : ℝ)^4509 ≤ (21424020914159/50000000000000 : ℝ)^3485 := by
    have hnat : (1298553839 : ℕ)^4509*50000000000000^3485 ≤ 21424020914159^3485*2500000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1298553839 2500000000 21424020914159 50000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1872757833/10000000000 : ℝ), (5459862577/10000000000 : ℝ), (1298553839/2500000000 : ℝ)] ![(228951968293/2000000000000 : ℝ), (4570435973913/10000000000000 : ℝ), (21424020914159/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1872757833/10000000000 : ℝ)|^4509 ≤ (228951968293/2000000000000 : ℝ)^3485
        have hw : |(-1872757833/10000000000 : ℝ)|=(1872757833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5459862577/10000000000 : ℝ)|^4509 ≤ (4570435973913/10000000000000 : ℝ)^3485
        have hw : |(5459862577/10000000000 : ℝ)|=(5459862577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1298553839/2500000000 : ℝ)|^4509 ≤ (21424020914159/50000000000000 : ℝ)^3485
        have hw : |(1298553839/2500000000 : ℝ)|=(1298553839/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_s2_1 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2679318243/5000000000 : ℝ)*x 0 + (-1004778459/5000000000 : ℝ)*x 1 + (207768649/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2679318243/5000000000 : ℝ)^4509 ≤ (1115275441309/2500000000000 : ℝ)^3485 := by
    have hnat : (2679318243 : ℕ)^4509*2500000000000^3485 ≤ 1115275441309^3485*5000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2679318243 5000000000 1115275441309 2500000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1004778459/5000000000 : ℝ)^4509 ≤ (6270465611731/50000000000000 : ℝ)^3485 := by
    have hnat : (1004778459 : ℕ)^4509*50000000000000^3485 ≤ 6270465611731^3485*5000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004778459 5000000000 6270465611731 50000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (207768649/400000000 : ℝ)^4509 ≤ (42848051103197/100000000000000 : ℝ)^3485 := by
    have hnat : (207768649 : ℕ)^4509*100000000000000^3485 ≤ 42848051103197^3485*400000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207768649 400000000 42848051103197 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2679318243/5000000000 : ℝ), (-1004778459/5000000000 : ℝ), (207768649/400000000 : ℝ)] ![(1115275441309/2500000000000 : ℝ), (6270465611731/50000000000000 : ℝ), (42848051103197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2679318243/5000000000 : ℝ)|^4509 ≤ (1115275441309/2500000000000 : ℝ)^3485
        have hw : |(2679318243/5000000000 : ℝ)|=(2679318243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1004778459/5000000000 : ℝ)|^4509 ≤ (6270465611731/50000000000000 : ℝ)^3485
        have hw : |(-1004778459/5000000000 : ℝ)|=(1004778459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(207768649/400000000 : ℝ)|^4509 ≤ (42848051103197/100000000000000 : ℝ)^3485
        have hw : |(207768649/400000000 : ℝ)|=(207768649/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_s2_2 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5358637407/10000000000 : ℝ)*x 0 + (5194215607/10000000000 : ℝ)*x 1 + (-1004778253/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5358637407/10000000000 : ℝ)^4509 ≤ (44611027572663/100000000000000 : ℝ)^3485 := by
    have hnat : (5358637407 : ℕ)^4509*100000000000000^3485 ≤ 44611027572663^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5358637407 10000000000 44611027572663 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5194215607/10000000000 : ℝ)^4509 ≤ (42848044507253/100000000000000 : ℝ)^3485 := by
    have hnat : (5194215607 : ℕ)^4509*100000000000000^3485 ≤ 42848044507253^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5194215607 10000000000 42848044507253 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1004778253/5000000000 : ℝ)^4509 ≤ (6270463948417/50000000000000 : ℝ)^3485 := by
    have hnat : (1004778253 : ℕ)^4509*50000000000000^3485 ≤ 6270463948417^3485*5000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004778253 5000000000 6270463948417 50000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5358637407/10000000000 : ℝ), (5194215607/10000000000 : ℝ), (-1004778253/5000000000 : ℝ)] ![(44611027572663/100000000000000 : ℝ), (42848044507253/100000000000000 : ℝ), (6270463948417/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5358637407/10000000000 : ℝ)|^4509 ≤ (44611027572663/100000000000000 : ℝ)^3485
        have hw : |(5358637407/10000000000 : ℝ)|=(5358637407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5194215607/10000000000 : ℝ)|^4509 ≤ (42848044507253/100000000000000 : ℝ)^3485
        have hw : |(5194215607/10000000000 : ℝ)|=(5194215607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1004778253/5000000000 : ℝ)|^4509 ≤ (6270463948417/50000000000000 : ℝ)^3485
        have hw : |(-1004778253/5000000000 : ℝ)|=(1004778253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_s2_3 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2134941463/5000000000 : ℝ)*x 0 + (1989472629/5000000000 : ℝ)*x 1 + (4578777839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2134941463/5000000000 : ℝ)^4509 ≤ (33252234255501/100000000000000 : ℝ)^3485 := by
    have hnat : (2134941463 : ℕ)^4509*100000000000000^3485 ≤ 33252234255501^3485*5000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2134941463 5000000000 33252234255501 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1989472629/5000000000 : ℝ)^4509 ≤ (30350615563581/100000000000000 : ℝ)^3485 := by
    have hnat : (1989472629 : ℕ)^4509*100000000000000^3485 ≤ 30350615563581^3485*5000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1989472629 5000000000 30350615563581 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4578777839/10000000000 : ℝ)^4509 ≤ (9099287541961/25000000000000 : ℝ)^3485 := by
    have hnat : (4578777839 : ℕ)^4509*25000000000000^3485 ≤ 9099287541961^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4578777839 10000000000 9099287541961 25000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2134941463/5000000000 : ℝ), (1989472629/5000000000 : ℝ), (4578777839/10000000000 : ℝ)] ![(33252234255501/100000000000000 : ℝ), (30350615563581/100000000000000 : ℝ), (9099287541961/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2134941463/5000000000 : ℝ)|^4509 ≤ (33252234255501/100000000000000 : ℝ)^3485
        have hw : |(2134941463/5000000000 : ℝ)|=(2134941463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1989472629/5000000000 : ℝ)|^4509 ≤ (30350615563581/100000000000000 : ℝ)^3485
        have hw : |(1989472629/5000000000 : ℝ)|=(1989472629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4578777839/10000000000 : ℝ)|^4509 ≤ (9099287541961/25000000000000 : ℝ)^3485
        have hw : |(4578777839/10000000000 : ℝ)|=(4578777839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_s2_4 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1872810549/10000000000 : ℝ)*x 0 + (1039177597/2000000000 : ℝ)*x 1 + (5458175633/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1872810549/10000000000 : ℝ)^4509 ≤ (11448015336313/100000000000000 : ℝ)^3485 := by
    have hnat : (1872810549 : ℕ)^4509*100000000000000^3485 ≤ 11448015336313^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1872810549 10000000000 11448015336313 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1039177597/2000000000 : ℝ)^4509 ≤ (8573178944631/20000000000000 : ℝ)^3485 := by
    have hnat : (1039177597 : ℕ)^4509*20000000000000^3485 ≤ 8573178944631^3485*2000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039177597 2000000000 8573178944631 20000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5458175633/10000000000 : ℝ)^4509 ≤ (5710761239617/12500000000000 : ℝ)^3485 := by
    have hnat : (5458175633 : ℕ)^4509*12500000000000^3485 ≤ 5710761239617^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5458175633 10000000000 5710761239617 12500000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1872810549/10000000000 : ℝ), (1039177597/2000000000 : ℝ), (5458175633/10000000000 : ℝ)] ![(11448015336313/100000000000000 : ℝ), (8573178944631/20000000000000 : ℝ), (5710761239617/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1872810549/10000000000 : ℝ)|^4509 ≤ (11448015336313/100000000000000 : ℝ)^3485
        have hw : |(-1872810549/10000000000 : ℝ)|=(1872810549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1039177597/2000000000 : ℝ)|^4509 ≤ (8573178944631/20000000000000 : ℝ)^3485
        have hw : |(1039177597/2000000000 : ℝ)|=(1039177597/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5458175633/10000000000 : ℝ)|^4509 ≤ (5710761239617/12500000000000 : ℝ)^3485
        have hw : |(5458175633/10000000000 : ℝ)|=(5458175633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_s2_5 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644472653/5000000000 : ℝ)*x 0 + (-872798321/5000000000 : ℝ)*x 1 + (341136029/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644472653/5000000000 : ℝ)^4509 ≤ (109654491603/250000000000 : ℝ)^3485 := by
    have hnat : (2644472653 : ℕ)^4509*250000000000^3485 ≤ 109654491603^3485*5000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644472653 5000000000 109654491603 250000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (872798321/5000000000 : ℝ)^4509 ≤ (5226052216451/50000000000000 : ℝ)^3485 := by
    have hnat : (872798321 : ℕ)^4509*50000000000000^3485 ≤ 5226052216451^3485*5000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      872798321 5000000000 5226052216451 50000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (341136029/625000000 : ℝ)^4509 ≤ (9137219783273/20000000000000 : ℝ)^3485 := by
    have hnat : (341136029 : ℕ)^4509*20000000000000^3485 ≤ 9137219783273^3485*625000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341136029 625000000 9137219783273 20000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644472653/5000000000 : ℝ), (-872798321/5000000000 : ℝ), (341136029/625000000 : ℝ)] ![(109654491603/250000000000 : ℝ), (5226052216451/50000000000000 : ℝ), (9137219783273/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644472653/5000000000 : ℝ)|^4509 ≤ (109654491603/250000000000 : ℝ)^3485
        have hw : |(2644472653/5000000000 : ℝ)|=(2644472653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-872798321/5000000000 : ℝ)|^4509 ≤ (5226052216451/50000000000000 : ℝ)^3485
        have hw : |(-872798321/5000000000 : ℝ)|=(872798321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(341136029/625000000 : ℝ)|^4509 ≤ (9137219783273/20000000000000 : ℝ)^3485
        have hw : |(341136029/625000000 : ℝ)|=(341136029/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_s2_6 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644472761/5000000000 : ℝ)*x 0 + (1364543971/2500000000 : ℝ)*x 1 + (-872798577/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644472761/5000000000 : ℝ)^4509 ≤ (43861798958853/100000000000000 : ℝ)^3485 := by
    have hnat : (2644472761 : ℕ)^4509*100000000000000^3485 ≤ 43861798958853^3485*5000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644472761 5000000000 43861798958853 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1364543971/2500000000 : ℝ)^4509 ≤ (1827443705407/4000000000000 : ℝ)^3485 := by
    have hnat : (1364543971 : ℕ)^4509*4000000000000^3485 ≤ 1827443705407^3485*2500000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1364543971 2500000000 1827443705407 4000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (872798577/5000000000 : ℝ)^4509 ≤ (52260541997/500000000000 : ℝ)^3485 := by
    have hnat : (872798577 : ℕ)^4509*500000000000^3485 ≤ 52260541997^3485*5000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      872798577 5000000000 52260541997 500000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644472761/5000000000 : ℝ), (1364543971/2500000000 : ℝ), (-872798577/5000000000 : ℝ)] ![(43861798958853/100000000000000 : ℝ), (1827443705407/4000000000000 : ℝ), (52260541997/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644472761/5000000000 : ℝ)|^4509 ≤ (43861798958853/100000000000000 : ℝ)^3485
        have hw : |(2644472761/5000000000 : ℝ)|=(2644472761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1364543971/2500000000 : ℝ)|^4509 ≤ (1827443705407/4000000000000 : ℝ)^3485
        have hw : |(1364543971/2500000000 : ℝ)|=(1364543971/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-872798577/5000000000 : ℝ)|^4509 ≤ (52260541997/500000000000 : ℝ)^3485
        have hw : |(-872798577/5000000000 : ℝ)|=(872798577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_s2_7 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (533750651/1250000000 : ℝ)*x 0 + (4575002911/10000000000 : ℝ)*x 1 + (1991376667/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (533750651/1250000000 : ℝ)^4509 ≤ (33253466357543/100000000000000 : ℝ)^3485 := by
    have hnat : (533750651 : ℕ)^4509*100000000000000^3485 ≤ 33253466357543^3485*1250000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533750651 1250000000 33253466357543 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4575002911/10000000000 : ℝ)^4509 ≤ (36358330544483/100000000000000 : ℝ)^3485 := by
    have hnat : (4575002911 : ℕ)^4509*100000000000000^3485 ≤ 36358330544483^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4575002911 10000000000 36358330544483 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1991376667/5000000000 : ℝ)^4509 ≤ (30388203081331/100000000000000 : ℝ)^3485 := by
    have hnat : (1991376667 : ℕ)^4509*100000000000000^3485 ≤ 30388203081331^3485*5000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1991376667 5000000000 30388203081331 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(533750651/1250000000 : ℝ), (4575002911/10000000000 : ℝ), (1991376667/5000000000 : ℝ)] ![(33253466357543/100000000000000 : ℝ), (36358330544483/100000000000000 : ℝ), (30388203081331/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(533750651/1250000000 : ℝ)|^4509 ≤ (33253466357543/100000000000000 : ℝ)^3485
        have hw : |(533750651/1250000000 : ℝ)|=(533750651/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4575002911/10000000000 : ℝ)|^4509 ≤ (36358330544483/100000000000000 : ℝ)^3485
        have hw : |(4575002911/10000000000 : ℝ)|=(4575002911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1991376667/5000000000 : ℝ)|^4509 ≤ (30388203081331/100000000000000 : ℝ)^3485
        have hw : |(1991376667/5000000000 : ℝ)|=(1991376667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1506_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32580013/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9199/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (331/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (10397/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (801/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9199/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (331/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9199/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (331/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9199/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (331/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9199/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (331/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9199/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (331/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9199/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (331/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (331/4000 : ℝ) ^ (4507/1024 : ℝ) ≤ (862322267778003/50000000000000000000 : ℝ) := by
    have hpowers : (331/4000 : ℝ)^4507 ≤ (862322267778003/50000000000000000000 : ℝ)^1024 := by
      have hnat : (331 : ℕ)^4507*50000000000000000000^1024 ≤ 862322267778003^1024*4000^4507 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        331 4000 862322267778003 50000000000000000000 4507 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (331/4000 : ℝ)) (X := (862322267778003/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4507 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (9199/50000 : ℝ) ^ (4507/1024 : ℝ) ≤ (29037251878619561/50000000000000000000 : ℝ) := by
    have hpowers : (9199/50000 : ℝ)^4507 ≤ (29037251878619561/50000000000000000000 : ℝ)^1024 := by
      have hnat : (9199 : ℕ)^4507*50000000000000000000^1024 ≤ 29037251878619561^1024*50000^4507 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9199 50000 29037251878619561 50000000000000000000 4507 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9199/50000 : ℝ)) (X := (29037251878619561/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4507 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000862322267778003/25000000000000000000 : ℝ) ≤ (400003134701517/400000000000000 : ℝ) ^ (4507/1024 : ℝ) := by
    have hpowers : (25000862322267778003/25000000000000000000 : ℝ)^1024 ≤ (400003134701517/400000000000000 : ℝ)^4507 := by
      have hnat : (25000862322267778003 : ℕ)^1024*400000000000000^4507 ≤ 400003134701517^4507*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000862322267778003 25000000000000000000 400003134701517 400000000000000 1024 4507 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400003134701517/400000000000000 : ℝ)) (X := (25000862322267778003/25000000000000000000 : ℝ)) (by norm_num) 4507 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12507474893536599391/12500000000000000000 : ℝ) ≤ (2500339583890867/2500000000000000 : ℝ) ^ (4507/1024 : ℝ) := by
    have hpowers : (12507474893536599391/12500000000000000000 : ℝ)^1024 ≤ (2500339583890867/2500000000000000 : ℝ)^4507 := by
      have hnat : (12507474893536599391 : ℕ)^1024*2500000000000000^4507 ≤ 2500339583890867^4507*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507474893536599391 12500000000000000000 2500339583890867 2500000000000000 1024 4507 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500339583890867/2500000000000000 : ℝ)) (X := (12507474893536599391/12500000000000000000 : ℝ)) (by norm_num) 4507 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25029037251878619561/25000000000000000000 : ℝ) ≤ (10002638303589011/10000000000000000 : ℝ) ^ (4507/1024 : ℝ) := by
    have hpowers : (25029037251878619561/25000000000000000000 : ℝ)^1024 ≤ (10002638303589011/10000000000000000 : ℝ)^4507 := by
      have hnat : (25029037251878619561 : ℕ)^1024*10000000000000000^4507 ≤ 10002638303589011^4507*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25029037251878619561 25000000000000000000 10002638303589011 10000000000000000 1024 4507 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002638303589011/10000000000000000 : ℝ)) (X := (25029037251878619561/25000000000000000000 : ℝ)) (by norm_num) 4507 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(862322267778003/50000000000000000000 : ℝ) ≤ ((32387075150004377/32393600000000000 : ℝ)+2*(1279968025543/1012300000000000 : ℝ)*(331/4000 : ℝ))^(4507/1024 : ℝ) := by
    rw [show (32387075150004377/32393600000000000 : ℝ)+2*(1279968025543/1012300000000000 : ℝ)*(331/4000 : ℝ)=(400003134701517/400000000000000 : ℝ) by norm_num, show 1+2*(862322267778003/50000000000000000000 : ℝ)=(25000862322267778003/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(29037251878619561/50000000000000000000 : ℝ)+(862322267778003/50000000000000000000 : ℝ) ≤ ((32387075150004377/32393600000000000 : ℝ)+(1279968025543/1012300000000000 : ℝ)*((9199/50000 : ℝ)+(331/4000 : ℝ)))^(4507/1024 : ℝ) := by
    rw [show (32387075150004377/32393600000000000 : ℝ)+(1279968025543/1012300000000000 : ℝ)*((9199/50000 : ℝ)+(331/4000 : ℝ))=(2500339583890867/2500000000000000 : ℝ) by norm_num, show 1+(29037251878619561/50000000000000000000 : ℝ)+(862322267778003/50000000000000000000 : ℝ)=(12507474893536599391/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(29037251878619561/50000000000000000000 : ℝ) ≤ ((32387075150004377/32393600000000000 : ℝ)+2*(1279968025543/1012300000000000 : ℝ)*(9199/50000 : ℝ))^(4507/1024 : ℝ) := by
    rw [show (32387075150004377/32393600000000000 : ℝ)+2*(1279968025543/1012300000000000 : ℝ)*(9199/50000 : ℝ)=(10002638303589011/10000000000000000 : ℝ) by norm_num, show 1+2*(29037251878619561/50000000000000000000 : ℝ)=(25029037251878619561/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (32387075150004377/32393600000000000 : ℝ)*(X 1 0+X 2 0)+(1279968025543/1012300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4507/1024 : ℝ)) (lo := (331/4000 : ℝ)) (hi := (9199/50000 : ℝ)) (c := (32387075150004377/32393600000000000 : ℝ)) (alpha := (1279968025543/1012300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (32387075150004377/32393600000000000 : ℝ)*(X 0 1+X 2 1)+(1279968025543/1012300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4507/1024 : ℝ)) (lo := (331/4000 : ℝ)) (hi := (9199/50000 : ℝ)) (c := (32387075150004377/32393600000000000 : ℝ)) (alpha := (1279968025543/1012300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (32387075150004377/32393600000000000 : ℝ)*(X 0 2+X 1 2)+(1279968025543/1012300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4507/1024 : ℝ)) (lo := (331/4000 : ℝ)) (hi := (9199/50000 : ℝ)) (c := (32387075150004377/32393600000000000 : ℝ)) (alpha := (1279968025543/1012300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1872757833/10000000000 : ℝ)*X 0 0+(5459862577/10000000000 : ℝ)*X 0 1+(1298553839/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2679318243/5000000000 : ℝ)*X 1 0+(-1004778459/5000000000 : ℝ)*X 1 1+(207768649/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5358637407/10000000000 : ℝ)*X 2 0+(5194215607/10000000000 : ℝ)*X 2 1+(-1004778253/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2134941463/5000000000 : ℝ)*X 0 0+(1989472629/5000000000 : ℝ)*X 0 1+(4578777839/10000000000 : ℝ)*X 0 2+(2134941463/5000000000 : ℝ)*X 1 0+(1989472629/5000000000 : ℝ)*X 1 1+(4578777839/10000000000 : ℝ)*X 1 2+(2134941463/5000000000 : ℝ)*X 2 0+(1989472629/5000000000 : ℝ)*X 2 1+(4578777839/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1872810549/10000000000 : ℝ)*X 0 0+(1039177597/2000000000 : ℝ)*X 0 1+(5458175633/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2644472653/5000000000 : ℝ)*X 1 0+(-872798321/5000000000 : ℝ)*X 1 1+(341136029/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2644472761/5000000000 : ℝ)*X 2 0+(1364543971/2500000000 : ℝ)*X 2 1+(-872798577/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((533750651/1250000000 : ℝ)*X 0 0+(4575002911/10000000000 : ℝ)*X 0 1+(1991376667/5000000000 : ℝ)*X 0 2+(533750651/1250000000 : ℝ)*X 1 0+(4575002911/10000000000 : ℝ)*X 1 1+(1991376667/5000000000 : ℝ)*X 1 2+(533750651/1250000000 : ℝ)*X 2 0+(4575002911/10000000000 : ℝ)*X 2 1+(1991376667/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (82884803523519212698317/10123000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1601919079/100000000000000 : ℝ)*(base19) + (383248451/20000000000000 : ℝ)*(base23) + (131431779/100000000000000 : ℝ)*(upper3) + (4456789/2500000000000 : ℝ)*(upper4) + (16955689/5000000000000 : ℝ)*(upper5) + (271580732266207/10000000000000 : ℝ)*(major0) + (271580732266207/10000000000000 : ℝ)*(major1) + (271580732266207/10000000000000 : ℝ)*(major2) + (941104049422237/25000000000000 : ℝ)*(sp0) + (3764451175017711/100000000000000 : ℝ)*(sp1) + (752890172138907/20000000000000 : ℝ)*(sp2) + (833573269502267/50000000000000 : ℝ)*(sp3) + (36579247841/100000000000000 : ℝ)*(sp4) + (15056457119/100000000000000 : ℝ)*(sp7) + (1667161595461653/100000000000000 : ℝ)*(f.failure) + (376445277693679/10000000000000 : ℝ)*(f.sum) + (50867236906113/10123000000000000000000000000 : ℝ)*base65 + (595710760316839/323936000000000000000000000000 : ℝ)*base67 + (79976125428103/323936000000000000000000000000 : ℝ)*base69 + (610416411642919/323936000000000000000000000000 : ℝ)*base71 + (35562874107393/10123000000000000000000000000 : ℝ)*base73 + (1381434295291321/323936000000000000000000000000 : ℝ)*base76 + (97588551626469/64787200000000000000000000000 : ℝ)*base78 + (405363251448773/64787200000000000000000000000 : ℝ)*base80 + (1094722744103/1265375000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (4258511/2000000000000000000000 : ℝ)*base90 + (4258511/2000000000000000000000 : ℝ)*base92 + (4258511/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (21558546404855251686017073/1619680000000000000000000000000 : ℝ) := by norm_num
    linear_combination (445266461/50000000000000 : ℝ)*(base19) + (121559451/6250000000000 : ℝ)*(base23) + (55386003/12500000000000 : ℝ)*(upper3) + (99849399/25000000000000 : ℝ)*(lower4) + (2750536971641901/100000000000000 : ℝ)*(major0) + (2750536971641901/100000000000000 : ℝ)*(major1) + (2750536971641901/100000000000000 : ℝ)*(major2) + (2634892441/25000000000000 : ℝ)*(sp1) + (21434063167/100000000000000 : ℝ)*(sp2) + (174589311/25000000000000 : ℝ)*(sp3) + (1906296150008249/50000000000000 : ℝ)*(sp4) + (3812580869913811/100000000000000 : ℝ)*(sp5) + (1906284460501057/50000000000000 : ℝ)*(sp6) + (1688480501230921/100000000000000 : ℝ)*(sp7) + (337696239917633/20000000000000 : ℝ)*(f.failure) + (1906296150008249/50000000000000 : ℝ)*(f.sum) + (126823989284593/50615000000000000000000000000 : ℝ)*base65 + (11300484417679227/3239360000000000000000000000000 : ℝ)*base68 + (17953524262566587/3239360000000000000000000000000 : ℝ)*base70 + (23866829020500933/3239360000000000000000000000000 : ℝ)*base71 + (1255691000923/12653750000000000000000000000 : ℝ)*base74 + (25080168392694213/3239360000000000000000000000000 : ℝ)*base75 + (17860760776065413/3239360000000000000000000000000 : ℝ)*base77 + (34234908807074373/3239360000000000000000000000000 : ℝ)*base79 + (86000807139963/50615000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (1930771/400000000000000000000 : ℝ)*base90 + (1930771/400000000000000000000 : ℝ)*base92 + (1930771/400000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1506_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32580013/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9199/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (331/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10397/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (801/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1506_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1506_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32580013/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10397/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (801/5000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1506_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1506_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1506_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32580013/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10397/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (801/5000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1506_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
