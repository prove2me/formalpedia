-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1157_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:38:36.988426+00:00
-- url     : https://prove2.me/submissions/87cdd6b6-f822-4f3b-ab53-f8868ee48cd9

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
theorem support_rectangle_w1157_s3_0 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-4211123/19531250 : ℝ)*x 0 + (2713825749/5000000000 : ℝ)*x 1 + (654183977/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4211123/19531250 : ℝ)^4175 ≤ (6547806179251/50000000000000 : ℝ)^3151 := by
    have hnat : (4211123 : ℕ)^4175*50000000000000^3151 ≤ 6547806179251^3151*19531250^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4211123 19531250 6547806179251 50000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2713825749/5000000000 : ℝ)^4175 ≤ (22250366079977/50000000000000 : ℝ)^3151 := by
    have hnat : (2713825749 : ℕ)^4175*50000000000000^3151 ≤ 22250366079977^3151*5000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713825749 5000000000 22250366079977 50000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (654183977/1250000000 : ℝ)^4175 ≤ (42403655468547/100000000000000 : ℝ)^3151 := by
    have hnat : (654183977 : ℕ)^4175*100000000000000^3151 ≤ 42403655468547^3151*1250000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654183977 1250000000 42403655468547 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4211123/19531250 : ℝ), (2713825749/5000000000 : ℝ), (654183977/1250000000 : ℝ)] ![(6547806179251/50000000000000 : ℝ), (22250366079977/50000000000000 : ℝ), (42403655468547/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4211123/19531250 : ℝ)|^4175 ≤ (6547806179251/50000000000000 : ℝ)^3151
        have hw : |(-4211123/19531250 : ℝ)|=(4211123/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2713825749/5000000000 : ℝ)|^4175 ≤ (22250366079977/50000000000000 : ℝ)^3151
        have hw : |(2713825749/5000000000 : ℝ)|=(2713825749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(654183977/1250000000 : ℝ)|^4175 ≤ (42403655468547/100000000000000 : ℝ)^3151
        have hw : |(654183977/1250000000 : ℝ)|=(654183977/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s3_1 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676717683/5000000000 : ℝ)*x 0 + (-2255320849/10000000000 : ℝ)*x 1 + (5233471627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676717683/5000000000 : ℝ)^4175 ≤ (43696294106433/100000000000000 : ℝ)^3151 := by
    have hnat : (2676717683 : ℕ)^4175*100000000000000^3151 ≤ 43696294106433^3151*5000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676717683 5000000000 43696294106433 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2255320849/10000000000 : ℝ)^4175 ≤ (13900052430263/100000000000000 : ℝ)^3151 := by
    have hnat : (2255320849 : ℕ)^4175*100000000000000^3151 ≤ 13900052430263^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2255320849 10000000000 13900052430263 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5233471627/10000000000 : ℝ)^4175 ≤ (42403653439541/100000000000000 : ℝ)^3151 := by
    have hnat : (5233471627 : ℕ)^4175*100000000000000^3151 ≤ 42403653439541^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5233471627 10000000000 42403653439541 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676717683/5000000000 : ℝ), (-2255320849/10000000000 : ℝ), (5233471627/10000000000 : ℝ)] ![(43696294106433/100000000000000 : ℝ), (13900052430263/100000000000000 : ℝ), (42403653439541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676717683/5000000000 : ℝ)|^4175 ≤ (43696294106433/100000000000000 : ℝ)^3151
        have hw : |(2676717683/5000000000 : ℝ)|=(2676717683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2255320849/10000000000 : ℝ)|^4175 ≤ (13900052430263/100000000000000 : ℝ)^3151
        have hw : |(-2255320849/10000000000 : ℝ)|=(2255320849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5233471627/10000000000 : ℝ)|^4175 ≤ (42403653439541/100000000000000 : ℝ)^3151
        have hw : |(5233471627/10000000000 : ℝ)|=(5233471627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s3_2 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353435447/10000000000 : ℝ)*x 0 + (5233471667/10000000000 : ℝ)*x 1 + (-225532069/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353435447/10000000000 : ℝ)^4175 ≤ (8739258996487/20000000000000 : ℝ)^3151 := by
    have hnat : (5353435447 : ℕ)^4175*20000000000000^3151 ≤ 8739258996487^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353435447 10000000000 8739258996487 20000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5233471667/10000000000 : ℝ)^4175 ≤ (265022836681/625000000000 : ℝ)^3151 := by
    have hnat : (5233471667 : ℕ)^4175*625000000000^3151 ≤ 265022836681^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5233471667 10000000000 265022836681 625000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (225532069/1000000000 : ℝ)^4175 ≤ (13900051131849/100000000000000 : ℝ)^3151 := by
    have hnat : (225532069 : ℕ)^4175*100000000000000^3151 ≤ 13900051131849^3151*1000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225532069 1000000000 13900051131849 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353435447/10000000000 : ℝ), (5233471667/10000000000 : ℝ), (-225532069/1000000000 : ℝ)] ![(8739258996487/20000000000000 : ℝ), (265022836681/625000000000 : ℝ), (13900051131849/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353435447/10000000000 : ℝ)|^4175 ≤ (8739258996487/20000000000000 : ℝ)^3151
        have hw : |(5353435447/10000000000 : ℝ)|=(5353435447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5233471667/10000000000 : ℝ)|^4175 ≤ (265022836681/625000000000 : ℝ)^3151
        have hw : |(5233471667/10000000000 : ℝ)|=(5233471667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-225532069/1000000000 : ℝ)|^4175 ≤ (13900051131849/100000000000000 : ℝ)^3151
        have hw : |(-225532069/1000000000 : ℝ)|=(225532069/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s3_3 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4360400653/10000000000 : ℝ)*x 0 + (2085468089/5000000000 : ℝ)*x 1 + (911677697/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4360400653/10000000000 : ℝ)^4175 ≤ (33295156048479/100000000000000 : ℝ)^3151 := by
    have hnat : (4360400653 : ℕ)^4175*100000000000000^3151 ≤ 33295156048479^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4360400653 10000000000 33295156048479 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2085468089/5000000000 : ℝ)^4175 ≤ (31391963854751/100000000000000 : ℝ)^3151 := by
    have hnat : (2085468089 : ℕ)^4175*100000000000000^3151 ≤ 31391963854751^3151*5000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085468089 5000000000 31391963854751 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (911677697/2000000000 : ℝ)^4175 ≤ (35312880080517/100000000000000 : ℝ)^3151 := by
    have hnat : (911677697 : ℕ)^4175*100000000000000^3151 ≤ 35312880080517^3151*2000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      911677697 2000000000 35312880080517 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4360400653/10000000000 : ℝ), (2085468089/5000000000 : ℝ), (911677697/2000000000 : ℝ)] ![(33295156048479/100000000000000 : ℝ), (31391963854751/100000000000000 : ℝ), (35312880080517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4360400653/10000000000 : ℝ)|^4175 ≤ (33295156048479/100000000000000 : ℝ)^3151
        have hw : |(4360400653/10000000000 : ℝ)|=(4360400653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2085468089/5000000000 : ℝ)|^4175 ≤ (31391963854751/100000000000000 : ℝ)^3151
        have hw : |(2085468089/5000000000 : ℝ)|=(2085468089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(911677697/2000000000 : ℝ)|^4175 ≤ (35312880080517/100000000000000 : ℝ)^3151
        have hw : |(911677697/2000000000 : ℝ)|=(911677697/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s3_4 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-431222463/2000000000 : ℝ)*x 0 + (654277167/1250000000 : ℝ)*x 1 + (2713450937/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (431222463/2000000000 : ℝ)^4175 ≤ (6547875947949/50000000000000 : ℝ)^3151 := by
    have hnat : (431222463 : ℕ)^4175*50000000000000^3151 ≤ 6547875947949^3151*2000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431222463 2000000000 6547875947949 50000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (654277167/1250000000 : ℝ)^4175 ≤ (42411659169159/100000000000000 : ℝ)^3151 := by
    have hnat : (654277167 : ℕ)^4175*100000000000000^3151 ≤ 42411659169159^3151*1250000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654277167 1250000000 42411659169159 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2713450937/5000000000 : ℝ)^4175 ≤ (44492588924083/100000000000000 : ℝ)^3151 := by
    have hnat : (2713450937 : ℕ)^4175*100000000000000^3151 ≤ 44492588924083^3151*5000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713450937 5000000000 44492588924083 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-431222463/2000000000 : ℝ), (654277167/1250000000 : ℝ), (2713450937/5000000000 : ℝ)] ![(6547875947949/50000000000000 : ℝ), (42411659169159/100000000000000 : ℝ), (44492588924083/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-431222463/2000000000 : ℝ)|^4175 ≤ (6547875947949/50000000000000 : ℝ)^3151
        have hw : |(-431222463/2000000000 : ℝ)|=(431222463/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(654277167/1250000000 : ℝ)|^4175 ≤ (42411659169159/100000000000000 : ℝ)^3151
        have hw : |(654277167/1250000000 : ℝ)|=(654277167/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2713450937/5000000000 : ℝ)|^4175 ≤ (44492588924083/100000000000000 : ℝ)^3151
        have hw : |(2713450937/5000000000 : ℝ)|=(2713450937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s3_5 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652093519/5000000000 : ℝ)*x 0 + (-1030945569/5000000000 : ℝ)*x 1 + (271345083/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652093519/5000000000 : ℝ)^4175 ≤ (1348889971663/3125000000000 : ℝ)^3151 := by
    have hnat : (2652093519 : ℕ)^4175*3125000000000^3151 ≤ 1348889971663^3151*5000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652093519 5000000000 1348889971663 3125000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1030945569/5000000000 : ℝ)^4175 ≤ (6171467142529/50000000000000 : ℝ)^3151 := by
    have hnat : (1030945569 : ℕ)^4175*50000000000000^3151 ≤ 6171467142529^3151*5000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030945569 5000000000 6171467142529 50000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (271345083/500000000 : ℝ)^4175 ≤ (44492586599433/100000000000000 : ℝ)^3151 := by
    have hnat : (271345083 : ℕ)^4175*100000000000000^3151 ≤ 44492586599433^3151*500000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271345083 500000000 44492586599433 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652093519/5000000000 : ℝ), (-1030945569/5000000000 : ℝ), (271345083/500000000 : ℝ)] ![(1348889971663/3125000000000 : ℝ), (6171467142529/50000000000000 : ℝ), (44492586599433/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652093519/5000000000 : ℝ)|^4175 ≤ (1348889971663/3125000000000 : ℝ)^3151
        have hw : |(2652093519/5000000000 : ℝ)|=(2652093519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1030945569/5000000000 : ℝ)|^4175 ≤ (6171467142529/50000000000000 : ℝ)^3151
        have hw : |(-1030945569/5000000000 : ℝ)|=(1030945569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(271345083/500000000 : ℝ)|^4175 ≤ (44492586599433/100000000000000 : ℝ)^3151
        have hw : |(271345083/500000000 : ℝ)|=(271345083/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s3_6 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5304187909/10000000000 : ℝ)*x 0 + (1356725243/2500000000 : ℝ)*x 1 + (-2061890897/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304187909/10000000000 : ℝ)^4175 ≤ (21582244242347/50000000000000 : ℝ)^3151 := by
    have hnat : (5304187909 : ℕ)^4175*50000000000000^3151 ≤ 21582244242347^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304187909 10000000000 21582244242347 50000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1356725243/2500000000 : ℝ)^4175 ≤ (44492579125793/100000000000000 : ℝ)^3151 := by
    have hnat : (1356725243 : ℕ)^4175*100000000000000^3151 ≤ 44492579125793^3151*2500000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356725243 2500000000 44492579125793 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2061890897/10000000000 : ℝ)^4175 ≤ (12342932373543/100000000000000 : ℝ)^3151 := by
    have hnat : (2061890897 : ℕ)^4175*100000000000000^3151 ≤ 12342932373543^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2061890897 10000000000 12342932373543 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304187909/10000000000 : ℝ), (1356725243/2500000000 : ℝ), (-2061890897/10000000000 : ℝ)] ![(21582244242347/50000000000000 : ℝ), (44492579125793/100000000000000 : ℝ), (12342932373543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304187909/10000000000 : ℝ)|^4175 ≤ (21582244242347/50000000000000 : ℝ)^3151
        have hw : |(5304187909/10000000000 : ℝ)|=(5304187909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1356725243/2500000000 : ℝ)|^4175 ≤ (44492579125793/100000000000000 : ℝ)^3151
        have hw : |(1356725243/2500000000 : ℝ)|=(1356725243/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2061890897/10000000000 : ℝ)|^4175 ≤ (12342932373543/100000000000000 : ℝ)^3151
        have hw : |(-2061890897/10000000000 : ℝ)|=(2061890897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s3_7 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4360435029/10000000000 : ℝ)*x 0 + (1139225257/2500000000 : ℝ)*x 1 + (1043108039/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4360435029/10000000000 : ℝ)^4175 ≤ (33295503839713/100000000000000 : ℝ)^3151 := by
    have hnat : (4360435029 : ℕ)^4175*100000000000000^3151 ≤ 33295503839713^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4360435029 10000000000 33295503839713 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1139225257/2500000000 : ℝ)^4175 ≤ (35297613166071/100000000000000 : ℝ)^3151 := by
    have hnat : (1139225257 : ℕ)^4175*100000000000000^3151 ≤ 35297613166071^3151*2500000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1139225257 2500000000 35297613166071 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043108039/2500000000 : ℝ)^4175 ≤ (6281376597183/20000000000000 : ℝ)^3151 := by
    have hnat : (1043108039 : ℕ)^4175*20000000000000^3151 ≤ 6281376597183^3151*2500000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043108039 2500000000 6281376597183 20000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4360435029/10000000000 : ℝ), (1139225257/2500000000 : ℝ), (1043108039/2500000000 : ℝ)] ![(33295503839713/100000000000000 : ℝ), (35297613166071/100000000000000 : ℝ), (6281376597183/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4360435029/10000000000 : ℝ)|^4175 ≤ (33295503839713/100000000000000 : ℝ)^3151
        have hw : |(4360435029/10000000000 : ℝ)|=(4360435029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1139225257/2500000000 : ℝ)|^4175 ≤ (35297613166071/100000000000000 : ℝ)^3151
        have hw : |(1139225257/2500000000 : ℝ)|=(1139225257/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043108039/2500000000 : ℝ)|^4175 ≤ (6281376597183/20000000000000 : ℝ)^3151
        have hw : |(1043108039/2500000000 : ℝ)|=(1043108039/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1157_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149766461/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8229/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9137/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10679/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3697/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8229/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9137/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8229/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9137/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8229/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9137/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8229/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9137/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8229/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9137/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8229/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9137/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9137/100000 : ℝ) ^ (8349/2048 : ℝ) ≤ (5801623521245447/100000000000000000000 : ℝ) := by
    have hpowers : (9137/100000 : ℝ)^8349 ≤ (5801623521245447/100000000000000000000 : ℝ)^2048 := by
      have hnat : (9137 : ℕ)^8349*100000000000000000000^2048 ≤ 5801623521245447^2048*100000^8349 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9137 100000 5801623521245447 100000000000000000000 8349 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9137/100000 : ℝ)) (X := (5801623521245447/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8349 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (8229/50000 : ℝ) ^ (8349/2048 : ℝ) ≤ (63890395239352507/100000000000000000000 : ℝ) := by
    have hpowers : (8229/50000 : ℝ)^8349 ≤ (63890395239352507/100000000000000000000 : ℝ)^2048 := by
      have hnat : (8229 : ℕ)^8349*100000000000000000000^2048 ≤ 63890395239352507^2048*50000^8349 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8229 50000 63890395239352507 100000000000000000000 8349 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8229/50000 : ℝ)) (X := (63890395239352507/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8349 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005801623521245447/50000000000000000000 : ℝ) ≤ (80002276910723/80000000000000 : ℝ) ^ (8349/2048 : ℝ) := by
    have hpowers : (50005801623521245447/50000000000000000000 : ℝ)^2048 ≤ (80002276910723/80000000000000 : ℝ)^8349 := by
      have hnat : (50005801623521245447 : ℕ)^2048*80000000000000^8349 ≤ 80002276910723^8349*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005801623521245447 50000000000000000000 80002276910723 80000000000000 2048 8349 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (80002276910723/80000000000000 : ℝ)) (X := (50005801623521245447/50000000000000000000 : ℝ)) (by norm_num) 8349 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50034846009380298977/50000000000000000000 : ℝ) ≤ (2000341817545367/2000000000000000 : ℝ) ^ (8349/2048 : ℝ) := by
    have hpowers : (50034846009380298977/50000000000000000000 : ℝ)^2048 ≤ (2000341817545367/2000000000000000 : ℝ)^8349 := by
      have hnat : (50034846009380298977 : ℕ)^2048*2000000000000000^8349 ≤ 2000341817545367^8349*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034846009380298977 50000000000000000000 2000341817545367 2000000000000000 2048 8349 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000341817545367/2000000000000000 : ℝ)) (X := (50034846009380298977/50000000000000000000 : ℝ)) (by norm_num) 8349 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50063890395239352507/50000000000000000000 : ℝ) ≤ (2000626712322659/2000000000000000 : ℝ) ^ (8349/2048 : ℝ) := by
    have hpowers : (50063890395239352507/50000000000000000000 : ℝ)^2048 ≤ (2000626712322659/2000000000000000 : ℝ)^8349 := by
      have hnat : (50063890395239352507 : ℕ)^2048*2000000000000000^8349 ≤ 2000626712322659^8349*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50063890395239352507 50000000000000000000 2000626712322659 2000000000000000 2048 8349 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000626712322659/2000000000000000 : ℝ)) (X := (50063890395239352507/50000000000000000000 : ℝ)) (by norm_num) 8349 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5801623521245447/100000000000000000000 : ℝ) ≤ ((14637210564424843067/14642000000000000000 : ℝ)+2*(71223694323/36605000000000 : ℝ)*(9137/100000 : ℝ))^(8349/2048 : ℝ) := by
    rw [show (14637210564424843067/14642000000000000000 : ℝ)+2*(71223694323/36605000000000 : ℝ)*(9137/100000 : ℝ)=(80002276910723/80000000000000 : ℝ) by norm_num, show 1+2*(5801623521245447/100000000000000000000 : ℝ)=(50005801623521245447/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(63890395239352507/100000000000000000000 : ℝ)+(5801623521245447/100000000000000000000 : ℝ) ≤ ((14637210564424843067/14642000000000000000 : ℝ)+(71223694323/36605000000000 : ℝ)*((8229/50000 : ℝ)+(9137/100000 : ℝ)))^(8349/2048 : ℝ) := by
    rw [show (14637210564424843067/14642000000000000000 : ℝ)+(71223694323/36605000000000 : ℝ)*((8229/50000 : ℝ)+(9137/100000 : ℝ))=(2000341817545367/2000000000000000 : ℝ) by norm_num, show 1+(63890395239352507/100000000000000000000 : ℝ)+(5801623521245447/100000000000000000000 : ℝ)=(50034846009380298977/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(63890395239352507/100000000000000000000 : ℝ) ≤ ((14637210564424843067/14642000000000000000 : ℝ)+2*(71223694323/36605000000000 : ℝ)*(8229/50000 : ℝ))^(8349/2048 : ℝ) := by
    rw [show (14637210564424843067/14642000000000000000 : ℝ)+2*(71223694323/36605000000000 : ℝ)*(8229/50000 : ℝ)=(2000626712322659/2000000000000000 : ℝ) by norm_num, show 1+2*(63890395239352507/100000000000000000000 : ℝ)=(50063890395239352507/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14637210564424843067/14642000000000000000 : ℝ)*(X 1 0+X 2 0)+(71223694323/36605000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8349/2048 : ℝ)) (lo := (9137/100000 : ℝ)) (hi := (8229/50000 : ℝ)) (c := (14637210564424843067/14642000000000000000 : ℝ)) (alpha := (71223694323/36605000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14637210564424843067/14642000000000000000 : ℝ)*(X 0 1+X 2 1)+(71223694323/36605000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8349/2048 : ℝ)) (lo := (9137/100000 : ℝ)) (hi := (8229/50000 : ℝ)) (c := (14637210564424843067/14642000000000000000 : ℝ)) (alpha := (71223694323/36605000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14637210564424843067/14642000000000000000 : ℝ)*(X 0 2+X 1 2)+(71223694323/36605000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8349/2048 : ℝ)) (lo := (9137/100000 : ℝ)) (hi := (8229/50000 : ℝ)) (c := (14637210564424843067/14642000000000000000 : ℝ)) (alpha := (71223694323/36605000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-4211123/19531250 : ℝ)*X 0 0+(2713825749/5000000000 : ℝ)*X 0 1+(654183977/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676717683/5000000000 : ℝ)*X 1 0+(-2255320849/10000000000 : ℝ)*X 1 1+(5233471627/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353435447/10000000000 : ℝ)*X 2 0+(5233471667/10000000000 : ℝ)*X 2 1+(-225532069/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4360400653/10000000000 : ℝ)*X 0 0+(2085468089/5000000000 : ℝ)*X 0 1+(911677697/2000000000 : ℝ)*X 0 2+(4360400653/10000000000 : ℝ)*X 1 0+(2085468089/5000000000 : ℝ)*X 1 1+(911677697/2000000000 : ℝ)*X 1 2+(4360400653/10000000000 : ℝ)*X 2 0+(2085468089/5000000000 : ℝ)*X 2 1+(911677697/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-431222463/2000000000 : ℝ)*X 0 0+(654277167/1250000000 : ℝ)*X 0 1+(2713450937/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652093519/5000000000 : ℝ)*X 1 0+(-1030945569/5000000000 : ℝ)*X 1 1+(271345083/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5304187909/10000000000 : ℝ)*X 2 0+(1356725243/2500000000 : ℝ)*X 2 1+(-2061890897/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4360435029/10000000000 : ℝ)*X 0 0+(1139225257/2500000000 : ℝ)*X 0 1+(1043108039/2500000000 : ℝ)*X 0 2+(4360435029/10000000000 : ℝ)*X 1 0+(1139225257/2500000000 : ℝ)*X 1 1+(1043108039/2500000000 : ℝ)*X 1 2+(4360435029/10000000000 : ℝ)*X 2 0+(1139225257/2500000000 : ℝ)*X 2 1+(1043108039/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (236880855645563353411052217/45756250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (677091021/50000000000000 : ℝ)*(base19) + (4070751/312500000000 : ℝ)*(base23) + (34653407/50000000000000 : ℝ)*(lower2) + (15478593/20000000000000 : ℝ)*(upper3) + (41081019/25000000000000 : ℝ)*(upper5) + (483181103295817/12500000000000 : ℝ)*(major0) + (483181103295817/12500000000000 : ℝ)*(major1) + (3865448826366537/100000000000000 : ℝ)*(major2) + (5149888855779137/100000000000000 : ℝ)*(sp0) + (5149911838475983/100000000000000 : ℝ)*(sp1) + (1029982378003541/20000000000000 : ℝ)*(sp2) + (2580973729684521/100000000000000 : ℝ)*(sp3) + (3042109861/12500000000000 : ℝ)*(sp4) + (5278911653/50000000000000 : ℝ)*(sp7) + (1290492143753913/50000000000000 : ℝ)*(f.failure) + (205996527706321/4000000000000 : ℝ)*(f.sum) + (8982605582097/7321000000000000000000000000 : ℝ)*base66 + (1953548529997399261/183025000000000000000000000000000 : ℝ)*base68 + (7734852097168551021/1464200000000000000000000000000000 : ℝ)*base70 + (2098126193941524261/183025000000000000000000000000000 : ℝ)*base72 + (38766178409939/7321000000000000000000000000 : ℝ)*base73 + (11090520403976048979/1464200000000000000000000000000000 : ℝ)*base75 + (2187850855347599261/183025000000000000000000000000000 : ℝ)*base78 + (2075831560632574261/183025000000000000000000000000000 : ℝ)*base80 + (1262016120821/7321000000000000000000000000 : ℝ)*base81 + (4911893/5000000000000000000000 : ℝ)*base89 + (4911893/5000000000000000000000 : ℝ)*base91 + (45088107/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (46663725562885181105018667/9151250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (98944597/12500000000000 : ℝ)*(base19) + (438348483/25000000000000 : ℝ)*(base23) + (9499547/20000000000000 : ℝ)*(upper3) + (2303393/20000000000000 : ℝ)*(lower4) + (94034929/100000000000000 : ℝ)*(upper5) + (97385388179767/2500000000000 : ℝ)*(major0) + (97385388179767/2500000000000 : ℝ)*(major1) + (97385388179767/2500000000000 : ℝ)*(major2) + (164324953/1562500000000 : ℝ)*(sp1) + (19984392513/100000000000000 : ℝ)*(sp2) + (2594918821939713/50000000000000 : ℝ)*(sp4) + (5189826335525657/100000000000000 : ℝ)*(sp5) + (5189815906092981/100000000000000 : ℝ)*(sp6) + (650248310132447/25000000000000 : ℝ)*(sp7) + (650248310132447/25000000000000 : ℝ)*(f.failure) + (2594918821939713/50000000000000 : ℝ)*(f.sum) + (12990411029971/3660500000000000000000000000 : ℝ)*base66 + (356246691819974611/36605000000000000000000000000000 : ℝ)*base68 + (374075378603434611/36605000000000000000000000000000 : ℝ)*base70 + (250181716302424611/36605000000000000000000000000000 : ℝ)*base72 + (2132756172043/732100000000000000000000000 : ℝ)*base74 + (434624526987165389/36605000000000000000000000000000 : ℝ)*base75 + (334904794185634611/36605000000000000000000000000000 : ℝ)*base78 + (445591354660009611/36605000000000000000000000000000 : ℝ)*base80 + (15571548543761/7321000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (28460067/2500000000000000000000 : ℝ)*base89 + (28460067/2500000000000000000000 : ℝ)*base91 + (28460067/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1157_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149766461/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8229/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9137/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10679/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3697/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1157_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1157_s4_0 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2158976693/10000000000 : ℝ)*x 0 + (135029551/250000000 : ℝ)*x 1 + (5258055849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2158976693/10000000000 : ℝ)^4175 ≤ (409962758711/3125000000000 : ℝ)^3151 := by
    have hnat : (2158976693 : ℕ)^4175*3125000000000^3151 ≤ 409962758711^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158976693 10000000000 409962758711 3125000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (135029551/250000000 : ℝ)^4175 ≤ (11053353401991/25000000000000 : ℝ)^3151 := by
    have hnat : (135029551 : ℕ)^4175*25000000000000^3151 ≤ 11053353401991^3151*250000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135029551 250000000 11053353401991 25000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5258055849/10000000000 : ℝ)^4175 ≤ (8533555621459/20000000000000 : ℝ)^3151 := by
    have hnat : (5258055849 : ℕ)^4175*20000000000000^3151 ≤ 8533555621459^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258055849 10000000000 8533555621459 20000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2158976693/10000000000 : ℝ), (135029551/250000000 : ℝ), (5258055849/10000000000 : ℝ)] ![(409962758711/3125000000000 : ℝ), (11053353401991/25000000000000 : ℝ), (8533555621459/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2158976693/10000000000 : ℝ)|^4175 ≤ (409962758711/3125000000000 : ℝ)^3151
        have hw : |(-2158976693/10000000000 : ℝ)|=(2158976693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(135029551/250000000 : ℝ)|^4175 ≤ (11053353401991/25000000000000 : ℝ)^3151
        have hw : |(135029551/250000000 : ℝ)|=(135029551/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5258055849/10000000000 : ℝ)|^4175 ≤ (8533555621459/20000000000000 : ℝ)^3151
        have hw : |(5258055849/10000000000 : ℝ)|=(5258055849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s4_1 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346816123/10000000000 : ℝ)*x 0 + (-111585043/500000000 : ℝ)*x 1 + (5258056021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346816123/10000000000 : ℝ)^4175 ≤ (43624722435347/100000000000000 : ℝ)^3151 := by
    have hnat : (5346816123 : ℕ)^4175*100000000000000^3151 ≤ 43624722435347^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346816123 10000000000 43624722435347 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (111585043/500000000 : ℝ)^4175 ≤ (6853748796381/50000000000000 : ℝ)^3151 := by
    have hnat : (111585043 : ℕ)^4175*50000000000000^3151 ≤ 6853748796381^3151*500000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111585043 500000000 6853748796381 50000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5258056021/10000000000 : ℝ)^4175 ≤ (10666944989153/25000000000000 : ℝ)^3151 := by
    have hnat : (5258056021 : ℕ)^4175*25000000000000^3151 ≤ 10666944989153^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258056021 10000000000 10666944989153 25000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346816123/10000000000 : ℝ), (-111585043/500000000 : ℝ), (5258056021/10000000000 : ℝ)] ![(43624722435347/100000000000000 : ℝ), (6853748796381/50000000000000 : ℝ), (10666944989153/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346816123/10000000000 : ℝ)|^4175 ≤ (43624722435347/100000000000000 : ℝ)^3151
        have hw : |(5346816123/10000000000 : ℝ)|=(5346816123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-111585043/500000000 : ℝ)|^4175 ≤ (6853748796381/50000000000000 : ℝ)^3151
        have hw : |(-111585043/500000000 : ℝ)|=(111585043/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5258056021/10000000000 : ℝ)|^4175 ≤ (10666944989153/25000000000000 : ℝ)^3151
        have hw : |(5258056021/10000000000 : ℝ)|=(5258056021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s4_2 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346816119/10000000000 : ℝ)*x 0 + (2629028099/5000000000 : ℝ)*x 1 + (-2231700631/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346816119/10000000000 : ℝ)^4175 ≤ (8724944478421/20000000000000 : ℝ)^3151 := by
    have hnat : (5346816119 : ℕ)^4175*20000000000000^3151 ≤ 8724944478421^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346816119 10000000000 8724944478421 20000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2629028099/5000000000 : ℝ)^4175 ≤ (5333472732461/12500000000000 : ℝ)^3151 := by
    have hnat : (2629028099 : ℕ)^4175*12500000000000^3151 ≤ 5333472732461^3151*5000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629028099 5000000000 5333472732461 12500000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2231700631/10000000000 : ℝ)^4175 ≤ (6853747864553/50000000000000 : ℝ)^3151 := by
    have hnat : (2231700631 : ℕ)^4175*50000000000000^3151 ≤ 6853747864553^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2231700631 10000000000 6853747864553 50000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346816119/10000000000 : ℝ), (2629028099/5000000000 : ℝ), (-2231700631/10000000000 : ℝ)] ![(8724944478421/20000000000000 : ℝ), (5333472732461/12500000000000 : ℝ), (6853747864553/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346816119/10000000000 : ℝ)|^4175 ≤ (8724944478421/20000000000000 : ℝ)^3151
        have hw : |(5346816119/10000000000 : ℝ)|=(5346816119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2629028099/5000000000 : ℝ)|^4175 ≤ (5333472732461/12500000000000 : ℝ)^3151
        have hw : |(2629028099/5000000000 : ℝ)|=(2629028099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2231700631/10000000000 : ℝ)|^4175 ≤ (6853747864553/50000000000000 : ℝ)^3151
        have hw : |(-2231700631/10000000000 : ℝ)|=(2231700631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s4_3 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1090530817/2500000000 : ℝ)*x 0 + (4221647709/10000000000 : ℝ)*x 1 + (4507231289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1090530817/2500000000 : ℝ)^4175 ≤ (33312585303921/100000000000000 : ℝ)^3151 := by
    have hnat : (1090530817 : ℕ)^4175*100000000000000^3151 ≤ 33312585303921^3151*2500000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090530817 2500000000 33312585303921 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4221647709/10000000000 : ℝ)^4175 ≤ (31898668104383/100000000000000 : ℝ)^3151 := by
    have hnat : (4221647709 : ℕ)^4175*100000000000000^3151 ≤ 31898668104383^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4221647709 10000000000 31898668104383 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4507231289/10000000000 : ℝ)^4175 ≤ (34788746577227/100000000000000 : ℝ)^3151 := by
    have hnat : (4507231289 : ℕ)^4175*100000000000000^3151 ≤ 34788746577227^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4507231289 10000000000 34788746577227 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1090530817/2500000000 : ℝ), (4221647709/10000000000 : ℝ), (4507231289/10000000000 : ℝ)] ![(33312585303921/100000000000000 : ℝ), (31898668104383/100000000000000 : ℝ), (34788746577227/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1090530817/2500000000 : ℝ)|^4175 ≤ (33312585303921/100000000000000 : ℝ)^3151
        have hw : |(1090530817/2500000000 : ℝ)|=(1090530817/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4221647709/10000000000 : ℝ)|^4175 ≤ (31898668104383/100000000000000 : ℝ)^3151
        have hw : |(4221647709/10000000000 : ℝ)|=(4221647709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4507231289/10000000000 : ℝ)|^4175 ≤ (34788746577227/100000000000000 : ℝ)^3151
        have hw : |(4507231289/10000000000 : ℝ)|=(4507231289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s4_4 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-53974597/250000000 : ℝ)*x 0 + (2629230863/5000000000 : ℝ)*x 1 + (675096793/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53974597/250000000 : ℝ)^4175 ≤ (1639858267743/12500000000000 : ℝ)^3151 := by
    have hnat : (53974597 : ℕ)^4175*12500000000000^3151 ≤ 1639858267743^3151*250000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53974597 250000000 1639858267743 12500000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2629230863/5000000000 : ℝ)^4175 ≤ (5334017760971/12500000000000 : ℝ)^3151 := by
    have hnat : (2629230863 : ℕ)^4175*12500000000000^3151 ≤ 5334017760971^3151*5000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629230863 5000000000 5334017760971 12500000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (675096793/1250000000 : ℝ)^4175 ≤ (44208991753623/100000000000000 : ℝ)^3151 := by
    have hnat : (675096793 : ℕ)^4175*100000000000000^3151 ≤ 44208991753623^3151*1250000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675096793 1250000000 44208991753623 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-53974597/250000000 : ℝ), (2629230863/5000000000 : ℝ), (675096793/1250000000 : ℝ)] ![(1639858267743/12500000000000 : ℝ), (5334017760971/12500000000000 : ℝ), (44208991753623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-53974597/250000000 : ℝ)|^4175 ≤ (1639858267743/12500000000000 : ℝ)^3151
        have hw : |(-53974597/250000000 : ℝ)|=(53974597/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2629230863/5000000000 : ℝ)|^4175 ≤ (5334017760971/12500000000000 : ℝ)^3151
        have hw : |(2629230863/5000000000 : ℝ)|=(2629230863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(675096793/1250000000 : ℝ)|^4175 ≤ (44208991753623/100000000000000 : ℝ)^3151
        have hw : |(675096793/1250000000 : ℝ)|=(675096793/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s4_5 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5310516777/10000000000 : ℝ)*x 0 + (-2088982183/10000000000 : ℝ)*x 1 + (5400774261/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310516777/10000000000 : ℝ)^4175 ≤ (864654843009/2000000000000 : ℝ)^3151 := by
    have hnat : (5310516777 : ℕ)^4175*2000000000000^3151 ≤ 864654843009^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310516777 10000000000 864654843009 2000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2088982183/10000000000 : ℝ)^4175 ≤ (1569783373653/12500000000000 : ℝ)^3151 := by
    have hnat : (2088982183 : ℕ)^4175*12500000000000^3151 ≤ 1569783373653^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2088982183 10000000000 1569783373653 12500000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5400774261/10000000000 : ℝ)^4175 ≤ (44208990853419/100000000000000 : ℝ)^3151 := by
    have hnat : (5400774261 : ℕ)^4175*100000000000000^3151 ≤ 44208990853419^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400774261 10000000000 44208990853419 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310516777/10000000000 : ℝ), (-2088982183/10000000000 : ℝ), (5400774261/10000000000 : ℝ)] ![(864654843009/2000000000000 : ℝ), (1569783373653/12500000000000 : ℝ), (44208990853419/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310516777/10000000000 : ℝ)|^4175 ≤ (864654843009/2000000000000 : ℝ)^3151
        have hw : |(5310516777/10000000000 : ℝ)|=(5310516777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2088982183/10000000000 : ℝ)|^4175 ≤ (1569783373653/12500000000000 : ℝ)^3151
        have hw : |(-2088982183/10000000000 : ℝ)|=(2088982183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5400774261/10000000000 : ℝ)|^4175 ≤ (44208990853419/100000000000000 : ℝ)^3151
        have hw : |(5400774261/10000000000 : ℝ)|=(5400774261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s4_6 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5310516609/10000000000 : ℝ)*x 0 + (5400774279/10000000000 : ℝ)*x 1 + (-1044491193/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310516609/10000000000 : ℝ)^4175 ≤ (43232740338303/100000000000000 : ℝ)^3151 := by
    have hnat : (5310516609 : ℕ)^4175*100000000000000^3151 ≤ 43232740338303^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310516609 10000000000 43232740338303 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5400774279/10000000000 : ℝ)^4175 ≤ (11052247762161/25000000000000 : ℝ)^3151 := by
    have hnat : (5400774279 : ℕ)^4175*25000000000000^3151 ≤ 11052247762161^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400774279 10000000000 11052247762161 25000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1044491193/5000000000 : ℝ)^4175 ≤ (12558268606183/100000000000000 : ℝ)^3151 := by
    have hnat : (1044491193 : ℕ)^4175*100000000000000^3151 ≤ 12558268606183^3151*5000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044491193 5000000000 12558268606183 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310516609/10000000000 : ℝ), (5400774279/10000000000 : ℝ), (-1044491193/5000000000 : ℝ)] ![(43232740338303/100000000000000 : ℝ), (11052247762161/25000000000000 : ℝ), (12558268606183/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310516609/10000000000 : ℝ)|^4175 ≤ (43232740338303/100000000000000 : ℝ)^3151
        have hw : |(5310516609/10000000000 : ℝ)|=(5310516609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5400774279/10000000000 : ℝ)|^4175 ≤ (11052247762161/25000000000000 : ℝ)^3151
        have hw : |(5400774279/10000000000 : ℝ)|=(5400774279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1044491193/5000000000 : ℝ)|^4175 ≤ (12558268606183/100000000000000 : ℝ)^3151
        have hw : |(-1044491193/5000000000 : ℝ)|=(1044491193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s4_7 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (872427349/2000000000 : ℝ)*x 0 + (4506421359/10000000000 : ℝ)*x 1 + (2111230691/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (872427349/2000000000 : ℝ)^4175 ≤ (133250886687/400000000000 : ℝ)^3151 := by
    have hnat : (872427349 : ℕ)^4175*400000000000^3151 ≤ 133250886687^3151*2000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      872427349 2000000000 133250886687 400000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4506421359/10000000000 : ℝ)^4175 ≤ (1086889496231/3125000000000 : ℝ)^3151 := by
    have hnat : (4506421359 : ℕ)^4175*3125000000000^3151 ≤ 1086889496231^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4506421359 10000000000 1086889496231 3125000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2111230691/5000000000 : ℝ)^4175 ≤ (31906814437081/100000000000000 : ℝ)^3151 := by
    have hnat : (2111230691 : ℕ)^4175*100000000000000^3151 ≤ 31906814437081^3151*5000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111230691 5000000000 31906814437081 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(872427349/2000000000 : ℝ), (4506421359/10000000000 : ℝ), (2111230691/5000000000 : ℝ)] ![(133250886687/400000000000 : ℝ), (1086889496231/3125000000000 : ℝ), (31906814437081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(872427349/2000000000 : ℝ)|^4175 ≤ (133250886687/400000000000 : ℝ)^3151
        have hw : |(872427349/2000000000 : ℝ)|=(872427349/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4506421359/10000000000 : ℝ)|^4175 ≤ (1086889496231/3125000000000 : ℝ)^3151
        have hw : |(4506421359/10000000000 : ℝ)|=(4506421359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2111230691/5000000000 : ℝ)|^4175 ≤ (31906814437081/100000000000000 : ℝ)^3151
        have hw : |(2111230691/5000000000 : ℝ)|=(2111230691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1157_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149766461/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3697/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10679/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2801/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2847/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3697/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10679/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3697/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10679/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3697/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10679/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3697/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10679/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3697/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10679/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3697/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10679/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10679/100000 : ℝ) ^ (8349/2048 : ℝ) ≤ (5477966264292703/50000000000000000000 : ℝ) := by
    have hpowers : (10679/100000 : ℝ)^8349 ≤ (5477966264292703/50000000000000000000 : ℝ)^2048 := by
      have hnat : (10679 : ℕ)^8349*50000000000000000000^2048 ≤ 5477966264292703^2048*100000^8349 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10679 100000 5477966264292703 50000000000000000000 8349 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10679/100000 : ℝ)) (X := (5477966264292703/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8349 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3697/25000 : ℝ) ^ (8349/2048 : ℝ) ≤ (5163128200636463/12500000000000000000 : ℝ) := by
    have hpowers : (3697/25000 : ℝ)^8349 ≤ (5163128200636463/12500000000000000000 : ℝ)^2048 := by
      have hnat : (3697 : ℕ)^8349*12500000000000000000^2048 ≤ 5163128200636463^2048*25000^8349 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3697 25000 5163128200636463 12500000000000000000 8349 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3697/25000 : ℝ)) (X := (5163128200636463/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8349 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005477966264292703/25000000000000000000 : ℝ) ≤ (10000537451067219/10000000000000000 : ℝ) ^ (8349/2048 : ℝ) := by
    have hpowers : (25005477966264292703/25000000000000000000 : ℝ)^2048 ≤ (10000537451067219/10000000000000000 : ℝ)^8349 := by
      have hnat : (25005477966264292703 : ℕ)^2048*10000000000000000^8349 ≤ 10000537451067219^8349*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005477966264292703 25000000000000000000 10000537451067219 10000000000000000 2048 8349 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000537451067219/10000000000000000 : ℝ)) (X := (25005477966264292703/25000000000000000000 : ℝ)) (by norm_num) 8349 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (10005226095813367711/10000000000000000000 : ℝ) ≤ (5000640851248963/5000000000000000 : ℝ) ^ (8349/2048 : ℝ) := by
    have hpowers : (10005226095813367711/10000000000000000000 : ℝ)^2048 ≤ (5000640851248963/5000000000000000 : ℝ)^8349 := by
      have hnat : (10005226095813367711 : ℕ)^2048*5000000000000000^8349 ≤ 5000640851248963^8349*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005226095813367711 10000000000000000000 5000640851248963 5000000000000000 2048 8349 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000640851248963/5000000000000000 : ℝ)) (X := (10005226095813367711/10000000000000000000 : ℝ)) (by norm_num) 8349 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (6255163128200636463/6250000000000000000 : ℝ) ≤ (10002025953928633/10000000000000000 : ℝ) ^ (8349/2048 : ℝ) := by
    have hpowers : (6255163128200636463/6250000000000000000 : ℝ)^2048 ≤ (10002025953928633/10000000000000000 : ℝ)^8349 := by
      have hnat : (6255163128200636463 : ℕ)^2048*10000000000000000^8349 ≤ 10002025953928633^8349*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6255163128200636463 6250000000000000000 10002025953928633 10000000000000000 2048 8349 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002025953928633/10000000000000000 : ℝ)) (X := (6255163128200636463/6250000000000000000 : ℝ)) (by norm_num) 8349 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5477966264292703/50000000000000000000 : ℝ) ≤ ((8215262532875632553/8218000000000000000 : ℝ)+2*(744251430707/410900000000000 : ℝ)*(10679/100000 : ℝ))^(8349/2048 : ℝ) := by
    rw [show (8215262532875632553/8218000000000000000 : ℝ)+2*(744251430707/410900000000000 : ℝ)*(10679/100000 : ℝ)=(10000537451067219/10000000000000000 : ℝ) by norm_num, show 1+2*(5477966264292703/50000000000000000000 : ℝ)=(25005477966264292703/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5163128200636463/12500000000000000000 : ℝ)+(5477966264292703/50000000000000000000 : ℝ) ≤ ((8215262532875632553/8218000000000000000 : ℝ)+(744251430707/410900000000000 : ℝ)*((3697/25000 : ℝ)+(10679/100000 : ℝ)))^(8349/2048 : ℝ) := by
    rw [show (8215262532875632553/8218000000000000000 : ℝ)+(744251430707/410900000000000 : ℝ)*((3697/25000 : ℝ)+(10679/100000 : ℝ))=(5000640851248963/5000000000000000 : ℝ) by norm_num, show 1+(5163128200636463/12500000000000000000 : ℝ)+(5477966264292703/50000000000000000000 : ℝ)=(10005226095813367711/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5163128200636463/12500000000000000000 : ℝ) ≤ ((8215262532875632553/8218000000000000000 : ℝ)+2*(744251430707/410900000000000 : ℝ)*(3697/25000 : ℝ))^(8349/2048 : ℝ) := by
    rw [show (8215262532875632553/8218000000000000000 : ℝ)+2*(744251430707/410900000000000 : ℝ)*(3697/25000 : ℝ)=(10002025953928633/10000000000000000 : ℝ) by norm_num, show 1+2*(5163128200636463/12500000000000000000 : ℝ)=(6255163128200636463/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8215262532875632553/8218000000000000000 : ℝ)*(X 1 0+X 2 0)+(744251430707/410900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8349/2048 : ℝ)) (lo := (10679/100000 : ℝ)) (hi := (3697/25000 : ℝ)) (c := (8215262532875632553/8218000000000000000 : ℝ)) (alpha := (744251430707/410900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8215262532875632553/8218000000000000000 : ℝ)*(X 0 1+X 2 1)+(744251430707/410900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8349/2048 : ℝ)) (lo := (10679/100000 : ℝ)) (hi := (3697/25000 : ℝ)) (c := (8215262532875632553/8218000000000000000 : ℝ)) (alpha := (744251430707/410900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8215262532875632553/8218000000000000000 : ℝ)*(X 0 2+X 1 2)+(744251430707/410900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8349/2048 : ℝ)) (lo := (10679/100000 : ℝ)) (hi := (3697/25000 : ℝ)) (c := (8215262532875632553/8218000000000000000 : ℝ)) (alpha := (744251430707/410900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2158976693/10000000000 : ℝ)*X 0 0+(135029551/250000000 : ℝ)*X 0 1+(5258055849/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346816123/10000000000 : ℝ)*X 1 0+(-111585043/500000000 : ℝ)*X 1 1+(5258056021/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346816119/10000000000 : ℝ)*X 2 0+(2629028099/5000000000 : ℝ)*X 2 1+(-2231700631/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1090530817/2500000000 : ℝ)*X 0 0+(4221647709/10000000000 : ℝ)*X 0 1+(4507231289/10000000000 : ℝ)*X 0 2+(1090530817/2500000000 : ℝ)*X 1 0+(4221647709/10000000000 : ℝ)*X 1 1+(4507231289/10000000000 : ℝ)*X 1 2+(1090530817/2500000000 : ℝ)*X 2 0+(4221647709/10000000000 : ℝ)*X 2 1+(4507231289/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-53974597/250000000 : ℝ)*X 0 0+(2629230863/5000000000 : ℝ)*X 0 1+(675096793/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5310516777/10000000000 : ℝ)*X 1 0+(-2088982183/10000000000 : ℝ)*X 1 1+(5400774261/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5310516609/10000000000 : ℝ)*X 2 0+(5400774279/10000000000 : ℝ)*X 2 1+(-1044491193/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((872427349/2000000000 : ℝ)*X 0 0+(4506421359/10000000000 : ℝ)*X 0 1+(2111230691/5000000000 : ℝ)*X 0 2+(872427349/2000000000 : ℝ)*X 1 0+(4506421359/10000000000 : ℝ)*X 1 1+(2111230691/5000000000 : ℝ)*X 1 2+(872427349/2000000000 : ℝ)*X 2 0+(4506421359/10000000000 : ℝ)*X 2 1+(2111230691/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1037102875170599968804572573/410900000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (58152911/10000000000000 : ℝ)*(base19) + (50214829/20000000000000 : ℝ)*(base23) + (543417/312500000000 : ℝ)*(lower2) + (59771907/100000000000000 : ℝ)*(upper3) + (9001277/6250000000000 : ℝ)*(upper5) + (5244249037000723/100000000000000 : ℝ)*(major0) + (5244249037000723/100000000000000 : ℝ)*(major1) + (1311062259250181/25000000000000 : ℝ)*(major2) + (3493428324506693/50000000000000 : ℝ)*(sp0) + (1397375924312769/20000000000000 : ℝ)*(sp1) + (6986879952018811/100000000000000 : ℝ)*(sp2) + (1750804887221323/50000000000000 : ℝ)*(sp3) + (23554079569/100000000000000 : ℝ)*(sp4) + (1001541651/12500000000000 : ℝ)*(sp7) + (700323557355171/20000000000000 : ℝ)*(f.failure) + (1746720050773239/25000000000000 : ℝ)*(f.sum) + (47287775624729/41090000000000000000000000000 : ℝ)*base65 + (7769861985415304181/821800000000000000000000000000000 : ℝ)*base68 + (2921083253609452907/205450000000000000000000000000000 : ℝ)*base70 + (10357207809879295819/821800000000000000000000000000000 : ℝ)*base71 + (20154314481711/41090000000000000000000000000 : ℝ)*base74 + (2820780158817202907/205450000000000000000000000000000 : ℝ)*base76 + (6361700364248044181/821800000000000000000000000000000 : ℝ)*base78 + (1919788088788644181/821800000000000000000000000000000 : ℝ)*base80 + (1542943564633/642031250000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (20719831/2000000000000000000000 : ℝ)*base89 + (20719831/2000000000000000000000 : ℝ)*base91 + (719831/2000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (942188916194145572627161947/102725000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1335453129/50000000000000 : ℝ)*(base19) + (1252915063/50000000000000 : ℝ)*(base23) + (81435393/100000000000000 : ℝ)*(upper2) + (73963331/50000000000000 : ℝ)*(upper3) + (8069291/2500000000000 : ℝ)*(upper5) + (1318550558189611/25000000000000 : ℝ)*(major0) + (1318550558189611/25000000000000 : ℝ)*(major1) + (1318550558189611/25000000000000 : ℝ)*(major2) + (71620914809/100000000000000 : ℝ)*(sp1) + (57557211151/100000000000000 : ℝ)*(sp2) + (7026786437404353/100000000000000 : ℝ)*(sp4) + (3513356072791643/50000000000000 : ℝ)*(sp5) + (1756681593590769/25000000000000 : ℝ)*(sp6) + (440202215297593/12500000000000 : ℝ)*(sp7) + (440202215297593/12500000000000 : ℝ)*(f.failure) + (7026786437404353/100000000000000 : ℝ)*(f.sum) + (11488206907777/5136250000000000000000000000 : ℝ)*base65 + (992316416800753117/205450000000000000000000000000000 : ℝ)*base68 + (1783410530800453117/205450000000000000000000000000000 : ℝ)*base70 + (2761875476861503117/205450000000000000000000000000000 : ℝ)*base72 + (898003040049/10272500000000000000000000000 : ℝ)*base73 + (2854790616156803117/205450000000000000000000000000000 : ℝ)*base76 + (1164135517167303117/205450000000000000000000000000000 : ℝ)*base78 + (7760269387491553117/205450000000000000000000000000000 : ℝ)*base80 + (14997594957813/20545000000000000000000000000 : ℝ)*base81 + (15428373/1250000000000000000000 : ℝ)*base89 + (15428373/1250000000000000000000 : ℝ)*base91 + (15428373/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1157_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149766461/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3697/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10679/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2801/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1157_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1157_s5_0 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-431915647/2000000000 : ℝ)*x 0 + (269726209/500000000 : ℝ)*x 1 + (5264319051/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (431915647/2000000000 : ℝ)^4175 ≤ (3280912891211/25000000000000 : ℝ)^3151 := by
    have hnat : (431915647 : ℕ)^4175*25000000000000^3151 ≤ 3280912891211^3151*2000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431915647 2000000000 3280912891211 25000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269726209/500000000 : ℝ)^4175 ≤ (44141216309331/100000000000000 : ℝ)^3151 := by
    have hnat : (269726209 : ℕ)^4175*100000000000000^3151 ≤ 44141216309331^3151*500000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269726209 500000000 44141216309331 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264319051/10000000000 : ℝ)^4175 ≤ (42735132101551/100000000000000 : ℝ)^3151 := by
    have hnat : (5264319051 : ℕ)^4175*100000000000000^3151 ≤ 42735132101551^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264319051 10000000000 42735132101551 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-431915647/2000000000 : ℝ), (269726209/500000000 : ℝ), (5264319051/10000000000 : ℝ)] ![(3280912891211/25000000000000 : ℝ), (44141216309331/100000000000000 : ℝ), (42735132101551/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-431915647/2000000000 : ℝ)|^4175 ≤ (3280912891211/25000000000000 : ℝ)^3151
        have hw : |(-431915647/2000000000 : ℝ)|=(431915647/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269726209/500000000 : ℝ)|^4175 ≤ (44141216309331/100000000000000 : ℝ)^3151
        have hw : |(269726209/500000000 : ℝ)|=(269726209/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264319051/10000000000 : ℝ)|^4175 ≤ (42735132101551/100000000000000 : ℝ)^3151
        have hw : |(5264319051/10000000000 : ℝ)|=(5264319051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s5_1 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069029017/2000000000 : ℝ)*x 0 + (-2225641923/10000000000 : ℝ)*x 1 + (1316079739/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069029017/2000000000 : ℝ)^4175 ≤ (43606658607991/100000000000000 : ℝ)^3151 := by
    have hnat : (1069029017 : ℕ)^4175*100000000000000^3151 ≤ 43606658607991^3151*2000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069029017 2000000000 43606658607991 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2225641923/10000000000 : ℝ)^4175 ≤ (6829105149983/50000000000000 : ℝ)^3151 := by
    have hnat : (2225641923 : ℕ)^4175*50000000000000^3151 ≤ 6829105149983^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2225641923 10000000000 6829105149983 50000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316079739/2500000000 : ℝ)^4175 ≤ (42735131079731/100000000000000 : ℝ)^3151 := by
    have hnat : (1316079739 : ℕ)^4175*100000000000000^3151 ≤ 42735131079731^3151*2500000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316079739 2500000000 42735131079731 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069029017/2000000000 : ℝ), (-2225641923/10000000000 : ℝ), (1316079739/2500000000 : ℝ)] ![(43606658607991/100000000000000 : ℝ), (6829105149983/50000000000000 : ℝ), (42735131079731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069029017/2000000000 : ℝ)|^4175 ≤ (43606658607991/100000000000000 : ℝ)^3151
        have hw : |(1069029017/2000000000 : ℝ)|=(1069029017/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2225641923/10000000000 : ℝ)|^4175 ≤ (6829105149983/50000000000000 : ℝ)^3151
        have hw : |(-2225641923/10000000000 : ℝ)|=(2225641923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316079739/2500000000 : ℝ)|^4175 ≤ (42735131079731/100000000000000 : ℝ)^3151
        have hw : |(1316079739/2500000000 : ℝ)|=(1316079739/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s5_2 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668143099/1250000000 : ℝ)*x 0 + (5264319099/10000000000 : ℝ)*x 1 + (-2225642123/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668143099/1250000000 : ℝ)^4175 ≤ (21803327720419/50000000000000 : ℝ)^3151 := by
    have hnat : (668143099 : ℕ)^4175*50000000000000^3151 ≤ 21803327720419^3151*1250000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668143099 1250000000 21803327720419 50000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264319099/10000000000 : ℝ)^4175 ≤ (42735132617839/100000000000000 : ℝ)^3151 := by
    have hnat : (5264319099 : ℕ)^4175*100000000000000^3151 ≤ 42735132617839^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264319099 10000000000 42735132617839 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2225642123/10000000000 : ℝ)^4175 ≤ (546328477047/4000000000000 : ℝ)^3151 := by
    have hnat : (2225642123 : ℕ)^4175*4000000000000^3151 ≤ 546328477047^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2225642123 10000000000 546328477047 4000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668143099/1250000000 : ℝ), (5264319099/10000000000 : ℝ), (-2225642123/10000000000 : ℝ)] ![(21803327720419/50000000000000 : ℝ), (42735132617839/100000000000000 : ℝ), (546328477047/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668143099/1250000000 : ℝ)|^4175 ≤ (21803327720419/50000000000000 : ℝ)^3151
        have hw : |(668143099/1250000000 : ℝ)|=(668143099/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264319099/10000000000 : ℝ)|^4175 ≤ (42735132617839/100000000000000 : ℝ)^3151
        have hw : |(5264319099/10000000000 : ℝ)|=(5264319099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2225642123/10000000000 : ℝ)|^4175 ≤ (546328477047/4000000000000 : ℝ)^3151
        have hw : |(-2225642123/10000000000 : ℝ)|=(2225642123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s5_3 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4362475847/10000000000 : ℝ)*x 0 + (846898587/2000000000 : ℝ)*x 1 + (112357383/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4362475847/10000000000 : ℝ)^4175 ≤ (33316152940651/100000000000000 : ℝ)^3151 := by
    have hnat : (4362475847 : ℕ)^4175*100000000000000^3151 ≤ 33316152940651^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4362475847 10000000000 33316152940651 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (846898587/2000000000 : ℝ)^4175 ≤ (3202733146889/10000000000000 : ℝ)^3151 := by
    have hnat : (846898587 : ℕ)^4175*10000000000000^3151 ≤ 3202733146889^3151*2000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      846898587 2000000000 3202733146889 10000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (112357383/250000000 : ℝ)^4175 ≤ (34656515581277/100000000000000 : ℝ)^3151 := by
    have hnat : (112357383 : ℕ)^4175*100000000000000^3151 ≤ 34656515581277^3151*250000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112357383 250000000 34656515581277 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4362475847/10000000000 : ℝ), (846898587/2000000000 : ℝ), (112357383/250000000 : ℝ)] ![(33316152940651/100000000000000 : ℝ), (3202733146889/10000000000000 : ℝ), (34656515581277/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4362475847/10000000000 : ℝ)|^4175 ≤ (33316152940651/100000000000000 : ℝ)^3151
        have hw : |(4362475847/10000000000 : ℝ)|=(4362475847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(846898587/2000000000 : ℝ)|^4175 ≤ (3202733146889/10000000000000 : ℝ)^3151
        have hw : |(846898587/2000000000 : ℝ)|=(846898587/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(112357383/250000000 : ℝ)|^4175 ≤ (34656515581277/100000000000000 : ℝ)^3151
        have hw : |(112357383/250000000 : ℝ)|=(112357383/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s5_4 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1079791823/5000000000 : ℝ)*x 0 + (5264654859/10000000000 : ℝ)*x 1 + (5394187003/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079791823/5000000000 : ℝ)^4175 ≤ (3280923783309/25000000000000 : ℝ)^3151 := by
    have hnat : (1079791823 : ℕ)^4175*25000000000000^3151 ≤ 3280923783309^3151*5000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079791823 5000000000 3280923783309 25000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264654859/10000000000 : ℝ)^4175 ≤ (4273874409093/10000000000000 : ℝ)^3151 := by
    have hnat : (5264654859 : ℕ)^4175*10000000000000^3151 ≤ 4273874409093^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264654859 10000000000 4273874409093 10000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394187003/10000000000 : ℝ)^4175 ≤ (22068780379533/50000000000000 : ℝ)^3151 := by
    have hnat : (5394187003 : ℕ)^4175*50000000000000^3151 ≤ 22068780379533^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394187003 10000000000 22068780379533 50000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1079791823/5000000000 : ℝ), (5264654859/10000000000 : ℝ), (5394187003/10000000000 : ℝ)] ![(3280923783309/25000000000000 : ℝ), (4273874409093/10000000000000 : ℝ), (22068780379533/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1079791823/5000000000 : ℝ)|^4175 ≤ (3280923783309/25000000000000 : ℝ)^3151
        have hw : |(-1079791823/5000000000 : ℝ)|=(1079791823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264654859/10000000000 : ℝ)|^4175 ≤ (4273874409093/10000000000000 : ℝ)^3151
        have hw : |(5264654859/10000000000 : ℝ)|=(5264654859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394187003/10000000000 : ℝ)|^4175 ≤ (22068780379533/50000000000000 : ℝ)^3151
        have hw : |(5394187003/10000000000 : ℝ)|=(5394187003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s5_5 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312120823/10000000000 : ℝ)*x 0 + (-2095774109/10000000000 : ℝ)*x 1 + (5394186879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312120823/10000000000 : ℝ)^4175 ≤ (43250045182243/100000000000000 : ℝ)^3151 := by
    have hnat : (5312120823 : ℕ)^4175*100000000000000^3151 ≤ 43250045182243^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312120823 10000000000 43250045182243 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2095774109/10000000000 : ℝ)^4175 ≤ (1576549423927/12500000000000 : ℝ)^3151 := by
    have hnat : (2095774109 : ℕ)^4175*12500000000000^3151 ≤ 1576549423927^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2095774109 10000000000 1576549423927 12500000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394186879/10000000000 : ℝ)^4175 ≤ (44137559414717/100000000000000 : ℝ)^3151 := by
    have hnat : (5394186879 : ℕ)^4175*100000000000000^3151 ≤ 44137559414717^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394186879 10000000000 44137559414717 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312120823/10000000000 : ℝ), (-2095774109/10000000000 : ℝ), (5394186879/10000000000 : ℝ)] ![(43250045182243/100000000000000 : ℝ), (1576549423927/12500000000000 : ℝ), (44137559414717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312120823/10000000000 : ℝ)|^4175 ≤ (43250045182243/100000000000000 : ℝ)^3151
        have hw : |(5312120823/10000000000 : ℝ)|=(5312120823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2095774109/10000000000 : ℝ)|^4175 ≤ (1576549423927/12500000000000 : ℝ)^3151
        have hw : |(-2095774109/10000000000 : ℝ)|=(2095774109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394186879/10000000000 : ℝ)|^4175 ≤ (44137559414717/100000000000000 : ℝ)^3151
        have hw : |(5394186879/10000000000 : ℝ)|=(5394186879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s5_6 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656060533/5000000000 : ℝ)*x 0 + (5394186707/10000000000 : ℝ)*x 1 + (-1047887007/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656060533/5000000000 : ℝ)^4175 ≤ (43250047803641/100000000000000 : ℝ)^3151 := by
    have hnat : (2656060533 : ℕ)^4175*100000000000000^3151 ≤ 43250047803641^3151*5000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656060533 5000000000 43250047803641 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394186707/10000000000 : ℝ)^4175 ≤ (1765502301999/4000000000000 : ℝ)^3151 := by
    have hnat : (5394186707 : ℕ)^4175*4000000000000^3151 ≤ 1765502301999^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394186707 10000000000 1765502301999 4000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1047887007/5000000000 : ℝ)^4175 ≤ (1576549329239/12500000000000 : ℝ)^3151 := by
    have hnat : (1047887007 : ℕ)^4175*12500000000000^3151 ≤ 1576549329239^3151*5000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047887007 5000000000 1576549329239 12500000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656060533/5000000000 : ℝ), (5394186707/10000000000 : ℝ), (-1047887007/5000000000 : ℝ)] ![(43250047803641/100000000000000 : ℝ), (1765502301999/4000000000000 : ℝ), (1576549329239/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656060533/5000000000 : ℝ)|^4175 ≤ (43250047803641/100000000000000 : ℝ)^3151
        have hw : |(2656060533/5000000000 : ℝ)|=(2656060533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394186707/10000000000 : ℝ)|^4175 ≤ (1765502301999/4000000000000 : ℝ)^3151
        have hw : |(5394186707/10000000000 : ℝ)|=(5394186707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1047887007/5000000000 : ℝ)|^4175 ≤ (1576549329239/12500000000000 : ℝ)^3151
        have hw : |(-1047887007/5000000000 : ℝ)|=(1047887007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s5_7 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2181243309/5000000000 : ℝ)*x 0 + (1123406163/2500000000 : ℝ)*x 1 + (4235165797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2181243309/5000000000 : ℝ)^4175 ≤ (33316261930509/100000000000000 : ℝ)^3151 := by
    have hnat : (2181243309 : ℕ)^4175*100000000000000^3151 ≤ 33316261930509^3151*5000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181243309 5000000000 33316261930509 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1123406163/2500000000 : ℝ)^4175 ≤ (17324831703343/50000000000000 : ℝ)^3151 := by
    have hnat : (1123406163 : ℕ)^4175*50000000000000^3151 ≤ 17324831703343^3151*2500000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123406163 2500000000 17324831703343 50000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4235165797/10000000000 : ℝ)^4175 ≤ (32034074647037/100000000000000 : ℝ)^3151 := by
    have hnat : (4235165797 : ℕ)^4175*100000000000000^3151 ≤ 32034074647037^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4235165797 10000000000 32034074647037 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2181243309/5000000000 : ℝ), (1123406163/2500000000 : ℝ), (4235165797/10000000000 : ℝ)] ![(33316261930509/100000000000000 : ℝ), (17324831703343/50000000000000 : ℝ), (32034074647037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2181243309/5000000000 : ℝ)|^4175 ≤ (33316261930509/100000000000000 : ℝ)^3151
        have hw : |(2181243309/5000000000 : ℝ)|=(2181243309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1123406163/2500000000 : ℝ)|^4175 ≤ (17324831703343/50000000000000 : ℝ)^3151
        have hw : |(1123406163/2500000000 : ℝ)|=(1123406163/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4235165797/10000000000 : ℝ)|^4175 ≤ (32034074647037/100000000000000 : ℝ)^3151
        have hw : |(4235165797/10000000000 : ℝ)|=(4235165797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1157_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149766461/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2801/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11337/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2819/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2801/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2801/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2801/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2801/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2801/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2801/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2801/25000 : ℝ) ^ (8349/2048 : ℝ) ≤ (1665433157719039/12500000000000000000 : ℝ) := by
    have hpowers : (2801/25000 : ℝ)^8349 ≤ (1665433157719039/12500000000000000000 : ℝ)^2048 := by
      have hnat : (2801 : ℕ)^8349*12500000000000000000^2048 ≤ 1665433157719039^2048*25000^8349 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2801 25000 1665433157719039 12500000000000000000 8349 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2801/25000 : ℝ)) (X := (1665433157719039/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8349 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2847/20000 : ℝ) ^ (8349/2048 : ℝ) ≤ (35361130206319577/100000000000000000000 : ℝ) := by
    have hpowers : (2847/20000 : ℝ)^8349 ≤ (35361130206319577/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2847 : ℕ)^8349*100000000000000000000^2048 ≤ 35361130206319577^2048*20000^8349 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2847 20000 35361130206319577 100000000000000000000 8349 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2847/20000 : ℝ)) (X := (35361130206319577/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8349 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251665433157719039/6250000000000000000 : ℝ) ≤ (10000653580394451/10000000000000000 : ℝ) ^ (8349/2048 : ℝ) := by
    have hpowers : (6251665433157719039/6250000000000000000 : ℝ)^2048 ≤ (10000653580394451/10000000000000000 : ℝ)^8349 := by
      have hnat : (6251665433157719039 : ℕ)^2048*10000000000000000^8349 ≤ 10000653580394451^8349*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251665433157719039 6250000000000000000 10000653580394451 10000000000000000 2048 8349 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000653580394451/10000000000000000 : ℝ)) (X := (6251665433157719039/6250000000000000000 : ℝ)) (by norm_num) 8349 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048684595468071889/100000000000000000000 : ℝ) ≤ (2500298502034897/2500000000000000 : ℝ) ^ (8349/2048 : ℝ) := by
    have hpowers : (100048684595468071889/100000000000000000000 : ℝ)^2048 ≤ (2500298502034897/2500000000000000 : ℝ)^8349 := by
      have hnat : (100048684595468071889 : ℕ)^2048*2500000000000000^8349 ≤ 2500298502034897^8349*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048684595468071889 100000000000000000000 2500298502034897 2500000000000000 2048 8349 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500298502034897/2500000000000000 : ℝ)) (X := (100048684595468071889/100000000000000000000 : ℝ)) (by norm_num) 8349 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035361130206319577/50000000000000000000 : ℝ) ≤ (400069377435389/400000000000000 : ℝ) ^ (8349/2048 : ℝ) := by
    have hpowers : (50035361130206319577/50000000000000000000 : ℝ)^2048 ≤ (400069377435389/400000000000000 : ℝ)^8349 := by
      have hnat : (50035361130206319577 : ℕ)^2048*400000000000000^8349 ≤ 400069377435389^8349*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035361130206319577 50000000000000000000 400069377435389 400000000000000 2048 8349 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400069377435389/400000000000000 : ℝ)) (X := (50035361130206319577/50000000000000000000 : ℝ)) (by norm_num) 8349 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1665433157719039/12500000000000000000 : ℝ) ≤ ((865710602778930031/866000000000000000 : ℝ)+2*(77203963591/43300000000000 : ℝ)*(2801/25000 : ℝ))^(8349/2048 : ℝ) := by
    rw [show (865710602778930031/866000000000000000 : ℝ)+2*(77203963591/43300000000000 : ℝ)*(2801/25000 : ℝ)=(10000653580394451/10000000000000000 : ℝ) by norm_num, show 1+2*(1665433157719039/12500000000000000000 : ℝ)=(6251665433157719039/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35361130206319577/100000000000000000000 : ℝ)+(1665433157719039/12500000000000000000 : ℝ) ≤ ((865710602778930031/866000000000000000 : ℝ)+(77203963591/43300000000000 : ℝ)*((2847/20000 : ℝ)+(2801/25000 : ℝ)))^(8349/2048 : ℝ) := by
    rw [show (865710602778930031/866000000000000000 : ℝ)+(77203963591/43300000000000 : ℝ)*((2847/20000 : ℝ)+(2801/25000 : ℝ))=(2500298502034897/2500000000000000 : ℝ) by norm_num, show 1+(35361130206319577/100000000000000000000 : ℝ)+(1665433157719039/12500000000000000000 : ℝ)=(100048684595468071889/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35361130206319577/100000000000000000000 : ℝ) ≤ ((865710602778930031/866000000000000000 : ℝ)+2*(77203963591/43300000000000 : ℝ)*(2847/20000 : ℝ))^(8349/2048 : ℝ) := by
    rw [show (865710602778930031/866000000000000000 : ℝ)+2*(77203963591/43300000000000 : ℝ)*(2847/20000 : ℝ)=(400069377435389/400000000000000 : ℝ) by norm_num, show 1+2*(35361130206319577/100000000000000000000 : ℝ)=(50035361130206319577/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (865710602778930031/866000000000000000 : ℝ)*(X 1 0+X 2 0)+(77203963591/43300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8349/2048 : ℝ)) (lo := (2801/25000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (865710602778930031/866000000000000000 : ℝ)) (alpha := (77203963591/43300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (865710602778930031/866000000000000000 : ℝ)*(X 0 1+X 2 1)+(77203963591/43300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8349/2048 : ℝ)) (lo := (2801/25000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (865710602778930031/866000000000000000 : ℝ)) (alpha := (77203963591/43300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (865710602778930031/866000000000000000 : ℝ)*(X 0 2+X 1 2)+(77203963591/43300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8349/2048 : ℝ)) (lo := (2801/25000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (865710602778930031/866000000000000000 : ℝ)) (alpha := (77203963591/43300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-431915647/2000000000 : ℝ)*X 0 0+(269726209/500000000 : ℝ)*X 0 1+(5264319051/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069029017/2000000000 : ℝ)*X 1 0+(-2225641923/10000000000 : ℝ)*X 1 1+(1316079739/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668143099/1250000000 : ℝ)*X 2 0+(5264319099/10000000000 : ℝ)*X 2 1+(-2225642123/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4362475847/10000000000 : ℝ)*X 0 0+(846898587/2000000000 : ℝ)*X 0 1+(112357383/250000000 : ℝ)*X 0 2+(4362475847/10000000000 : ℝ)*X 1 0+(846898587/2000000000 : ℝ)*X 1 1+(112357383/250000000 : ℝ)*X 1 2+(4362475847/10000000000 : ℝ)*X 2 0+(846898587/2000000000 : ℝ)*X 2 1+(112357383/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1079791823/5000000000 : ℝ)*X 0 0+(5264654859/10000000000 : ℝ)*X 0 1+(5394187003/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312120823/10000000000 : ℝ)*X 1 0+(-2095774109/10000000000 : ℝ)*X 1 1+(5394186879/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656060533/5000000000 : ℝ)*X 2 0+(5394186707/10000000000 : ℝ)*X 2 1+(-1047887007/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2181243309/5000000000 : ℝ)*X 0 0+(1123406163/2500000000 : ℝ)*X 0 1+(4235165797/10000000000 : ℝ)*X 0 2+(2181243309/5000000000 : ℝ)*X 1 0+(1123406163/2500000000 : ℝ)*X 1 1+(4235165797/10000000000 : ℝ)*X 1 2+(2181243309/5000000000 : ℝ)*X 2 0+(1123406163/2500000000 : ℝ)*X 2 1+(4235165797/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (180412794914159561882415657/21650000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1028138061/100000000000000 : ℝ)*(base19) + (207779393/25000000000000 : ℝ)*(base23) + (60871211/50000000000000 : ℝ)*(upper2) + (21262539/10000000000000 : ℝ)*(upper3) + (5764673394338167/100000000000000 : ℝ)*(major0) + (5764673394338167/100000000000000 : ℝ)*(major1) + (720584174292271/12500000000000 : ℝ)*(major2) + (7680222634404191/100000000000000 : ℝ)*(sp0) + (1920059276766997/25000000000000 : ℝ)*(sp1) + (7680236691868349/100000000000000 : ℝ)*(sp2) + (481136673547273/12500000000000 : ℝ)*(sp3) + (7750400929/50000000000000 : ℝ)*(sp4) + (612220129/100000000000000 : ℝ)*(sp6) + (3746830069/25000000000000 : ℝ)*(sp7) + (192455418784923/5000000000000 : ℝ)*(f.failure) + (7680238135206049/100000000000000 : ℝ)*(f.sum) + (357407030039/866000000000000000000000000 : ℝ)*base65 + (969537072351153177/86600000000000000000000000000000 : ℝ)*base67 + (156982565714557901/10825000000000000000000000000000 : ℝ)*base69 + (1154437857977953177/86600000000000000000000000000000 : ℝ)*base71 + (311943253091/866000000000000000000000000 : ℝ)*base74 + (31501479958832901/10825000000000000000000000000000 : ℝ)*base75 + (817051449528933177/86600000000000000000000000000000 : ℝ)*base77 + (891338452996133177/86600000000000000000000000000000 : ℝ)*base79 + (7357498465031/1082500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (2867503/500000000000000000000 : ℝ)*base89 + (2867503/500000000000000000000 : ℝ)*base91 + (2132497/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6042932567409662461569/1082500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1217439441/100000000000000 : ℝ)*(base19) + (959041901/50000000000000 : ℝ)*(base23) + (152448731/100000000000000 : ℝ)*(upper2) + (93715333/100000000000000 : ℝ)*(upper3) + (251788179/100000000000000 : ℝ)*(upper5) + (5794592129181147/100000000000000 : ℝ)*(major0) + (5794592129181147/100000000000000 : ℝ)*(major1) + (5794592129181147/100000000000000 : ℝ)*(major2) + (28589453799/100000000000000 : ℝ)*(sp1) + (7664684917/20000000000000 : ℝ)*(sp2) + (965012346343387/12500000000000 : ℝ)*(sp4) + (241252155120433/3125000000000 : ℝ)*(sp5) + (7720058529238709/100000000000000 : ℝ)*(sp6) + (967271325383917/25000000000000 : ℝ)*(sp7) + (967271325383917/25000000000000 : ℝ)*(f.failure) + (965012346343387/12500000000000 : ℝ)*(f.sum) + (12198622300443/2165000000000000000000000000 : ℝ)*base66 + (270673855014865557/86600000000000000000000000000000 : ℝ)*base67 + (563389250019534443/86600000000000000000000000000000 : ℝ)*base70 + (54157135643334443/86600000000000000000000000000000 : ℝ)*base72 + (3301437210349/1082500000000000000000000000 : ℝ)*base74 + (369511330112465557/86600000000000000000000000000000 : ℝ)*base75 + (555846845015934443/86600000000000000000000000000000 : ℝ)*base78 + (201155643182465557/86600000000000000000000000000000 : ℝ)*base79 + (4365304960549/1082500000000000000000000000 : ℝ)*base82 + (40407737/2500000000000000000000 : ℝ)*base89 + (40407737/2500000000000000000000 : ℝ)*base91 + (40407737/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1157_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149766461/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2801/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11337/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2819/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1157_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1157_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149766461/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8229/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9137/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11337/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2819/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1157_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1157_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1157_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149766461/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8229/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9137/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11337/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2819/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1157_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
