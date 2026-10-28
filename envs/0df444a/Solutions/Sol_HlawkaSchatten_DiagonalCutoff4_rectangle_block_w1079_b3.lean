-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1079_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:48:56.204873+00:00
-- url     : https://prove2.me/submissions/2a159941-81e5-4bc1-a2f5-06ec59ed9e08

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
theorem support_rectangle_w1079_s9_0 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5344941199/10000000000 : ℝ)*x 0 + (-2263023733/10000000000 : ℝ)*x 1 + (5264718253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344941199/10000000000 : ℝ)^517 ≤ (10873337712371/25000000000000 : ℝ)^389 := by
    have hnat : (5344941199 : ℕ)^517*25000000000000^389 ≤ 10873337712371^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344941199 10000000000 10873337712371 25000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2263023733/10000000000 : ℝ)^517 ≤ (13878748510923/100000000000000 : ℝ)^389 := by
    have hnat : (2263023733 : ℕ)^517*100000000000000^389 ≤ 13878748510923^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2263023733 10000000000 13878748510923 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264718253/10000000000 : ℝ)^517 ≤ (8525580125709/20000000000000 : ℝ)^389 := by
    have hnat : (5264718253 : ℕ)^517*20000000000000^389 ≤ 8525580125709^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264718253 10000000000 8525580125709 20000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344941199/10000000000 : ℝ), (-2263023733/10000000000 : ℝ), (5264718253/10000000000 : ℝ)] ![(10873337712371/25000000000000 : ℝ), (13878748510923/100000000000000 : ℝ), (8525580125709/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344941199/10000000000 : ℝ)|^517 ≤ (10873337712371/25000000000000 : ℝ)^389
        have hw : |(5344941199/10000000000 : ℝ)|=(5344941199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2263023733/10000000000 : ℝ)|^517 ≤ (13878748510923/100000000000000 : ℝ)^389
        have hw : |(-2263023733/10000000000 : ℝ)|=(2263023733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264718253/10000000000 : ℝ)|^517 ≤ (8525580125709/20000000000000 : ℝ)^389
        have hw : |(5264718253/10000000000 : ℝ)|=(5264718253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s9_1 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-549347031/2500000000 : ℝ)*x 0 + (5265042277/10000000000 : ℝ)*x 1 + (1348443879/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (549347031/2500000000 : ℝ)^517 ≤ (13346333041633/100000000000000 : ℝ)^389 := by
    have hnat : (549347031 : ℕ)^517*100000000000000^389 ≤ 13346333041633^389*2500000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549347031 2500000000 13346333041633 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265042277/10000000000 : ℝ)^517 ≤ (42631387543287/100000000000000 : ℝ)^389 := by
    have hnat : (5265042277 : ℕ)^517*100000000000000^389 ≤ 42631387543287^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265042277 10000000000 42631387543287 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348443879/2500000000 : ℝ)^517 ≤ (22011139696507/50000000000000 : ℝ)^389 := by
    have hnat : (1348443879 : ℕ)^517*50000000000000^389 ≤ 22011139696507^389*2500000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348443879 2500000000 22011139696507 50000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-549347031/2500000000 : ℝ), (5265042277/10000000000 : ℝ), (1348443879/2500000000 : ℝ)] ![(13346333041633/100000000000000 : ℝ), (42631387543287/100000000000000 : ℝ), (22011139696507/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-549347031/2500000000 : ℝ)|^517 ≤ (13346333041633/100000000000000 : ℝ)^389
        have hw : |(-549347031/2500000000 : ℝ)|=(549347031/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265042277/10000000000 : ℝ)|^517 ≤ (42631387543287/100000000000000 : ℝ)^389
        have hw : |(5265042277/10000000000 : ℝ)|=(5265042277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348443879/2500000000 : ℝ)|^517 ≤ (22011139696507/50000000000000 : ℝ)^389
        have hw : |(1348443879/2500000000 : ℝ)|=(1348443879/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s9_2 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2656159317/5000000000 : ℝ)*x 0 + (-1066983259/5000000000 : ℝ)*x 1 + (674221943/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656159317/5000000000 : ℝ)^517 ≤ (4314089715847/10000000000000 : ℝ)^389 := by
    have hnat : (2656159317 : ℕ)^517*10000000000000^389 ≤ 4314089715847^389*5000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656159317 5000000000 4314089715847 10000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1066983259/5000000000 : ℝ)^517 ≤ (12836823123661/100000000000000 : ℝ)^389 := by
    have hnat : (1066983259 : ℕ)^517*100000000000000^389 ≤ 12836823123661^389*5000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1066983259 5000000000 12836823123661 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674221943/1250000000 : ℝ)^517 ≤ (22011139848369/50000000000000 : ℝ)^389 := by
    have hnat : (674221943 : ℕ)^517*50000000000000^389 ≤ 22011139848369^389*1250000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674221943 1250000000 22011139848369 50000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656159317/5000000000 : ℝ), (-1066983259/5000000000 : ℝ), (674221943/1250000000 : ℝ)] ![(4314089715847/10000000000000 : ℝ), (12836823123661/100000000000000 : ℝ), (22011139848369/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656159317/5000000000 : ℝ)|^517 ≤ (4314089715847/10000000000000 : ℝ)^389
        have hw : |(2656159317/5000000000 : ℝ)|=(2656159317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1066983259/5000000000 : ℝ)|^517 ≤ (12836823123661/100000000000000 : ℝ)^389
        have hw : |(-1066983259/5000000000 : ℝ)|=(1066983259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674221943/1250000000 : ℝ)|^517 ≤ (22011139848369/50000000000000 : ℝ)^389
        have hw : |(674221943/1250000000 : ℝ)|=(674221943/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s9_3 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2656159327/5000000000 : ℝ)*x 0 + (5393775499/10000000000 : ℝ)*x 1 + (-1066983277/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656159327/5000000000 : ℝ)^517 ≤ (10785224343583/25000000000000 : ℝ)^389 := by
    have hnat : (2656159327 : ℕ)^517*25000000000000^389 ≤ 10785224343583^389*5000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656159327 5000000000 10785224343583 25000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393775499/10000000000 : ℝ)^517 ≤ (4402227920861/10000000000000 : ℝ)^389 := by
    have hnat : (5393775499 : ℕ)^517*10000000000000^389 ≤ 4402227920861^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393775499 10000000000 4402227920861 10000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1066983277/5000000000 : ℝ)^517 ≤ (3209205852869/25000000000000 : ℝ)^389 := by
    have hnat : (1066983277 : ℕ)^517*25000000000000^389 ≤ 3209205852869^389*5000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1066983277 5000000000 3209205852869 25000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656159327/5000000000 : ℝ), (5393775499/10000000000 : ℝ), (-1066983277/5000000000 : ℝ)] ![(10785224343583/25000000000000 : ℝ), (4402227920861/10000000000000 : ℝ), (3209205852869/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656159327/5000000000 : ℝ)|^517 ≤ (10785224343583/25000000000000 : ℝ)^389
        have hw : |(2656159327/5000000000 : ℝ)|=(2656159327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393775499/10000000000 : ℝ)|^517 ≤ (4402227920861/10000000000000 : ℝ)^389
        have hw : |(5393775499/10000000000 : ℝ)|=(5393775499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1066983277/5000000000 : ℝ)|^517 ≤ (3209205852869/25000000000000 : ℝ)^389
        have hw : |(-1066983277/5000000000 : ℝ)|=(1066983277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s9_4 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1093409319/2500000000 : ℝ)*x 0 + (1125492337/2500000000 : ℝ)*x 1 + (4249018921/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1093409319/2500000000 : ℝ)^517 ≤ (33316739164337/100000000000000 : ℝ)^389 := by
    have hnat : (1093409319 : ℕ)^517*100000000000000^389 ≤ 33316739164337^389*2500000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093409319 2500000000 33316739164337 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1125492337/2500000000 : ℝ)^517 ≤ (34622230103747/100000000000000 : ℝ)^389 := by
    have hnat : (1125492337 : ℕ)^517*100000000000000^389 ≤ 34622230103747^389*2500000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125492337 2500000000 34622230103747 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4249018921/10000000000 : ℝ)^517 ≤ (32061030720353/100000000000000 : ℝ)^389 := by
    have hnat : (4249018921 : ℕ)^517*100000000000000^389 ≤ 32061030720353^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4249018921 10000000000 32061030720353 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1093409319/2500000000 : ℝ), (1125492337/2500000000 : ℝ), (4249018921/10000000000 : ℝ)] ![(33316739164337/100000000000000 : ℝ), (34622230103747/100000000000000 : ℝ), (32061030720353/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1093409319/2500000000 : ℝ)|^517 ≤ (33316739164337/100000000000000 : ℝ)^389
        have hw : |(1093409319/2500000000 : ℝ)|=(1093409319/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1125492337/2500000000 : ℝ)|^517 ≤ (34622230103747/100000000000000 : ℝ)^389
        have hw : |(1125492337/2500000000 : ℝ)|=(1125492337/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4249018921/10000000000 : ℝ)|^517 ≤ (32061030720353/100000000000000 : ℝ)^389
        have hw : |(4249018921/10000000000 : ℝ)|=(4249018921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1079_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74122999/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14011/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1127/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (1127/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1401/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14011/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1127/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14011/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1127/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14011/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1127/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14011/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1127/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14011/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1127/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14011/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1127/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1127/10000 : ℝ) ^ (8271/2048 : ℝ) ≤ (14829426981262067/100000000000000000000 : ℝ) := by
    have hpowers : (1127/10000 : ℝ)^8271 ≤ (14829426981262067/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1127 : ℕ)^8271*100000000000000000000^2048 ≤ 14829426981262067^2048*10000^8271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1127 10000 14829426981262067 100000000000000000000 8271 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1127/10000 : ℝ)) (X := (14829426981262067/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8271 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14011/100000 : ℝ) ^ (8271/2048 : ℝ) ≤ (7144671107240271/20000000000000000000 : ℝ) := by
    have hpowers : (14011/100000 : ℝ)^8271 ≤ (7144671107240271/20000000000000000000 : ℝ)^2048 := by
      have hnat : (14011 : ℕ)^8271*20000000000000000000^2048 ≤ 7144671107240271^2048*100000^8271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14011 100000 7144671107240271 20000000000000000000 8271 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14011/100000 : ℝ)) (X := (7144671107240271/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8271 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014829426981262067/50000000000000000000 : ℝ) ≤ (2500183576825313/2500000000000000 : ℝ) ^ (8271/2048 : ℝ) := by
    have hpowers : (50014829426981262067/50000000000000000000 : ℝ)^2048 ≤ (2500183576825313/2500000000000000 : ℝ)^8271 := by
      have hnat : (50014829426981262067 : ℕ)^2048*2500000000000000^8271 ≤ 2500183576825313^8271*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014829426981262067 50000000000000000000 2500183576825313 2500000000000000 2048 8271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500183576825313/2500000000000000 : ℝ)) (X := (50014829426981262067/50000000000000000000 : ℝ)) (by norm_num) 8271 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025276391258731711/50000000000000000000 : ℝ) ≤ (1250156438784663/1250000000000000 : ℝ) ^ (8271/2048 : ℝ) := by
    have hpowers : (50025276391258731711/50000000000000000000 : ℝ)^2048 ≤ (1250156438784663/1250000000000000 : ℝ)^8271 := by
      have hnat : (50025276391258731711 : ℕ)^2048*1250000000000000^8271 ≤ 1250156438784663^8271*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025276391258731711 50000000000000000000 1250156438784663 1250000000000000 2048 8271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250156438784663/1250000000000000 : ℝ)) (X := (50025276391258731711/50000000000000000000 : ℝ)) (by norm_num) 8271 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10007144671107240271/10000000000000000000 : ℝ) ≤ (2500442178313339/2500000000000000 : ℝ) ^ (8271/2048 : ℝ) := by
    have hpowers : (10007144671107240271/10000000000000000000 : ℝ)^2048 ≤ (2500442178313339/2500000000000000 : ℝ)^8271 := by
      have hnat : (10007144671107240271 : ℕ)^2048*2500000000000000^8271 ≤ 2500442178313339^8271*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10007144671107240271 10000000000000000000 2500442178313339 2500000000000000 2048 8271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500442178313339/2500000000000000 : ℝ)) (X := (10007144671107240271/10000000000000000000 : ℝ)) (by norm_num) 8271 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14829426981262067/100000000000000000000 : ℝ) ≤ ((6850088745308129913/6852500000000000000 : ℝ)+2*(129300744013/68525000000000 : ℝ)*(1127/10000 : ℝ))^(8271/2048 : ℝ) := by
    rw [show (6850088745308129913/6852500000000000000 : ℝ)+2*(129300744013/68525000000000 : ℝ)*(1127/10000 : ℝ)=(2500183576825313/2500000000000000 : ℝ) by norm_num, show 1+2*(14829426981262067/100000000000000000000 : ℝ)=(50014829426981262067/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7144671107240271/20000000000000000000 : ℝ)+(14829426981262067/100000000000000000000 : ℝ) ≤ ((6850088745308129913/6852500000000000000 : ℝ)+(129300744013/68525000000000 : ℝ)*((14011/100000 : ℝ)+(1127/10000 : ℝ)))^(8271/2048 : ℝ) := by
    rw [show (6850088745308129913/6852500000000000000 : ℝ)+(129300744013/68525000000000 : ℝ)*((14011/100000 : ℝ)+(1127/10000 : ℝ))=(1250156438784663/1250000000000000 : ℝ) by norm_num, show 1+(7144671107240271/20000000000000000000 : ℝ)+(14829426981262067/100000000000000000000 : ℝ)=(50025276391258731711/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7144671107240271/20000000000000000000 : ℝ) ≤ ((6850088745308129913/6852500000000000000 : ℝ)+2*(129300744013/68525000000000 : ℝ)*(14011/100000 : ℝ))^(8271/2048 : ℝ) := by
    rw [show (6850088745308129913/6852500000000000000 : ℝ)+2*(129300744013/68525000000000 : ℝ)*(14011/100000 : ℝ)=(2500442178313339/2500000000000000 : ℝ) by norm_num, show 1+2*(7144671107240271/20000000000000000000 : ℝ)=(10007144671107240271/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6850088745308129913/6852500000000000000 : ℝ)*(X 1 0+X 2 0)+(129300744013/68525000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8271/2048 : ℝ)) (lo := (1127/10000 : ℝ)) (hi := (14011/100000 : ℝ)) (c := (6850088745308129913/6852500000000000000 : ℝ)) (alpha := (129300744013/68525000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6850088745308129913/6852500000000000000 : ℝ)*(X 0 1+X 2 1)+(129300744013/68525000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8271/2048 : ℝ)) (lo := (1127/10000 : ℝ)) (hi := (14011/100000 : ℝ)) (c := (6850088745308129913/6852500000000000000 : ℝ)) (alpha := (129300744013/68525000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6850088745308129913/6852500000000000000 : ℝ)*(X 0 2+X 1 2)+(129300744013/68525000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8271/2048 : ℝ)) (lo := (1127/10000 : ℝ)) (hi := (14011/100000 : ℝ)) (c := (6850088745308129913/6852500000000000000 : ℝ)) (alpha := (129300744013/68525000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((5344941199/10000000000 : ℝ)*X 1 0+(-2263023733/10000000000 : ℝ)*X 1 1+(5264718253/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s9_0 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-549347031/2500000000 : ℝ)*X 0 0+(5265042277/10000000000 : ℝ)*X 0 1+(1348443879/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s9_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2656159317/5000000000 : ℝ)*X 1 0+(-1066983259/5000000000 : ℝ)*X 1 1+(674221943/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s9_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2656159327/5000000000 : ℝ)*X 2 0+(5393775499/10000000000 : ℝ)*X 2 1+(-1066983277/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s9_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((1093409319/2500000000 : ℝ)*X 0 0+(1125492337/2500000000 : ℝ)*X 0 1+(4249018921/10000000000 : ℝ)*X 0 2+(1093409319/2500000000 : ℝ)*X 1 0+(1125492337/2500000000 : ℝ)*X 1 1+(4249018921/10000000000 : ℝ)*X 1 2+(1093409319/2500000000 : ℝ)*X 2 0+(1125492337/2500000000 : ℝ)*X 2 1+(4249018921/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s9_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (341693619177640144677493641/171312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (81703207/25000000000000 : ℝ)*(base19) + (384269251/100000000000000 : ℝ)*(base23) + (115424427/100000000000000 : ℝ)*(lower1) + (15225221/50000000000000 : ℝ)*(upper3) + (21663223/100000000000000 : ℝ)*(lower4) + (12181611/20000000000000 : ℝ)*(upper5) + (2930333017612581/50000000000000 : ℝ)*(major0) + (2930333017612581/50000000000000 : ℝ)*(major1) + (2930333017612581/50000000000000 : ℝ)*(major2) + (409319571/20000000000000 : ℝ)*(sp0) + (7767993556862133/100000000000000 : ℝ)*(sp1) + (155359823669029/2000000000000 : ℝ)*(sp2) + (3883996586296441/50000000000000 : ℝ)*(sp3) + (1976669223551371/50000000000000 : ℝ)*(sp4) + (1976669223551371/50000000000000 : ℝ)*(f.failure) + (7767993556862133/100000000000000 : ℝ)*(f.sum) + (2294233800269/3426250000000000000000000000 : ℝ)*base66 + (2639086464151910453/342625000000000000000000000000000 : ℝ)*base67 + (3220703381755285453/342625000000000000000000000000000 : ℝ)*base69 + (2766134418645589547/342625000000000000000000000000000 : ℝ)*base72 + (597387184719/13705000000000000000000000000 : ℝ)*base73 + (4753076396146910453/342625000000000000000000000000000 : ℝ)*base75 + (1173741348995964547/342625000000000000000000000000000 : ℝ)*base78 + (5541805026619785453/342625000000000000000000000000000 : ℝ)*base79 + (50992088263427/6852500000000000000000000000 : ℝ)*base81 + (918371/2500000000000000000000 : ℝ)*base90 + (918371/2500000000000000000000 : ℝ)*base92 + (918371/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1079_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74122999/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14011/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1127/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1127/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1401/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1079_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1079_box_0 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-129273701/625000000 : ℝ)*x 0 + (537718753/1000000000 : ℝ)*x 1 + (5377187169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (129273701/625000000 : ℝ)^517 ≤ (2463026351611/20000000000000 : ℝ)^389 := by
    have hnat : (129273701 : ℕ)^517*20000000000000^389 ≤ 2463026351611^389*625000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129273701 625000000 2463026351611 20000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (537718753/1000000000 : ℝ)^517 ≤ (21921218036789/50000000000000 : ℝ)^389 := by
    have hnat : (537718753 : ℕ)^517*50000000000000^389 ≤ 21921218036789^389*1000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537718753 1000000000 21921218036789 50000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5377187169/10000000000 : ℝ)^517 ≤ (43842432161679/100000000000000 : ℝ)^389 := by
    have hnat : (5377187169 : ℕ)^517*100000000000000^389 ≤ 43842432161679^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377187169 10000000000 43842432161679 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-129273701/625000000 : ℝ), (537718753/1000000000 : ℝ), (5377187169/10000000000 : ℝ)] ![(2463026351611/20000000000000 : ℝ), (21921218036789/50000000000000 : ℝ), (43842432161679/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-129273701/625000000 : ℝ)|^517 ≤ (2463026351611/20000000000000 : ℝ)^389
        have hw : |(-129273701/625000000 : ℝ)|=(129273701/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(537718753/1000000000 : ℝ)|^517 ≤ (21921218036789/50000000000000 : ℝ)^389
        have hw : |(537718753/1000000000 : ℝ)|=(537718753/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5377187169/10000000000 : ℝ)|^517 ≤ (43842432161679/100000000000000 : ℝ)^389
        have hw : |(5377187169/10000000000 : ℝ)|=(5377187169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_box_1 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5295348813/10000000000 : ℝ)*x 0 + (-2179201891/10000000000 : ℝ)*x 1 + (5377187377/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295348813/10000000000 : ℝ)^517 ≤ (42957836598069/100000000000000 : ℝ)^389 := by
    have hnat : (5295348813 : ℕ)^517*100000000000000^389 ≤ 42957836598069^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295348813 10000000000 42957836598069 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2179201891/10000000000 : ℝ)^517 ≤ (527989159011/4000000000000 : ℝ)^389 := by
    have hnat : (2179201891 : ℕ)^517*4000000000000^389 ≤ 527989159011^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179201891 10000000000 527989159011 4000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5377187377/10000000000 : ℝ)^517 ≤ (21921217207813/50000000000000 : ℝ)^389 := by
    have hnat : (5377187377 : ℕ)^517*50000000000000^389 ≤ 21921217207813^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377187377 10000000000 21921217207813 50000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295348813/10000000000 : ℝ), (-2179201891/10000000000 : ℝ), (5377187377/10000000000 : ℝ)] ![(42957836598069/100000000000000 : ℝ), (527989159011/4000000000000 : ℝ), (21921217207813/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295348813/10000000000 : ℝ)|^517 ≤ (42957836598069/100000000000000 : ℝ)^389
        have hw : |(5295348813/10000000000 : ℝ)|=(5295348813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2179201891/10000000000 : ℝ)|^517 ≤ (527989159011/4000000000000 : ℝ)^389
        have hw : |(-2179201891/10000000000 : ℝ)|=(2179201891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5377187377/10000000000 : ℝ)|^517 ≤ (21921217207813/50000000000000 : ℝ)^389
        have hw : |(5377187377/10000000000 : ℝ)|=(5377187377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_box_2 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1323837217/2500000000 : ℝ)*x 0 + (134429683/250000000 : ℝ)*x 1 + (-1089600947/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323837217/2500000000 : ℝ)^517 ≤ (5369729648883/12500000000000 : ℝ)^389 := by
    have hnat : (1323837217 : ℕ)^517*12500000000000^389 ≤ 5369729648883^389*2500000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323837217 2500000000 5369729648883 12500000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (134429683/250000000 : ℝ)^517 ≤ (21921216898979/50000000000000 : ℝ)^389 := by
    have hnat : (134429683 : ℕ)^517*50000000000000^389 ≤ 21921216898979^389*250000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134429683 250000000 21921216898979 50000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1089600947/5000000000 : ℝ)^517 ≤ (6599864499713/50000000000000 : ℝ)^389 := by
    have hnat : (1089600947 : ℕ)^517*50000000000000^389 ≤ 6599864499713^389*5000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089600947 5000000000 6599864499713 50000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323837217/2500000000 : ℝ), (134429683/250000000 : ℝ), (-1089600947/5000000000 : ℝ)] ![(5369729648883/12500000000000 : ℝ), (21921216898979/50000000000000 : ℝ), (6599864499713/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323837217/2500000000 : ℝ)|^517 ≤ (5369729648883/12500000000000 : ℝ)^389
        have hw : |(1323837217/2500000000 : ℝ)|=(1323837217/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(134429683/250000000 : ℝ)|^517 ≤ (21921216898979/50000000000000 : ℝ)^389
        have hw : |(134429683/250000000 : ℝ)|=(134429683/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1089600947/5000000000 : ℝ)|^517 ≤ (6599864499713/50000000000000 : ℝ)^389
        have hw : |(-1089600947/5000000000 : ℝ)|=(1089600947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_box_3 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (280116267/625000000 : ℝ)*x 0 + (4321663539/10000000000 : ℝ)*x 1 + (2160831627/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (280116267/625000000 : ℝ)^517 ≤ (34416846406309/100000000000000 : ℝ)^389 := by
    have hnat : (280116267 : ℕ)^517*100000000000000^389 ≤ 34416846406309^389*625000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280116267 625000000 34416846406309 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4321663539/10000000000 : ℝ)^517 ≤ (32791578226817/100000000000000 : ℝ)^389 := by
    have hnat : (4321663539 : ℕ)^517*100000000000000^389 ≤ 32791578226817^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4321663539 10000000000 32791578226817 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2160831627/5000000000 : ℝ)^517 ≤ (8197893838187/25000000000000 : ℝ)^389 := by
    have hnat : (2160831627 : ℕ)^517*25000000000000^389 ≤ 8197893838187^389*5000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2160831627 5000000000 8197893838187 25000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(280116267/625000000 : ℝ), (4321663539/10000000000 : ℝ), (2160831627/5000000000 : ℝ)] ![(34416846406309/100000000000000 : ℝ), (32791578226817/100000000000000 : ℝ), (8197893838187/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(280116267/625000000 : ℝ)|^517 ≤ (34416846406309/100000000000000 : ℝ)^389
        have hw : |(280116267/625000000 : ℝ)|=(280116267/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4321663539/10000000000 : ℝ)|^517 ≤ (32791578226817/100000000000000 : ℝ)^389
        have hw : |(4321663539/10000000000 : ℝ)|=(4321663539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2160831627/5000000000 : ℝ)|^517 ≤ (8197893838187/25000000000000 : ℝ)^389
        have hw : |(2160831627/5000000000 : ℝ)|=(2160831627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_box_4 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-7274311/31250000 : ℝ)*x 0 + (2640141859/5000000000 : ℝ)*x 1 + (5280283627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7274311/31250000 : ℝ)^517 ≤ (14409031429187/100000000000000 : ℝ)^389 := by
    have hnat : (7274311 : ℕ)^517*100000000000000^389 ≤ 14409031429187^389*31250000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7274311 31250000 14409031429187 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2640141859/5000000000 : ℝ)^517 ≤ (10698871191931/25000000000000 : ℝ)^389 := by
    have hnat : (2640141859 : ℕ)^517*25000000000000^389 ≤ 10698871191931^389*5000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640141859 5000000000 10698871191931 25000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5280283627/10000000000 : ℝ)^517 ≤ (8559096757501/20000000000000 : ℝ)^389 := by
    have hnat : (5280283627 : ℕ)^517*20000000000000^389 ≤ 8559096757501^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280283627 10000000000 8559096757501 20000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-7274311/31250000 : ℝ), (2640141859/5000000000 : ℝ), (5280283627/10000000000 : ℝ)] ![(14409031429187/100000000000000 : ℝ), (10698871191931/25000000000000 : ℝ), (8559096757501/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-7274311/31250000 : ℝ)|^517 ≤ (14409031429187/100000000000000 : ℝ)^389
        have hw : |(-7274311/31250000 : ℝ)|=(7274311/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2640141859/5000000000 : ℝ)|^517 ≤ (10698871191931/25000000000000 : ℝ)^389
        have hw : |(2640141859/5000000000 : ℝ)|=(2640141859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5280283627/10000000000 : ℝ)|^517 ≤ (8559096757501/20000000000000 : ℝ)^389
        have hw : |(5280283627/10000000000 : ℝ)|=(5280283627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_box_5 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2681954607/5000000000 : ℝ)*x 0 + (-88685093/400000000 : ℝ)*x 1 + (1320070927/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681954607/5000000000 : ℝ)^517 ≤ (10924651735307/25000000000000 : ℝ)^389 := by
    have hnat : (2681954607 : ℕ)^517*25000000000000^389 ≤ 10924651735307^389*5000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681954607 5000000000 10924651735307 25000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (88685093/400000000 : ℝ)^517 ≤ (1688238548477/12500000000000 : ℝ)^389 := by
    have hnat : (88685093 : ℕ)^517*12500000000000^389 ≤ 1688238548477^389*400000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88685093 400000000 1688238548477 12500000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1320070927/2500000000 : ℝ)^517 ≤ (42795484660007/100000000000000 : ℝ)^389 := by
    have hnat : (1320070927 : ℕ)^517*100000000000000^389 ≤ 42795484660007^389*2500000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320070927 2500000000 42795484660007 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681954607/5000000000 : ℝ), (-88685093/400000000 : ℝ), (1320070927/2500000000 : ℝ)] ![(10924651735307/25000000000000 : ℝ), (1688238548477/12500000000000 : ℝ), (42795484660007/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681954607/5000000000 : ℝ)|^517 ≤ (10924651735307/25000000000000 : ℝ)^389
        have hw : |(2681954607/5000000000 : ℝ)|=(2681954607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-88685093/400000000 : ℝ)|^517 ≤ (1688238548477/12500000000000 : ℝ)^389
        have hw : |(-88685093/400000000 : ℝ)|=(88685093/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1320070927/2500000000 : ℝ)|^517 ≤ (42795484660007/100000000000000 : ℝ)^389
        have hw : |(1320070927/2500000000 : ℝ)|=(1320070927/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_box_6 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5363908869/10000000000 : ℝ)*x 0 + (264014167/500000000 : ℝ)*x 1 + (-554282069/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363908869/10000000000 : ℝ)^517 ≤ (174794412823/400000000000 : ℝ)^389 := by
    have hnat : (5363908869 : ℕ)^517*400000000000^389 ≤ 174794412823^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363908869 10000000000 174794412823 400000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (264014167/500000000 : ℝ)^517 ≤ (21397740348023/50000000000000 : ℝ)^389 := by
    have hnat : (264014167 : ℕ)^517*50000000000000^389 ≤ 21397740348023^389*500000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264014167 500000000 21397740348023 50000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (554282069/2500000000 : ℝ)^517 ≤ (13505916087177/100000000000000 : ℝ)^389 := by
    have hnat : (554282069 : ℕ)^517*100000000000000^389 ≤ 13505916087177^389*2500000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      554282069 2500000000 13505916087177 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363908869/10000000000 : ℝ), (264014167/500000000 : ℝ), (-554282069/2500000000 : ℝ)] ![(174794412823/400000000000 : ℝ), (21397740348023/50000000000000 : ℝ), (13505916087177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363908869/10000000000 : ℝ)|^517 ≤ (174794412823/400000000000 : ℝ)^389
        have hw : |(5363908869/10000000000 : ℝ)|=(5363908869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(264014167/500000000 : ℝ)|^517 ≤ (21397740348023/50000000000000 : ℝ)^389
        have hw : |(264014167/500000000 : ℝ)|=(264014167/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-554282069/2500000000 : ℝ)|^517 ≤ (13505916087177/100000000000000 : ℝ)^389
        have hw : |(-554282069/2500000000 : ℝ)|=(554282069/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_box_7 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4265060017/10000000000 : ℝ)*x 0 + (4430042113/10000000000 : ℝ)*x 1 + (1107510561/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4265060017/10000000000 : ℝ)^517 ≤ (32221996379761/100000000000000 : ℝ)^389 := by
    have hnat : (4265060017 : ℕ)^517*100000000000000^389 ≤ 32221996379761^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4265060017 10000000000 32221996379761 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4430042113/10000000000 : ℝ)^517 ≤ (8472250284203/25000000000000 : ℝ)^389 := by
    have hnat : (4430042113 : ℕ)^517*25000000000000^389 ≤ 8472250284203^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4430042113 10000000000 8472250284203 25000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1107510561/2500000000 : ℝ)^517 ≤ (16944501234343/50000000000000 : ℝ)^389 := by
    have hnat : (1107510561 : ℕ)^517*50000000000000^389 ≤ 16944501234343^389*2500000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1107510561 2500000000 16944501234343 50000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4265060017/10000000000 : ℝ), (4430042113/10000000000 : ℝ), (1107510561/2500000000 : ℝ)] ![(32221996379761/100000000000000 : ℝ), (8472250284203/25000000000000 : ℝ), (16944501234343/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4265060017/10000000000 : ℝ)|^517 ≤ (32221996379761/100000000000000 : ℝ)^389
        have hw : |(4265060017/10000000000 : ℝ)|=(4265060017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4430042113/10000000000 : ℝ)|^517 ≤ (8472250284203/25000000000000 : ℝ)^389
        have hw : |(4430042113/10000000000 : ℝ)|=(4430042113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1107510561/2500000000 : ℝ)|^517 ≤ (16944501234343/50000000000000 : ℝ)^389
        have hw : |(1107510561/2500000000 : ℝ)|=(1107510561/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_box_8 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2273611233/10000000000 : ℝ)*x 0 + (5214503451/10000000000 : ℝ)*x 1 + (5386788741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2273611233/10000000000 : ℝ)^517 ≤ (218204872491/1562500000000 : ℝ)^389 := by
    have hnat : (2273611233 : ℕ)^517*1562500000000^389 ≤ 218204872491^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2273611233 10000000000 218204872491 1562500000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5214503451/10000000000 : ℝ)^517 ≤ (10522095016659/25000000000000 : ℝ)^389 := by
    have hnat : (5214503451 : ℕ)^517*25000000000000^389 ≤ 10522095016659^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5214503451 10000000000 10522095016659 25000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5386788741/10000000000 : ℝ)^517 ≤ (43946508088181/100000000000000 : ℝ)^389 := by
    have hnat : (5386788741 : ℕ)^517*100000000000000^389 ≤ 43946508088181^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386788741 10000000000 43946508088181 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2273611233/10000000000 : ℝ), (5214503451/10000000000 : ℝ), (5386788741/10000000000 : ℝ)] ![(218204872491/1562500000000 : ℝ), (10522095016659/25000000000000 : ℝ), (43946508088181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2273611233/10000000000 : ℝ)|^517 ≤ (218204872491/1562500000000 : ℝ)^389
        have hw : |(-2273611233/10000000000 : ℝ)|=(2273611233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5214503451/10000000000 : ℝ)|^517 ≤ (10522095016659/25000000000000 : ℝ)^389
        have hw : |(5214503451/10000000000 : ℝ)|=(5214503451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5386788741/10000000000 : ℝ)|^517 ≤ (43946508088181/100000000000000 : ℝ)^389
        have hw : |(5386788741/10000000000 : ℝ)|=(5386788741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_box_9 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (330534503/625000000 : ℝ)*x 0 + (-435074513/2000000000 : ℝ)*x 1 + (336674353/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330534503/625000000 : ℝ)^517 ≤ (214422855693/500000000000 : ℝ)^389 := by
    have hnat : (330534503 : ℕ)^517*500000000000^389 ≤ 214422855693^389*625000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330534503 625000000 214422855693 500000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (435074513/2000000000 : ℝ)^517 ≤ (52675643687/400000000000 : ℝ)^389 := by
    have hnat : (435074513 : ℕ)^517*400000000000^389 ≤ 52675643687^389*2000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435074513 2000000000 52675643687 400000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (336674353/625000000 : ℝ)^517 ≤ (43946517922463/100000000000000 : ℝ)^389 := by
    have hnat : (336674353 : ℕ)^517*100000000000000^389 ≤ 43946517922463^389*625000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336674353 625000000 43946517922463 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330534503/625000000 : ℝ), (-435074513/2000000000 : ℝ), (336674353/625000000 : ℝ)] ![(214422855693/500000000000 : ℝ), (52675643687/400000000000 : ℝ), (43946517922463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330534503/625000000 : ℝ)|^517 ≤ (214422855693/500000000000 : ℝ)^389
        have hw : |(330534503/625000000 : ℝ)|=(330534503/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-435074513/2000000000 : ℝ)|^517 ≤ (52675643687/400000000000 : ℝ)^389
        have hw : |(-435074513/2000000000 : ℝ)|=(435074513/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(336674353/625000000 : ℝ)|^517 ≤ (43946517922463/100000000000000 : ℝ)^389
        have hw : |(336674353/625000000 : ℝ)|=(336674353/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_box_10 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5288551969/10000000000 : ℝ)*x 0 + (5386788637/10000000000 : ℝ)*x 1 + (-2175374033/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288551969/10000000000 : ℝ)^517 ≤ (42884570287203/100000000000000 : ℝ)^389 := by
    have hnat : (5288551969 : ℕ)^517*100000000000000^389 ≤ 42884570287203^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288551969 10000000000 42884570287203 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5386788637/10000000000 : ℝ)^517 ≤ (8789301392109/20000000000000 : ℝ)^389 := by
    have hnat : (5386788637 : ℕ)^517*20000000000000^389 ≤ 8789301392109^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386788637 10000000000 8789301392109 20000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2175374033/10000000000 : ℝ)^517 ≤ (13168922732657/100000000000000 : ℝ)^389 := by
    have hnat : (2175374033 : ℕ)^517*100000000000000^389 ≤ 13168922732657^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175374033 10000000000 13168922732657 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288551969/10000000000 : ℝ), (5386788637/10000000000 : ℝ), (-2175374033/10000000000 : ℝ)] ![(42884570287203/100000000000000 : ℝ), (8789301392109/20000000000000 : ℝ), (13168922732657/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288551969/10000000000 : ℝ)|^517 ≤ (42884570287203/100000000000000 : ℝ)^389
        have hw : |(5288551969/10000000000 : ℝ)|=(5288551969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5386788637/10000000000 : ℝ)|^517 ≤ (8789301392109/20000000000000 : ℝ)^389
        have hw : |(5386788637/10000000000 : ℝ)|=(5386788637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2175374033/10000000000 : ℝ)|^517 ≤ (13168922732657/100000000000000 : ℝ)^389
        have hw : |(-2175374033/10000000000 : ℝ)|=(2175374033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_box_11 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4503069243/10000000000 : ℝ)*x 0 + (4310918417/10000000000 : ℝ)*x 1 + (538864797/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4503069243/10000000000 : ℝ)^517 ≤ (34633472583903/100000000000000 : ℝ)^389 := by
    have hnat : (4503069243 : ℕ)^517*100000000000000^389 ≤ 34633472583903^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4503069243 10000000000 34633472583903 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4310918417/10000000000 : ℝ)^517 ≤ (16341631954281/50000000000000 : ℝ)^389 := by
    have hnat : (4310918417 : ℕ)^517*50000000000000^389 ≤ 16341631954281^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4310918417 10000000000 16341631954281 50000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (538864797/1250000000 : ℝ)^517 ≤ (16341631747719/50000000000000 : ℝ)^389 := by
    have hnat : (538864797 : ℕ)^517*50000000000000^389 ≤ 16341631747719^389*1250000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538864797 1250000000 16341631747719 50000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4503069243/10000000000 : ℝ), (4310918417/10000000000 : ℝ), (538864797/1250000000 : ℝ)] ![(34633472583903/100000000000000 : ℝ), (16341631954281/50000000000000 : ℝ), (16341631747719/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4503069243/10000000000 : ℝ)|^517 ≤ (34633472583903/100000000000000 : ℝ)^389
        have hw : |(4503069243/10000000000 : ℝ)|=(4503069243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4310918417/10000000000 : ℝ)|^517 ≤ (16341631954281/50000000000000 : ℝ)^389
        have hw : |(4310918417/10000000000 : ℝ)|=(4310918417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(538864797/1250000000 : ℝ)|^517 ≤ (16341631747719/50000000000000 : ℝ)^389
        have hw : |(538864797/1250000000 : ℝ)|=(538864797/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_box_12 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-530726851/2500000000 : ℝ)*x 0 + (340102667/625000000 : ℝ)*x 1 + (52722763/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530726851/2500000000 : ℝ)^517 ≤ (12748482522623/100000000000000 : ℝ)^389 := by
    have hnat : (530726851 : ℕ)^517*100000000000000^389 ≤ 12748482522623^389*2500000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530726851 2500000000 12748482522623 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (340102667/625000000 : ℝ)^517 ≤ (22271132075011/50000000000000 : ℝ)^389 := by
    have hnat : (340102667 : ℕ)^517*50000000000000^389 ≤ 22271132075011^389*625000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340102667 625000000 22271132075011 50000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (52722763/100000000 : ℝ)^517 ≤ (42709253309977/100000000000000 : ℝ)^389 := by
    have hnat : (52722763 : ℕ)^517*100000000000000^389 ≤ 42709253309977^389*100000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52722763 100000000 42709253309977 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-530726851/2500000000 : ℝ), (340102667/625000000 : ℝ), (52722763/100000000 : ℝ)] ![(12748482522623/100000000000000 : ℝ), (22271132075011/50000000000000 : ℝ), (42709253309977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-530726851/2500000000 : ℝ)|^517 ≤ (12748482522623/100000000000000 : ℝ)^389
        have hw : |(-530726851/2500000000 : ℝ)|=(530726851/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(340102667/625000000 : ℝ)|^517 ≤ (22271132075011/50000000000000 : ℝ)^389
        have hw : |(340102667/625000000 : ℝ)|=(340102667/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(52722763/100000000 : ℝ)|^517 ≤ (42709253309977/100000000000000 : ℝ)^389
        have hw : |(52722763/100000000 : ℝ)|=(52722763/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_box_13 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (107391437/200000000 : ℝ)*x 0 + (-2220202097/10000000000 : ℝ)*x 1 + (210891087/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107391437/200000000 : ℝ)^517 ≤ (8751985925417/20000000000000 : ℝ)^389 := by
    have hnat : (107391437 : ℕ)^517*20000000000000^389 ≤ 8751985925417^389*200000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107391437 200000000 8751985925417 20000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2220202097/10000000000 : ℝ)^517 ≤ (541232305073/4000000000000 : ℝ)^389 := by
    have hnat : (2220202097 : ℕ)^517*4000000000000^389 ≤ 541232305073^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2220202097 10000000000 541232305073 4000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210891087/400000000 : ℝ)^517 ≤ (42709262730453/100000000000000 : ℝ)^389 := by
    have hnat : (210891087 : ℕ)^517*100000000000000^389 ≤ 42709262730453^389*400000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210891087 400000000 42709262730453 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(107391437/200000000 : ℝ), (-2220202097/10000000000 : ℝ), (210891087/400000000 : ℝ)] ![(8751985925417/20000000000000 : ℝ), (541232305073/4000000000000 : ℝ), (42709262730453/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(107391437/200000000 : ℝ)|^517 ≤ (8751985925417/20000000000000 : ℝ)^389
        have hw : |(107391437/200000000 : ℝ)|=(107391437/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2220202097/10000000000 : ℝ)|^517 ≤ (541232305073/4000000000000 : ℝ)^389
        have hw : |(-2220202097/10000000000 : ℝ)|=(2220202097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210891087/400000000 : ℝ)|^517 ≤ (42709262730453/100000000000000 : ℝ)^389
        have hw : |(210891087/400000000 : ℝ)|=(210891087/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_box_14 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5369572031/10000000000 : ℝ)*x 0 + (2636137991/5000000000 : ℝ)*x 1 + (-27752543/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369572031/10000000000 : ℝ)^517 ≤ (21879965793769/50000000000000 : ℝ)^389 := by
    have hnat : (5369572031 : ℕ)^517*50000000000000^389 ≤ 21879965793769^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369572031 10000000000 21879965793769 50000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2636137991/5000000000 : ℝ)^517 ≤ (42709249886307/100000000000000 : ℝ)^389 := by
    have hnat : (2636137991 : ℕ)^517*100000000000000^389 ≤ 42709249886307^389*5000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636137991 5000000000 42709249886307 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (27752543/125000000 : ℝ)^517 ≤ (13530818504803/100000000000000 : ℝ)^389 := by
    have hnat : (27752543 : ℕ)^517*100000000000000^389 ≤ 13530818504803^389*125000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27752543 125000000 13530818504803 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369572031/10000000000 : ℝ), (2636137991/5000000000 : ℝ), (-27752543/125000000 : ℝ)] ![(21879965793769/50000000000000 : ℝ), (42709249886307/100000000000000 : ℝ), (13530818504803/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369572031/10000000000 : ℝ)|^517 ≤ (21879965793769/50000000000000 : ℝ)^389
        have hw : |(5369572031/10000000000 : ℝ)|=(5369572031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2636137991/5000000000 : ℝ)|^517 ≤ (42709249886307/100000000000000 : ℝ)^389
        have hw : |(2636137991/5000000000 : ℝ)|=(2636137991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-27752543/125000000 : ℝ)|^517 ≤ (13530818504803/100000000000000 : ℝ)^389
        have hw : |(-27752543/125000000 : ℝ)|=(27752543/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_box_15 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (849382807/2000000000 : ℝ)*x 0 + (4438992301/10000000000 : ℝ)*x 1 + (4438994329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (849382807/2000000000 : ℝ)^517 ≤ (320399238941/1000000000000 : ℝ)^389 := by
    have hnat : (849382807 : ℕ)^517*1000000000000^389 ≤ 320399238941^389*2000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849382807 2000000000 320399238941 1000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4438992301/10000000000 : ℝ)^517 ≤ (530937933257/1562500000000 : ℝ)^389 := by
    have hnat : (4438992301 : ℕ)^517*1562500000000^389 ≤ 530937933257^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4438992301 10000000000 530937933257 1562500000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4438994329/10000000000 : ℝ)^517 ≤ (33980048360777/100000000000000 : ℝ)^389 := by
    have hnat : (4438994329 : ℕ)^517*100000000000000^389 ≤ 33980048360777^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4438994329 10000000000 33980048360777 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(849382807/2000000000 : ℝ), (4438992301/10000000000 : ℝ), (4438994329/10000000000 : ℝ)] ![(320399238941/1000000000000 : ℝ), (530937933257/1562500000000 : ℝ), (33980048360777/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(849382807/2000000000 : ℝ)|^517 ≤ (320399238941/1000000000000 : ℝ)^389
        have hw : |(849382807/2000000000 : ℝ)|=(849382807/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4438992301/10000000000 : ℝ)|^517 ≤ (530937933257/1562500000000 : ℝ)^389
        have hw : |(4438992301/10000000000 : ℝ)|=(4438992301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4438994329/10000000000 : ℝ)|^517 ≤ (33980048360777/100000000000000 : ℝ)^389
        have hw : |(4438994329/10000000000 : ℝ)|=(4438994329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1079_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74122999/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1401/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1127/10000 : ℝ)*pair X i i ≤ pair X i h) :
    -(2489/4000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59251/100000 : ℝ) ∧ (79613/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (41491/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1401/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1127/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1401/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1127/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1401/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1127/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1401/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1127/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1401/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1127/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1401/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1127/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1127/10000 : ℝ) ^ (8271/2048 : ℝ) ≤ (14829426981262067/100000000000000000000 : ℝ) := by
    have hpowers : (1127/10000 : ℝ)^8271 ≤ (14829426981262067/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1127 : ℕ)^8271*100000000000000000000^2048 ≤ 14829426981262067^2048*10000^8271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1127 10000 14829426981262067 100000000000000000000 8271 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1127/10000 : ℝ)) (X := (14829426981262067/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8271 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1401/10000 : ℝ) ^ (8271/2048 : ℝ) ≤ (4464132455199477/12500000000000000000 : ℝ) := by
    have hpowers : (1401/10000 : ℝ)^8271 ≤ (4464132455199477/12500000000000000000 : ℝ)^2048 := by
      have hnat : (1401 : ℕ)^8271*12500000000000000000^2048 ≤ 4464132455199477^2048*10000^8271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1401 10000 4464132455199477 12500000000000000000 8271 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1401/10000 : ℝ)) (X := (4464132455199477/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8271 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014829426981262067/50000000000000000000 : ℝ) ≤ (2500183576825313/2500000000000000 : ℝ) ^ (8271/2048 : ℝ) := by
    have hpowers : (50014829426981262067/50000000000000000000 : ℝ)^2048 ≤ (2500183576825313/2500000000000000 : ℝ)^8271 := by
      have hnat : (50014829426981262067 : ℕ)^2048*2500000000000000^8271 ≤ 2500183576825313^8271*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014829426981262067 50000000000000000000 2500183576825313 2500000000000000 2048 8271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500183576825313/2500000000000000 : ℝ)) (X := (50014829426981262067/50000000000000000000 : ℝ)) (by norm_num) 8271 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100050542486622857883/100000000000000000000 : ℝ) ≤ (1000125125543537/1000000000000000 : ℝ) ^ (8271/2048 : ℝ) := by
    have hpowers : (100050542486622857883/100000000000000000000 : ℝ)^2048 ≤ (1000125125543537/1000000000000000 : ℝ)^8271 := by
      have hnat : (100050542486622857883 : ℕ)^2048*1000000000000000^8271 ≤ 1000125125543537^8271*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100050542486622857883 100000000000000000000 1000125125543537 1000000000000000 2048 8271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000125125543537/1000000000000000 : ℝ)) (X := (100050542486622857883/100000000000000000000 : ℝ)) (by norm_num) 8271 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254464132455199477/6250000000000000000 : ℝ) ≤ (625110512723093/625000000000000 : ℝ) ^ (8271/2048 : ℝ) := by
    have hpowers : (6254464132455199477/6250000000000000000 : ℝ)^2048 ≤ (625110512723093/625000000000000 : ℝ)^8271 := by
      have hnat : (6254464132455199477 : ℕ)^2048*625000000000000^8271 ≤ 625110512723093^8271*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254464132455199477 6250000000000000000 625110512723093 625000000000000 2048 8271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625110512723093/625000000000000 : ℝ)) (X := (6254464132455199477/6250000000000000000 : ℝ)) (by norm_num) 8271 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14829426981262067/100000000000000000000 : ℝ) ≤ ((684758999776560269/685000000000000000 : ℝ)+2*(258474067059/137000000000000 : ℝ)*(1127/10000 : ℝ))^(8271/2048 : ℝ) := by
    rw [show (684758999776560269/685000000000000000 : ℝ)+2*(258474067059/137000000000000 : ℝ)*(1127/10000 : ℝ)=(2500183576825313/2500000000000000 : ℝ) by norm_num, show 1+2*(14829426981262067/100000000000000000000 : ℝ)=(50014829426981262067/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4464132455199477/12500000000000000000 : ℝ)+(14829426981262067/100000000000000000000 : ℝ) ≤ ((684758999776560269/685000000000000000 : ℝ)+(258474067059/137000000000000 : ℝ)*((1401/10000 : ℝ)+(1127/10000 : ℝ)))^(8271/2048 : ℝ) := by
    rw [show (684758999776560269/685000000000000000 : ℝ)+(258474067059/137000000000000 : ℝ)*((1401/10000 : ℝ)+(1127/10000 : ℝ))=(1000125125543537/1000000000000000 : ℝ) by norm_num, show 1+(4464132455199477/12500000000000000000 : ℝ)+(14829426981262067/100000000000000000000 : ℝ)=(100050542486622857883/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4464132455199477/12500000000000000000 : ℝ) ≤ ((684758999776560269/685000000000000000 : ℝ)+2*(258474067059/137000000000000 : ℝ)*(1401/10000 : ℝ))^(8271/2048 : ℝ) := by
    rw [show (684758999776560269/685000000000000000 : ℝ)+2*(258474067059/137000000000000 : ℝ)*(1401/10000 : ℝ)=(625110512723093/625000000000000 : ℝ) by norm_num, show 1+2*(4464132455199477/12500000000000000000 : ℝ)=(6254464132455199477/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (684758999776560269/685000000000000000 : ℝ)*(X 1 0+X 2 0)+(258474067059/137000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8271/2048 : ℝ)) (lo := (1127/10000 : ℝ)) (hi := (1401/10000 : ℝ)) (c := (684758999776560269/685000000000000000 : ℝ)) (alpha := (258474067059/137000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (684758999776560269/685000000000000000 : ℝ)*(X 0 1+X 2 1)+(258474067059/137000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8271/2048 : ℝ)) (lo := (1127/10000 : ℝ)) (hi := (1401/10000 : ℝ)) (c := (684758999776560269/685000000000000000 : ℝ)) (alpha := (258474067059/137000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (684758999776560269/685000000000000000 : ℝ)*(X 0 2+X 1 2)+(258474067059/137000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8271/2048 : ℝ)) (lo := (1127/10000 : ℝ)) (hi := (1401/10000 : ℝ)) (c := (684758999776560269/685000000000000000 : ℝ)) (alpha := (258474067059/137000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-129273701/625000000 : ℝ)*X 0 0+(537718753/1000000000 : ℝ)*X 0 1+(5377187169/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5295348813/10000000000 : ℝ)*X 1 0+(-2179201891/10000000000 : ℝ)*X 1 1+(5377187377/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1323837217/2500000000 : ℝ)*X 2 0+(134429683/250000000 : ℝ)*X 2 1+(-1089600947/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((280116267/625000000 : ℝ)*X 0 0+(4321663539/10000000000 : ℝ)*X 0 1+(2160831627/5000000000 : ℝ)*X 0 2+(280116267/625000000 : ℝ)*X 1 0+(4321663539/10000000000 : ℝ)*X 1 1+(2160831627/5000000000 : ℝ)*X 1 2+(280116267/625000000 : ℝ)*X 2 0+(4321663539/10000000000 : ℝ)*X 2 1+(2160831627/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-7274311/31250000 : ℝ)*X 0 0+(2640141859/5000000000 : ℝ)*X 0 1+(5280283627/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2681954607/5000000000 : ℝ)*X 1 0+(-88685093/400000000 : ℝ)*X 1 1+(1320070927/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5363908869/10000000000 : ℝ)*X 2 0+(264014167/500000000 : ℝ)*X 2 1+(-554282069/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4265060017/10000000000 : ℝ)*X 0 0+(4430042113/10000000000 : ℝ)*X 0 1+(1107510561/2500000000 : ℝ)*X 0 2+(4265060017/10000000000 : ℝ)*X 1 0+(4430042113/10000000000 : ℝ)*X 1 1+(1107510561/2500000000 : ℝ)*X 1 2+(4265060017/10000000000 : ℝ)*X 2 0+(4430042113/10000000000 : ℝ)*X 2 1+(1107510561/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2273611233/10000000000 : ℝ)*X 0 0+(5214503451/10000000000 : ℝ)*X 0 1+(5386788741/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((330534503/625000000 : ℝ)*X 1 0+(-435074513/2000000000 : ℝ)*X 1 1+(336674353/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5288551969/10000000000 : ℝ)*X 2 0+(5386788637/10000000000 : ℝ)*X 2 1+(-2175374033/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4503069243/10000000000 : ℝ)*X 0 0+(4310918417/10000000000 : ℝ)*X 0 1+(538864797/1250000000 : ℝ)*X 0 2+(4503069243/10000000000 : ℝ)*X 1 0+(4310918417/10000000000 : ℝ)*X 1 1+(538864797/1250000000 : ℝ)*X 1 2+(4503069243/10000000000 : ℝ)*X 2 0+(4310918417/10000000000 : ℝ)*X 2 1+(538864797/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-530726851/2500000000 : ℝ)*X 0 0+(340102667/625000000 : ℝ)*X 0 1+(52722763/100000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((107391437/200000000 : ℝ)*X 1 0+(-2220202097/10000000000 : ℝ)*X 1 1+(210891087/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5369572031/10000000000 : ℝ)*X 2 0+(2636137991/5000000000 : ℝ)*X 2 1+(-27752543/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((849382807/2000000000 : ℝ)*X 0 0+(4438992301/10000000000 : ℝ)*X 0 1+(4438994329/10000000000 : ℝ)*X 0 2+(849382807/2000000000 : ℝ)*X 1 0+(4438992301/10000000000 : ℝ)*X 1 1+(4438994329/10000000000 : ℝ)*X 1 2+(849382807/2000000000 : ℝ)*X 2 0+(4438992301/10000000000 : ℝ)*X 2 1+(4438994329/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-2489/4000 : ℝ) ≤ (-21311298786305635235190800028741/34250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (284120133/100000000000000 : ℝ)*(upper1) + (25883573/20000000000000 : ℝ)*(upper2) + (451201899/100000000000000 : ℝ)*(lower4) + (3087429/6250000000000 : ℝ)*(upper5) + (3867780823969921/100000000000000 : ℝ)*(major0) + (3867780823969921/100000000000000 : ℝ)*(major1) + (3867780823969921/100000000000000 : ℝ)*(major2) + (25176036329/100000000000000 : ℝ)*(sp2) + (8128221837/100000000000000 : ℝ)*(sp3) + (1286818435868013/25000000000000 : ℝ)*(sp4) + (2573433404735699/50000000000000 : ℝ)*(sp5) + (5147248567435723/100000000000000 : ℝ)*(sp6) + (1304510349819473/50000000000000 : ℝ)*(sp7) + (203467000327/50000000000000 : ℝ)*(sp13) + (163064301741299/6250000000000 : ℝ)*(f.failure) + (1286818435868013/25000000000000 : ℝ)*(f.sum) + (559876996239/6850000000000000000000000000 : ℝ)*base65 + (461494255836863749/68500000000000000000000000000000 : ℝ)*base67 + (117109022880363749/68500000000000000000000000000000 : ℝ)*base69 + (118833319128363749/68500000000000000000000000000000 : ℝ)*base71 + (36291493999289/6850000000000000000000000000 : ℝ)*base73 + (242946014225363749/68500000000000000000000000000000 : ℝ)*base75 + (58381946718863749/68500000000000000000000000000000 : ℝ)*base77 + (59244873002863749/68500000000000000000000000000000 : ℝ)*base79 + (55567465958539/6850000000000000000000000000 : ℝ)*base81 + (910701/312500000000000000000 : ℝ)*base89 + (910701/312500000000000000000 : ℝ)*base91 + (910701/312500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (59251/100000 : ℝ) ≤ (5073543917740430104789159120341/8562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (388183/4000000000000 : ℝ)*(upper3) + (11852613/20000000000000 : ℝ)*(upper4) + (21103951/25000000000000 : ℝ)*(lower5) + (982730781088937/25000000000000 : ℝ)*(major0) + (982730781088937/25000000000000 : ℝ)*(major1) + (982730781088937/25000000000000 : ℝ)*(major2) + (1038092765513447/20000000000000 : ℝ)*(sp0) + (1297616073515657/25000000000000 : ℝ)*(sp1) + (103809196278487/2000000000000 : ℝ)*(sp2) + (265161221178741/10000000000000 : ℝ)*(sp3) + (1836705191/20000000000000 : ℝ)*(sp5) + (1707958029/12500000000000 : ℝ)*(sp6) + (4768392341/50000000000000 : ℝ)*(sp7) + (9650021347/100000000000000 : ℝ)*(sp8) + (662905437143023/25000000000000 : ℝ)*(f.failure) + (5190473477588583/100000000000000 : ℝ)*(f.sum) + (3652276470209/3425000000000000000000000000 : ℝ)*base66 + (104177248272184053/17125000000000000000000000000000 : ℝ)*base67 + (68780033517690947/17125000000000000000000000000000 : ℝ)*base70 + (9358864214059053/17125000000000000000000000000000 : ℝ)*base71 + (20855539877959/3425000000000000000000000000 : ℝ)*base74 + (146778004692440947/17125000000000000000000000000000 : ℝ)*base76 + (55375460721809053/17125000000000000000000000000000 : ℝ)*base77 + (114298314507059053/17125000000000000000000000000000 : ℝ)*base79 + (8744191466117/1712500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (6685977/1250000000000000000000 : ℝ)*base89 + (6685977/1250000000000000000000 : ℝ)*base91 + (6685977/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (79613/100000 : ℝ) ≤ (27268357134509220203344505003787/34250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (49482041/25000000000000 : ℝ)*(upper0) + (4015021/50000000000000 : ℝ)*(lower1) + (83370487/20000000000000 : ℝ)*(upper2) + (861176807/100000000000000 : ℝ)*(lower5) + (4399133815329953/100000000000000 : ℝ)*(major0) + (4399133815329953/100000000000000 : ℝ)*(major1) + (4399133815329953/100000000000000 : ℝ)*(major2) + (5955795719/100000000000000 : ℝ)*(sp0) + (1364614903/250000000000 : ℝ)*(sp1) + (28143861897/10000000000000 : ℝ)*(sp3) + (1160853553326459/20000000000000 : ℝ)*(sp8) + (2901863938233407/50000000000000 : ℝ)*(sp9) + (1160854744485603/20000000000000 : ℝ)*(sp10) + (2967173922523361/100000000000000 : ℝ)*(sp11) + (2967455361142331/100000000000000 : ℝ)*(f.failure) + (1160854744485603/20000000000000 : ℝ)*(f.sum) + (3541441578827/6850000000000000000000000000 : ℝ)*base65 + (897711407199572357/68500000000000000000000000000000 : ℝ)*base67 + (944337868009572357/68500000000000000000000000000000 : ℝ)*base69 + (970367456119072357/68500000000000000000000000000000 : ℝ)*base71 + (184877999392223/6850000000000000000000000000 : ℝ)*base74 + (673242695038572357/68500000000000000000000000000000 : ℝ)*base75 + (508593827003572357/68500000000000000000000000000000 : ℝ)*base77 + (1110559303559572357/68500000000000000000000000000000 : ℝ)*base79 + (4644829685623/6850000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (10429331/5000000000000000000000 : ℝ)*base90 + (10429331/5000000000000000000000 : ℝ)*base92 + (10429331/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-41491/50000 : ℝ) ≤ (-14210252416900223273263799799681/17125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (179088947/50000000000000 : ℝ)*(lower1) + (73646731/50000000000000 : ℝ)*(upper3) + (315733547/50000000000000 : ℝ)*(lower4) + (1754881/50000000000000 : ℝ)*(upper5) + (2216901197027061/50000000000000 : ℝ)*(major0) + (2216901197027061/50000000000000 : ℝ)*(major1) + (2216901197027061/50000000000000 : ℝ)*(major2) + (2788868831/20000000000000 : ℝ)*(sp4) + (1303754259197/100000000000000 : ℝ)*(sp6) + (145160875507/25000000000000 : ℝ)*(sp7) + (1180881899347321/20000000000000 : ℝ)*(sp12) + (147610586027019/2500000000000 : ℝ)*(sp13) + (5903119686821563/100000000000000 : ℝ)*(sp14) + (186891285140279/6250000000000 : ℝ)*(sp15) + (747710301436623/25000000000000 : ℝ)*(f.failure) + (147610586027019/2500000000000 : ℝ)*(f.sum) + (5203267425201/3425000000000000000000000000 : ℝ)*base66 + (357964690436934409/34250000000000000000000000000000 : ℝ)*base67 + (1399001198233184409/34250000000000000000000000000000 : ℝ)*base69 + (363022763385434409/34250000000000000000000000000000 : ℝ)*base71 + (21485752538699/3425000000000000000000000000 : ℝ)*base73 + (457261783194434409/34250000000000000000000000000000 : ℝ)*base75 + (198176943259934409/34250000000000000000000000000000 : ℝ)*base77 + (147734731323934409/34250000000000000000000000000000 : ℝ)*base79 + (67181884872701/3425000000000000000000000000 : ℝ)*base82 + (19807623/1250000000000000000000 : ℝ)*base90 + (19807623/1250000000000000000000 : ℝ)*base92 + (19807623/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1079_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74122999/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1401/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1127/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2489/4000 : ℝ) ≤ X j i ∧ X j i ≤ -(59251/100000 : ℝ) else (79613/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41491/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1079_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1079_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74122999/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14011/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1127/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2489/4000 : ℝ) ≤ X j i ∧ X j i ≤ -(59251/100000 : ℝ) else (79613/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41491/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1079_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1079_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74122999/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14011/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1127/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2489/4000 : ℝ) ≤ X j i ∧ X j i ≤ -(59251/100000 : ℝ) else (79613/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41491/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1079_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
