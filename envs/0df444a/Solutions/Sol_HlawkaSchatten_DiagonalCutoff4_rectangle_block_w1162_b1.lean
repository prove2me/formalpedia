-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1162_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:40:25.825003+00:00
-- url     : https://prove2.me/submissions/d8100f84-b571-482e-a33d-4e8baee53f1a

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
theorem support_rectangle_w1162_s3_0 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-10768839/50000000 : ℝ)*x 0 + (5427152243/10000000000 : ℝ)*x 1 + (5233927667/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10768839/50000000 : ℝ)^8355 ≤ (13082061176111/100000000000000 : ℝ)^6307 := by
    have hnat : (10768839 : ℕ)^8355*100000000000000^6307 ≤ 13082061176111^6307*50000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10768839 50000000 13082061176111 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5427152243/10000000000 : ℝ)^8355 ≤ (44502315301409/100000000000000 : ℝ)^6307 := by
    have hnat : (5427152243 : ℕ)^8355*100000000000000^6307 ≤ 44502315301409^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427152243 10000000000 44502315301409 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5233927667/10000000000 : ℝ)^8355 ≤ (4241562350469/10000000000000 : ℝ)^6307 := by
    have hnat : (5233927667 : ℕ)^8355*10000000000000^6307 ≤ 4241562350469^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5233927667 10000000000 4241562350469 10000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-10768839/50000000 : ℝ), (5427152243/10000000000 : ℝ), (5233927667/10000000000 : ℝ)] ![(13082061176111/100000000000000 : ℝ), (44502315301409/100000000000000 : ℝ), (4241562350469/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-10768839/50000000 : ℝ)|^8355 ≤ (13082061176111/100000000000000 : ℝ)^6307
        have hw : |(-10768839/50000000 : ℝ)|=(10768839/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5427152243/10000000000 : ℝ)|^8355 ≤ (44502315301409/100000000000000 : ℝ)^6307
        have hw : |(5427152243/10000000000 : ℝ)|=(5427152243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5233927667/10000000000 : ℝ)|^8355 ≤ (4241562350469/10000000000000 : ℝ)^6307
        have hw : |(5233927667/10000000000 : ℝ)|=(5233927667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s3_1 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2676659327/5000000000 : ℝ)*x 0 + (-28156189/125000000 : ℝ)*x 1 + (209357099/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676659327/5000000000 : ℝ)^8355 ≤ (43702066730769/100000000000000 : ℝ)^6307 := by
    have hnat : (2676659327 : ℕ)^8355*100000000000000^6307 ≤ 43702066730769^6307*5000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676659327 5000000000 43702066730769 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (28156189/125000000 : ℝ)^8355 ≤ (6941155904601/50000000000000 : ℝ)^6307 := by
    have hnat : (28156189 : ℕ)^8355*50000000000000^6307 ≤ 6941155904601^6307*125000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28156189 125000000 6941155904601 50000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209357099/400000000 : ℝ)^8355 ≤ (42415621443477/100000000000000 : ℝ)^6307 := by
    have hnat : (209357099 : ℕ)^8355*100000000000000^6307 ≤ 42415621443477^6307*400000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209357099 400000000 42415621443477 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676659327/5000000000 : ℝ), (-28156189/125000000 : ℝ), (209357099/400000000 : ℝ)] ![(43702066730769/100000000000000 : ℝ), (6941155904601/50000000000000 : ℝ), (42415621443477/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676659327/5000000000 : ℝ)|^8355 ≤ (43702066730769/100000000000000 : ℝ)^6307
        have hw : |(2676659327/5000000000 : ℝ)|=(2676659327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-28156189/125000000 : ℝ)|^8355 ≤ (6941155904601/50000000000000 : ℝ)^6307
        have hw : |(-28156189/125000000 : ℝ)|=(28156189/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(209357099/400000000 : ℝ)|^8355 ≤ (42415621443477/100000000000000 : ℝ)^6307
        have hw : |(209357099/400000000 : ℝ)|=(209357099/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s3_2 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (334582421/625000000 : ℝ)*x 0 + (2616963749/5000000000 : ℝ)*x 1 + (-1126247491/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334582421/625000000 : ℝ)^8355 ≤ (874041352351/2000000000000 : ℝ)^6307 := by
    have hnat : (334582421 : ℕ)^8355*2000000000000^6307 ≤ 874041352351^6307*625000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334582421 625000000 874041352351 2000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2616963749/5000000000 : ℝ)^8355 ≤ (42415621690393/100000000000000 : ℝ)^6307 := by
    have hnat : (2616963749 : ℕ)^8355*100000000000000^6307 ≤ 42415621690393^6307*5000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2616963749 5000000000 42415621690393 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1126247491/5000000000 : ℝ)^8355 ≤ (6941155341261/50000000000000 : ℝ)^6307 := by
    have hnat : (1126247491 : ℕ)^8355*50000000000000^6307 ≤ 6941155341261^6307*5000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126247491 5000000000 6941155341261 50000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334582421/625000000 : ℝ), (2616963749/5000000000 : ℝ), (-1126247491/5000000000 : ℝ)] ![(874041352351/2000000000000 : ℝ), (42415621690393/100000000000000 : ℝ), (6941155341261/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334582421/625000000 : ℝ)|^8355 ≤ (874041352351/2000000000000 : ℝ)^6307
        have hw : |(334582421/625000000 : ℝ)|=(334582421/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2616963749/5000000000 : ℝ)|^8355 ≤ (42415621690393/100000000000000 : ℝ)^6307
        have hw : |(2616963749/5000000000 : ℝ)|=(2616963749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1126247491/5000000000 : ℝ)|^8355 ≤ (6941155341261/50000000000000 : ℝ)^6307
        have hw : |(-1126247491/5000000000 : ℝ)|=(1126247491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s3_3 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2179865037/5000000000 : ℝ)*x 0 + (260687003/625000000 : ℝ)*x 1 + (455691591/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2179865037/5000000000 : ℝ)^8355 ≤ (16647746123567/50000000000000 : ℝ)^6307 := by
    have hnat : (2179865037 : ℕ)^8355*50000000000000^6307 ≤ 16647746123567^6307*5000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179865037 5000000000 16647746123567 50000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (260687003/625000000 : ℝ)^8355 ≤ (31399593937307/100000000000000 : ℝ)^6307 := by
    have hnat : (260687003 : ℕ)^8355*100000000000000^6307 ≤ 31399593937307^6307*625000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260687003 625000000 31399593937307 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (455691591/1000000000 : ℝ)^8355 ≤ (35304913808479/100000000000000 : ℝ)^6307 := by
    have hnat : (455691591 : ℕ)^8355*100000000000000^6307 ≤ 35304913808479^6307*1000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      455691591 1000000000 35304913808479 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2179865037/5000000000 : ℝ), (260687003/625000000 : ℝ), (455691591/1000000000 : ℝ)] ![(16647746123567/50000000000000 : ℝ), (31399593937307/100000000000000 : ℝ), (35304913808479/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2179865037/5000000000 : ℝ)|^8355 ≤ (16647746123567/50000000000000 : ℝ)^6307
        have hw : |(2179865037/5000000000 : ℝ)|=(2179865037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(260687003/625000000 : ℝ)|^8355 ≤ (31399593937307/100000000000000 : ℝ)^6307
        have hw : |(260687003/625000000 : ℝ)|=(260687003/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(455691591/1000000000 : ℝ)|^8355 ≤ (35304913808479/100000000000000 : ℝ)^6307
        have hw : |(455691591/1000000000 : ℝ)|=(455691591/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s3_4 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-26922311/125000000 : ℝ)*x 0 + (654333363/1250000000 : ℝ)*x 1 + (1356602243/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26922311/125000000 : ℝ)^8355 ≤ (13082198608579/100000000000000 : ℝ)^6307 := by
    have hnat : (26922311 : ℕ)^8355*100000000000000^6307 ≤ 13082198608579^6307*125000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26922311 125000000 13082198608579 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (654333363/1250000000 : ℝ)^8355 ≤ (10605889939023/25000000000000 : ℝ)^6307 := by
    have hnat : (654333363 : ℕ)^8355*25000000000000^6307 ≤ 10605889939023^6307*1250000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654333363 1250000000 10605889939023 25000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1356602243/2500000000 : ℝ)^8355 ≤ (8898848323449/20000000000000 : ℝ)^6307 := by
    have hnat : (1356602243 : ℕ)^8355*20000000000000^6307 ≤ 8898848323449^6307*2500000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356602243 2500000000 8898848323449 20000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-26922311/125000000 : ℝ), (654333363/1250000000 : ℝ), (1356602243/2500000000 : ℝ)] ![(13082198608579/100000000000000 : ℝ), (10605889939023/25000000000000 : ℝ), (8898848323449/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-26922311/125000000 : ℝ)|^8355 ≤ (13082198608579/100000000000000 : ℝ)^6307
        have hw : |(-26922311/125000000 : ℝ)|=(26922311/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(654333363/1250000000 : ℝ)|^8355 ≤ (10605889939023/25000000000000 : ℝ)^6307
        have hw : |(654333363/1250000000 : ℝ)|=(654333363/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1356602243/2500000000 : ℝ)|^8355 ≤ (8898848323449/20000000000000 : ℝ)^6307
        have hw : |(1356602243/2500000000 : ℝ)|=(1356602243/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s3_5 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5304294681/10000000000 : ℝ)*x 0 + (-2060014391/10000000000 : ℝ)*x 1 + (1356602173/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304294681/10000000000 : ℝ)^8355 ≤ (539658646057/1250000000000 : ℝ)^6307 := by
    have hnat : (5304294681 : ℕ)^8355*1250000000000^6307 ≤ 539658646057^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304294681 10000000000 539658646057 1250000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2060014391/10000000000 : ℝ)^8355 ≤ (12333069723379/100000000000000 : ℝ)^6307 := by
    have hnat : (2060014391 : ℕ)^8355*100000000000000^6307 ≤ 12333069723379^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2060014391 10000000000 12333069723379 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1356602173/2500000000 : ℝ)^8355 ≤ (889884771517/2000000000000 : ℝ)^6307 := by
    have hnat : (1356602173 : ℕ)^8355*2000000000000^6307 ≤ 889884771517^6307*2500000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356602173 2500000000 889884771517 2000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304294681/10000000000 : ℝ), (-2060014391/10000000000 : ℝ), (1356602173/2500000000 : ℝ)] ![(539658646057/1250000000000 : ℝ), (12333069723379/100000000000000 : ℝ), (889884771517/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304294681/10000000000 : ℝ)|^8355 ≤ (539658646057/1250000000000 : ℝ)^6307
        have hw : |(5304294681/10000000000 : ℝ)|=(5304294681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2060014391/10000000000 : ℝ)|^8355 ≤ (12333069723379/100000000000000 : ℝ)^6307
        have hw : |(-2060014391/10000000000 : ℝ)|=(2060014391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1356602173/2500000000 : ℝ)|^8355 ≤ (889884771517/2000000000000 : ℝ)^6307
        have hw : |(1356602173/2500000000 : ℝ)|=(1356602173/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s3_6 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (530429601/1000000000 : ℝ)*x 0 + (5426407559/10000000000 : ℝ)*x 1 + (-257501767/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530429601/1000000000 : ℝ)^8355 ≤ (43172706014029/100000000000000 : ℝ)^6307 := by
    have hnat : (530429601 : ℕ)^8355*100000000000000^6307 ≤ 43172706014029^6307*1000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530429601 1000000000 43172706014029 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5426407559/10000000000 : ℝ)^8355 ≤ (44494226269059/100000000000000 : ℝ)^6307 := by
    have hnat : (5426407559 : ℕ)^8355*100000000000000^6307 ≤ 44494226269059^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426407559 10000000000 44494226269059 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (257501767/1250000000 : ℝ)^8355 ≤ (12333067700989/100000000000000 : ℝ)^6307 := by
    have hnat : (257501767 : ℕ)^8355*100000000000000^6307 ≤ 12333067700989^6307*1250000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257501767 1250000000 12333067700989 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530429601/1000000000 : ℝ), (5426407559/10000000000 : ℝ), (-257501767/1250000000 : ℝ)] ![(43172706014029/100000000000000 : ℝ), (44494226269059/100000000000000 : ℝ), (12333067700989/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530429601/1000000000 : ℝ)|^8355 ≤ (43172706014029/100000000000000 : ℝ)^6307
        have hw : |(530429601/1000000000 : ℝ)|=(530429601/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5426407559/10000000000 : ℝ)|^8355 ≤ (44494226269059/100000000000000 : ℝ)^6307
        have hw : |(5426407559/10000000000 : ℝ)|=(5426407559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-257501767/1250000000 : ℝ)|^8355 ≤ (12333067700989/100000000000000 : ℝ)^6307
        have hw : |(-257501767/1250000000 : ℝ)|=(257501767/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s3_7 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4359763871/10000000000 : ℝ)*x 0 + (4555439629/10000000000 : ℝ)*x 1 + (260779807/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4359763871/10000000000 : ℝ)^8355 ≤ (8323958542503/25000000000000 : ℝ)^6307 := by
    have hnat : (4359763871 : ℕ)^8355*25000000000000^6307 ≤ 8323958542503^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4359763871 10000000000 8323958542503 25000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4555439629/10000000000 : ℝ)^8355 ≤ (35289763064863/100000000000000 : ℝ)^6307 := by
    have hnat : (4555439629 : ℕ)^8355*100000000000000^6307 ≤ 35289763064863^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4555439629 10000000000 35289763064863 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (260779807/625000000 : ℝ)^8355 ≤ (31414402744219/100000000000000 : ℝ)^6307 := by
    have hnat : (260779807 : ℕ)^8355*100000000000000^6307 ≤ 31414402744219^6307*625000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260779807 625000000 31414402744219 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4359763871/10000000000 : ℝ), (4555439629/10000000000 : ℝ), (260779807/625000000 : ℝ)] ![(8323958542503/25000000000000 : ℝ), (35289763064863/100000000000000 : ℝ), (31414402744219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4359763871/10000000000 : ℝ)|^8355 ≤ (8323958542503/25000000000000 : ℝ)^6307
        have hw : |(4359763871/10000000000 : ℝ)|=(4359763871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4555439629/10000000000 : ℝ)|^8355 ≤ (35289763064863/100000000000000 : ℝ)^6307
        have hw : |(4555439629/10000000000 : ℝ)|=(4555439629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(260779807/625000000 : ℝ)|^8355 ≤ (31414402744219/100000000000000 : ℝ)^6307
        have hw : |(260779807/625000000 : ℝ)|=(260779807/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1162_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74932041/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4111/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (229/2500 : ℝ)*pair X i i ≤ pair X i h) :
    (10693/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7391/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4111/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (229/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4111/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (229/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4111/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (229/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4111/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (229/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4111/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (229/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4111/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (229/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (229/2500 : ℝ) ^ (4177/1024 : ℝ) ≤ (5827284269799777/100000000000000000000 : ℝ) := by
    have hpowers : (229/2500 : ℝ)^4177 ≤ (5827284269799777/100000000000000000000 : ℝ)^1024 := by
      have hnat : (229 : ℕ)^4177*100000000000000000000^1024 ≤ 5827284269799777^1024*2500^4177 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        229 2500 5827284269799777 100000000000000000000 4177 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (229/2500 : ℝ)) (X := (5827284269799777/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4177 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4111/25000 : ℝ) ^ (4177/1024 : ℝ) ≤ (63389136851726521/100000000000000000000 : ℝ) := by
    have hpowers : (4111/25000 : ℝ)^4177 ≤ (63389136851726521/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4111 : ℕ)^4177*100000000000000000000^1024 ≤ 63389136851726521^1024*25000^4177 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4111 25000 63389136851726521 100000000000000000000 4177 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4111/25000 : ℝ)) (X := (63389136851726521/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4177 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005827284269799777/50000000000000000000 : ℝ) ≤ (10000285701538559/10000000000000000 : ℝ) ^ (4177/1024 : ℝ) := by
    have hpowers : (50005827284269799777/50000000000000000000 : ℝ)^1024 ≤ (10000285701538559/10000000000000000 : ℝ)^4177 := by
      have hnat : (50005827284269799777 : ℕ)^1024*10000000000000000^4177 ≤ 10000285701538559^4177*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005827284269799777 50000000000000000000 10000285701538559 10000000000000000 1024 4177 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000285701538559/10000000000000000 : ℝ)) (X := (50005827284269799777/50000000000000000000 : ℝ)) (by norm_num) 4177 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50034608210560763149/50000000000000000000 : ℝ) ≤ (10001696411460321/10000000000000000 : ℝ) ^ (4177/1024 : ℝ) := by
    have hpowers : (50034608210560763149/50000000000000000000 : ℝ)^1024 ≤ (10001696411460321/10000000000000000 : ℝ)^4177 := by
      have hnat : (50034608210560763149 : ℕ)^1024*10000000000000000^4177 ≤ 10001696411460321^4177*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034608210560763149 50000000000000000000 10001696411460321 10000000000000000 1024 4177 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001696411460321/10000000000000000 : ℝ)) (X := (50034608210560763149/50000000000000000000 : ℝ)) (by norm_num) 4177 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50063389136851726521/50000000000000000000 : ℝ) ≤ (10003107121382083/10000000000000000 : ℝ) ^ (4177/1024 : ℝ) := by
    have hpowers : (50063389136851726521/50000000000000000000 : ℝ)^1024 ≤ (10003107121382083/10000000000000000 : ℝ)^4177 := by
      have hnat : (50063389136851726521 : ℕ)^1024*10000000000000000^4177 ≤ 10003107121382083^4177*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50063389136851726521 50000000000000000000 10003107121382083 10000000000000000 1024 4177 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003107121382083/10000000000000000 : ℝ)) (X := (50063389136851726521/50000000000000000000 : ℝ)) (by norm_num) 4177 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5827284269799777/100000000000000000000 : ℝ) ≤ ((18204059211060045979/18210000000000000000 : ℝ)+2*(705354960881/364200000000000 : ℝ)*(229/2500 : ℝ))^(4177/1024 : ℝ) := by
    rw [show (18204059211060045979/18210000000000000000 : ℝ)+2*(705354960881/364200000000000 : ℝ)*(229/2500 : ℝ)=(10000285701538559/10000000000000000 : ℝ) by norm_num, show 1+2*(5827284269799777/100000000000000000000 : ℝ)=(50005827284269799777/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(63389136851726521/100000000000000000000 : ℝ)+(5827284269799777/100000000000000000000 : ℝ) ≤ ((18204059211060045979/18210000000000000000 : ℝ)+(705354960881/364200000000000 : ℝ)*((4111/25000 : ℝ)+(229/2500 : ℝ)))^(4177/1024 : ℝ) := by
    rw [show (18204059211060045979/18210000000000000000 : ℝ)+(705354960881/364200000000000 : ℝ)*((4111/25000 : ℝ)+(229/2500 : ℝ))=(10001696411460321/10000000000000000 : ℝ) by norm_num, show 1+(63389136851726521/100000000000000000000 : ℝ)+(5827284269799777/100000000000000000000 : ℝ)=(50034608210560763149/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(63389136851726521/100000000000000000000 : ℝ) ≤ ((18204059211060045979/18210000000000000000 : ℝ)+2*(705354960881/364200000000000 : ℝ)*(4111/25000 : ℝ))^(4177/1024 : ℝ) := by
    rw [show (18204059211060045979/18210000000000000000 : ℝ)+2*(705354960881/364200000000000 : ℝ)*(4111/25000 : ℝ)=(10003107121382083/10000000000000000 : ℝ) by norm_num, show 1+2*(63389136851726521/100000000000000000000 : ℝ)=(50063389136851726521/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18204059211060045979/18210000000000000000 : ℝ)*(X 1 0+X 2 0)+(705354960881/364200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4177/1024 : ℝ)) (lo := (229/2500 : ℝ)) (hi := (4111/25000 : ℝ)) (c := (18204059211060045979/18210000000000000000 : ℝ)) (alpha := (705354960881/364200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18204059211060045979/18210000000000000000 : ℝ)*(X 0 1+X 2 1)+(705354960881/364200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4177/1024 : ℝ)) (lo := (229/2500 : ℝ)) (hi := (4111/25000 : ℝ)) (c := (18204059211060045979/18210000000000000000 : ℝ)) (alpha := (705354960881/364200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18204059211060045979/18210000000000000000 : ℝ)*(X 0 2+X 1 2)+(705354960881/364200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4177/1024 : ℝ)) (lo := (229/2500 : ℝ)) (hi := (4111/25000 : ℝ)) (c := (18204059211060045979/18210000000000000000 : ℝ)) (alpha := (705354960881/364200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-10768839/50000000 : ℝ)*X 0 0+(5427152243/10000000000 : ℝ)*X 0 1+(5233927667/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676659327/5000000000 : ℝ)*X 1 0+(-28156189/125000000 : ℝ)*X 1 1+(209357099/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334582421/625000000 : ℝ)*X 2 0+(2616963749/5000000000 : ℝ)*X 2 1+(-1126247491/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2179865037/5000000000 : ℝ)*X 0 0+(260687003/625000000 : ℝ)*X 0 1+(455691591/1000000000 : ℝ)*X 0 2+(2179865037/5000000000 : ℝ)*X 1 0+(260687003/625000000 : ℝ)*X 1 1+(455691591/1000000000 : ℝ)*X 1 2+(2179865037/5000000000 : ℝ)*X 2 0+(260687003/625000000 : ℝ)*X 2 1+(455691591/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-26922311/125000000 : ℝ)*X 0 0+(654333363/1250000000 : ℝ)*X 0 1+(1356602243/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5304294681/10000000000 : ℝ)*X 1 0+(-2060014391/10000000000 : ℝ)*X 1 1+(1356602173/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((530429601/1000000000 : ℝ)*X 2 0+(5426407559/10000000000 : ℝ)*X 2 1+(-257501767/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4359763871/10000000000 : ℝ)*X 0 0+(4555439629/10000000000 : ℝ)*X 0 1+(260779807/625000000 : ℝ)*X 0 2+(4359763871/10000000000 : ℝ)*X 1 0+(4555439629/10000000000 : ℝ)*X 1 1+(260779807/625000000 : ℝ)*X 1 2+(4359763871/10000000000 : ℝ)*X 2 0+(4555439629/10000000000 : ℝ)*X 2 1+(260779807/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (293469067580356016130492959/30350000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4480107/200000000000 : ℝ)*(base19) + (534009133/25000000000000 : ℝ)*(base23) + (6132617/6250000000000 : ℝ)*(lower2) + (202844159/100000000000000 : ℝ)*(upper3) + (56487667/25000000000000 : ℝ)*(upper5) + (388331210360621/10000000000000 : ℝ)*(major0) + (388331210360621/10000000000000 : ℝ)*(major1) + (388331210360621/10000000000000 : ℝ)*(major2) + (2587680712414327/50000000000000 : ℝ)*(sp0) + (2587699475198581/50000000000000 : ℝ)*(sp1) + (5175399054414131/100000000000000 : ℝ)*(sp2) + (647800822965917/25000000000000 : ℝ)*(sp3) + (4970702751/12500000000000 : ℝ)*(sp4) + (303165339/1562500000000 : ℝ)*(sp7) + (647805673611341/25000000000000 : ℝ)*(f.failure) + (5175401190450663/100000000000000 : ℝ)*(f.sum) + (1819192728133/1821000000000000000000000000 : ℝ)*base65 + (1343353785278157041/182100000000000000000000000000000 : ℝ)*base68 + (477331641808557041/182100000000000000000000000000000 : ℝ)*base70 + (351964510654442959/182100000000000000000000000000000 : ℝ)*base71 + (683586171133/1821000000000000000000000000 : ℝ)*base73 + (1219753333796157041/182100000000000000000000000000000 : ℝ)*base76 + (3458190169631642959/182100000000000000000000000000000 : ℝ)*base77 + (3314090988574557041/182100000000000000000000000000000 : ℝ)*base80 + (1605186084689/1821000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (3123019/1250000000000000000000 : ℝ)*base90 + (3123019/1250000000000000000000 : ℝ)*base92 + (3123019/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8879376461097608799496797/4742187500000000000000000000000 : ℝ) := by norm_num
    linear_combination (367593/10000000000000 : ℝ)*(base19) + (1327176409/100000000000000 : ℝ)*(base23) + (44412677/100000000000000 : ℝ)*(lower3) + (8058987/20000000000000 : ℝ)*(upper4) + (30572623897297/781250000000 : ℝ)*(major0) + (30572623897297/781250000000 : ℝ)*(major1) + (30572623897297/781250000000 : ℝ)*(major2) + (1297999157/25000000000000 : ℝ)*(sp0) + (2508897729/25000000000000 : ℝ)*(sp2) + (2669456409/100000000000000 : ℝ)*(sp3) + (208614258786913/4000000000000 : ℝ)*(sp4) + (5215361657993523/100000000000000 : ℝ)*(sp5) + (325959393681383/6250000000000 : ℝ)*(sp6) + (261122732416809/10000000000000 : ℝ)*(sp7) + (5222459987249/200000000000 : ℝ)*(f.failure) + (5215361661669453/100000000000000 : ℝ)*(f.sum) + (2141760786349/284531250000000000000000000 : ℝ)*base65 + (21761242086421097/3556640625000000000000000000000 : ℝ)*base67 + (3879831424241993/889160156250000000000000000000 : ℝ)*base69 + (418428951815853151/28453125000000000000000000000000 : ℝ)*base71 + (12408313234403/9105000000000000000000000000 : ℝ)*base73 + (82663936378545319/7113281250000000000000000000000 : ℝ)*base75 + (106729729864543763/14226562500000000000000000000000 : ℝ)*base77 + (52929988436764069/7113281250000000000000000000000 : ℝ)*base79 + (32607037743649/4552500000000000000000000000 : ℝ)*base81 + (54791/10000000000000000000 : ℝ)*base90 + (54791/10000000000000000000 : ℝ)*base92 + (54791/10000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1162_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74932041/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4111/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (229/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10693/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7391/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1162_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1162_s4_0 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2156617893/10000000000 : ℝ)*x 0 + (5400949899/10000000000 : ℝ)*x 1 + (1051652897/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2156617893/10000000000 : ℝ)^8355 ≤ (3276249763303/25000000000000 : ℝ)^6307 := by
    have hnat : (2156617893 : ℕ)^8355*25000000000000^6307 ≤ 3276249763303^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2156617893 10000000000 3276249763303 25000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5400949899/10000000000 : ℝ)^8355 ≤ (44217912786029/100000000000000 : ℝ)^6307 := by
    have hnat : (5400949899 : ℕ)^8355*100000000000000^6307 ≤ 44217912786029^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400949899 10000000000 44217912786029 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1051652897/2000000000 : ℝ)^8355 ≤ (42677088140807/100000000000000 : ℝ)^6307 := by
    have hnat : (1051652897 : ℕ)^8355*100000000000000^6307 ≤ 42677088140807^6307*2000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051652897 2000000000 42677088140807 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2156617893/10000000000 : ℝ), (5400949899/10000000000 : ℝ), (1051652897/2000000000 : ℝ)] ![(3276249763303/25000000000000 : ℝ), (44217912786029/100000000000000 : ℝ), (42677088140807/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2156617893/10000000000 : ℝ)|^8355 ≤ (3276249763303/25000000000000 : ℝ)^6307
        have hw : |(-2156617893/10000000000 : ℝ)|=(2156617893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5400949899/10000000000 : ℝ)|^8355 ≤ (44217912786029/100000000000000 : ℝ)^6307
        have hw : |(5400949899/10000000000 : ℝ)|=(5400949899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1051652897/2000000000 : ℝ)|^8355 ≤ (42677088140807/100000000000000 : ℝ)^6307
        have hw : |(1051652897/2000000000 : ℝ)|=(1051652897/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s4_1 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5346761041/10000000000 : ℝ)*x 0 + (-139319647/625000000 : ℝ)*x 1 + (1051652937/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346761041/10000000000 : ℝ)^8355 ≤ (8726232835327/20000000000000 : ℝ)^6307 := by
    have hnat : (5346761041 : ℕ)^8355*20000000000000^6307 ≤ 8726232835327^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346761041 10000000000 8726232835327 20000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (139319647/625000000 : ℝ)^8355 ≤ (547669820643/4000000000000 : ℝ)^6307 := by
    have hnat : (139319647 : ℕ)^8355*4000000000000^6307 ≤ 547669820643^6307*625000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      139319647 625000000 547669820643 4000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1051652937/2000000000 : ℝ)^8355 ≤ (42677090291141/100000000000000 : ℝ)^6307 := by
    have hnat : (1051652937 : ℕ)^8355*100000000000000^6307 ≤ 42677090291141^6307*2000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051652937 2000000000 42677090291141 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346761041/10000000000 : ℝ), (-139319647/625000000 : ℝ), (1051652937/2000000000 : ℝ)] ![(8726232835327/20000000000000 : ℝ), (547669820643/4000000000000 : ℝ), (42677090291141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346761041/10000000000 : ℝ)|^8355 ≤ (8726232835327/20000000000000 : ℝ)^6307
        have hw : |(5346761041/10000000000 : ℝ)|=(5346761041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-139319647/625000000 : ℝ)|^8355 ≤ (547669820643/4000000000000 : ℝ)^6307
        have hw : |(-139319647/625000000 : ℝ)|=(139319647/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1051652937/2000000000 : ℝ)|^8355 ≤ (42677090291141/100000000000000 : ℝ)^6307
        have hw : |(1051652937/2000000000 : ℝ)|=(1051652937/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s4_2 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (213870439/400000000 : ℝ)*x 0 + (5258264731/10000000000 : ℝ)*x 1 + (-111455719/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213870439/400000000 : ℝ)^8355 ≤ (43631163463169/100000000000000 : ℝ)^6307 := by
    have hnat : (213870439 : ℕ)^8355*100000000000000^6307 ≤ 43631163463169^6307*400000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213870439 400000000 43631163463169 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5258264731/10000000000 : ℝ)^8355 ≤ (21338545392859/50000000000000 : ℝ)^6307 := by
    have hnat : (5258264731 : ℕ)^8355*50000000000000^6307 ≤ 21338545392859^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258264731 10000000000 21338545392859 50000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (111455719/500000000 : ℝ)^8355 ≤ (13691745743903/100000000000000 : ℝ)^6307 := by
    have hnat : (111455719 : ℕ)^8355*100000000000000^6307 ≤ 13691745743903^6307*500000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111455719 500000000 13691745743903 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213870439/400000000 : ℝ), (5258264731/10000000000 : ℝ), (-111455719/500000000 : ℝ)] ![(43631163463169/100000000000000 : ℝ), (21338545392859/50000000000000 : ℝ), (13691745743903/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213870439/400000000 : ℝ)|^8355 ≤ (43631163463169/100000000000000 : ℝ)^6307
        have hw : |(213870439/400000000 : ℝ)|=(213870439/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5258264731/10000000000 : ℝ)|^8355 ≤ (21338545392859/50000000000000 : ℝ)^6307
        have hw : |(5258264731/10000000000 : ℝ)|=(5258264731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-111455719/500000000 : ℝ)|^8355 ≤ (13691745743903/100000000000000 : ℝ)^6307
        have hw : |(-111455719/500000000 : ℝ)|=(111455719/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s4_3 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2180714899/5000000000 : ℝ)*x 0 + (4221242967/10000000000 : ℝ)*x 1 + (4506225783/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2180714899/5000000000 : ℝ)^8355 ≤ (4164086169079/12500000000000 : ℝ)^6307 := by
    have hnat : (2180714899 : ℕ)^8355*12500000000000^6307 ≤ 4164086169079^6307*5000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180714899 5000000000 4164086169079 12500000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4221242967/10000000000 : ℝ)^8355 ≤ (31901703727731/100000000000000 : ℝ)^6307 := by
    have hnat : (4221242967 : ℕ)^8355*100000000000000^6307 ≤ 31901703727731^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4221242967 10000000000 31901703727731 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4506225783/10000000000 : ℝ)^8355 ≤ (4348200862421/12500000000000 : ℝ)^6307 := by
    have hnat : (4506225783 : ℕ)^8355*12500000000000^6307 ≤ 4348200862421^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4506225783 10000000000 4348200862421 12500000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2180714899/5000000000 : ℝ), (4221242967/10000000000 : ℝ), (4506225783/10000000000 : ℝ)] ![(4164086169079/12500000000000 : ℝ), (31901703727731/100000000000000 : ℝ), (4348200862421/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2180714899/5000000000 : ℝ)|^8355 ≤ (4164086169079/12500000000000 : ℝ)^6307
        have hw : |(2180714899/5000000000 : ℝ)|=(2180714899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4221242967/10000000000 : ℝ)|^8355 ≤ (31901703727731/100000000000000 : ℝ)^6307
        have hw : |(4221242967/10000000000 : ℝ)|=(4221242967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4506225783/10000000000 : ℝ)|^8355 ≤ (4348200862421/12500000000000 : ℝ)^6307
        have hw : |(4506225783/10000000000 : ℝ)|=(4506225783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s4_4 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1078312469/5000000000 : ℝ)*x 0 + (5258668449/10000000000 : ℝ)*x 1 + (2700272097/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1078312469/5000000000 : ℝ)^8355 ≤ (6552527882193/50000000000000 : ℝ)^6307 := by
    have hnat : (1078312469 : ℕ)^8355*50000000000000^6307 ≤ 6552527882193^6307*5000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078312469 5000000000 6552527882193 50000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5258668449/10000000000 : ℝ)^8355 ≤ (42681431483101/100000000000000 : ℝ)^6307 := by
    have hnat : (5258668449 : ℕ)^8355*100000000000000^6307 ≤ 42681431483101^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258668449 10000000000 42681431483101 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2700272097/5000000000 : ℝ)^8355 ≤ (5526689093061/12500000000000 : ℝ)^6307 := by
    have hnat : (2700272097 : ℕ)^8355*12500000000000^6307 ≤ 5526689093061^6307*5000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700272097 5000000000 5526689093061 12500000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1078312469/5000000000 : ℝ), (5258668449/10000000000 : ℝ), (2700272097/5000000000 : ℝ)] ![(6552527882193/50000000000000 : ℝ), (42681431483101/100000000000000 : ℝ), (5526689093061/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1078312469/5000000000 : ℝ)|^8355 ≤ (6552527882193/50000000000000 : ℝ)^6307
        have hw : |(-1078312469/5000000000 : ℝ)|=(1078312469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5258668449/10000000000 : ℝ)|^8355 ≤ (42681431483101/100000000000000 : ℝ)^6307
        have hw : |(5258668449/10000000000 : ℝ)|=(5258668449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2700272097/5000000000 : ℝ)|^8355 ≤ (5526689093061/12500000000000 : ℝ)^6307
        have hw : |(2700272097/5000000000 : ℝ)|=(2700272097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s4_5 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2655280173/5000000000 : ℝ)*x 0 + (-1043417223/5000000000 : ℝ)*x 1 + (1350136027/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655280173/5000000000 : ℝ)^8355 ≤ (21620130968303/50000000000000 : ℝ)^6307 := by
    have hnat : (2655280173 : ℕ)^8355*50000000000000^6307 ≤ 21620130968303^6307*5000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655280173 5000000000 21620130968303 50000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043417223/5000000000 : ℝ)^8355 ≤ (12546226231953/100000000000000 : ℝ)^6307 := by
    have hnat : (1043417223 : ℕ)^8355*100000000000000^6307 ≤ 12546226231953^6307*5000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043417223 5000000000 12546226231953 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1350136027/2500000000 : ℝ)^8355 ≤ (44213511811793/100000000000000 : ℝ)^6307 := by
    have hnat : (1350136027 : ℕ)^8355*100000000000000^6307 ≤ 44213511811793^6307*2500000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350136027 2500000000 44213511811793 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655280173/5000000000 : ℝ), (-1043417223/5000000000 : ℝ), (1350136027/2500000000 : ℝ)] ![(21620130968303/50000000000000 : ℝ), (12546226231953/100000000000000 : ℝ), (44213511811793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655280173/5000000000 : ℝ)|^8355 ≤ (21620130968303/50000000000000 : ℝ)^6307
        have hw : |(2655280173/5000000000 : ℝ)|=(2655280173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1043417223/5000000000 : ℝ)|^8355 ≤ (12546226231953/100000000000000 : ℝ)^6307
        have hw : |(-1043417223/5000000000 : ℝ)|=(1043417223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1350136027/2500000000 : ℝ)|^8355 ≤ (44213511811793/100000000000000 : ℝ)^6307
        have hw : |(1350136027/2500000000 : ℝ)|=(1350136027/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s4_6 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5310560117/10000000000 : ℝ)*x 0 + (5400544103/10000000000 : ℝ)*x 1 + (-2086834763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310560117/10000000000 : ℝ)^8355 ≤ (43240259466549/100000000000000 : ℝ)^6307 := by
    have hnat : (5310560117 : ℕ)^8355*100000000000000^6307 ≤ 43240259466549^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310560117 10000000000 43240259466549 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5400544103/10000000000 : ℝ)^8355 ≤ (44213511757567/100000000000000 : ℝ)^6307 := by
    have hnat : (5400544103 : ℕ)^8355*100000000000000^6307 ≤ 44213511757567^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400544103 10000000000 44213511757567 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2086834763/10000000000 : ℝ)^8355 ≤ (6273114378321/50000000000000 : ℝ)^6307 := by
    have hnat : (2086834763 : ℕ)^8355*50000000000000^6307 ≤ 6273114378321^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086834763 10000000000 6273114378321 50000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310560117/10000000000 : ℝ), (5400544103/10000000000 : ℝ), (-2086834763/10000000000 : ℝ)] ![(43240259466549/100000000000000 : ℝ), (44213511757567/100000000000000 : ℝ), (6273114378321/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310560117/10000000000 : ℝ)|^8355 ≤ (43240259466549/100000000000000 : ℝ)^6307
        have hw : |(5310560117/10000000000 : ℝ)|=(5310560117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5400544103/10000000000 : ℝ)|^8355 ≤ (44213511757567/100000000000000 : ℝ)^6307
        have hw : |(5400544103/10000000000 : ℝ)|=(5400544103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2086834763/10000000000 : ℝ)|^8355 ≤ (6273114378321/50000000000000 : ℝ)^6307
        have hw : |(-2086834763/10000000000 : ℝ)|=(2086834763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s4_7 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2180721697/5000000000 : ℝ)*x 0 + (4505418691/10000000000 : ℝ)*x 1 + (2111026787/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2180721697/5000000000 : ℝ)^8355 ≤ (832820673003/2500000000000 : ℝ)^6307 := by
    have hnat : (2180721697 : ℕ)^8355*2500000000000^6307 ≤ 832820673003^6307*5000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180721697 5000000000 832820673003 2500000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4505418691/10000000000 : ℝ)^8355 ≤ (34777353731613/100000000000000 : ℝ)^6307 := by
    have hnat : (4505418691 : ℕ)^8355*100000000000000^6307 ≤ 34777353731613^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4505418691 10000000000 34777353731613 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2111026787/5000000000 : ℝ)^8355 ≤ (31909819335327/100000000000000 : ℝ)^6307 := by
    have hnat : (2111026787 : ℕ)^8355*100000000000000^6307 ≤ 31909819335327^6307*5000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111026787 5000000000 31909819335327 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2180721697/5000000000 : ℝ), (4505418691/10000000000 : ℝ), (2111026787/5000000000 : ℝ)] ![(832820673003/2500000000000 : ℝ), (34777353731613/100000000000000 : ℝ), (31909819335327/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2180721697/5000000000 : ℝ)|^8355 ≤ (832820673003/2500000000000 : ℝ)^6307
        have hw : |(2180721697/5000000000 : ℝ)|=(2180721697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4505418691/10000000000 : ℝ)|^8355 ≤ (34777353731613/100000000000000 : ℝ)^6307
        have hw : |(4505418691/10000000000 : ℝ)|=(4505418691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2111026787/5000000000 : ℝ)|^8355 ≤ (31909819335327/100000000000000 : ℝ)^6307
        have hw : |(2111026787/5000000000 : ℝ)|=(2111026787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1162_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74932041/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7391/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10693/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11213/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7117/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7391/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10693/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7391/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10693/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7391/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10693/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7391/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10693/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7391/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10693/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7391/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10693/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10693/100000 : ℝ) ^ (4177/1024 : ℝ) ≤ (10954650493028089/100000000000000000000 : ℝ) := by
    have hpowers : (10693/100000 : ℝ)^4177 ≤ (10954650493028089/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10693 : ℕ)^4177*100000000000000000000^1024 ≤ 10954650493028089^1024*100000^4177 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10693 100000 10954650493028089 100000000000000000000 4177 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10693/100000 : ℝ)) (X := (10954650493028089/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4177 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7391/50000 : ℝ) ^ (4177/1024 : ℝ) ≤ (4104472879929711/10000000000000000000 : ℝ) := by
    have hpowers : (7391/50000 : ℝ)^4177 ≤ (4104472879929711/10000000000000000000 : ℝ)^1024 := by
      have hnat : (7391 : ℕ)^4177*10000000000000000000^1024 ≤ 4104472879929711^1024*50000^4177 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7391 50000 4104472879929711 10000000000000000000 4177 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7391/50000 : ℝ)) (X := (4104472879929711/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4177 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010954650493028089/50000000000000000000 : ℝ) ≤ (10000537066537361/10000000000000000 : ℝ) ^ (4177/1024 : ℝ) := by
    have hpowers : (50010954650493028089/50000000000000000000 : ℝ)^1024 ≤ (10000537066537361/10000000000000000 : ℝ)^4177 := by
      have hnat : (50010954650493028089 : ℕ)^1024*10000000000000000^4177 ≤ 10000537066537361^4177*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010954650493028089 50000000000000000000 10000537066537361 10000000000000000 1024 4177 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000537066537361/10000000000000000 : ℝ)) (X := (50010954650493028089/50000000000000000000 : ℝ)) (by norm_num) 4177 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051999379292325199/100000000000000000000 : ℝ) ≤ (10001274525193791/10000000000000000 : ℝ) ^ (4177/1024 : ℝ) := by
    have hpowers : (100051999379292325199/100000000000000000000 : ℝ)^1024 ≤ (10001274525193791/10000000000000000 : ℝ)^4177 := by
      have hnat : (100051999379292325199 : ℕ)^1024*10000000000000000^4177 ≤ 10001274525193791^4177*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051999379292325199 100000000000000000000 10001274525193791 10000000000000000 1024 4177 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001274525193791/10000000000000000 : ℝ)) (X := (100051999379292325199/100000000000000000000 : ℝ)) (by norm_num) 4177 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5004104472879929711/5000000000000000000 : ℝ) ≤ (10002011983850221/10000000000000000 : ℝ) ^ (4177/1024 : ℝ) := by
    have hpowers : (5004104472879929711/5000000000000000000 : ℝ)^1024 ≤ (10002011983850221/10000000000000000 : ℝ)^4177 := by
      have hnat : (5004104472879929711 : ℕ)^1024*10000000000000000^4177 ≤ 10002011983850221^4177*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5004104472879929711 5000000000000000000 10002011983850221 10000000000000000 1024 4177 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002011983850221/10000000000000000 : ℝ)) (X := (5004104472879929711/5000000000000000000 : ℝ)) (by norm_num) 4177 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10954650493028089/100000000000000000000 : ℝ) ≤ ((40876424774244857149/40890000000000000000 : ℝ)+2*(73745865643/40890000000000 : ℝ)*(10693/100000 : ℝ))^(4177/1024 : ℝ) := by
    rw [show (40876424774244857149/40890000000000000000 : ℝ)+2*(73745865643/40890000000000 : ℝ)*(10693/100000 : ℝ)=(10000537066537361/10000000000000000 : ℝ) by norm_num, show 1+2*(10954650493028089/100000000000000000000 : ℝ)=(50010954650493028089/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4104472879929711/10000000000000000000 : ℝ)+(10954650493028089/100000000000000000000 : ℝ) ≤ ((40876424774244857149/40890000000000000000 : ℝ)+(73745865643/40890000000000 : ℝ)*((7391/50000 : ℝ)+(10693/100000 : ℝ)))^(4177/1024 : ℝ) := by
    rw [show (40876424774244857149/40890000000000000000 : ℝ)+(73745865643/40890000000000 : ℝ)*((7391/50000 : ℝ)+(10693/100000 : ℝ))=(10001274525193791/10000000000000000 : ℝ) by norm_num, show 1+(4104472879929711/10000000000000000000 : ℝ)+(10954650493028089/100000000000000000000 : ℝ)=(100051999379292325199/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4104472879929711/10000000000000000000 : ℝ) ≤ ((40876424774244857149/40890000000000000000 : ℝ)+2*(73745865643/40890000000000 : ℝ)*(7391/50000 : ℝ))^(4177/1024 : ℝ) := by
    rw [show (40876424774244857149/40890000000000000000 : ℝ)+2*(73745865643/40890000000000 : ℝ)*(7391/50000 : ℝ)=(10002011983850221/10000000000000000 : ℝ) by norm_num, show 1+2*(4104472879929711/10000000000000000000 : ℝ)=(5004104472879929711/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (40876424774244857149/40890000000000000000 : ℝ)*(X 1 0+X 2 0)+(73745865643/40890000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4177/1024 : ℝ)) (lo := (10693/100000 : ℝ)) (hi := (7391/50000 : ℝ)) (c := (40876424774244857149/40890000000000000000 : ℝ)) (alpha := (73745865643/40890000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (40876424774244857149/40890000000000000000 : ℝ)*(X 0 1+X 2 1)+(73745865643/40890000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4177/1024 : ℝ)) (lo := (10693/100000 : ℝ)) (hi := (7391/50000 : ℝ)) (c := (40876424774244857149/40890000000000000000 : ℝ)) (alpha := (73745865643/40890000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (40876424774244857149/40890000000000000000 : ℝ)*(X 0 2+X 1 2)+(73745865643/40890000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4177/1024 : ℝ)) (lo := (10693/100000 : ℝ)) (hi := (7391/50000 : ℝ)) (c := (40876424774244857149/40890000000000000000 : ℝ)) (alpha := (73745865643/40890000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2156617893/10000000000 : ℝ)*X 0 0+(5400949899/10000000000 : ℝ)*X 0 1+(1051652897/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346761041/10000000000 : ℝ)*X 1 0+(-139319647/625000000 : ℝ)*X 1 1+(1051652937/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((213870439/400000000 : ℝ)*X 2 0+(5258264731/10000000000 : ℝ)*X 2 1+(-111455719/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2180714899/5000000000 : ℝ)*X 0 0+(4221242967/10000000000 : ℝ)*X 0 1+(4506225783/10000000000 : ℝ)*X 0 2+(2180714899/5000000000 : ℝ)*X 1 0+(4221242967/10000000000 : ℝ)*X 1 1+(4506225783/10000000000 : ℝ)*X 1 2+(2180714899/5000000000 : ℝ)*X 2 0+(4221242967/10000000000 : ℝ)*X 2 1+(4506225783/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1078312469/5000000000 : ℝ)*X 0 0+(5258668449/10000000000 : ℝ)*X 0 1+(2700272097/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2655280173/5000000000 : ℝ)*X 1 0+(-1043417223/5000000000 : ℝ)*X 1 1+(1350136027/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5310560117/10000000000 : ℝ)*X 2 0+(5400544103/10000000000 : ℝ)*X 2 1+(-2086834763/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2180721697/5000000000 : ℝ)*X 0 0+(4505418691/10000000000 : ℝ)*X 0 1+(2111026787/5000000000 : ℝ)*X 0 2+(2180721697/5000000000 : ℝ)*X 1 0+(4505418691/10000000000 : ℝ)*X 1 1+(2111026787/5000000000 : ℝ)*X 1 2+(2180721697/5000000000 : ℝ)*X 2 0+(4505418691/10000000000 : ℝ)*X 2 1+(2111026787/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (780180836902379019064097189/170375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (831856651/100000000000000 : ℝ)*(base19) + (357898787/50000000000000 : ℝ)*(base23) + (7899029/50000000000000 : ℝ)*(lower2) + (545971/312500000000 : ℝ)*(upper3) + (19311997/20000000000000 : ℝ)*(upper5) + (2629372089198961/50000000000000 : ℝ)*(major0) + (2629372089198961/50000000000000 : ℝ)*(major1) + (2629372089198961/50000000000000 : ℝ)*(major2) + (7008453873148973/100000000000000 : ℝ)*(sp0) + (3504239168383347/50000000000000 : ℝ)*(sp1) + (7008478452825771/100000000000000 : ℝ)*(sp2) + (3508995658380873/100000000000000 : ℝ)*(sp3) + (25295474373/100000000000000 : ℝ)*(sp4) + (2675430337/20000000000000 : ℝ)*(sp7) + (1754504517766279/50000000000000 : ℝ)*(f.failure) + (3504239584311673/50000000000000 : ℝ)*(f.sum) + (30693790381817/4089000000000000000000000000 : ℝ)*base66 + (12132857637777777811/2044500000000000000000000000000000 : ℝ)*base68 + (38712398873004777811/2044500000000000000000000000000000 : ℝ)*base70 + (20854010278203777811/2044500000000000000000000000000000 : ℝ)*base72 + (1267004044349/408900000000000000000000000 : ℝ)*base74 + (53855738379021722189/2044500000000000000000000000000000 : ℝ)*base75 + (7506529383263277811/2044500000000000000000000000000000 : ℝ)*base78 + (5217789033944277811/2044500000000000000000000000000000 : ℝ)*base80 + (20609289993749/4089000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (3554561/2500000000000000000000 : ℝ)*base90 + (3554561/2500000000000000000000 : ℝ)*base92 + (3554561/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18756603743695594243314837/85187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1069800787/100000000000000 : ℝ)*(base19) + (101992881/10000000000000 : ℝ)*(base23) + (183206701/100000000000000 : ℝ)*(upper2) + (108130601/100000000000000 : ℝ)*(upper5) + (661089901805613/12500000000000 : ℝ)*(major0) + (661089901805613/12500000000000 : ℝ)*(major1) + (661089901805613/12500000000000 : ℝ)*(major2) + (1062560917/20000000000000 : ℝ)*(sp0) + (17817899871/50000000000000 : ℝ)*(sp1) + (5574559269/25000000000000 : ℝ)*(sp2) + (7048422592106603/100000000000000 : ℝ)*(sp4) + (7048391199310659/100000000000000 : ℝ)*(sp5) + (3524202293372651/50000000000000 : ℝ)*(sp6) + (3529010516639273/100000000000000 : ℝ)*(sp7) + (3529010516639273/100000000000000 : ℝ)*(f.failure) + (1762106976227797/25000000000000 : ℝ)*(f.sum) + (8583123107739/1363000000000000000000000000 : ℝ)*base65 + (1931888993419249221/170375000000000000000000000000000 : ℝ)*base68 + (1367569699013249221/170375000000000000000000000000000 : ℝ)*base70 + (205476510489124221/170375000000000000000000000000000 : ℝ)*base72 + (5365119675987/1363000000000000000000000000 : ℝ)*base74 + (1044433362113874221/170375000000000000000000000000000 : ℝ)*base76 + (941275021101625779/170375000000000000000000000000000 : ℝ)*base77 + (371024732205750779/170375000000000000000000000000000 : ℝ)*base79 + (6007952259/13630000000000000000000000 : ℝ)*base82 + (13353807/5000000000000000000000 : ℝ)*base90 + (13353807/5000000000000000000000 : ℝ)*base92 + (13353807/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1162_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74932041/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7391/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10693/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11213/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1162_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1162_s5_0 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1078604843/5000000000 : ℝ)*x 0 + (2697195337/5000000000 : ℝ)*x 1 + (1052887081/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1078604843/5000000000 : ℝ)^8355 ≤ (1310976310621/10000000000000 : ℝ)^6307 := by
    have hnat : (1078604843 : ℕ)^8355*10000000000000^6307 ≤ 1310976310621^6307*5000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078604843 5000000000 1310976310621 10000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697195337/5000000000 : ℝ)^8355 ≤ (4414678839243/10000000000000 : ℝ)^6307 := by
    have hnat : (2697195337 : ℕ)^8355*10000000000000^6307 ≤ 4414678839243^6307*5000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697195337 5000000000 4414678839243 10000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052887081/2000000000 : ℝ)^8355 ≤ (42743448482399/100000000000000 : ℝ)^6307 := by
    have hnat : (1052887081 : ℕ)^8355*100000000000000^6307 ≤ 42743448482399^6307*2000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052887081 2000000000 42743448482399 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1078604843/5000000000 : ℝ), (2697195337/5000000000 : ℝ), (1052887081/2000000000 : ℝ)] ![(1310976310621/10000000000000 : ℝ), (4414678839243/10000000000000 : ℝ), (42743448482399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1078604843/5000000000 : ℝ)|^8355 ≤ (1310976310621/10000000000000 : ℝ)^6307
        have hw : |(-1078604843/5000000000 : ℝ)|=(1078604843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697195337/5000000000 : ℝ)|^8355 ≤ (4414678839243/10000000000000 : ℝ)^6307
        have hw : |(2697195337/5000000000 : ℝ)|=(2697195337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052887081/2000000000 : ℝ)|^8355 ≤ (42743448482399/100000000000000 : ℝ)^6307
        have hw : |(1052887081/2000000000 : ℝ)|=(1052887081/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s5_1 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345113041/10000000000 : ℝ)*x 0 + (-1111572991/5000000000 : ℝ)*x 1 + (5264435207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345113041/10000000000 : ℝ)^8355 ≤ (43613350025961/100000000000000 : ℝ)^6307 := by
    have hnat : (5345113041 : ℕ)^8355*100000000000000^6307 ≤ 43613350025961^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345113041 10000000000 43613350025961 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1111572991/5000000000 : ℝ)^8355 ≤ (13643203603381/100000000000000 : ℝ)^6307 := by
    have hnat : (1111572991 : ℕ)^8355*100000000000000^6307 ≤ 13643203603381^6307*5000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1111572991 5000000000 13643203603381 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264435207/10000000000 : ℝ)^8355 ≤ (42743446352757/100000000000000 : ℝ)^6307 := by
    have hnat : (5264435207 : ℕ)^8355*100000000000000^6307 ≤ 42743446352757^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264435207 10000000000 42743446352757 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345113041/10000000000 : ℝ), (-1111572991/5000000000 : ℝ), (5264435207/10000000000 : ℝ)] ![(43613350025961/100000000000000 : ℝ), (13643203603381/100000000000000 : ℝ), (42743446352757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345113041/10000000000 : ℝ)|^8355 ≤ (43613350025961/100000000000000 : ℝ)^6307
        have hw : |(5345113041/10000000000 : ℝ)|=(5345113041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1111572991/5000000000 : ℝ)|^8355 ≤ (13643203603381/100000000000000 : ℝ)^6307
        have hw : |(-1111572991/5000000000 : ℝ)|=(1111572991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264435207/10000000000 : ℝ)|^8355 ≤ (42743446352757/100000000000000 : ℝ)^6307
        have hw : |(5264435207/10000000000 : ℝ)|=(5264435207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s5_2 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336278387/2500000000 : ℝ)*x 0 + (5264434671/10000000000 : ℝ)*x 1 + (-69473313/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336278387/2500000000 : ℝ)^8355 ≤ (43613355506133/100000000000000 : ℝ)^6307 := by
    have hnat : (1336278387 : ℕ)^8355*100000000000000^6307 ≤ 43613355506133^6307*2500000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336278387 2500000000 43613355506133 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264434671/10000000000 : ℝ)^8355 ≤ (21371720293833/50000000000000 : ℝ)^6307 := by
    have hnat : (5264434671 : ℕ)^8355*50000000000000^6307 ≤ 21371720293833^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264434671 10000000000 21371720293833 50000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (69473313/312500000 : ℝ)^8355 ≤ (13643203879789/100000000000000 : ℝ)^6307 := by
    have hnat : (69473313 : ℕ)^8355*100000000000000^6307 ≤ 13643203879789^6307*312500000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69473313 312500000 13643203879789 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336278387/2500000000 : ℝ), (5264434671/10000000000 : ℝ), (-69473313/312500000 : ℝ)] ![(43613355506133/100000000000000 : ℝ), (21371720293833/50000000000000 : ℝ), (13643203879789/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336278387/2500000000 : ℝ)|^8355 ≤ (43613355506133/100000000000000 : ℝ)^6307
        have hw : |(1336278387/2500000000 : ℝ)|=(1336278387/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264434671/10000000000 : ℝ)|^8355 ≤ (21371720293833/50000000000000 : ℝ)^6307
        have hw : |(5264434671/10000000000 : ℝ)|=(5264434671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-69473313/312500000 : ℝ)|^8355 ≤ (13643203879789/100000000000000 : ℝ)^6307
        have hw : |(-69473313/312500000 : ℝ)|=(69473313/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s5_3 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4361777233/10000000000 : ℝ)*x 0 + (2116955097/5000000000 : ℝ)*x 1 + (4493468769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4361777233/10000000000 : ℝ)^8355 ≤ (8329051206101/25000000000000 : ℝ)^6307 := by
    have hnat : (4361777233 : ℕ)^8355*25000000000000^6307 ≤ 8329051206101^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4361777233 10000000000 8329051206101 25000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2116955097/5000000000 : ℝ)^8355 ≤ (8007145707951/25000000000000 : ℝ)^6307 := by
    have hnat : (2116955097 : ℕ)^8355*25000000000000^6307 ≤ 8007145707951^6307*5000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116955097 5000000000 8007145707951 25000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4493468769/10000000000 : ℝ)^8355 ≤ (34655212330789/100000000000000 : ℝ)^6307 := by
    have hnat : (4493468769 : ℕ)^8355*100000000000000^6307 ≤ 34655212330789^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4493468769 10000000000 34655212330789 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4361777233/10000000000 : ℝ), (2116955097/5000000000 : ℝ), (4493468769/10000000000 : ℝ)] ![(8329051206101/25000000000000 : ℝ), (8007145707951/25000000000000 : ℝ), (34655212330789/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4361777233/10000000000 : ℝ)|^8355 ≤ (8329051206101/25000000000000 : ℝ)^6307
        have hw : |(4361777233/10000000000 : ℝ)|=(4361777233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2116955097/5000000000 : ℝ)|^8355 ≤ (8007145707951/25000000000000 : ℝ)^6307
        have hw : |(2116955097/5000000000 : ℝ)|=(2116955097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4493468769/10000000000 : ℝ)|^8355 ≤ (34655212330789/100000000000000 : ℝ)^6307
        have hw : |(4493468769/10000000000 : ℝ)|=(4493468769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s5_4 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-107860759/500000000 : ℝ)*x 0 + (2632385533/5000000000 : ℝ)*x 1 + (5394053573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107860759/500000000 : ℝ)^8355 ≤ (6554903668003/50000000000000 : ℝ)^6307 := by
    have hnat : (107860759 : ℕ)^8355*50000000000000^6307 ≤ 6554903668003^6307*500000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107860759 500000000 6554903668003 50000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632385533/5000000000 : ℝ)^8355 ≤ (42747058811229/100000000000000 : ℝ)^6307 := by
    have hnat : (2632385533 : ℕ)^8355*100000000000000^6307 ≤ 42747058811229^6307*5000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632385533 5000000000 42747058811229 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394053573/10000000000 : ℝ)^8355 ≤ (21554264563/48828125000 : ℝ)^6307 := by
    have hnat : (5394053573 : ℕ)^8355*48828125000^6307 ≤ 21554264563^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394053573 10000000000 21554264563 48828125000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-107860759/500000000 : ℝ), (2632385533/5000000000 : ℝ), (5394053573/10000000000 : ℝ)] ![(6554903668003/50000000000000 : ℝ), (42747058811229/100000000000000 : ℝ), (21554264563/48828125000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-107860759/500000000 : ℝ)|^8355 ≤ (6554903668003/50000000000000 : ℝ)^6307
        have hw : |(-107860759/500000000 : ℝ)|=(107860759/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632385533/5000000000 : ℝ)|^8355 ≤ (42747058811229/100000000000000 : ℝ)^6307
        have hw : |(2632385533/5000000000 : ℝ)|=(2632385533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394053573/10000000000 : ℝ)|^8355 ≤ (21554264563/48828125000 : ℝ)^6307
        have hw : |(5394053573/10000000000 : ℝ)|=(5394053573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s5_5 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312141619/10000000000 : ℝ)*x 0 + (-261690693/1250000000 : ℝ)*x 1 + (2697026941/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312141619/10000000000 : ℝ)^8355 ≤ (10814329702641/25000000000000 : ℝ)^6307 := by
    have hnat : (5312141619 : ℕ)^8355*25000000000000^6307 ≤ 10814329702641^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312141619 10000000000 10814329702641 25000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (261690693/1250000000 : ℝ)^8355 ≤ (2519908800823/20000000000000 : ℝ)^6307 := by
    have hnat : (261690693 : ℕ)^8355*20000000000000^6307 ≤ 2519908800823^6307*1250000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261690693 1250000000 2519908800823 20000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697026941/5000000000 : ℝ)^8355 ≤ (44143137174909/100000000000000 : ℝ)^6307 := by
    have hnat : (2697026941 : ℕ)^8355*100000000000000^6307 ≤ 44143137174909^6307*5000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697026941 5000000000 44143137174909 100000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312141619/10000000000 : ℝ), (-261690693/1250000000 : ℝ), (2697026941/5000000000 : ℝ)] ![(10814329702641/25000000000000 : ℝ), (2519908800823/20000000000000 : ℝ), (44143137174909/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312141619/10000000000 : ℝ)|^8355 ≤ (10814329702641/25000000000000 : ℝ)^6307
        have hw : |(5312141619/10000000000 : ℝ)|=(5312141619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-261690693/1250000000 : ℝ)|^8355 ≤ (2519908800823/20000000000000 : ℝ)^6307
        have hw : |(-261690693/1250000000 : ℝ)|=(261690693/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697026941/5000000000 : ℝ)|^8355 ≤ (44143137174909/100000000000000 : ℝ)^6307
        have hw : |(2697026941/5000000000 : ℝ)|=(2697026941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s5_6 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656070367/5000000000 : ℝ)*x 0 + (674256819/1250000000 : ℝ)*x 1 + (-209352583/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656070367/5000000000 : ℝ)^8355 ≤ (21628654631893/50000000000000 : ℝ)^6307 := by
    have hnat : (2656070367 : ℕ)^8355*50000000000000^6307 ≤ 21628654631893^6307*5000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656070367 5000000000 21628654631893 50000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674256819/1250000000 : ℝ)^8355 ≤ (2758946527401/6250000000000 : ℝ)^6307 := by
    have hnat : (674256819 : ℕ)^8355*6250000000000^6307 ≤ 2758946527401^6307*1250000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674256819 1250000000 2758946527401 6250000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209352583/1000000000 : ℝ)^8355 ≤ (314988657107/2500000000000 : ℝ)^6307 := by
    have hnat : (209352583 : ℕ)^8355*2500000000000^6307 ≤ 314988657107^6307*1000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209352583 1000000000 314988657107 2500000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656070367/5000000000 : ℝ), (674256819/1250000000 : ℝ), (-209352583/1000000000 : ℝ)] ![(21628654631893/50000000000000 : ℝ), (2758946527401/6250000000000 : ℝ), (314988657107/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656070367/5000000000 : ℝ)|^8355 ≤ (21628654631893/50000000000000 : ℝ)^6307
        have hw : |(2656070367/5000000000 : ℝ)|=(2656070367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674256819/1250000000 : ℝ)|^8355 ≤ (2758946527401/6250000000000 : ℝ)^6307
        have hw : |(674256819/1250000000 : ℝ)|=(674256819/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-209352583/1000000000 : ℝ)|^8355 ≤ (314988657107/2500000000000 : ℝ)^6307
        have hw : |(-209352583/1000000000 : ℝ)|=(209352583/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1162_s5_7 (p : ℝ) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4361788319/10000000000 : ℝ)*x 0 + (898559683/2000000000 : ℝ)*x 1 + (4234582397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4361788319/10000000000 : ℝ)^8355 ≤ (1665815849901/5000000000000 : ℝ)^6307 := by
    have hnat : (4361788319 : ℕ)^8355*5000000000000^6307 ≤ 1665815849901^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4361788319 10000000000 1665815849901 5000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (898559683/2000000000 : ℝ)^8355 ≤ (3464836369383/10000000000000 : ℝ)^6307 := by
    have hnat : (898559683 : ℕ)^8355*10000000000000^6307 ≤ 3464836369383^6307*2000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898559683 2000000000 3464836369383 10000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4234582397/10000000000 : ℝ)^8355 ≤ (8008829821437/25000000000000 : ℝ)^6307 := by
    have hnat : (4234582397 : ℕ)^8355*25000000000000^6307 ≤ 8008829821437^6307*10000000000^8355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4234582397 10000000000 8008829821437 25000000000000 8355 6307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8355/2048 : ℝ)) 8355 6307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4361788319/10000000000 : ℝ), (898559683/2000000000 : ℝ), (4234582397/10000000000 : ℝ)] ![(1665815849901/5000000000000 : ℝ), (3464836369383/10000000000000 : ℝ), (8008829821437/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4361788319/10000000000 : ℝ)|^8355 ≤ (1665815849901/5000000000000 : ℝ)^6307
        have hw : |(4361788319/10000000000 : ℝ)|=(4361788319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(898559683/2000000000 : ℝ)|^8355 ≤ (3464836369383/10000000000000 : ℝ)^6307
        have hw : |(898559683/2000000000 : ℝ)|=(898559683/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4234582397/10000000000 : ℝ)|^8355 ≤ (8008829821437/25000000000000 : ℝ)^6307
        have hw : |(4234582397/10000000000 : ℝ)|=(4234582397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1162_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74932041/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11213/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (709/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14097/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7117/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11213/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7117/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11213/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11213/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11213/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11213/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11213/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11213/100000 : ℝ) ^ (4177/1024 : ℝ) ≤ (13295932447560459/100000000000000000000 : ℝ) := by
    have hpowers : (11213/100000 : ℝ)^4177 ≤ (13295932447560459/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11213 : ℕ)^4177*100000000000000000000^1024 ≤ 13295932447560459^1024*100000^4177 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11213 100000 13295932447560459 100000000000000000000 4177 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11213/100000 : ℝ)) (X := (13295932447560459/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4177 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7117/50000 : ℝ) ^ (4177/1024 : ℝ) ≤ (35183147228957753/100000000000000000000 : ℝ) := by
    have hpowers : (7117/50000 : ℝ)^4177 ≤ (35183147228957753/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7117 : ℕ)^4177*100000000000000000000^1024 ≤ 35183147228957753^1024*50000^4177 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7117 50000 35183147228957753 100000000000000000000 4177 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7117/50000 : ℝ)) (X := (35183147228957753/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4177 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013295932447560459/50000000000000000000 : ℝ) ≤ (1000065183952973/1000000000000000 : ℝ) ^ (4177/1024 : ℝ) := by
    have hpowers : (50013295932447560459/50000000000000000000 : ℝ)^1024 ≤ (1000065183952973/1000000000000000 : ℝ)^4177 := by
      have hnat : (50013295932447560459 : ℕ)^1024*1000000000000000^4177 ≤ 1000065183952973^4177*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013295932447560459 50000000000000000000 1000065183952973 1000000000000000 1024 4177 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000065183952973/1000000000000000 : ℝ)) (X := (50013295932447560459/50000000000000000000 : ℝ)) (by norm_num) 4177 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25012119769919129553/25000000000000000000 : ℝ) ≤ (1000118825704999/1000000000000000 : ℝ) ^ (4177/1024 : ℝ) := by
    have hpowers : (25012119769919129553/25000000000000000000 : ℝ)^1024 ≤ (1000118825704999/1000000000000000 : ℝ)^4177 := by
      have hnat : (25012119769919129553 : ℕ)^1024*1000000000000000^4177 ≤ 1000118825704999^4177*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012119769919129553 25000000000000000000 1000118825704999 1000000000000000 1024 4177 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000118825704999/1000000000000000 : ℝ)) (X := (25012119769919129553/25000000000000000000 : ℝ)) (by norm_num) 4177 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035183147228957753/50000000000000000000 : ℝ) ≤ (40006898698281/40000000000000 : ℝ) ^ (4177/1024 : ℝ) := by
    have hpowers : (50035183147228957753/50000000000000000000 : ℝ)^1024 ≤ (40006898698281/40000000000000 : ℝ)^4177 := by
      have hnat : (50035183147228957753 : ℕ)^1024*40000000000000^4177 ≤ 40006898698281^4177*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035183147228957753 50000000000000000000 40006898698281 40000000000000 1024 4177 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (40006898698281/40000000000000 : ℝ)) (X := (50035183147228957753/50000000000000000000 : ℝ)) (by norm_num) 4177 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13295932447560459/100000000000000000000 : ℝ) ≤ ((3019993950790996357/3021000000000000000 : ℝ)+2*(26820876013/15105000000000 : ℝ)*(11213/100000 : ℝ))^(4177/1024 : ℝ) := by
    rw [show (3019993950790996357/3021000000000000000 : ℝ)+2*(26820876013/15105000000000 : ℝ)*(11213/100000 : ℝ)=(1000065183952973/1000000000000000 : ℝ) by norm_num, show 1+2*(13295932447560459/100000000000000000000 : ℝ)=(50013295932447560459/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35183147228957753/100000000000000000000 : ℝ)+(13295932447560459/100000000000000000000 : ℝ) ≤ ((3019993950790996357/3021000000000000000 : ℝ)+(26820876013/15105000000000 : ℝ)*((7117/50000 : ℝ)+(11213/100000 : ℝ)))^(4177/1024 : ℝ) := by
    rw [show (3019993950790996357/3021000000000000000 : ℝ)+(26820876013/15105000000000 : ℝ)*((7117/50000 : ℝ)+(11213/100000 : ℝ))=(1000118825704999/1000000000000000 : ℝ) by norm_num, show 1+(35183147228957753/100000000000000000000 : ℝ)+(13295932447560459/100000000000000000000 : ℝ)=(25012119769919129553/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35183147228957753/100000000000000000000 : ℝ) ≤ ((3019993950790996357/3021000000000000000 : ℝ)+2*(26820876013/15105000000000 : ℝ)*(7117/50000 : ℝ))^(4177/1024 : ℝ) := by
    rw [show (3019993950790996357/3021000000000000000 : ℝ)+2*(26820876013/15105000000000 : ℝ)*(7117/50000 : ℝ)=(40006898698281/40000000000000 : ℝ) by norm_num, show 1+2*(35183147228957753/100000000000000000000 : ℝ)=(50035183147228957753/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3019993950790996357/3021000000000000000 : ℝ)*(X 1 0+X 2 0)+(26820876013/15105000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4177/1024 : ℝ)) (lo := (11213/100000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (3019993950790996357/3021000000000000000 : ℝ)) (alpha := (26820876013/15105000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3019993950790996357/3021000000000000000 : ℝ)*(X 0 1+X 2 1)+(26820876013/15105000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4177/1024 : ℝ)) (lo := (11213/100000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (3019993950790996357/3021000000000000000 : ℝ)) (alpha := (26820876013/15105000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3019993950790996357/3021000000000000000 : ℝ)*(X 0 2+X 1 2)+(26820876013/15105000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4177/1024 : ℝ)) (lo := (11213/100000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (3019993950790996357/3021000000000000000 : ℝ)) (alpha := (26820876013/15105000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1078604843/5000000000 : ℝ)*X 0 0+(2697195337/5000000000 : ℝ)*X 0 1+(1052887081/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345113041/10000000000 : ℝ)*X 1 0+(-1111572991/5000000000 : ℝ)*X 1 1+(5264435207/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336278387/2500000000 : ℝ)*X 2 0+(5264434671/10000000000 : ℝ)*X 2 1+(-69473313/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4361777233/10000000000 : ℝ)*X 0 0+(2116955097/5000000000 : ℝ)*X 0 1+(4493468769/10000000000 : ℝ)*X 0 2+(4361777233/10000000000 : ℝ)*X 1 0+(2116955097/5000000000 : ℝ)*X 1 1+(4493468769/10000000000 : ℝ)*X 1 2+(4361777233/10000000000 : ℝ)*X 2 0+(2116955097/5000000000 : ℝ)*X 2 1+(4493468769/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-107860759/500000000 : ℝ)*X 0 0+(2632385533/5000000000 : ℝ)*X 0 1+(5394053573/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312141619/10000000000 : ℝ)*X 1 0+(-261690693/1250000000 : ℝ)*X 1 1+(2697026941/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656070367/5000000000 : ℝ)*X 2 0+(674256819/1250000000 : ℝ)*X 2 1+(-209352583/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4361788319/10000000000 : ℝ)*X 0 0+(898559683/2000000000 : ℝ)*X 0 1+(4234582397/10000000000 : ℝ)*X 0 2+(4361788319/10000000000 : ℝ)*X 1 0+(898559683/2000000000 : ℝ)*X 1 1+(4234582397/10000000000 : ℝ)*X 1 2+(4361788319/10000000000 : ℝ)*X 2 0+(898559683/2000000000 : ℝ)*X 2 1+(4234582397/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1162_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (745624403032037182602585753/50350000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (321735033/100000000000000 : ℝ)*(base19) + (25420011/25000000000000 : ℝ)*(base23) + (263480861/50000000000000 : ℝ)*(lower2) + (11568631/12500000000000 : ℝ)*(lower4) + (39181941/100000000000000 : ℝ)*(upper5) + (5773819746260229/100000000000000 : ℝ)*(major0) + (5773819746260229/100000000000000 : ℝ)*(major1) + (5773819746260229/100000000000000 : ℝ)*(major2) + (3847467411205511/50000000000000 : ℝ)*(sp0) + (769493450067599/10000000000000 : ℝ)*(sp1) + (7694912477438181/100000000000000 : ℝ)*(sp2) + (3852696168243471/100000000000000 : ℝ)*(sp3) + (22243292797/100000000000000 : ℝ)*(sp6) + (8008238409/100000000000000 : ℝ)*(sp7) + (3852704176481879/100000000000000 : ℝ)*(f.failure) + (3847467411205511/50000000000000 : ℝ)*(f.sum) + (1067184253609/503500000000000000000000000 : ℝ)*base66 + (1458172771153104749/100700000000000000000000000000000 : ℝ)*base68 + (919528828134604749/100700000000000000000000000000000 : ℝ)*base70 + (452282265839995251/100700000000000000000000000000000 : ℝ)*base71 + (518762503133/1007000000000000000000000000 : ℝ)*base73 + (1460947012348604749/100700000000000000000000000000000 : ℝ)*base76 + (1120579467722795251/100700000000000000000000000000000 : ℝ)*base77 + (971854866450004749/100700000000000000000000000000000 : ℝ)*base80 + (701118297737/503500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (57014961/5000000000000000000000 : ℝ)*base90 + (57014961/5000000000000000000000 : ℝ)*base92 + (57014961/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (17069268104862226734626613/5035000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1161069949/50000000000000 : ℝ)*(base19) + (2170116011/100000000000000 : ℝ)*(base23) + (8009877/25000000000000 : ℝ)*(upper3) + (583781083/100000000000000 : ℝ)*(lower4) + (1160771510475791/20000000000000 : ℝ)*(major0) + (1160771510475791/20000000000000 : ℝ)*(major1) + (1160771510475791/20000000000000 : ℝ)*(major2) + (98483965371/100000000000000 : ℝ)*(sp1) + (104547261621/100000000000000 : ℝ)*(sp2) + (3262057389/20000000000000 : ℝ)*(sp3) + (3867483724749087/50000000000000 : ℝ)*(sp4) + (1546973328678581/20000000000000 : ℝ)*(sp5) + (3867430366060271/50000000000000 : ℝ)*(sp6) + (96818280799217/2500000000000 : ℝ)*(sp7) + (484093442781953/12500000000000 : ℝ)*(f.failure) + (3867483724749087/50000000000000 : ℝ)*(f.sum) + (231710761433/120840000000000000000000000 : ℝ)*base66 + (413213582789471129/20140000000000000000000000000000 : ℝ)*base67 + (124874653620051129/20140000000000000000000000000000 : ℝ)*base69 + (397137925479891129/20140000000000000000000000000000 : ℝ)*base71 + (2250051835247/755250000000000000000000000 : ℝ)*base74 + (84703159242648871/20140000000000000000000000000000 : ℝ)*base76 + (314169529297691129/20140000000000000000000000000000 : ℝ)*base77 + (308629878014731129/20140000000000000000000000000000 : ℝ)*base79 + (9182041273589/3021000000000000000000000000 : ℝ)*base82 + (12493927/625000000000000000000 : ℝ)*base90 + (12493927/625000000000000000000 : ℝ)*base92 + (12493927/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1162_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74932041/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11213/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (709/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14097/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1162_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1162_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74932041/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4111/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (229/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (709/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14097/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1162_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1162_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1162_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4177/1024 : ℝ) ≤ p) (hpb : p ≤ (8355/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74932041/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4111/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (229/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (709/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14097/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1162_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
