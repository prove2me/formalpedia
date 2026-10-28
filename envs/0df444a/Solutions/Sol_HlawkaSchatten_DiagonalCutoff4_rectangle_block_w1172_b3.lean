-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1172_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:46:35.994202+00:00
-- url     : https://prove2.me/submissions/0854e8f5-7e48-4b23-88fd-5a29de466669

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
theorem support_rectangle_w1172_s9_0 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2152625439/10000000000 : ℝ)*x 0 + (5392440359/10000000000 : ℝ)*x 1 + (5266257707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2152625439/10000000000 : ℝ)^8365 ≤ (1308319534183/10000000000000 : ℝ)^6317 := by
    have hnat : (2152625439 : ℕ)^8365*10000000000000^6317 ≤ 1308319534183^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2152625439 10000000000 1308319534183 10000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392440359/10000000000 : ℝ)^8365 ≤ (44139656259327/100000000000000 : ℝ)^6317 := by
    have hnat : (5392440359 : ℕ)^8365*100000000000000^6317 ≤ 44139656259327^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392440359 10000000000 44139656259327 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266257707/10000000000 : ℝ)^8365 ≤ (42777148377939/100000000000000 : ℝ)^6317 := by
    have hnat : (5266257707 : ℕ)^8365*100000000000000^6317 ≤ 42777148377939^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266257707 10000000000 42777148377939 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2152625439/10000000000 : ℝ), (5392440359/10000000000 : ℝ), (5266257707/10000000000 : ℝ)] ![(1308319534183/10000000000000 : ℝ), (44139656259327/100000000000000 : ℝ), (42777148377939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2152625439/10000000000 : ℝ)|^8365 ≤ (1308319534183/10000000000000 : ℝ)^6317
        have hw : |(-2152625439/10000000000 : ℝ)|=(2152625439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392440359/10000000000 : ℝ)|^8365 ≤ (44139656259327/100000000000000 : ℝ)^6317
        have hw : |(5392440359/10000000000 : ℝ)|=(5392440359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266257707/10000000000 : ℝ)|^8365 ≤ (42777148377939/100000000000000 : ℝ)^6317
        have hw : |(5266257707/10000000000 : ℝ)|=(5266257707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s9_1 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068925597/2000000000 : ℝ)*x 0 + (-13853871/62500000 : ℝ)*x 1 + (526625769/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068925597/2000000000 : ℝ)^8365 ≤ (6815961411/15625000000 : ℝ)^6317 := by
    have hnat : (1068925597 : ℕ)^8365*15625000000^6317 ≤ 6815961411^6317*2000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068925597 2000000000 6815961411 15625000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (13853871/62500000 : ℝ)^8365 ≤ (13600698755899/100000000000000 : ℝ)^6317 := by
    have hnat : (13853871 : ℕ)^8365*100000000000000^6317 ≤ 13600698755899^6317*62500000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13853871 62500000 13600698755899 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526625769/1000000000 : ℝ)^8365 ≤ (42777148195081/100000000000000 : ℝ)^6317 := by
    have hnat : (526625769 : ℕ)^8365*100000000000000^6317 ≤ 42777148195081^6317*1000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526625769 1000000000 42777148195081 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068925597/2000000000 : ℝ), (-13853871/62500000 : ℝ), (526625769/1000000000 : ℝ)] ![(6815961411/15625000000 : ℝ), (13600698755899/100000000000000 : ℝ), (42777148195081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068925597/2000000000 : ℝ)|^8365 ≤ (6815961411/15625000000 : ℝ)^6317
        have hw : |(1068925597/2000000000 : ℝ)|=(1068925597/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-13853871/62500000 : ℝ)|^8365 ≤ (13600698755899/100000000000000 : ℝ)^6317
        have hw : |(-13853871/62500000 : ℝ)|=(13853871/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526625769/1000000000 : ℝ)|^8365 ≤ (42777148195081/100000000000000 : ℝ)^6317
        have hw : |(526625769/1000000000 : ℝ)|=(526625769/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s9_2 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344627971/10000000000 : ℝ)*x 0 + (1316564429/2500000000 : ℝ)*x 1 + (-138538709/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344627971/10000000000 : ℝ)^8365 ≤ (2726384554943/6250000000000 : ℝ)^6317 := by
    have hnat : (5344627971 : ℕ)^8365*6250000000000^6317 ≤ 2726384554943^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344627971 10000000000 2726384554943 6250000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316564429/2500000000 : ℝ)^8365 ≤ (21388574237373/50000000000000 : ℝ)^6317 := by
    have hnat : (1316564429 : ℕ)^8365*50000000000000^6317 ≤ 21388574237373^6317*2500000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316564429 2500000000 21388574237373 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (138538709/625000000 : ℝ)^8365 ≤ (6800349312949/50000000000000 : ℝ)^6317 := by
    have hnat : (138538709 : ℕ)^8365*50000000000000^6317 ≤ 6800349312949^6317*625000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138538709 625000000 6800349312949 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344627971/10000000000 : ℝ), (1316564429/2500000000 : ℝ), (-138538709/625000000 : ℝ)] ![(2726384554943/6250000000000 : ℝ), (21388574237373/50000000000000 : ℝ), (6800349312949/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344627971/10000000000 : ℝ)|^8365 ≤ (2726384554943/6250000000000 : ℝ)^6317
        have hw : |(5344627971/10000000000 : ℝ)|=(5344627971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316564429/2500000000 : ℝ)|^8365 ≤ (21388574237373/50000000000000 : ℝ)^6317
        have hw : |(1316564429/2500000000 : ℝ)|=(1316564429/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-138538709/625000000 : ℝ)|^8365 ≤ (6800349312949/50000000000000 : ℝ)^6317
        have hw : |(-138538709/625000000 : ℝ)|=(138538709/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s9_3 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4360466269/10000000000 : ℝ)*x 0 + (4236014911/10000000000 : ℝ)*x 1 + (4488530109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4360466269/10000000000 : ℝ)^8365 ≤ (33317152417083/100000000000000 : ℝ)^6317 := by
    have hnat : (4360466269 : ℕ)^8365*100000000000000^6317 ≤ 33317152417083^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4360466269 10000000000 33317152417083 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4236014911/10000000000 : ℝ)^8365 ≤ (16031915334221/50000000000000 : ℝ)^6317 := by
    have hnat : (4236014911 : ℕ)^8365*50000000000000^6317 ≤ 16031915334221^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4236014911 10000000000 16031915334221 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4488530109/10000000000 : ℝ)^8365 ≤ (1730950845059/5000000000000 : ℝ)^6317 := by
    have hnat : (4488530109 : ℕ)^8365*5000000000000^6317 ≤ 1730950845059^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4488530109 10000000000 1730950845059 5000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4360466269/10000000000 : ℝ), (4236014911/10000000000 : ℝ), (4488530109/10000000000 : ℝ)] ![(33317152417083/100000000000000 : ℝ), (16031915334221/50000000000000 : ℝ), (1730950845059/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4360466269/10000000000 : ℝ)|^8365 ≤ (33317152417083/100000000000000 : ℝ)^6317
        have hw : |(4360466269/10000000000 : ℝ)|=(4360466269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4236014911/10000000000 : ℝ)|^8365 ≤ (16031915334221/50000000000000 : ℝ)^6317
        have hw : |(4236014911/10000000000 : ℝ)|=(4236014911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4488530109/10000000000 : ℝ)|^8365 ≤ (1730950845059/5000000000000 : ℝ)^6317
        have hw : |(4488530109/10000000000 : ℝ)|=(4488530109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s9_4 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2152630221/10000000000 : ℝ)*x 0 + (2633287411/5000000000 : ℝ)*x 1 + (5392122113/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2152630221/10000000000 : ℝ)^8365 ≤ (3270808457121/25000000000000 : ℝ)^6317 := by
    have hnat : (2152630221 : ℕ)^8365*25000000000000^6317 ≤ 3270808457121^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2152630221 10000000000 3270808457121 25000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633287411/5000000000 : ℝ)^8365 ≤ (10695139852527/25000000000000 : ℝ)^6317 := by
    have hnat : (2633287411 : ℕ)^8365*25000000000000^6317 ≤ 10695139852527^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633287411 5000000000 10695139852527 25000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392122113/10000000000 : ℝ)^8365 ≤ (5517025843611/12500000000000 : ℝ)^6317 := by
    have hnat : (5392122113 : ℕ)^8365*12500000000000^6317 ≤ 5517025843611^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392122113 10000000000 5517025843611 12500000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2152630221/10000000000 : ℝ), (2633287411/5000000000 : ℝ), (5392122113/10000000000 : ℝ)] ![(3270808457121/25000000000000 : ℝ), (10695139852527/25000000000000 : ℝ), (5517025843611/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2152630221/10000000000 : ℝ)|^8365 ≤ (3270808457121/25000000000000 : ℝ)^6317
        have hw : |(-2152630221/10000000000 : ℝ)|=(2152630221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633287411/5000000000 : ℝ)|^8365 ≤ (10695139852527/25000000000000 : ℝ)^6317
        have hw : |(2633287411/5000000000 : ℝ)|=(2633287411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392122113/10000000000 : ℝ)|^8365 ≤ (5517025843611/12500000000000 : ℝ)^6317
        have hw : |(5392122113/10000000000 : ℝ)|=(5392122113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s9_5 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (43604759/100000000 : ℝ)*x 0 + (1121973867/2500000000 : ℝ)*x 1 + (2118325913/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (43604759/100000000 : ℝ)^8365 ≤ (3331724986253/10000000000000 : ℝ)^6317 := by
    have hnat : (43604759 : ℕ)^8365*10000000000000^6317 ≤ 3331724986253^6317*100000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43604759 100000000 3331724986253 10000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1121973867/2500000000 : ℝ)^8365 ≤ (1384501411091/4000000000000 : ℝ)^6317 := by
    have hnat : (1121973867 : ℕ)^8365*4000000000000^6317 ≤ 1384501411091^6317*2500000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121973867 2500000000 1384501411091 4000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2118325913/5000000000 : ℝ)^8365 ≤ (32070214847457/100000000000000 : ℝ)^6317 := by
    have hnat : (2118325913 : ℕ)^8365*100000000000000^6317 ≤ 32070214847457^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118325913 5000000000 32070214847457 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(43604759/100000000 : ℝ), (1121973867/2500000000 : ℝ), (2118325913/5000000000 : ℝ)] ![(3331724986253/10000000000000 : ℝ), (1384501411091/4000000000000 : ℝ), (32070214847457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(43604759/100000000 : ℝ)|^8365 ≤ (3331724986253/10000000000000 : ℝ)^6317
        have hw : |(43604759/100000000 : ℝ)|=(43604759/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1121973867/2500000000 : ℝ)|^8365 ≤ (1384501411091/4000000000000 : ℝ)^6317
        have hw : |(1121973867/2500000000 : ℝ)|=(1121973867/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2118325913/5000000000 : ℝ)|^8365 ≤ (32070214847457/100000000000000 : ℝ)^6317
        have hw : |(2118325913/5000000000 : ℝ)|=(2118325913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1172_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150059381/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7033/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (356/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (11393/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7033/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7033/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (356/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7033/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (356/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7033/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (356/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7033/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (356/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7033/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (356/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7033/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (356/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (356/3125 : ℝ) ^ (2091/512 : ℝ) ≤ (7016799194435273/50000000000000000000 : ℝ) := by
    have hpowers : (356/3125 : ℝ)^2091 ≤ (7016799194435273/50000000000000000000 : ℝ)^512 := by
      have hnat : (356 : ℕ)^2091*50000000000000000000^512 ≤ 7016799194435273^512*3125^2091 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        356 3125 7016799194435273 50000000000000000000 2091 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (356/3125 : ℝ)) (X := (7016799194435273/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2091 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7033/50000 : ℝ) ^ (2091/512 : ℝ) ≤ (1660015327222413/5000000000000000000 : ℝ) := by
    have hpowers : (7033/50000 : ℝ)^2091 ≤ (1660015327222413/5000000000000000000 : ℝ)^512 := by
      have hnat : (7033 : ℕ)^2091*5000000000000000000^512 ≤ 1660015327222413^512*50000^2091 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7033 50000 1660015327222413 5000000000000000000 2091 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7033/50000 : ℝ)) (X := (1660015327222413/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2091 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007016799194435273/25000000000000000000 : ℝ) ≤ (1000068717752839/1000000000000000 : ℝ) ^ (2091/512 : ℝ) := by
    have hpowers : (25007016799194435273/25000000000000000000 : ℝ)^512 ≤ (1000068717752839/1000000000000000 : ℝ)^2091 := by
      have hnat : (25007016799194435273 : ℕ)^512*1000000000000000^2091 ≤ 1000068717752839^2091*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007016799194435273 25000000000000000000 1000068717752839 1000000000000000 512 2091 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000068717752839/1000000000000000 : ℝ)) (X := (25007016799194435273/25000000000000000000 : ℝ)) (by norm_num) 2091 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023616952466659403/50000000000000000000 : ℝ) ≤ (250028908952121/250000000000000 : ℝ) ^ (2091/512 : ℝ) := by
    have hpowers : (50023616952466659403/50000000000000000000 : ℝ)^512 ≤ (250028908952121/250000000000000 : ℝ)^2091 := by
      have hnat : (50023616952466659403 : ℕ)^512*250000000000000^2091 ≤ 250028908952121^2091*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023616952466659403 50000000000000000000 250028908952121 250000000000000 512 2091 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250028908952121/250000000000000 : ℝ)) (X := (50023616952466659403/50000000000000000000 : ℝ)) (by norm_num) 2091 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501660015327222413/2500000000000000000 : ℝ) ≤ (1000162553864129/1000000000000000 : ℝ) ^ (2091/512 : ℝ) := by
    have hpowers : (2501660015327222413/2500000000000000000 : ℝ)^512 ≤ (1000162553864129/1000000000000000 : ℝ)^2091 := by
      have hnat : (2501660015327222413 : ℕ)^512*1000000000000000^2091 ≤ 1000162553864129^2091*2500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501660015327222413 2500000000000000000 1000162553864129 1000000000000000 512 2091 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000162553864129/1000000000000000 : ℝ)) (X := (2501660015327222413/2500000000000000000 : ℝ)) (by norm_num) 2091 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7016799194435273/50000000000000000000 : ℝ) ≤ ((1336557385145637903/1337000000000000000 : ℝ)+2*(9383611129/5348000000000 : ℝ)*(356/3125 : ℝ))^(2091/512 : ℝ) := by
    rw [show (1336557385145637903/1337000000000000000 : ℝ)+2*(9383611129/5348000000000 : ℝ)*(356/3125 : ℝ)=(1000068717752839/1000000000000000 : ℝ) by norm_num, show 1+2*(7016799194435273/50000000000000000000 : ℝ)=(25007016799194435273/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1660015327222413/5000000000000000000 : ℝ)+(7016799194435273/50000000000000000000 : ℝ) ≤ ((1336557385145637903/1337000000000000000 : ℝ)+(9383611129/5348000000000 : ℝ)*((7033/50000 : ℝ)+(356/3125 : ℝ)))^(2091/512 : ℝ) := by
    rw [show (1336557385145637903/1337000000000000000 : ℝ)+(9383611129/5348000000000 : ℝ)*((7033/50000 : ℝ)+(356/3125 : ℝ))=(250028908952121/250000000000000 : ℝ) by norm_num, show 1+(1660015327222413/5000000000000000000 : ℝ)+(7016799194435273/50000000000000000000 : ℝ)=(50023616952466659403/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1660015327222413/5000000000000000000 : ℝ) ≤ ((1336557385145637903/1337000000000000000 : ℝ)+2*(9383611129/5348000000000 : ℝ)*(7033/50000 : ℝ))^(2091/512 : ℝ) := by
    rw [show (1336557385145637903/1337000000000000000 : ℝ)+2*(9383611129/5348000000000 : ℝ)*(7033/50000 : ℝ)=(1000162553864129/1000000000000000 : ℝ) by norm_num, show 1+2*(1660015327222413/5000000000000000000 : ℝ)=(2501660015327222413/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1336557385145637903/1337000000000000000 : ℝ)*(X 1 0+X 2 0)+(9383611129/5348000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2091/512 : ℝ)) (lo := (356/3125 : ℝ)) (hi := (7033/50000 : ℝ)) (c := (1336557385145637903/1337000000000000000 : ℝ)) (alpha := (9383611129/5348000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1336557385145637903/1337000000000000000 : ℝ)*(X 0 1+X 2 1)+(9383611129/5348000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2091/512 : ℝ)) (lo := (356/3125 : ℝ)) (hi := (7033/50000 : ℝ)) (c := (1336557385145637903/1337000000000000000 : ℝ)) (alpha := (9383611129/5348000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1336557385145637903/1337000000000000000 : ℝ)*(X 0 2+X 1 2)+(9383611129/5348000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2091/512 : ℝ)) (lo := (356/3125 : ℝ)) (hi := (7033/50000 : ℝ)) (c := (1336557385145637903/1337000000000000000 : ℝ)) (alpha := (9383611129/5348000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2152625439/10000000000 : ℝ)*X 0 0+(5392440359/10000000000 : ℝ)*X 0 1+(5266257707/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1068925597/2000000000 : ℝ)*X 1 0+(-13853871/62500000 : ℝ)*X 1 1+(526625769/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s9_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344627971/10000000000 : ℝ)*X 2 0+(1316564429/2500000000 : ℝ)*X 2 1+(-138538709/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s9_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4360466269/10000000000 : ℝ)*X 0 0+(4236014911/10000000000 : ℝ)*X 0 1+(4488530109/10000000000 : ℝ)*X 0 2+(4360466269/10000000000 : ℝ)*X 1 0+(4236014911/10000000000 : ℝ)*X 1 1+(4488530109/10000000000 : ℝ)*X 1 2+(4360466269/10000000000 : ℝ)*X 2 0+(4236014911/10000000000 : ℝ)*X 2 1+(4488530109/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s9_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2152630221/10000000000 : ℝ)*X 0 0+(2633287411/5000000000 : ℝ)*X 0 1+(5392122113/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s9_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((43604759/100000000 : ℝ)*X 0 0+(1121973867/2500000000 : ℝ)*X 0 1+(2118325913/5000000000 : ℝ)*X 0 2+(43604759/100000000 : ℝ)*X 1 0+(1121973867/2500000000 : ℝ)*X 1 1+(2118325913/5000000000 : ℝ)*X 1 2+(43604759/100000000 : ℝ)*X 2 0+(1121973867/2500000000 : ℝ)*X 2 1+(2118325913/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s9_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (45285228452840752919128983/16712500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (273789731/50000000000000 : ℝ)*(base19) + (494863529/100000000000000 : ℝ)*(base23) + (3415927/20000000000000 : ℝ)*(lower2) + (14316499/25000000000000 : ℝ)*(upper3) + (27813437/50000000000000 : ℝ)*(upper5) + (2971305636964213/50000000000000 : ℝ)*(major0) + (2971305636964213/50000000000000 : ℝ)*(major1) + (2971305636964213/50000000000000 : ℝ)*(major2) + (495314647563727/6250000000000 : ℝ)*(sp0) + (7925048787604209/100000000000000 : ℝ)*(sp1) + (3962524420160071/50000000000000 : ℝ)*(sp2) + (3960165328054893/100000000000000 : ℝ)*(sp3) + (14974164039/100000000000000 : ℝ)*(sp4) + (3897148101/50000000000000 : ℝ)*(sp5) + (495021640293887/12500000000000 : ℝ)*(f.failure) + (7925049335183671/100000000000000 : ℝ)*(f.sum) + (296963149169/66850000000000000000000000 : ℝ)*base66 + (1186212892952365339/66850000000000000000000000000000 : ℝ)*base67 + (1991557489209615339/66850000000000000000000000000000 : ℝ)*base69 + (515510260524915339/66850000000000000000000000000000 : ℝ)*base71 + (1162826374767/1337000000000000000000000000 : ℝ)*base73 + (1554156670463465339/66850000000000000000000000000000 : ℝ)*base75 + (621120436161534661/66850000000000000000000000000000 : ℝ)*base78 + (1090325811569265339/66850000000000000000000000000000 : ℝ)*base79 + (7285784301853/1337000000000000000000000000 : ℝ)*base81 + (16303947/1250000000000000000000 : ℝ)*base89 + (16303947/1250000000000000000000 : ℝ)*base91 + (16303947/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1172_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150059381/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7033/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (356/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11393/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7033/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1172_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1172_s10_0 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672313871/5000000000 : ℝ)*x 0 + (5266263387/10000000000 : ℝ)*x 1 + (-1108306071/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672313871/5000000000 : ℝ)^8365 ≤ (2181107520203/5000000000000 : ℝ)^6317 := by
    have hnat : (2672313871 : ℕ)^8365*5000000000000^6317 ≤ 2181107520203^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672313871 5000000000 2181107520203 5000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266263387/10000000000 : ℝ)^8365 ≤ (21388604736999/50000000000000 : ℝ)^6317 := by
    have hnat : (5266263387 : ℕ)^8365*50000000000000^6317 ≤ 21388604736999^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266263387 10000000000 21388604736999 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1108306071/5000000000 : ℝ)^8365 ≤ (13600640109437/100000000000000 : ℝ)^6317 := by
    have hnat : (1108306071 : ℕ)^8365*100000000000000^6317 ≤ 13600640109437^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1108306071 5000000000 13600640109437 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672313871/5000000000 : ℝ), (5266263387/10000000000 : ℝ), (-1108306071/5000000000 : ℝ)] ![(2181107520203/5000000000000 : ℝ), (21388604736999/50000000000000 : ℝ), (13600640109437/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672313871/5000000000 : ℝ)|^8365 ≤ (2181107520203/5000000000000 : ℝ)^6317
        have hw : |(2672313871/5000000000 : ℝ)|=(2672313871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266263387/10000000000 : ℝ)|^8365 ≤ (21388604736999/50000000000000 : ℝ)^6317
        have hw : |(5266263387/10000000000 : ℝ)|=(5266263387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1108306071/5000000000 : ℝ)|^8365 ≤ (13600640109437/100000000000000 : ℝ)^6317
        have hw : |(-1108306071/5000000000 : ℝ)|=(1108306071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s10_1 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2180233109/5000000000 : ℝ)*x 0 + (847204843/2000000000 : ℝ)*x 1 + (1122130257/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2180233109/5000000000 : ℝ)^8365 ≤ (33317151901071/100000000000000 : ℝ)^6317 := by
    have hnat : (2180233109 : ℕ)^8365*100000000000000^6317 ≤ 33317151901071^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180233109 5000000000 33317151901071 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (847204843/2000000000 : ℝ)^8365 ≤ (6412784785149/20000000000000 : ℝ)^6317 := by
    have hnat : (847204843 : ℕ)^8365*20000000000000^6317 ≤ 6412784785149^6317*2000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847204843 2000000000 6412784785149 20000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1122130257/2500000000 : ℝ)^8365 ≤ (17309462077163/50000000000000 : ℝ)^6317 := by
    have hnat : (1122130257 : ℕ)^8365*50000000000000^6317 ≤ 17309462077163^6317*2500000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122130257 2500000000 17309462077163 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2180233109/5000000000 : ℝ), (847204843/2000000000 : ℝ), (1122130257/2500000000 : ℝ)] ![(33317151901071/100000000000000 : ℝ), (6412784785149/20000000000000 : ℝ), (17309462077163/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2180233109/5000000000 : ℝ)|^8365 ≤ (33317151901071/100000000000000 : ℝ)^6317
        have hw : |(2180233109/5000000000 : ℝ)|=(2180233109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(847204843/2000000000 : ℝ)|^8365 ≤ (6412784785149/20000000000000 : ℝ)^6317
        have hw : |(847204843/2000000000 : ℝ)|=(847204843/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1122130257/2500000000 : ℝ)|^8365 ≤ (17309462077163/50000000000000 : ℝ)^6317
        have hw : |(1122130257/2500000000 : ℝ)|=(1122130257/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s10_2 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1076313571/5000000000 : ℝ)*x 0 + (2633290209/5000000000 : ℝ)*x 1 + (1078423769/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1076313571/5000000000 : ℝ)^8365 ≤ (13083209047969/100000000000000 : ℝ)^6317 := by
    have hnat : (1076313571 : ℕ)^8365*100000000000000^6317 ≤ 13083209047969^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076313571 5000000000 13083209047969 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633290209/5000000000 : ℝ)^8365 ≤ (42780619603809/100000000000000 : ℝ)^6317 := by
    have hnat : (2633290209 : ℕ)^8365*100000000000000^6317 ≤ 42780619603809^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633290209 5000000000 42780619603809 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078423769/2000000000 : ℝ)^8365 ≤ (44136171326947/100000000000000 : ℝ)^6317 := by
    have hnat : (1078423769 : ℕ)^8365*100000000000000^6317 ≤ 44136171326947^6317*2000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078423769 2000000000 44136171326947 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1076313571/5000000000 : ℝ), (2633290209/5000000000 : ℝ), (1078423769/2000000000 : ℝ)] ![(13083209047969/100000000000000 : ℝ), (42780619603809/100000000000000 : ℝ), (44136171326947/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1076313571/5000000000 : ℝ)|^8365 ≤ (13083209047969/100000000000000 : ℝ)^6317
        have hw : |(-1076313571/5000000000 : ℝ)|=(1076313571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633290209/5000000000 : ℝ)|^8365 ≤ (42780619603809/100000000000000 : ℝ)^6317
        have hw : |(2633290209/5000000000 : ℝ)|=(2633290209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078423769/2000000000 : ℝ)|^8365 ≤ (44136171326947/100000000000000 : ℝ)^6317
        have hw : |(1078423769/2000000000 : ℝ)|=(1078423769/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s10_3 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312590943/10000000000 : ℝ)*x 0 + (-2090756509/10000000000 : ℝ)*x 1 + (1348029701/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312590943/10000000000 : ℝ)^8365 ≤ (43276234106187/100000000000000 : ℝ)^6317 := by
    have hnat : (5312590943 : ℕ)^8365*100000000000000^6317 ≤ 43276234106187^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312590943 10000000000 43276234106187 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2090756509/10000000000 : ℝ)^8365 ≤ (3146898749253/25000000000000 : ℝ)^6317 := by
    have hnat : (2090756509 : ℕ)^8365*25000000000000^6317 ≤ 3146898749253^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2090756509 10000000000 3146898749253 25000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348029701/2500000000 : ℝ)^8365 ≤ (22068085441273/50000000000000 : ℝ)^6317 := by
    have hnat : (1348029701 : ℕ)^8365*50000000000000^6317 ≤ 22068085441273^6317*2500000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348029701 2500000000 22068085441273 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312590943/10000000000 : ℝ), (-2090756509/10000000000 : ℝ), (1348029701/2500000000 : ℝ)] ![(43276234106187/100000000000000 : ℝ), (3146898749253/25000000000000 : ℝ), (22068085441273/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312590943/10000000000 : ℝ)|^8365 ≤ (43276234106187/100000000000000 : ℝ)^6317
        have hw : |(5312590943/10000000000 : ℝ)|=(5312590943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2090756509/10000000000 : ℝ)|^8365 ≤ (3146898749253/25000000000000 : ℝ)^6317
        have hw : |(-2090756509/10000000000 : ℝ)|=(2090756509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348029701/2500000000 : ℝ)|^8365 ≤ (22068085441273/50000000000000 : ℝ)^6317
        have hw : |(1348029701/2500000000 : ℝ)|=(1348029701/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s10_4 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (53125911/100000000 : ℝ)*x 0 + (215684749/400000000 : ℝ)*x 1 + (-522689101/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53125911/100000000 : ℝ)^8365 ≤ (5409529474967/12500000000000 : ℝ)^6317 := by
    have hnat : (53125911 : ℕ)^8365*12500000000000^6317 ≤ 5409529474967^6317*100000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53125911 100000000 5409529474967 12500000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215684749/400000000 : ℝ)^8365 ≤ (44136170026263/100000000000000 : ℝ)^6317 := by
    have hnat : (215684749 : ℕ)^8365*100000000000000^6317 ≤ 44136170026263^6317*400000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215684749 400000000 44136170026263 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (522689101/2500000000 : ℝ)^8365 ≤ (125875941599/1000000000000 : ℝ)^6317 := by
    have hnat : (522689101 : ℕ)^8365*1000000000000^6317 ≤ 125875941599^6317*2500000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522689101 2500000000 125875941599 1000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53125911/100000000 : ℝ), (215684749/400000000 : ℝ), (-522689101/2500000000 : ℝ)] ![(5409529474967/12500000000000 : ℝ), (44136170026263/100000000000000 : ℝ), (125875941599/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53125911/100000000 : ℝ)|^8365 ≤ (5409529474967/12500000000000 : ℝ)^6317
        have hw : |(53125911/100000000 : ℝ)|=(53125911/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(215684749/400000000 : ℝ)|^8365 ≤ (44136170026263/100000000000000 : ℝ)^6317
        have hw : |(215684749/400000000 : ℝ)|=(215684749/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-522689101/2500000000 : ℝ)|^8365 ≤ (125875941599/1000000000000 : ℝ)^6317
        have hw : |(-522689101/2500000000 : ℝ)|=(522689101/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s10_5 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (872095247/2000000000 : ℝ)*x 0 + (4487886601/10000000000 : ℝ)*x 1 + (2118330261/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (872095247/2000000000 : ℝ)^8365 ≤ (16658626626013/50000000000000 : ℝ)^6317 := by
    have hnat : (872095247 : ℕ)^8365*50000000000000^6317 ≤ 16658626626013^6317*2000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      872095247 2000000000 16658626626013 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4487886601/10000000000 : ℝ)^8365 ≤ (6922488944043/20000000000000 : ℝ)^6317 := by
    have hnat : (4487886601 : ℕ)^8365*20000000000000^6317 ≤ 6922488944043^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4487886601 10000000000 6922488944043 20000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2118330261/5000000000 : ℝ)^8365 ≤ (16035151007403/50000000000000 : ℝ)^6317 := by
    have hnat : (2118330261 : ℕ)^8365*50000000000000^6317 ≤ 16035151007403^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118330261 5000000000 16035151007403 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(872095247/2000000000 : ℝ), (4487886601/10000000000 : ℝ), (2118330261/5000000000 : ℝ)] ![(16658626626013/50000000000000 : ℝ), (6922488944043/20000000000000 : ℝ), (16035151007403/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(872095247/2000000000 : ℝ)|^8365 ≤ (16658626626013/50000000000000 : ℝ)^6317
        have hw : |(872095247/2000000000 : ℝ)|=(872095247/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4487886601/10000000000 : ℝ)|^8365 ≤ (6922488944043/20000000000000 : ℝ)^6317
        have hw : |(4487886601/10000000000 : ℝ)|=(4487886601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2118330261/5000000000 : ℝ)|^8365 ≤ (16035151007403/50000000000000 : ℝ)^6317
        have hw : |(2118330261/5000000000 : ℝ)|=(2118330261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1172_s10 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150059381/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7033/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11393/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11393/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2813/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7033/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11393/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7033/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11393/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7033/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11393/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7033/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11393/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7033/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11393/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7033/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11393/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11393/100000 : ℝ) ^ (2091/512 : ℝ) ≤ (14038630056247643/100000000000000000000 : ℝ) := by
    have hpowers : (11393/100000 : ℝ)^2091 ≤ (14038630056247643/100000000000000000000 : ℝ)^512 := by
      have hnat : (11393 : ℕ)^2091*100000000000000000000^512 ≤ 14038630056247643^512*100000^2091 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11393 100000 14038630056247643 100000000000000000000 2091 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11393/100000 : ℝ)) (X := (14038630056247643/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2091 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7033/50000 : ℝ) ^ (2091/512 : ℝ) ≤ (1660015327222413/5000000000000000000 : ℝ) := by
    have hpowers : (7033/50000 : ℝ)^2091 ≤ (1660015327222413/5000000000000000000 : ℝ)^512 := by
      have hnat : (7033 : ℕ)^2091*5000000000000000000^512 ≤ 1660015327222413^512*50000^2091 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7033 50000 1660015327222413 5000000000000000000 2091 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7033/50000 : ℝ)) (X := (1660015327222413/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2091 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014038630056247643/50000000000000000000 : ℝ) ≤ (5000343711942947/5000000000000000 : ℝ) ^ (2091/512 : ℝ) := by
    have hpowers : (50014038630056247643/50000000000000000000 : ℝ)^512 ≤ (5000343711942947/5000000000000000 : ℝ)^2091 := by
      have hnat : (50014038630056247643 : ℕ)^512*5000000000000000^2091 ≤ 5000343711942947^2091*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014038630056247643 50000000000000000000 5000343711942947 5000000000000000 512 2091 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000343711942947/5000000000000000 : ℝ)) (X := (50014038630056247643/50000000000000000000 : ℝ)) (by norm_num) 2091 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047238936600695903/100000000000000000000 : ℝ) ≤ (400046259249831/400000000000000 : ℝ) ^ (2091/512 : ℝ) := by
    have hpowers : (100047238936600695903/100000000000000000000 : ℝ)^512 ≤ (400046259249831/400000000000000 : ℝ)^2091 := by
      have hnat : (100047238936600695903 : ℕ)^512*400000000000000^2091 ≤ 400046259249831^2091*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047238936600695903 100000000000000000000 400046259249831 400000000000000 512 2091 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400046259249831/400000000000000 : ℝ)) (X := (100047238936600695903/100000000000000000000 : ℝ)) (by norm_num) 2091 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501660015327222413/2500000000000000000 : ℝ) ≤ (1250203192325707/1250000000000000 : ℝ) ^ (2091/512 : ℝ) := by
    have hpowers : (2501660015327222413/2500000000000000000 : ℝ)^512 ≤ (1250203192325707/1250000000000000 : ℝ)^2091 := by
      have hnat : (2501660015327222413 : ℕ)^512*1250000000000000^2091 ≤ 1250203192325707^2091*2500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501660015327222413 2500000000000000000 1250203192325707 1250000000000000 512 2091 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250203192325707/1250000000000000 : ℝ)) (X := (2501660015327222413/2500000000000000000 : ℝ)) (by norm_num) 2091 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14038630056247643/100000000000000000000 : ℝ) ≤ ((607298853251016959/607500000000000000 : ℝ)+2*(42641578171/24300000000000 : ℝ)*(11393/100000 : ℝ))^(2091/512 : ℝ) := by
    rw [show (607298853251016959/607500000000000000 : ℝ)+2*(42641578171/24300000000000 : ℝ)*(11393/100000 : ℝ)=(5000343711942947/5000000000000000 : ℝ) by norm_num, show 1+2*(14038630056247643/100000000000000000000 : ℝ)=(50014038630056247643/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1660015327222413/5000000000000000000 : ℝ)+(14038630056247643/100000000000000000000 : ℝ) ≤ ((607298853251016959/607500000000000000 : ℝ)+(42641578171/24300000000000 : ℝ)*((7033/50000 : ℝ)+(11393/100000 : ℝ)))^(2091/512 : ℝ) := by
    rw [show (607298853251016959/607500000000000000 : ℝ)+(42641578171/24300000000000 : ℝ)*((7033/50000 : ℝ)+(11393/100000 : ℝ))=(400046259249831/400000000000000 : ℝ) by norm_num, show 1+(1660015327222413/5000000000000000000 : ℝ)+(14038630056247643/100000000000000000000 : ℝ)=(100047238936600695903/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1660015327222413/5000000000000000000 : ℝ) ≤ ((607298853251016959/607500000000000000 : ℝ)+2*(42641578171/24300000000000 : ℝ)*(7033/50000 : ℝ))^(2091/512 : ℝ) := by
    rw [show (607298853251016959/607500000000000000 : ℝ)+2*(42641578171/24300000000000 : ℝ)*(7033/50000 : ℝ)=(1250203192325707/1250000000000000 : ℝ) by norm_num, show 1+2*(1660015327222413/5000000000000000000 : ℝ)=(2501660015327222413/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (607298853251016959/607500000000000000 : ℝ)*(X 1 0+X 2 0)+(42641578171/24300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2091/512 : ℝ)) (lo := (11393/100000 : ℝ)) (hi := (7033/50000 : ℝ)) (c := (607298853251016959/607500000000000000 : ℝ)) (alpha := (42641578171/24300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (607298853251016959/607500000000000000 : ℝ)*(X 0 1+X 2 1)+(42641578171/24300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2091/512 : ℝ)) (lo := (11393/100000 : ℝ)) (hi := (7033/50000 : ℝ)) (c := (607298853251016959/607500000000000000 : ℝ)) (alpha := (42641578171/24300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (607298853251016959/607500000000000000 : ℝ)*(X 0 2+X 1 2)+(42641578171/24300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2091/512 : ℝ)) (lo := (11393/100000 : ℝ)) (hi := (7033/50000 : ℝ)) (c := (607298853251016959/607500000000000000 : ℝ)) (alpha := (42641578171/24300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((2672313871/5000000000 : ℝ)*X 2 0+(5266263387/10000000000 : ℝ)*X 2 1+(-1108306071/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s10_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2180233109/5000000000 : ℝ)*X 0 0+(847204843/2000000000 : ℝ)*X 0 1+(1122130257/2500000000 : ℝ)*X 0 2+(2180233109/5000000000 : ℝ)*X 1 0+(847204843/2000000000 : ℝ)*X 1 1+(1122130257/2500000000 : ℝ)*X 1 2+(2180233109/5000000000 : ℝ)*X 2 0+(847204843/2000000000 : ℝ)*X 2 1+(1122130257/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s10_1 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((-1076313571/5000000000 : ℝ)*X 0 0+(2633290209/5000000000 : ℝ)*X 0 1+(1078423769/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s10_2 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5312590943/10000000000 : ℝ)*X 1 0+(-2090756509/10000000000 : ℝ)*X 1 1+(1348029701/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s10_3 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((53125911/100000000 : ℝ)*X 2 0+(215684749/400000000 : ℝ)*X 2 1+(-522689101/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s10_4 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((872095247/2000000000 : ℝ)*X 0 0+(4487886601/10000000000 : ℝ)*X 0 1+(2118330261/5000000000 : ℝ)*X 0 2+(872095247/2000000000 : ℝ)*X 1 0+(4487886601/10000000000 : ℝ)*X 1 1+(2118330261/5000000000 : ℝ)*X 1 2+(872095247/2000000000 : ℝ)*X 2 0+(4487886601/10000000000 : ℝ)*X 2 1+(2118330261/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s10_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2805872472895360895233763/843750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14175429/20000000000000 : ℝ)*(base19) + (12304163/25000000000000 : ℝ)*(base23) + (10967451/5000000000000 : ℝ)*(lower2) + (76761127/100000000000000 : ℝ)*(lower4) + (28040847/100000000000000 : ℝ)*(lower5) + (1493272175135379/25000000000000 : ℝ)*(major0) + (1493272175135379/25000000000000 : ℝ)*(major1) + (1493272175135379/25000000000000 : ℝ)*(major2) + (117427331/6250000000000 : ℝ)*(sp0) + (195359089/25000000000000 : ℝ)*(sp1) + (7965693923757959/100000000000000 : ℝ)*(sp2) + (3982846926440407/50000000000000 : ℝ)*(sp3) + (1991422998926003/25000000000000 : ℝ)*(sp4) + (3980482585039423/100000000000000 : ℝ)*(sp5) + (199024168323789/5000000000000 : ℝ)*(f.failure) + (7965693923757959/100000000000000 : ℝ)*(f.sum) + (1117750394237/405000000000000000000000000 : ℝ)*base65 + (17630474603103329/1687500000000000000000000000000 : ℝ)*base67 + (11310092690103329/1687500000000000000000000000000 : ℝ)*base69 + (12674923307478329/1687500000000000000000000000000 : ℝ)*base71 + (729617659573/405000000000000000000000000 : ℝ)*base74 + (10285838917834171/1687500000000000000000000000000 : ℝ)*base76 + (28914594356853329/1687500000000000000000000000000 : ℝ)*base77 + (20973888117521671/1687500000000000000000000000000 : ℝ)*base80 + (1314493017329/202500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (4914609/500000000000000000000 : ℝ)*base89 + (4914609/500000000000000000000 : ℝ)*base91 + (4914609/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1172_s10 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150059381/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7033/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11393/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11393/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2813/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1172_s10 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1172_box_0 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1013360959/5000000000 : ℝ)*x 0 + (1343968813/2500000000 : ℝ)*x 1 + (2687936841/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1013360959/5000000000 : ℝ)^8365 ≤ (6039815858847/50000000000000 : ℝ)^6317 := by
    have hnat : (1013360959 : ℕ)^8365*50000000000000^6317 ≤ 6039815858847^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1013360959 5000000000 6039815858847 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1343968813/2500000000 : ℝ)^8365 ≤ (21980096315611/50000000000000 : ℝ)^6317 := by
    have hnat : (1343968813 : ℕ)^8365*50000000000000^6317 ≤ 21980096315611^6317*2500000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343968813 2500000000 21980096315611 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2687936841/5000000000 : ℝ)^8365 ≤ (43960175630589/100000000000000 : ℝ)^6317 := by
    have hnat : (2687936841 : ℕ)^8365*100000000000000^6317 ≤ 43960175630589^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687936841 5000000000 43960175630589 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1013360959/5000000000 : ℝ), (1343968813/2500000000 : ℝ), (2687936841/5000000000 : ℝ)] ![(6039815858847/50000000000000 : ℝ), (21980096315611/50000000000000 : ℝ), (43960175630589/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1013360959/5000000000 : ℝ)|^8365 ≤ (6039815858847/50000000000000 : ℝ)^6317
        have hw : |(-1013360959/5000000000 : ℝ)|=(1013360959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1343968813/2500000000 : ℝ)|^8365 ≤ (21980096315611/50000000000000 : ℝ)^6317
        have hw : |(1343968813/2500000000 : ℝ)|=(1343968813/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2687936841/5000000000 : ℝ)|^8365 ≤ (43960175630589/100000000000000 : ℝ)^6317
        have hw : |(2687936841/5000000000 : ℝ)|=(2687936841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_box_1 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5296254623/10000000000 : ℝ)*x 0 + (-266846657/1250000000 : ℝ)*x 1 + (1343968671/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296254623/10000000000 : ℝ)^8365 ≤ (43100103147773/100000000000000 : ℝ)^6317 := by
    have hnat : (5296254623 : ℕ)^8365*100000000000000^6317 ≤ 43100103147773^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296254623 10000000000 43100103147773 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (266846657/1250000000 : ℝ)^8365 ≤ (12939710367649/100000000000000 : ℝ)^6317 := by
    have hnat : (266846657 : ℕ)^8365*100000000000000^6317 ≤ 12939710367649^6317*1250000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266846657 1250000000 12939710367649 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1343968671/2500000000 : ℝ)^8365 ≤ (21980093240337/50000000000000 : ℝ)^6317 := by
    have hnat : (1343968671 : ℕ)^8365*50000000000000^6317 ≤ 21980093240337^6317*2500000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343968671 2500000000 21980093240337 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296254623/10000000000 : ℝ), (-266846657/1250000000 : ℝ), (1343968671/2500000000 : ℝ)] ![(43100103147773/100000000000000 : ℝ), (12939710367649/100000000000000 : ℝ), (21980093240337/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296254623/10000000000 : ℝ)|^8365 ≤ (43100103147773/100000000000000 : ℝ)^6317
        have hw : |(5296254623/10000000000 : ℝ)|=(5296254623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-266846657/1250000000 : ℝ)|^8365 ≤ (12939710367649/100000000000000 : ℝ)^6317
        have hw : |(-266846657/1250000000 : ℝ)|=(266846657/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1343968671/2500000000 : ℝ)|^8365 ≤ (21980093240337/50000000000000 : ℝ)^6317
        have hw : |(1343968671/2500000000 : ℝ)|=(1343968671/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_box_2 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (529625561/1000000000 : ℝ)*x 0 + (5375873597/10000000000 : ℝ)*x 1 + (-426954679/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529625561/1000000000 : ℝ)^8365 ≤ (8620022756771/20000000000000 : ℝ)^6317 := by
    have hnat : (529625561 : ℕ)^8365*20000000000000^6317 ≤ 8620022756771^6317*1000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529625561 1000000000 8620022756771 20000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5375873597/10000000000 : ℝ)^8365 ≤ (10990043677543/25000000000000 : ℝ)^6317 := by
    have hnat : (5375873597 : ℕ)^8365*25000000000000^6317 ≤ 10990043677543^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375873597 10000000000 10990043677543 25000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (426954679/2000000000 : ℝ)^8365 ≤ (12939711483337/100000000000000 : ℝ)^6317 := by
    have hnat : (426954679 : ℕ)^8365*100000000000000^6317 ≤ 12939711483337^6317*2000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      426954679 2000000000 12939711483337 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529625561/1000000000 : ℝ), (5375873597/10000000000 : ℝ), (-426954679/2000000000 : ℝ)] ![(8620022756771/20000000000000 : ℝ), (10990043677543/25000000000000 : ℝ), (12939711483337/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529625561/1000000000 : ℝ)|^8365 ≤ (8620022756771/20000000000000 : ℝ)^6317
        have hw : |(529625561/1000000000 : ℝ)|=(529625561/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5375873597/10000000000 : ℝ)|^8365 ≤ (10990043677543/25000000000000 : ℝ)^6317
        have hw : |(5375873597/10000000000 : ℝ)|=(5375873597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-426954679/2000000000 : ℝ)|^8365 ≤ (12939711483337/100000000000000 : ℝ)^6317
        have hw : |(-426954679/2000000000 : ℝ)|=(426954679/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_box_3 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (558460891/1250000000 : ℝ)*x 0 + (2154471389/5000000000 : ℝ)*x 1 + (2154471837/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (558460891/1250000000 : ℝ)^8365 ≤ (34406301902987/100000000000000 : ℝ)^6317 := by
    have hnat : (558460891 : ℕ)^8365*100000000000000^6317 ≤ 34406301902987^6317*1250000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      558460891 1250000000 34406301902987 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2154471389/5000000000 : ℝ)^8365 ≤ (6559368904521/20000000000000 : ℝ)^6317 := by
    have hnat : (2154471389 : ℕ)^8365*20000000000000^6317 ≤ 6559368904521^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2154471389 5000000000 6559368904521 20000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2154471837/5000000000 : ℝ)^8365 ≤ (4099606694171/12500000000000 : ℝ)^6317 := by
    have hnat : (2154471837 : ℕ)^8365*12500000000000^6317 ≤ 4099606694171^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2154471837 5000000000 4099606694171 12500000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(558460891/1250000000 : ℝ), (2154471389/5000000000 : ℝ), (2154471837/5000000000 : ℝ)] ![(34406301902987/100000000000000 : ℝ), (6559368904521/20000000000000 : ℝ), (4099606694171/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(558460891/1250000000 : ℝ)|^8365 ≤ (34406301902987/100000000000000 : ℝ)^6317
        have hw : |(558460891/1250000000 : ℝ)|=(558460891/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2154471389/5000000000 : ℝ)|^8365 ≤ (6559368904521/20000000000000 : ℝ)^6317
        have hw : |(2154471389/5000000000 : ℝ)|=(2154471389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2154471837/5000000000 : ℝ)|^8365 ≤ (4099606694171/12500000000000 : ℝ)^6317
        have hw : |(2154471837/5000000000 : ℝ)|=(2154471837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_box_4 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2279912161/10000000000 : ℝ)*x 0 + (660189329/1250000000 : ℝ)*x 1 + (1320378927/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2279912161/10000000000 : ℝ)^8365 ≤ (7058660031751/50000000000000 : ℝ)^6317 := by
    have hnat : (2279912161 : ℕ)^8365*50000000000000^6317 ≤ 7058660031751^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2279912161 10000000000 7058660031751 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (660189329/1250000000 : ℝ)^8365 ≤ (2683833385763/6250000000000 : ℝ)^6317 := by
    have hnat : (660189329 : ℕ)^8365*6250000000000^6317 ≤ 2683833385763^6317*1250000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660189329 1250000000 2683833385763 6250000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1320378927/2500000000 : ℝ)^8365 ≤ (42941345756897/100000000000000 : ℝ)^6317 := by
    have hnat : (1320378927 : ℕ)^8365*100000000000000^6317 ≤ 42941345756897^6317*2500000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320378927 2500000000 42941345756897 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2279912161/10000000000 : ℝ), (660189329/1250000000 : ℝ), (1320378927/2500000000 : ℝ)] ![(7058660031751/50000000000000 : ℝ), (2683833385763/6250000000000 : ℝ), (42941345756897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2279912161/10000000000 : ℝ)|^8365 ≤ (7058660031751/50000000000000 : ℝ)^6317
        have hw : |(-2279912161/10000000000 : ℝ)|=(2279912161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(660189329/1250000000 : ℝ)|^8365 ≤ (2683833385763/6250000000000 : ℝ)^6317
        have hw : |(660189329/1250000000 : ℝ)|=(660189329/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1320378927/2500000000 : ℝ)|^8365 ≤ (42941345756897/100000000000000 : ℝ)^6317
        have hw : |(1320378927/2500000000 : ℝ)|=(1320378927/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_box_5 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (21451501/40000000 : ℝ)*x 0 + (-434395771/2000000000 : ℝ)*x 1 + (528151509/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21451501/40000000 : ℝ)^8365 ≤ (10954869559407/25000000000000 : ℝ)^6317 := by
    have hnat : (21451501 : ℕ)^8365*25000000000000^6317 ≤ 10954869559407^6317*40000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21451501 40000000 10954869559407 25000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (434395771/2000000000 : ℝ)^8365 ≤ (13239182649317/100000000000000 : ℝ)^6317 := by
    have hnat : (434395771 : ℕ)^8365*100000000000000^6317 ≤ 13239182649317^6317*2000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434395771 2000000000 13239182649317 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (528151509/1000000000 : ℝ)^8365 ≤ (42941339103237/100000000000000 : ℝ)^6317 := by
    have hnat : (528151509 : ℕ)^8365*100000000000000^6317 ≤ 42941339103237^6317*1000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528151509 1000000000 42941339103237 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(21451501/40000000 : ℝ), (-434395771/2000000000 : ℝ), (528151509/1000000000 : ℝ)] ![(10954869559407/25000000000000 : ℝ), (13239182649317/100000000000000 : ℝ), (42941339103237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(21451501/40000000 : ℝ)|^8365 ≤ (10954869559407/25000000000000 : ℝ)^6317
        have hw : |(21451501/40000000 : ℝ)|=(21451501/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-434395771/2000000000 : ℝ)|^8365 ≤ (13239182649317/100000000000000 : ℝ)^6317
        have hw : |(-434395771/2000000000 : ℝ)|=(434395771/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(528151509/1000000000 : ℝ)|^8365 ≤ (42941339103237/100000000000000 : ℝ)^6317
        have hw : |(528151509/1000000000 : ℝ)|=(528151509/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_box_6 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1072575063/2000000000 : ℝ)*x 0 + (5281514943/10000000000 : ℝ)*x 1 + (-1085989481/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072575063/2000000000 : ℝ)^8365 ≤ (43819478940923/100000000000000 : ℝ)^6317 := by
    have hnat : (1072575063 : ℕ)^8365*100000000000000^6317 ≤ 43819478940923^6317*2000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072575063 2000000000 43819478940923 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5281514943/10000000000 : ℝ)^8365 ≤ (42941337520571/100000000000000 : ℝ)^6317 := by
    have hnat : (5281514943 : ℕ)^8365*100000000000000^6317 ≤ 42941337520571^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281514943 10000000000 42941337520571 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1085989481/5000000000 : ℝ)^8365 ≤ (661959175649/5000000000000 : ℝ)^6317 := by
    have hnat : (1085989481 : ℕ)^8365*5000000000000^6317 ≤ 661959175649^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085989481 5000000000 661959175649 5000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072575063/2000000000 : ℝ), (5281514943/10000000000 : ℝ), (-1085989481/5000000000 : ℝ)] ![(43819478940923/100000000000000 : ℝ), (42941337520571/100000000000000 : ℝ), (661959175649/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072575063/2000000000 : ℝ)|^8365 ≤ (43819478940923/100000000000000 : ℝ)^6317
        have hw : |(1072575063/2000000000 : ℝ)|=(1072575063/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5281514943/10000000000 : ℝ)|^8365 ≤ (42941337520571/100000000000000 : ℝ)^6317
        have hw : |(5281514943/10000000000 : ℝ)|=(5281514943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1085989481/5000000000 : ℝ)|^8365 ≤ (661959175649/5000000000000 : ℝ)^6317
        have hw : |(-1085989481/5000000000 : ℝ)|=(1085989481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_box_7 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4252871921/10000000000 : ℝ)*x 0 + (2208165219/5000000000 : ℝ)*x 1 + (4416330013/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4252871921/10000000000 : ℝ)^8365 ≤ (32232903315383/100000000000000 : ℝ)^6317 := by
    have hnat : (4252871921 : ℕ)^8365*100000000000000^6317 ≤ 32232903315383^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4252871921 10000000000 32232903315383 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2208165219/5000000000 : ℝ)^8365 ≤ (33883550492019/100000000000000 : ℝ)^6317 := by
    have hnat : (2208165219 : ℕ)^8365*100000000000000^6317 ≤ 33883550492019^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2208165219 5000000000 33883550492019 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4416330013/10000000000 : ℝ)^8365 ≤ (33883546174131/100000000000000 : ℝ)^6317 := by
    have hnat : (4416330013 : ℕ)^8365*100000000000000^6317 ≤ 33883546174131^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4416330013 10000000000 33883546174131 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4252871921/10000000000 : ℝ), (2208165219/5000000000 : ℝ), (4416330013/10000000000 : ℝ)] ![(32232903315383/100000000000000 : ℝ), (33883550492019/100000000000000 : ℝ), (33883546174131/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4252871921/10000000000 : ℝ)|^8365 ≤ (32232903315383/100000000000000 : ℝ)^6317
        have hw : |(4252871921/10000000000 : ℝ)|=(4252871921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2208165219/5000000000 : ℝ)|^8365 ≤ (33883550492019/100000000000000 : ℝ)^6317
        have hw : |(2208165219/5000000000 : ℝ)|=(2208165219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4416330013/10000000000 : ℝ)|^8365 ≤ (33883546174131/100000000000000 : ℝ)^6317
        have hw : |(4416330013/10000000000 : ℝ)|=(4416330013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_box_8 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-139183277/625000000 : ℝ)*x 0 + (1043456811/2000000000 : ℝ)*x 1 + (5385484651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (139183277/625000000 : ℝ)^8365 ≤ (1710569493017/12500000000000 : ℝ)^6317 := by
    have hnat : (139183277 : ℕ)^8365*12500000000000^6317 ≤ 1710569493017^6317*625000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      139183277 625000000 1710569493017 12500000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043456811/2000000000 : ℝ)^8365 ≤ (4225116657217/10000000000000 : ℝ)^6317 := by
    have hnat : (1043456811 : ℕ)^8365*10000000000000^6317 ≤ 4225116657217^6317*2000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043456811 2000000000 4225116657217 10000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5385484651/10000000000 : ℝ)^8365 ≤ (2754017341833/6250000000000 : ℝ)^6317 := by
    have hnat : (5385484651 : ℕ)^8365*6250000000000^6317 ≤ 2754017341833^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385484651 10000000000 2754017341833 6250000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-139183277/625000000 : ℝ), (1043456811/2000000000 : ℝ), (5385484651/10000000000 : ℝ)] ![(1710569493017/12500000000000 : ℝ), (4225116657217/10000000000000 : ℝ), (2754017341833/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-139183277/625000000 : ℝ)|^8365 ≤ (1710569493017/12500000000000 : ℝ)^6317
        have hw : |(-139183277/625000000 : ℝ)|=(139183277/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043456811/2000000000 : ℝ)|^8365 ≤ (4225116657217/10000000000000 : ℝ)^6317
        have hw : |(1043456811/2000000000 : ℝ)|=(1043456811/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5385484651/10000000000 : ℝ)|^8365 ≤ (2754017341833/6250000000000 : ℝ)^6317
        have hw : |(5385484651/10000000000 : ℝ)|=(5385484651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_box_9 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (8264793/15625000 : ℝ)*x 0 + (-106545741/500000000 : ℝ)*x 1 + (5385484057/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8264793/15625000 : ℝ)^8365 ≤ (10756744838747/25000000000000 : ℝ)^6317 := by
    have hnat : (8264793 : ℕ)^8365*25000000000000^6317 ≤ 10756744838747^6317*15625000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8264793 15625000 10756744838747 25000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (106545741/500000000 : ℝ)^8365 ≤ (1613593698769/12500000000000 : ℝ)^6317 := by
    have hnat : (106545741 : ℕ)^8365*12500000000000^6317 ≤ 1613593698769^6317*500000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106545741 500000000 1613593698769 12500000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5385484057/10000000000 : ℝ)^8365 ≤ (11016067758379/25000000000000 : ℝ)^6317 := by
    have hnat : (5385484057 : ℕ)^8365*25000000000000^6317 ≤ 11016067758379^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385484057 10000000000 11016067758379 25000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8264793/15625000 : ℝ), (-106545741/500000000 : ℝ), (5385484057/10000000000 : ℝ)] ![(10756744838747/25000000000000 : ℝ), (1613593698769/12500000000000 : ℝ), (11016067758379/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8264793/15625000 : ℝ)|^8365 ≤ (10756744838747/25000000000000 : ℝ)^6317
        have hw : |(8264793/15625000 : ℝ)|=(8264793/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-106545741/500000000 : ℝ)|^8365 ≤ (1613593698769/12500000000000 : ℝ)^6317
        have hw : |(-106545741/500000000 : ℝ)|=(106545741/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5385484057/10000000000 : ℝ)|^8365 ≤ (11016067758379/25000000000000 : ℝ)^6317
        have hw : |(5385484057/10000000000 : ℝ)|=(5385484057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_box_10 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5289467251/10000000000 : ℝ)*x 0 + (2692741829/5000000000 : ℝ)*x 1 + (-2130915721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289467251/10000000000 : ℝ)^8365 ≤ (43026976457403/100000000000000 : ℝ)^6317 := by
    have hnat : (5289467251 : ℕ)^8365*100000000000000^6317 ≤ 43026976457403^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289467251 10000000000 43026976457403 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2692741829/5000000000 : ℝ)^8365 ≤ (4406426671047/10000000000000 : ℝ)^6317 := by
    have hnat : (2692741829 : ℕ)^8365*10000000000000^6317 ≤ 4406426671047^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692741829 5000000000 4406426671047 10000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2130915721/10000000000 : ℝ)^8365 ≤ (12908756817817/100000000000000 : ℝ)^6317 := by
    have hnat : (2130915721 : ℕ)^8365*100000000000000^6317 ≤ 12908756817817^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2130915721 10000000000 12908756817817 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289467251/10000000000 : ℝ), (2692741829/5000000000 : ℝ), (-2130915721/10000000000 : ℝ)] ![(43026976457403/100000000000000 : ℝ), (4406426671047/10000000000000 : ℝ), (12908756817817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289467251/10000000000 : ℝ)|^8365 ≤ (43026976457403/100000000000000 : ℝ)^6317
        have hw : |(5289467251/10000000000 : ℝ)|=(5289467251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2692741829/5000000000 : ℝ)|^8365 ≤ (4406426671047/10000000000000 : ℝ)^6317
        have hw : |(2692741829/5000000000 : ℝ)|=(2692741829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2130915721/10000000000 : ℝ)|^8365 ≤ (12908756817817/100000000000000 : ℝ)^6317
        have hw : |(-2130915721/10000000000 : ℝ)|=(2130915721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_box_11 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4489291881/10000000000 : ℝ)*x 0 + (2149000151/5000000000 : ℝ)*x 1 + (268625023/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4489291881/10000000000 : ℝ)^8365 ≤ (8656699328359/25000000000000 : ℝ)^6317 := by
    have hnat : (4489291881 : ℕ)^8365*25000000000000^6317 ≤ 8656699328359^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4489291881 10000000000 8656699328359 25000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2149000151/5000000000 : ℝ)^8365 ≤ (32686600998813/100000000000000 : ℝ)^6317 := by
    have hnat : (2149000151 : ℕ)^8365*100000000000000^6317 ≤ 32686600998813^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149000151 5000000000 32686600998813 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (268625023/625000000 : ℝ)^8365 ≤ (16343300831739/50000000000000 : ℝ)^6317 := by
    have hnat : (268625023 : ℕ)^8365*50000000000000^6317 ≤ 16343300831739^6317*625000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268625023 625000000 16343300831739 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4489291881/10000000000 : ℝ), (2149000151/5000000000 : ℝ), (268625023/625000000 : ℝ)] ![(8656699328359/25000000000000 : ℝ), (32686600998813/100000000000000 : ℝ), (16343300831739/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4489291881/10000000000 : ℝ)|^8365 ≤ (8656699328359/25000000000000 : ℝ)^6317
        have hw : |(4489291881/10000000000 : ℝ)|=(4489291881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2149000151/5000000000 : ℝ)|^8365 ≤ (32686600998813/100000000000000 : ℝ)^6317
        have hw : |(2149000151/5000000000 : ℝ)|=(2149000151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(268625023/625000000 : ℝ)|^8365 ≤ (16343300831739/50000000000000 : ℝ)^6317
        have hw : |(268625023/625000000 : ℝ)|=(268625023/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_box_12 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-16640023/80000000 : ℝ)*x 0 + (42491009/78125000 : ℝ)*x 1 + (5273463559/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16640023/80000000 : ℝ)^8365 ≤ (125019332447/1000000000000 : ℝ)^6317 := by
    have hnat : (16640023 : ℕ)^8365*1000000000000^6317 ≤ 125019332447^6317*80000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16640023 80000000 125019332447 1000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42491009/78125000 : ℝ)^8365 ≤ (22321696268977/50000000000000 : ℝ)^6317 := by
    have hnat : (42491009 : ℕ)^8365*50000000000000^6317 ≤ 22321696268977^6317*78125000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42491009 78125000 22321696268977 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5273463559/10000000000 : ℝ)^8365 ≤ (669604284479/1562500000000 : ℝ)^6317 := by
    have hnat : (5273463559 : ℕ)^8365*1562500000000^6317 ≤ 669604284479^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5273463559 10000000000 669604284479 1562500000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-16640023/80000000 : ℝ), (42491009/78125000 : ℝ), (5273463559/10000000000 : ℝ)] ![(125019332447/1000000000000 : ℝ), (22321696268977/50000000000000 : ℝ), (669604284479/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-16640023/80000000 : ℝ)|^8365 ≤ (125019332447/1000000000000 : ℝ)^6317
        have hw : |(-16640023/80000000 : ℝ)|=(16640023/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(42491009/78125000 : ℝ)|^8365 ≤ (22321696268977/50000000000000 : ℝ)^6317
        have hw : |(42491009/78125000 : ℝ)|=(42491009/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5273463559/10000000000 : ℝ)|^8365 ≤ (669604284479/1562500000000 : ℝ)^6317
        have hw : |(5273463559/10000000000 : ℝ)|=(5273463559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_box_13 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5368557329/10000000000 : ℝ)*x 0 + (-2175096531/10000000000 : ℝ)*x 1 + (2636731969/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368557329/10000000000 : ℝ)^8365 ≤ (685640132953/1562500000000 : ℝ)^6317 := by
    have hnat : (5368557329 : ℕ)^8365*1562500000000^6317 ≤ 685640132953^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368557329 10000000000 685640132953 1562500000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2175096531/10000000000 : ℝ)^8365 ≤ (1658044149423/12500000000000 : ℝ)^6317 := by
    have hnat : (2175096531 : ℕ)^8365*12500000000000^6317 ≤ 1658044149423^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175096531 10000000000 1658044149423 12500000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2636731969/5000000000 : ℝ)^8365 ≤ (42854678285119/100000000000000 : ℝ)^6317 := by
    have hnat : (2636731969 : ℕ)^8365*100000000000000^6317 ≤ 42854678285119^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636731969 5000000000 42854678285119 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368557329/10000000000 : ℝ), (-2175096531/10000000000 : ℝ), (2636731969/5000000000 : ℝ)] ![(685640132953/1562500000000 : ℝ), (1658044149423/12500000000000 : ℝ), (42854678285119/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368557329/10000000000 : ℝ)|^8365 ≤ (685640132953/1562500000000 : ℝ)^6317
        have hw : |(5368557329/10000000000 : ℝ)|=(5368557329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2175096531/10000000000 : ℝ)|^8365 ≤ (1658044149423/12500000000000 : ℝ)^6317
        have hw : |(-2175096531/10000000000 : ℝ)|=(2175096531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2636731969/5000000000 : ℝ)|^8365 ≤ (42854678285119/100000000000000 : ℝ)^6317
        have hw : |(2636731969/5000000000 : ℝ)|=(2636731969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_box_14 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (33553483/62500000 : ℝ)*x 0 + (5273464013/10000000000 : ℝ)*x 1 + (-135943531/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33553483/62500000 : ℝ)^8365 ≤ (21940483989317/50000000000000 : ℝ)^6317 := by
    have hnat : (33553483 : ℕ)^8365*50000000000000^6317 ≤ 21940483989317^6317*62500000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33553483 62500000 21940483989317 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5273464013/10000000000 : ℝ)^8365 ≤ (42854679092203/100000000000000 : ℝ)^6317 := by
    have hnat : (5273464013 : ℕ)^8365*100000000000000^6317 ≤ 42854679092203^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5273464013 10000000000 42854679092203 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135943531/625000000 : ℝ)^8365 ≤ (6632176456373/50000000000000 : ℝ)^6317 := by
    have hnat : (135943531 : ℕ)^8365*50000000000000^6317 ≤ 6632176456373^6317*625000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135943531 625000000 6632176456373 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33553483/62500000 : ℝ), (5273464013/10000000000 : ℝ), (-135943531/625000000 : ℝ)] ![(21940483989317/50000000000000 : ℝ), (42854679092203/100000000000000 : ℝ), (6632176456373/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33553483/62500000 : ℝ)|^8365 ≤ (21940483989317/50000000000000 : ℝ)^6317
        have hw : |(33553483/62500000 : ℝ)|=(33553483/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5273464013/10000000000 : ℝ)|^8365 ≤ (42854679092203/100000000000000 : ℝ)^6317
        have hw : |(5273464013/10000000000 : ℝ)|=(5273464013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-135943531/625000000 : ℝ)|^8365 ≤ (6632176456373/50000000000000 : ℝ)^6317
        have hw : |(-135943531/625000000 : ℝ)|=(135943531/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_box_15 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2117155697/5000000000 : ℝ)*x 0 + (4425488181/10000000000 : ℝ)*x 1 + (2212744049/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2117155697/5000000000 : ℝ)^8365 ≤ (32046756830637/100000000000000 : ℝ)^6317 := by
    have hnat : (2117155697 : ℕ)^8365*100000000000000^6317 ≤ 32046756830637^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117155697 5000000000 32046756830637 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4425488181/10000000000 : ℝ)^8365 ≤ (6795324400427/20000000000000 : ℝ)^6317 := by
    have hnat : (4425488181 : ℕ)^8365*20000000000000^6317 ≤ 6795324400427^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4425488181 10000000000 6795324400427 20000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2212744049/5000000000 : ℝ)^8365 ≤ (33976621158311/100000000000000 : ℝ)^6317 := by
    have hnat : (2212744049 : ℕ)^8365*100000000000000^6317 ≤ 33976621158311^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2212744049 5000000000 33976621158311 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2117155697/5000000000 : ℝ), (4425488181/10000000000 : ℝ), (2212744049/5000000000 : ℝ)] ![(32046756830637/100000000000000 : ℝ), (6795324400427/20000000000000 : ℝ), (33976621158311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2117155697/5000000000 : ℝ)|^8365 ≤ (32046756830637/100000000000000 : ℝ)^6317
        have hw : |(2117155697/5000000000 : ℝ)|=(2117155697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4425488181/10000000000 : ℝ)|^8365 ≤ (6795324400427/20000000000000 : ℝ)^6317
        have hw : |(4425488181/10000000000 : ℝ)|=(4425488181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2212744049/5000000000 : ℝ)|^8365 ≤ (33976621158311/100000000000000 : ℝ)^6317
        have hw : |(2212744049/5000000000 : ℝ)|=(2212744049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1172_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150059381/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2813/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11393/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(12447/20000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29661/50000 : ℝ) ∧ (799/1000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (83191/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2813/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11393/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2813/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11393/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2813/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11393/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2813/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11393/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2813/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11393/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2813/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11393/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11393/100000 : ℝ) ^ (2091/512 : ℝ) ≤ (14038630056247643/100000000000000000000 : ℝ) := by
    have hpowers : (11393/100000 : ℝ)^2091 ≤ (14038630056247643/100000000000000000000 : ℝ)^512 := by
      have hnat : (11393 : ℕ)^2091*100000000000000000000^512 ≤ 14038630056247643^512*100000^2091 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11393 100000 14038630056247643 100000000000000000000 2091 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11393/100000 : ℝ)) (X := (14038630056247643/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2091 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2813/20000 : ℝ) ^ (2091/512 : ℝ) ≤ (33190668077944823/100000000000000000000 : ℝ) := by
    have hpowers : (2813/20000 : ℝ)^2091 ≤ (33190668077944823/100000000000000000000 : ℝ)^512 := by
      have hnat : (2813 : ℕ)^2091*100000000000000000000^512 ≤ 33190668077944823^512*20000^2091 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2813 20000 33190668077944823 100000000000000000000 2091 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2813/20000 : ℝ)) (X := (33190668077944823/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2091 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014038630056247643/50000000000000000000 : ℝ) ≤ (5000343711942947/5000000000000000 : ℝ) ^ (2091/512 : ℝ) := by
    have hpowers : (50014038630056247643/50000000000000000000 : ℝ)^512 ≤ (5000343711942947/5000000000000000 : ℝ)^2091 := by
      have hnat : (50014038630056247643 : ℕ)^512*5000000000000000^2091 ≤ 5000343711942947^2091*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014038630056247643 50000000000000000000 5000343711942947 5000000000000000 512 2091 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000343711942947/5000000000000000 : ℝ)) (X := (50014038630056247643/50000000000000000000 : ℝ)) (by norm_num) 2091 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023614649067096233/50000000000000000000 : ℝ) ≤ (1000115624532347/1000000000000000 : ℝ) ^ (2091/512 : ℝ) := by
    have hpowers : (50023614649067096233/50000000000000000000 : ℝ)^512 ≤ (1000115624532347/1000000000000000 : ℝ)^2091 := by
      have hnat : (50023614649067096233 : ℕ)^512*1000000000000000^2091 ≤ 1000115624532347^2091*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023614649067096233 50000000000000000000 1000115624532347 1000000000000000 512 2091 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000115624532347/1000000000000000 : ℝ)) (X := (50023614649067096233/50000000000000000000 : ℝ)) (by norm_num) 2091 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033190668077944823/50000000000000000000 : ℝ) ≤ (5000812533380523/5000000000000000 : ℝ) ^ (2091/512 : ℝ) := by
    have hpowers : (50033190668077944823/50000000000000000000 : ℝ)^512 ≤ (5000812533380523/5000000000000000 : ℝ)^2091 := by
      have hnat : (50033190668077944823 : ℕ)^512*5000000000000000^2091 ≤ 5000812533380523^2091*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033190668077944823 50000000000000000000 5000812533380523 5000000000000000 512 2091 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000812533380523/5000000000000000 : ℝ)) (X := (50033190668077944823/50000000000000000000 : ℝ)) (by norm_num) 2091 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14038630056247643/100000000000000000000 : ℝ) ≤ ((1669447139459156377/1670000000000000000 : ℝ)+2*(58602679697/33400000000000 : ℝ)*(11393/100000 : ℝ))^(2091/512 : ℝ) := by
    rw [show (1669447139459156377/1670000000000000000 : ℝ)+2*(58602679697/33400000000000 : ℝ)*(11393/100000 : ℝ)=(5000343711942947/5000000000000000 : ℝ) by norm_num, show 1+2*(14038630056247643/100000000000000000000 : ℝ)=(50014038630056247643/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33190668077944823/100000000000000000000 : ℝ)+(14038630056247643/100000000000000000000 : ℝ) ≤ ((1669447139459156377/1670000000000000000 : ℝ)+(58602679697/33400000000000 : ℝ)*((2813/20000 : ℝ)+(11393/100000 : ℝ)))^(2091/512 : ℝ) := by
    rw [show (1669447139459156377/1670000000000000000 : ℝ)+(58602679697/33400000000000 : ℝ)*((2813/20000 : ℝ)+(11393/100000 : ℝ))=(1000115624532347/1000000000000000 : ℝ) by norm_num, show 1+(33190668077944823/100000000000000000000 : ℝ)+(14038630056247643/100000000000000000000 : ℝ)=(50023614649067096233/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33190668077944823/100000000000000000000 : ℝ) ≤ ((1669447139459156377/1670000000000000000 : ℝ)+2*(58602679697/33400000000000 : ℝ)*(2813/20000 : ℝ))^(2091/512 : ℝ) := by
    rw [show (1669447139459156377/1670000000000000000 : ℝ)+2*(58602679697/33400000000000 : ℝ)*(2813/20000 : ℝ)=(5000812533380523/5000000000000000 : ℝ) by norm_num, show 1+2*(33190668077944823/100000000000000000000 : ℝ)=(50033190668077944823/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1669447139459156377/1670000000000000000 : ℝ)*(X 1 0+X 2 0)+(58602679697/33400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2091/512 : ℝ)) (lo := (11393/100000 : ℝ)) (hi := (2813/20000 : ℝ)) (c := (1669447139459156377/1670000000000000000 : ℝ)) (alpha := (58602679697/33400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1669447139459156377/1670000000000000000 : ℝ)*(X 0 1+X 2 1)+(58602679697/33400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2091/512 : ℝ)) (lo := (11393/100000 : ℝ)) (hi := (2813/20000 : ℝ)) (c := (1669447139459156377/1670000000000000000 : ℝ)) (alpha := (58602679697/33400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1669447139459156377/1670000000000000000 : ℝ)*(X 0 2+X 1 2)+(58602679697/33400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2091/512 : ℝ)) (lo := (11393/100000 : ℝ)) (hi := (2813/20000 : ℝ)) (c := (1669447139459156377/1670000000000000000 : ℝ)) (alpha := (58602679697/33400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1013360959/5000000000 : ℝ)*X 0 0+(1343968813/2500000000 : ℝ)*X 0 1+(2687936841/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5296254623/10000000000 : ℝ)*X 1 0+(-266846657/1250000000 : ℝ)*X 1 1+(1343968671/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((529625561/1000000000 : ℝ)*X 2 0+(5375873597/10000000000 : ℝ)*X 2 1+(-426954679/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((558460891/1250000000 : ℝ)*X 0 0+(2154471389/5000000000 : ℝ)*X 0 1+(2154471837/5000000000 : ℝ)*X 0 2+(558460891/1250000000 : ℝ)*X 1 0+(2154471389/5000000000 : ℝ)*X 1 1+(2154471837/5000000000 : ℝ)*X 1 2+(558460891/1250000000 : ℝ)*X 2 0+(2154471389/5000000000 : ℝ)*X 2 1+(2154471837/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2279912161/10000000000 : ℝ)*X 0 0+(660189329/1250000000 : ℝ)*X 0 1+(1320378927/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((21451501/40000000 : ℝ)*X 1 0+(-434395771/2000000000 : ℝ)*X 1 1+(528151509/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1072575063/2000000000 : ℝ)*X 2 0+(5281514943/10000000000 : ℝ)*X 2 1+(-1085989481/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4252871921/10000000000 : ℝ)*X 0 0+(2208165219/5000000000 : ℝ)*X 0 1+(4416330013/10000000000 : ℝ)*X 0 2+(4252871921/10000000000 : ℝ)*X 1 0+(2208165219/5000000000 : ℝ)*X 1 1+(4416330013/10000000000 : ℝ)*X 1 2+(4252871921/10000000000 : ℝ)*X 2 0+(2208165219/5000000000 : ℝ)*X 2 1+(4416330013/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-139183277/625000000 : ℝ)*X 0 0+(1043456811/2000000000 : ℝ)*X 0 1+(5385484651/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((8264793/15625000 : ℝ)*X 1 0+(-106545741/500000000 : ℝ)*X 1 1+(5385484057/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5289467251/10000000000 : ℝ)*X 2 0+(2692741829/5000000000 : ℝ)*X 2 1+(-2130915721/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4489291881/10000000000 : ℝ)*X 0 0+(2149000151/5000000000 : ℝ)*X 0 1+(268625023/625000000 : ℝ)*X 0 2+(4489291881/10000000000 : ℝ)*X 1 0+(2149000151/5000000000 : ℝ)*X 1 1+(268625023/625000000 : ℝ)*X 1 2+(4489291881/10000000000 : ℝ)*X 2 0+(2149000151/5000000000 : ℝ)*X 2 1+(268625023/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-16640023/80000000 : ℝ)*X 0 0+(42491009/78125000 : ℝ)*X 0 1+(5273463559/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5368557329/10000000000 : ℝ)*X 1 0+(-2175096531/10000000000 : ℝ)*X 1 1+(2636731969/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((33553483/62500000 : ℝ)*X 2 0+(5273464013/10000000000 : ℝ)*X 2 1+(-135943531/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2117155697/5000000000 : ℝ)*X 0 0+(4425488181/10000000000 : ℝ)*X 0 1+(2212744049/5000000000 : ℝ)*X 0 2+(2117155697/5000000000 : ℝ)*X 1 0+(4425488181/10000000000 : ℝ)*X 1 1+(2212744049/5000000000 : ℝ)*X 1 2+(2117155697/5000000000 : ℝ)*X 2 0+(4425488181/10000000000 : ℝ)*X 2 1+(2212744049/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-12447/20000 : ℝ) ≤ (-811937733405334950665664092043/1304687500000000000000000000000 : ℝ) := by norm_num
    linear_combination (12868853/10000000000000 : ℝ)*(lower0) + (493603/100000000000000 : ℝ)*(upper1) + (8916013/25000000000000 : ℝ)*(lower4) + (30826571959493/781250000000 : ℝ)*(major0) + (30826571959493/781250000000 : ℝ)*(major1) + (30826571959493/781250000000 : ℝ)*(major2) + (32169963631/100000000000000 : ℝ)*(sp1) + (42678200603/100000000000000 : ℝ)*(sp2) + (2779373361/25000000000000 : ℝ)*(sp3) + (5282825486333619/100000000000000 : ℝ)*(sp4) + (2641410587549333/50000000000000 : ℝ)*(sp5) + (2641405333430847/50000000000000 : ℝ)*(sp6) + (328685259601769/12500000000000 : ℝ)*(sp7) + (13929364339/50000000000000 : ℝ)*(sp12) + (525898638861519/20000000000000 : ℝ)*(f.failure) + (5282853345062297/100000000000000 : ℝ)*(f.sum) + (4032041932281/835000000000000000000000000 : ℝ)*base66 + (15812449420938139/1304687500000000000000000000000 : ℝ)*base68 + (1907867665269691/326171875000000000000000000000 : ℝ)*base70 + (37732525038048153/2609375000000000000000000000000 : ℝ)*base72 + (6724386036663/417500000000000000000000000 : ℝ)*base74 + (13154545922250639/1304687500000000000000000000000 : ℝ)*base76 + (20158925793313139/1304687500000000000000000000000 : ℝ)*base78 + (98864522185889347/2609375000000000000000000000000 : ℝ)*base79 + (1743101108121/835000000000000000000000000 : ℝ)*base82 + (5859739/2000000000000000000000 : ℝ)*base89 + (5859739/2000000000000000000000 : ℝ)*base91 + (5859739/2000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (29661/50000 : ℝ) ≤ (3095990562874179244863450423747/5218750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (84806951/20000000000000 : ℝ)*(upper0) + (22280919/20000000000000 : ℝ)*(upper3) + (26228341/10000000000000 : ℝ)*(upper4) + (250652227084229/6250000000000 : ℝ)*(major0) + (250652227084229/6250000000000 : ℝ)*(major1) + (250652227084229/6250000000000 : ℝ)*(major2) + (666062572520783/12500000000000 : ℝ)*(sp0) + (213139560453703/4000000000000 : ℝ)*(sp1) + (5328528585028349/100000000000000 : ℝ)*(sp2) + (1336277466270227/50000000000000 : ℝ)*(sp3) + (10426820119/25000000000000 : ℝ)*(sp5) + (2133594701/100000000000000 : ℝ)*(sp6) + (10825509463/100000000000000 : ℝ)*(sp7) + (15069228393/50000000000000 : ℝ)*(sp8) + (1336282879024959/50000000000000 : ℝ)*(f.failure) + (106570614372461/2000000000000 : ℝ)*(f.sum) + (107772447981/835000000000000000000000000 : ℝ)*base66 + (21945972869621667/10437500000000000000000000000000 : ℝ)*base68 + (6098038025559167/10437500000000000000000000000000 : ℝ)*base70 + (176727167327871667/10437500000000000000000000000000 : ℝ)*base72 + (3416014644597/417500000000000000000000000 : ℝ)*base73 + (100020908888184167/10437500000000000000000000000000 : ℝ)*base76 + (49169441087871667/10437500000000000000000000000000 : ℝ)*base78 + (271772468528746667/10437500000000000000000000000000 : ℝ)*base80 + (2108162923787/417500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (31090379/5000000000000000000000 : ℝ)*base89 + (31090379/5000000000000000000000 : ℝ)*base91 + (31090379/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (799/1000 : ℝ) ≤ (13343656604882253970684035350337/16700000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (255379443/50000000000000 : ℝ)*(upper0) + (275365819/100000000000000 : ℝ)*(upper1) + (51332321/20000000000000 : ℝ)*(upper2) + (69636739/10000000000000 : ℝ)*(lower5) + (895605908109827/20000000000000 : ℝ)*(major0) + (895605908109827/20000000000000 : ℝ)*(major1) + (895605908109827/20000000000000 : ℝ)*(major2) + (142526625819/100000000000000 : ℝ)*(sp1) + (13511654757/25000000000000 : ℝ)*(sp3) + (10327188801/50000000000000 : ℝ)*(sp4) + (2972616354277911/50000000000000 : ℝ)*(sp8) + (2972555418153803/50000000000000 : ℝ)*(sp9) + (237810134517337/4000000000000 : ℝ)*(sp10) + (1492058813213141/50000000000000 : ℝ)*(sp11) + (298417167304531/10000000000000 : ℝ)*(f.failure) + (237810134517337/4000000000000 : ℝ)*(f.sum) + (2751679951581/334000000000000000000000000 : ℝ)*base66 + (53776735629566779/33400000000000000000000000000000 : ℝ)*base67 + (335141326728033221/33400000000000000000000000000000 : ℝ)*base70 + (409820232987833221/33400000000000000000000000000000 : ℝ)*base72 + (2042139094843/334000000000000000000000000 : ℝ)*base73 + (184161416288033221/33400000000000000000000000000000 : ℝ)*base76 + (600029770009033221/33400000000000000000000000000000 : ℝ)*base78 + (345513111231166779/33400000000000000000000000000000 : ℝ)*base79 + (996609923937/334000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (10355311/1000000000000000000000 : ℝ)*base89 + (10355311/1000000000000000000000 : ℝ)*base91 + (10355311/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-83191/100000 : ℝ) ≤ (-69462658630299137308762408348299/83500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14843439/50000000000000 : ℝ)*(lower0) + (18421037/25000000000000 : ℝ)*(upper3) + (83312721/100000000000000 : ℝ)*(upper5) + (4513187149312843/100000000000000 : ℝ)*(major0) + (4513187149312843/100000000000000 : ℝ)*(major1) + (4513187149312843/100000000000000 : ℝ)*(major2) + (456739391/6250000000000 : ℝ)*(sp0) + (26071324379/50000000000000 : ℝ)*(sp5) + (11637987231/25000000000000 : ℝ)*(sp7) + (437844609/4000000000000 : ℝ)*(sp8) + (6046484845004179/100000000000000 : ℝ)*(sp12) + (3023225478150451/50000000000000 : ℝ)*(sp13) + (302325154947483/5000000000000 : ℝ)*(sp14) + (18797214074817/625000000000 : ℝ)*(sp15) + (601520160783929/20000000000000 : ℝ)*(f.failure) + (302325154947483/5000000000000 : ℝ)*(f.sum) + (4537708017401/1670000000000000000000000000 : ℝ)*base65 + (1421006412250999811/167000000000000000000000000000000 : ℝ)*base67 + (1957340844559999811/167000000000000000000000000000000 : ℝ)*base69 + (1106592203145999811/167000000000000000000000000000000 : ℝ)*base71 + (25808399938029/1670000000000000000000000000 : ℝ)*base74 + (405446055503999811/167000000000000000000000000000000 : ℝ)*base75 + (1496758554631999811/167000000000000000000000000000000 : ℝ)*base77 + (10925724992255999811/167000000000000000000000000000000 : ℝ)*base79 + (3033155755469/1670000000000000000000000000 : ℝ)*base82 + (487949/2000000000000000000000 : ℝ)*base89 + (487949/2000000000000000000000 : ℝ)*base91 + (487949/2000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1172_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150059381/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2813/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11393/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12447/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(29661/50000 : ℝ) else (799/1000 : ℝ) ≤ X j i ∧ X j i ≤ (83191/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1172_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1172_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150059381/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7033/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (356/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12447/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(29661/50000 : ℝ) else (799/1000 : ℝ) ≤ X j i ∧ X j i ≤ (83191/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1172_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1172_s10 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1172_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150059381/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7033/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (356/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12447/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(29661/50000 : ℝ) else (799/1000 : ℝ) ≤ X j i ∧ X j i ≤ (83191/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1172_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
