-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1129_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:25:59.655536+00:00
-- url     : https://prove2.me/submissions/188bc272-492b-45ed-84d0-fb9b6d000591

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
theorem support_rectangle_w1129_s0_0 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1895931819/10000000000 : ℝ)*x 0 + (757167477/1250000000 : ℝ)*x 1 + (4778825999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1895931819/10000000000 : ℝ)^4161 ≤ (5508773297337/50000000000000 : ℝ)^3137 := by
    have hnat : (1895931819 : ℕ)^4161*50000000000000^3137 ≤ 5508773297337^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1895931819 10000000000 5508773297337 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (757167477/1250000000 : ℝ)^4161 ≤ (51429581282017/100000000000000 : ℝ)^3137 := by
    have hnat : (757167477 : ℕ)^4161*100000000000000^3137 ≤ 51429581282017^3137*1250000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      757167477 1250000000 51429581282017 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4778825999/10000000000 : ℝ)^4161 ≤ (37552872106719/100000000000000 : ℝ)^3137 := by
    have hnat : (4778825999 : ℕ)^4161*100000000000000^3137 ≤ 37552872106719^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4778825999 10000000000 37552872106719 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1895931819/10000000000 : ℝ), (757167477/1250000000 : ℝ), (4778825999/10000000000 : ℝ)] ![(5508773297337/50000000000000 : ℝ), (51429581282017/100000000000000 : ℝ), (37552872106719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1895931819/10000000000 : ℝ)|^4161 ≤ (5508773297337/50000000000000 : ℝ)^3137
        have hw : |(-1895931819/10000000000 : ℝ)|=(1895931819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(757167477/1250000000 : ℝ)|^4161 ≤ (51429581282017/100000000000000 : ℝ)^3137
        have hw : |(757167477/1250000000 : ℝ)|=(757167477/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4778825999/10000000000 : ℝ)|^4161 ≤ (37552872106719/100000000000000 : ℝ)^3137
        have hw : |(4778825999/10000000000 : ℝ)|=(4778825999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s0_1 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (86211343/156250000 : ℝ)*x 0 + (-164376387/625000000 : ℝ)*x 1 + (597353231/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (86211343/156250000 : ℝ)^4161 ≤ (45440479152327/100000000000000 : ℝ)^3137 := by
    have hnat : (86211343 : ℕ)^4161*100000000000000^3137 ≤ 45440479152327^3137*156250000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86211343 156250000 45440479152327 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (164376387/625000000 : ℝ)^4161 ≤ (4251662574559/25000000000000 : ℝ)^3137 := by
    have hnat : (164376387 : ℕ)^4161*25000000000000^3137 ≤ 4251662574559^3137*625000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164376387 625000000 4251662574559 25000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (597353231/1250000000 : ℝ)^4161 ≤ (37552870532801/100000000000000 : ℝ)^3137 := by
    have hnat : (597353231 : ℕ)^4161*100000000000000^3137 ≤ 37552870532801^3137*1250000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      597353231 1250000000 37552870532801 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(86211343/156250000 : ℝ), (-164376387/625000000 : ℝ), (597353231/1250000000 : ℝ)] ![(45440479152327/100000000000000 : ℝ), (4251662574559/25000000000000 : ℝ), (37552870532801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(86211343/156250000 : ℝ)|^4161 ≤ (45440479152327/100000000000000 : ℝ)^3137
        have hw : |(86211343/156250000 : ℝ)|=(86211343/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-164376387/625000000 : ℝ)|^4161 ≤ (4251662574559/25000000000000 : ℝ)^3137
        have hw : |(-164376387/625000000 : ℝ)|=(164376387/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(597353231/1250000000 : ℝ)|^4161 ≤ (37552870532801/100000000000000 : ℝ)^3137
        have hw : |(597353231/1250000000 : ℝ)|=(597353231/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s0_2 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5517526181/10000000000 : ℝ)*x 0 + (298676611/625000000 : ℝ)*x 1 + (-657505497/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5517526181/10000000000 : ℝ)^4161 ≤ (45440481653923/100000000000000 : ℝ)^3137 := by
    have hnat : (5517526181 : ℕ)^4161*100000000000000^3137 ≤ 45440481653923^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5517526181 10000000000 45440481653923 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (298676611/625000000 : ℝ)^4161 ≤ (9388217445581/25000000000000 : ℝ)^3137 := by
    have hnat : (298676611 : ℕ)^4161*25000000000000^3137 ≤ 9388217445581^3137*625000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      298676611 625000000 9388217445581 25000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (657505497/2500000000 : ℝ)^4161 ≤ (17006648548499/100000000000000 : ℝ)^3137 := by
    have hnat : (657505497 : ℕ)^4161*100000000000000^3137 ≤ 17006648548499^3137*2500000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657505497 2500000000 17006648548499 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5517526181/10000000000 : ℝ), (298676611/625000000 : ℝ), (-657505497/2500000000 : ℝ)] ![(45440481653923/100000000000000 : ℝ), (9388217445581/25000000000000 : ℝ), (17006648548499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5517526181/10000000000 : ℝ)|^4161 ≤ (45440481653923/100000000000000 : ℝ)^3137
        have hw : |(5517526181/10000000000 : ℝ)|=(5517526181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(298676611/625000000 : ℝ)|^4161 ≤ (9388217445581/25000000000000 : ℝ)^3137
        have hw : |(298676611/625000000 : ℝ)|=(298676611/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-657505497/2500000000 : ℝ)|^4161 ≤ (17006648548499/100000000000000 : ℝ)^3137
        have hw : |(-657505497/2500000000 : ℝ)|=(657505497/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s0_3 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2101022043/5000000000 : ℝ)*x 0 + (3121688397/10000000000 : ℝ)*x 1 + (1414693637/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2101022043/5000000000 : ℝ)^4161 ≤ (15831357769479/50000000000000 : ℝ)^3137 := by
    have hnat : (2101022043 : ℕ)^4161*50000000000000^3137 ≤ 15831357769479^3137*5000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2101022043 5000000000 15831357769479 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3121688397/10000000000 : ℝ)^4161 ≤ (21347395165049/100000000000000 : ℝ)^3137 := by
    have hnat : (3121688397 : ℕ)^4161*100000000000000^3137 ≤ 21347395165049^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3121688397 10000000000 21347395165049 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1414693637/2500000000 : ℝ)^4161 ≤ (23494944641449/50000000000000 : ℝ)^3137 := by
    have hnat : (1414693637 : ℕ)^4161*50000000000000^3137 ≤ 23494944641449^3137*2500000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1414693637 2500000000 23494944641449 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2101022043/5000000000 : ℝ), (3121688397/10000000000 : ℝ), (1414693637/2500000000 : ℝ)] ![(15831357769479/50000000000000 : ℝ), (21347395165049/100000000000000 : ℝ), (23494944641449/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2101022043/5000000000 : ℝ)|^4161 ≤ (15831357769479/50000000000000 : ℝ)^3137
        have hw : |(2101022043/5000000000 : ℝ)|=(2101022043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3121688397/10000000000 : ℝ)|^4161 ≤ (21347395165049/100000000000000 : ℝ)^3137
        have hw : |(3121688397/10000000000 : ℝ)|=(3121688397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1414693637/2500000000 : ℝ)|^4161 ≤ (23494944641449/50000000000000 : ℝ)^3137
        have hw : |(1414693637/2500000000 : ℝ)|=(1414693637/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s0_4 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1901115949/10000000000 : ℝ)*x 0 + (30073839/62500000 : ℝ)*x 1 + (1204638521/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1901115949/10000000000 : ℝ)^4161 ≤ (2211504805767/20000000000000 : ℝ)^3137 := by
    have hnat : (1901115949 : ℕ)^4161*20000000000000^3137 ≤ 2211504805767^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1901115949 10000000000 2211504805767 20000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (30073839/62500000 : ℝ)^4161 ≤ (18948552579697/50000000000000 : ℝ)^3137 := by
    have hnat : (30073839 : ℕ)^4161*50000000000000^3137 ≤ 18948552579697^3137*62500000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30073839 62500000 18948552579697 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1204638521/2000000000 : ℝ)^4161 ≤ (51045370803123/100000000000000 : ℝ)^3137 := by
    have hnat : (1204638521 : ℕ)^4161*100000000000000^3137 ≤ 51045370803123^3137*2000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1204638521 2000000000 51045370803123 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1901115949/10000000000 : ℝ), (30073839/62500000 : ℝ), (1204638521/2000000000 : ℝ)] ![(2211504805767/20000000000000 : ℝ), (18948552579697/50000000000000 : ℝ), (51045370803123/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1901115949/10000000000 : ℝ)|^4161 ≤ (2211504805767/20000000000000 : ℝ)^3137
        have hw : |(-1901115949/10000000000 : ℝ)|=(1901115949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(30073839/62500000 : ℝ)|^4161 ≤ (18948552579697/50000000000000 : ℝ)^3137
        have hw : |(30073839/62500000 : ℝ)|=(30073839/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1204638521/2000000000 : ℝ)|^4161 ≤ (51045370803123/100000000000000 : ℝ)^3137
        have hw : |(1204638521/2000000000 : ℝ)|=(1204638521/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s0_5 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1292547433/2500000000 : ℝ)*x 0 + (-34641387/250000000 : ℝ)*x 1 + (240927701/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1292547433/2500000000 : ℝ)^4161 ≤ (20842864350953/50000000000000 : ℝ)^3137 := by
    have hnat : (1292547433 : ℕ)^4161*50000000000000^3137 ≤ 20842864350953^3137*2500000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1292547433 2500000000 20842864350953 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (34641387/250000000 : ℝ)^4161 ≤ (1817225344609/25000000000000 : ℝ)^3137 := by
    have hnat : (34641387 : ℕ)^4161*25000000000000^3137 ≤ 1817225344609^3137*250000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34641387 250000000 1817225344609 25000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (240927701/400000000 : ℝ)^4161 ≤ (51045369903827/100000000000000 : ℝ)^3137 := by
    have hnat : (240927701 : ℕ)^4161*100000000000000^3137 ≤ 51045369903827^3137*400000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      240927701 400000000 51045369903827 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1292547433/2500000000 : ℝ), (-34641387/250000000 : ℝ), (240927701/400000000 : ℝ)] ![(20842864350953/50000000000000 : ℝ), (1817225344609/25000000000000 : ℝ), (51045369903827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1292547433/2500000000 : ℝ)|^4161 ≤ (20842864350953/50000000000000 : ℝ)^3137
        have hw : |(1292547433/2500000000 : ℝ)|=(1292547433/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-34641387/250000000 : ℝ)|^4161 ≤ (1817225344609/25000000000000 : ℝ)^3137
        have hw : |(-34641387/250000000 : ℝ)|=(34641387/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(240927701/400000000 : ℝ)|^4161 ≤ (51045369903827/100000000000000 : ℝ)^3137
        have hw : |(240927701/400000000 : ℝ)|=(240927701/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s0_6 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5170189757/10000000000 : ℝ)*x 0 + (6023192519/10000000000 : ℝ)*x 1 + (-1385655451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5170189757/10000000000 : ℝ)^4161 ≤ (41685728969271/100000000000000 : ℝ)^3137 := by
    have hnat : (5170189757 : ℕ)^4161*100000000000000^3137 ≤ 41685728969271^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5170189757 10000000000 41685728969271 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6023192519/10000000000 : ℝ)^4161 ≤ (51045369836379/100000000000000 : ℝ)^3137 := by
    have hnat : (6023192519 : ℕ)^4161*100000000000000^3137 ≤ 51045369836379^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6023192519 10000000000 51045369836379 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1385655451/10000000000 : ℝ)^4161 ≤ (908612647081/12500000000000 : ℝ)^3137 := by
    have hnat : (1385655451 : ℕ)^4161*12500000000000^3137 ≤ 908612647081^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1385655451 10000000000 908612647081 12500000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5170189757/10000000000 : ℝ), (6023192519/10000000000 : ℝ), (-1385655451/10000000000 : ℝ)] ![(41685728969271/100000000000000 : ℝ), (51045369836379/100000000000000 : ℝ), (908612647081/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5170189757/10000000000 : ℝ)|^4161 ≤ (41685728969271/100000000000000 : ℝ)^3137
        have hw : |(5170189757/10000000000 : ℝ)|=(5170189757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6023192519/10000000000 : ℝ)|^4161 ≤ (51045369836379/100000000000000 : ℝ)^3137
        have hw : |(6023192519/10000000000 : ℝ)|=(6023192519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1385655451/10000000000 : ℝ)|^4161 ≤ (908612647081/12500000000000 : ℝ)^3137
        have hw : |(-1385655451/10000000000 : ℝ)|=(1385655451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s0_7 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (526541429/1250000000 : ℝ)*x 0 + (349582011/625000000 : ℝ)*x 1 + (15947251/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (526541429/1250000000 : ℝ)^4161 ≤ (31765575771537/100000000000000 : ℝ)^3137 := by
    have hnat : (526541429 : ℕ)^4161*100000000000000^3137 ≤ 31765575771537^3137*1250000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526541429 1250000000 31765575771537 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (349582011/625000000 : ℝ)^4161 ≤ (11567554549147/25000000000000 : ℝ)^3137 := by
    have hnat : (349582011 : ℕ)^4161*25000000000000^3137 ≤ 11567554549147^3137*625000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      349582011 625000000 11567554549147 25000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (15947251/50000000 : ℝ)^4161 ≤ (5491051501593/25000000000000 : ℝ)^3137 := by
    have hnat : (15947251 : ℕ)^4161*25000000000000^3137 ≤ 5491051501593^3137*50000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15947251 50000000 5491051501593 25000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(526541429/1250000000 : ℝ), (349582011/625000000 : ℝ), (15947251/50000000 : ℝ)] ![(31765575771537/100000000000000 : ℝ), (11567554549147/25000000000000 : ℝ), (5491051501593/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(526541429/1250000000 : ℝ)|^4161 ≤ (31765575771537/100000000000000 : ℝ)^3137
        have hw : |(526541429/1250000000 : ℝ)|=(526541429/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(349582011/625000000 : ℝ)|^4161 ≤ (11567554549147/25000000000000 : ℝ)^3137
        have hw : |(349582011/625000000 : ℝ)|=(349582011/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(15947251/50000000 : ℝ)|^4161 ≤ (5491051501593/25000000000000 : ℝ)^3137
        have hw : |(15947251/50000000 : ℝ)|=(15947251/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1129_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1193761/800000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (9/2500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5573/20000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (8321/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8321 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8321*1^2048 ≤ 0^2048*1^8321 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8321 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8321 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8321/2048 : ℝ) ≤ (483286210614624869/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8321 ≤ (483286210614624869/20000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8321*20000000000000000000^2048 ≤ 483286210614624869^2048*5^8321 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 483286210614624869 20000000000000000000 8321 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (483286210614624869/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8321 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8321/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8321 := by
      have hnat : (1 : ℕ)^2048*1^8321 ≤ 1^8321*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8321 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8321 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20483286210614624869/20000000000000000000 : ℝ) ≤ (10058940041566361/10000000000000000 : ℝ) ^ (8321/2048 : ℝ) := by
    have hpowers : (20483286210614624869/20000000000000000000 : ℝ)^2048 ≤ (10058940041566361/10000000000000000 : ℝ)^8321 := by
      have hnat : (20483286210614624869 : ℕ)^2048*10000000000000000^8321 ≤ 10058940041566361^8321*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20483286210614624869 20000000000000000000 10058940041566361 10000000000000000 2048 8321 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10058940041566361/10000000000000000 : ℝ)) (X := (20483286210614624869/20000000000000000000 : ℝ)) (by norm_num) 8321 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10483286210614624869/10000000000000000000 : ℝ) ≤ (5058940041566361/5000000000000000 : ℝ) ^ (8321/2048 : ℝ) := by
    have hpowers : (10483286210614624869/10000000000000000000 : ℝ)^2048 ≤ (5058940041566361/5000000000000000 : ℝ)^8321 := by
      have hnat : (10483286210614624869 : ℕ)^2048*5000000000000000^8321 ≤ 5058940041566361^8321*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10483286210614624869 10000000000000000000 5058940041566361 5000000000000000 2048 8321 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5058940041566361/5000000000000000 : ℝ)) (X := (10483286210614624869/10000000000000000000 : ℝ)) (by norm_num) 8321 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(58940041566361/4000000000000000 : ℝ)*(0 : ℝ))^(8321/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(58940041566361/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(483286210614624869/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(58940041566361/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8321/2048 : ℝ) := by
    rw [show (1 : ℝ)+(58940041566361/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10058940041566361/10000000000000000 : ℝ) by norm_num, show 1+(483286210614624869/20000000000000000000 : ℝ)+(0 : ℝ)=(20483286210614624869/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(483286210614624869/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(58940041566361/4000000000000000 : ℝ)*(2/5 : ℝ))^(8321/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(58940041566361/4000000000000000 : ℝ)*(2/5 : ℝ)=(5058940041566361/5000000000000000 : ℝ) by norm_num, show 1+2*(483286210614624869/20000000000000000000 : ℝ)=(10483286210614624869/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(58940041566361/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8321/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (58940041566361/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(58940041566361/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8321/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (58940041566361/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(58940041566361/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8321/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (58940041566361/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1895931819/10000000000 : ℝ)*X 0 0+(757167477/1250000000 : ℝ)*X 0 1+(4778825999/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((86211343/156250000 : ℝ)*X 1 0+(-164376387/625000000 : ℝ)*X 1 1+(597353231/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5517526181/10000000000 : ℝ)*X 2 0+(298676611/625000000 : ℝ)*X 2 1+(-657505497/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2101022043/5000000000 : ℝ)*X 0 0+(3121688397/10000000000 : ℝ)*X 0 1+(1414693637/2500000000 : ℝ)*X 0 2+(2101022043/5000000000 : ℝ)*X 1 0+(3121688397/10000000000 : ℝ)*X 1 1+(1414693637/2500000000 : ℝ)*X 1 2+(2101022043/5000000000 : ℝ)*X 2 0+(3121688397/10000000000 : ℝ)*X 2 1+(1414693637/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1901115949/10000000000 : ℝ)*X 0 0+(30073839/62500000 : ℝ)*X 0 1+(1204638521/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1292547433/2500000000 : ℝ)*X 1 0+(-34641387/250000000 : ℝ)*X 1 1+(240927701/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5170189757/10000000000 : ℝ)*X 2 0+(6023192519/10000000000 : ℝ)*X 2 1+(-1385655451/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((526541429/1250000000 : ℝ)*X 0 0+(349582011/625000000 : ℝ)*X 0 1+(15947251/50000000 : ℝ)*X 0 2+(526541429/1250000000 : ℝ)*X 1 0+(349582011/625000000 : ℝ)*X 1 1+(15947251/50000000 : ℝ)*X 1 2+(526541429/1250000000 : ℝ)*X 2 0+(349582011/625000000 : ℝ)*X 2 1+(15947251/50000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1906585304566580037/500000000000000000000000 : ℝ) := by norm_num
    linear_combination (13748371/25000000000000 : ℝ)*(base1) + (26982389/3125000000000 : ℝ)*(base19) + (823907409/100000000000000 : ℝ)*(base23) + (35995983/50000000000000 : ℝ)*(base24) + (180286859/100000000000000 : ℝ)*(upper3) + (588159054862141/100000000000000 : ℝ)*(major0) + (588159054862141/100000000000000 : ℝ)*(major1) + (588159054862141/100000000000000 : ℝ)*(major2) + (78216085394189/10000000000000 : ℝ)*(sp0) + (6110639089283/781250000000 : ℝ)*(sp1) + (48885110685331/6250000000000 : ℝ)*(sp2) + (39415380733347/10000000000000 : ℝ)*(sp3) + (373583253/20000000000000 : ℝ)*(sp4) + (363356741/25000000000000 : ℝ)*(sp7) + (197077657876959/50000000000000 : ℝ)*(f.failure) + (24442583339521/3125000000000 : ℝ)*(f.sum) + (209817936561099/200000000000000000000000000000 : ℝ)*base66 + (2438931720438901/400000000000000000000000000000 : ℝ)*base67 + (399294559961099/400000000000000000000000000000 : ℝ)*base70 + (547894511638901/400000000000000000000000000000 : ℝ)*base71 + (54855708838901/200000000000000000000000000000 : ℝ)*base73 + (1275100766761099/400000000000000000000000000000 : ℝ)*base76 + (1414636380438901/400000000000000000000000000000 : ℝ)*base77 + (2029186178038901/400000000000000000000000000000 : ℝ)*base79 + (1476598624361099/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (52799/40000000000000000000 : ℝ)*base89 + (52799/40000000000000000000 : ℝ)*base91 + (52799/40000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1033757142694708463681223/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (65249193/100000000000000 : ℝ)*(base1) + (1269487153/100000000000000 : ℝ)*(base19) + (636405411/50000000000000 : ℝ)*(base23) + (69149273/50000000000000 : ℝ)*(upper3) + (37139617/25000000000000 : ℝ)*(upper5) + (620751693280473/100000000000000 : ℝ)*(major0) + (620751693280473/100000000000000 : ℝ)*(major1) + (620751693280473/100000000000000 : ℝ)*(major2) + (2576790003/100000000000000 : ℝ)*(sp1) + (641711337/25000000000000 : ℝ)*(sp2) + (825505978026963/100000000000000 : ℝ)*(sp4) + (165100413300123/20000000000000 : ℝ)*(sp5) + (825502073121601/100000000000000 : ℝ)*(sp6) + (415997236241121/100000000000000 : ℝ)*(sp7) + (207998650745157/50000000000000 : ℝ)*(f.failure) + (825505912777771/100000000000000 : ℝ)*(f.sum) + (68699062031247/200000000000000000000000000000 : ℝ)*base66 + (2361460448568753/400000000000000000000000000000 : ℝ)*base67 + (2191324288968753/400000000000000000000000000000 : ℝ)*base69 + (544654091768753/400000000000000000000000000000 : ℝ)*base71 + (663012910968753/200000000000000000000000000000 : ℝ)*base73 + (1252087567368753/400000000000000000000000000000 : ℝ)*base75 + (24287471831247/400000000000000000000000000000 : ℝ)*base78 + (1368964509768753/400000000000000000000000000000 : ℝ)*base79 + (337944349968753/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (165477/40000000000000000000 : ℝ)*base89 + (165477/40000000000000000000 : ℝ)*base91 + (165477/40000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1129_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1193761/800000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5573/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1129_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1129_s1_0 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1050767689/5000000000 : ℝ)*x 0 + (2852498111/5000000000 : ℝ)*x 1 + (249976857/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050767689/5000000000 : ℝ)^4161 ≤ (12629748963771/100000000000000 : ℝ)^3137 := by
    have hnat : (1050767689 : ℕ)^4161*100000000000000^3137 ≤ 12629748963771^3137*5000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050767689 5000000000 12629748963771 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2852498111/5000000000 : ℝ)^4161 ≤ (47499675904957/100000000000000 : ℝ)^3137 := by
    have hnat : (2852498111 : ℕ)^4161*100000000000000^3137 ≤ 47499675904957^3137*5000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2852498111 5000000000 47499675904957 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (249976857/500000000 : ℝ)^4161 ≤ (39870575125047/100000000000000 : ℝ)^3137 := by
    have hnat : (249976857 : ℕ)^4161*100000000000000^3137 ≤ 39870575125047^3137*500000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249976857 500000000 39870575125047 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1050767689/5000000000 : ℝ), (2852498111/5000000000 : ℝ), (249976857/500000000 : ℝ)] ![(12629748963771/100000000000000 : ℝ), (47499675904957/100000000000000 : ℝ), (39870575125047/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1050767689/5000000000 : ℝ)|^4161 ≤ (12629748963771/100000000000000 : ℝ)^3137
        have hw : |(-1050767689/5000000000 : ℝ)|=(1050767689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2852498111/5000000000 : ℝ)|^4161 ≤ (47499675904957/100000000000000 : ℝ)^3137
        have hw : |(2852498111/5000000000 : ℝ)|=(2852498111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(249976857/500000000 : ℝ)|^4161 ≤ (39870575125047/100000000000000 : ℝ)^3137
        have hw : |(249976857/500000000 : ℝ)|=(249976857/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s1_1 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1354959293/2500000000 : ℝ)*x 0 + (-620623257/2500000000 : ℝ)*x 1 + (499953673/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1354959293/2500000000 : ℝ)^4161 ≤ (8875284596813/20000000000000 : ℝ)^3137 := by
    have hnat : (1354959293 : ℕ)^4161*20000000000000^3137 ≤ 8875284596813^3137*2500000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354959293 2500000000 8875284596813 20000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (620623257/2500000000 : ℝ)^4161 ≤ (15753006203229/100000000000000 : ℝ)^3137 := by
    have hnat : (620623257 : ℕ)^4161*100000000000000^3137 ≤ 15753006203229^3137*2500000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      620623257 2500000000 15753006203229 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (499953673/1000000000 : ℝ)^4161 ≤ (9967642697011/25000000000000 : ℝ)^3137 := by
    have hnat : (499953673 : ℕ)^4161*25000000000000^3137 ≤ 9967642697011^3137*1000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      499953673 1000000000 9967642697011 25000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1354959293/2500000000 : ℝ), (-620623257/2500000000 : ℝ), (499953673/1000000000 : ℝ)] ![(8875284596813/20000000000000 : ℝ), (15753006203229/100000000000000 : ℝ), (9967642697011/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1354959293/2500000000 : ℝ)|^4161 ≤ (8875284596813/20000000000000 : ℝ)^3137
        have hw : |(1354959293/2500000000 : ℝ)|=(1354959293/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-620623257/2500000000 : ℝ)|^4161 ≤ (15753006203229/100000000000000 : ℝ)^3137
        have hw : |(-620623257/2500000000 : ℝ)|=(620623257/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(499953673/1000000000 : ℝ)|^4161 ≤ (9967642697011/25000000000000 : ℝ)^3137
        have hw : |(499953673/1000000000 : ℝ)|=(499953673/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s1_2 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5419838871/10000000000 : ℝ)*x 0 + (6249419/12500000 : ℝ)*x 1 + (-62062319/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5419838871/10000000000 : ℝ)^4161 ≤ (44376441436031/100000000000000 : ℝ)^3137 := by
    have hnat : (5419838871 : ℕ)^4161*100000000000000^3137 ≤ 44376441436031^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419838871 10000000000 44376441436031 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6249419/12500000 : ℝ)^4161 ≤ (19935277301809/50000000000000 : ℝ)^3137 := by
    have hnat : (6249419 : ℕ)^4161*50000000000000^3137 ≤ 19935277301809^3137*12500000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6249419 12500000 19935277301809 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (62062319/250000000 : ℝ)^4161 ≤ (7876501973733/50000000000000 : ℝ)^3137 := by
    have hnat : (62062319 : ℕ)^4161*50000000000000^3137 ≤ 7876501973733^3137*250000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62062319 250000000 7876501973733 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5419838871/10000000000 : ℝ), (6249419/12500000 : ℝ), (-62062319/250000000 : ℝ)] ![(44376441436031/100000000000000 : ℝ), (19935277301809/50000000000000 : ℝ), (7876501973733/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5419838871/10000000000 : ℝ)|^4161 ≤ (44376441436031/100000000000000 : ℝ)^3137
        have hw : |(5419838871/10000000000 : ℝ)|=(5419838871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6249419/12500000 : ℝ)|^4161 ≤ (19935277301809/50000000000000 : ℝ)^3137
        have hw : |(6249419/12500000 : ℝ)|=(6249419/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-62062319/250000000 : ℝ)|^4161 ≤ (7876501973733/50000000000000 : ℝ)^3137
        have hw : |(-62062319/250000000 : ℝ)|=(62062319/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s1_3 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4318537639/10000000000 : ℝ)*x 0 + (1837296289/5000000000 : ℝ)*x 1 + (1014901059/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4318537639/10000000000 : ℝ)^4161 ≤ (6566454434581/20000000000000 : ℝ)^3137 := by
    have hnat : (4318537639 : ℕ)^4161*20000000000000^3137 ≤ 6566454434581^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4318537639 10000000000 6566454434581 20000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1837296289/5000000000 : ℝ)^4161 ≤ (3312775119/12500000000 : ℝ)^3137 := by
    have hnat : (1837296289 : ℕ)^4161*12500000000^3137 ≤ 3312775119^3137*5000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1837296289 5000000000 3312775119 12500000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1014901059/2000000000 : ℝ)^4161 ≤ (10166381714951/25000000000000 : ℝ)^3137 := by
    have hnat : (1014901059 : ℕ)^4161*25000000000000^3137 ≤ 10166381714951^3137*2000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1014901059 2000000000 10166381714951 25000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4318537639/10000000000 : ℝ), (1837296289/5000000000 : ℝ), (1014901059/2000000000 : ℝ)] ![(6566454434581/20000000000000 : ℝ), (3312775119/12500000000 : ℝ), (10166381714951/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4318537639/10000000000 : ℝ)|^4161 ≤ (6566454434581/20000000000000 : ℝ)^3137
        have hw : |(4318537639/10000000000 : ℝ)|=(4318537639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1837296289/5000000000 : ℝ)|^4161 ≤ (3312775119/12500000000 : ℝ)^3137
        have hw : |(1837296289/5000000000 : ℝ)|=(1837296289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1014901059/2000000000 : ℝ)|^4161 ≤ (10166381714951/25000000000000 : ℝ)^3137
        have hw : |(1014901059/2000000000 : ℝ)|=(1014901059/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s1_4 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-525589999/2500000000 : ℝ)*x 0 + (5009217411/10000000000 : ℝ)*x 1 + (1139024643/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (525589999/2500000000 : ℝ)^4161 ≤ (2527264568931/20000000000000 : ℝ)^3137 := by
    have hnat : (525589999 : ℕ)^4161*20000000000000^3137 ≤ 2527264568931^3137*2500000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525589999 2500000000 2527264568931 20000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5009217411/10000000000 : ℝ)^4161 ≤ (9993251482053/25000000000000 : ℝ)^3137 := by
    have hnat : (5009217411 : ℕ)^4161*25000000000000^3137 ≤ 9993251482053^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5009217411 10000000000 9993251482053 25000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1139024643/2000000000 : ℝ)^4161 ≤ (740479237697/1562500000000 : ℝ)^3137 := by
    have hnat : (1139024643 : ℕ)^4161*1562500000000^3137 ≤ 740479237697^3137*2000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1139024643 2000000000 740479237697 1562500000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-525589999/2500000000 : ℝ), (5009217411/10000000000 : ℝ), (1139024643/2000000000 : ℝ)] ![(2527264568931/20000000000000 : ℝ), (9993251482053/25000000000000 : ℝ), (740479237697/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-525589999/2500000000 : ℝ)|^4161 ≤ (2527264568931/20000000000000 : ℝ)^3137
        have hw : |(-525589999/2500000000 : ℝ)|=(525589999/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5009217411/10000000000 : ℝ)|^4161 ≤ (9993251482053/25000000000000 : ℝ)^3137
        have hw : |(5009217411/10000000000 : ℝ)|=(5009217411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1139024643/2000000000 : ℝ)|^4161 ≤ (740479237697/1562500000000 : ℝ)^3137
        have hw : |(1139024643/2000000000 : ℝ)|=(1139024643/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s1_5 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5239088439/10000000000 : ℝ)*x 0 + (-223363273/1250000000 : ℝ)*x 1 + (1139024591/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5239088439/10000000000 : ℝ)^4161 ≤ (21212084974967/50000000000000 : ℝ)^3137 := by
    have hnat : (5239088439 : ℕ)^4161*50000000000000^3137 ≤ 21212084974967^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239088439 10000000000 21212084974967 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (223363273/1250000000 : ℝ)^4161 ≤ (1273145210927/12500000000000 : ℝ)^3137 := by
    have hnat : (223363273 : ℕ)^4161*12500000000000^3137 ≤ 1273145210927^3137*1250000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223363273 1250000000 1273145210927 12500000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1139024591/2000000000 : ℝ)^4161 ≤ (11847667085711/25000000000000 : ℝ)^3137 := by
    have hnat : (1139024591 : ℕ)^4161*25000000000000^3137 ≤ 11847667085711^3137*2000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1139024591 2000000000 11847667085711 25000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5239088439/10000000000 : ℝ), (-223363273/1250000000 : ℝ), (1139024591/2000000000 : ℝ)] ![(21212084974967/50000000000000 : ℝ), (1273145210927/12500000000000 : ℝ), (11847667085711/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5239088439/10000000000 : ℝ)|^4161 ≤ (21212084974967/50000000000000 : ℝ)^3137
        have hw : |(5239088439/10000000000 : ℝ)|=(5239088439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-223363273/1250000000 : ℝ)|^4161 ≤ (1273145210927/12500000000000 : ℝ)^3137
        have hw : |(-223363273/1250000000 : ℝ)|=(223363273/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1139024591/2000000000 : ℝ)|^4161 ≤ (11847667085711/25000000000000 : ℝ)^3137
        have hw : |(1139024591/2000000000 : ℝ)|=(1139024591/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s1_6 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5239088483/10000000000 : ℝ)*x 0 + (2847561563/5000000000 : ℝ)*x 1 + (-893452937/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5239088483/10000000000 : ℝ)^4161 ≤ (42424170422533/100000000000000 : ℝ)^3137 := by
    have hnat : (5239088483 : ℕ)^4161*100000000000000^3137 ≤ 42424170422533^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239088483 10000000000 42424170422533 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2847561563/5000000000 : ℝ)^4161 ≤ (23695335115133/50000000000000 : ℝ)^3137 := by
    have hnat : (2847561563 : ℕ)^4161*50000000000000^3137 ≤ 23695335115133^3137*5000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2847561563 5000000000 23695335115133 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (893452937/5000000000 : ℝ)^4161 ≤ (10185159343667/100000000000000 : ℝ)^3137 := by
    have hnat : (893452937 : ℕ)^4161*100000000000000^3137 ≤ 10185159343667^3137*5000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      893452937 5000000000 10185159343667 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5239088483/10000000000 : ℝ), (2847561563/5000000000 : ℝ), (-893452937/5000000000 : ℝ)] ![(42424170422533/100000000000000 : ℝ), (23695335115133/50000000000000 : ℝ), (10185159343667/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5239088483/10000000000 : ℝ)|^4161 ≤ (42424170422533/100000000000000 : ℝ)^3137
        have hw : |(5239088483/10000000000 : ℝ)|=(5239088483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2847561563/5000000000 : ℝ)|^4161 ≤ (23695335115133/50000000000000 : ℝ)^3137
        have hw : |(2847561563/5000000000 : ℝ)|=(2847561563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-893452937/5000000000 : ℝ)|^4161 ≤ (10185159343667/100000000000000 : ℝ)^3137
        have hw : |(-893452937/5000000000 : ℝ)|=(893452937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s1_7 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (864034219/2000000000 : ℝ)*x 0 + (2527648297/5000000000 : ℝ)*x 1 + (738836701/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (864034219/2000000000 : ℝ)^4161 ≤ (16424372756707/50000000000000 : ℝ)^3137 := by
    have hnat : (864034219 : ℕ)^4161*50000000000000^3137 ≤ 16424372756707^3137*2000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      864034219 2000000000 16424372756707 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2527648297/5000000000 : ℝ)^4161 ≤ (809229455801/2000000000000 : ℝ)^3137 := by
    have hnat : (2527648297 : ℕ)^4161*2000000000000^3137 ≤ 809229455801^3137*5000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2527648297 5000000000 809229455801 2000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (738836701/2000000000 : ℝ)^4161 ≤ (26689781683381/100000000000000 : ℝ)^3137 := by
    have hnat : (738836701 : ℕ)^4161*100000000000000^3137 ≤ 26689781683381^3137*2000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      738836701 2000000000 26689781683381 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(864034219/2000000000 : ℝ), (2527648297/5000000000 : ℝ), (738836701/2000000000 : ℝ)] ![(16424372756707/50000000000000 : ℝ), (809229455801/2000000000000 : ℝ), (26689781683381/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(864034219/2000000000 : ℝ)|^4161 ≤ (16424372756707/50000000000000 : ℝ)^3137
        have hw : |(864034219/2000000000 : ℝ)|=(864034219/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2527648297/5000000000 : ℝ)|^4161 ≤ (809229455801/2000000000000 : ℝ)^3137
        have hw : |(2527648297/5000000000 : ℝ)|=(2527648297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(738836701/2000000000 : ℝ)|^4161 ≤ (26689781683381/100000000000000 : ℝ)^3137
        have hw : |(738836701/2000000000 : ℝ)|=(738836701/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1129_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1193761/800000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5573/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9/2500 : ℝ)*pair X i i ≤ pair X i h) :
    (697/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1281/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5573/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5573/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5573/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5573/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5573/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5573/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9/2500 : ℝ) ^ (8321/2048 : ℝ) ≤ (5891904543/50000000000000000000 : ℝ) := by
    have hpowers : (9/2500 : ℝ)^8321 ≤ (5891904543/50000000000000000000 : ℝ)^2048 := by
      have hnat : (9 : ℕ)^8321*50000000000000000000^2048 ≤ 5891904543^2048*2500^8321 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9 2500 5891904543 50000000000000000000 8321 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9/2500 : ℝ)) (X := (5891904543/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8321 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (5573/20000 : ℝ) ^ (8321/2048 : ℝ) ≤ (139066146772029053/25000000000000000000 : ℝ) := by
    have hpowers : (5573/20000 : ℝ)^8321 ≤ (139066146772029053/25000000000000000000 : ℝ)^2048 := by
      have hnat : (5573 : ℕ)^8321*25000000000000000000^2048 ≤ 139066146772029053^2048*20000^8321 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5573 20000 139066146772029053 25000000000000000000 8321 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5573/20000 : ℝ)) (X := (139066146772029053/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8321 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000005891904543/25000000000000000000 : ℝ) ≤ (10000000000580057/10000000000000000 : ℝ) ^ (8321/2048 : ℝ) := by
    have hpowers : (25000000005891904543/25000000000000000000 : ℝ)^2048 ≤ (10000000000580057/10000000000000000 : ℝ)^8321 := by
      have hnat : (25000000005891904543 : ℕ)^2048*10000000000000000^8321 ≤ 10000000000580057^8321*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000005891904543 25000000000000000000 10000000000580057 10000000000000000 2048 8321 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000000580057/10000000000000000 : ℝ)) (X := (25000000005891904543/25000000000000000000 : ℝ)) (by norm_num) 8321 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50278132299435962649/50000000000000000000 : ℝ) ≤ (10013662407545041/10000000000000000 : ℝ) ^ (8321/2048 : ℝ) := by
    have hpowers : (50278132299435962649/50000000000000000000 : ℝ)^2048 ≤ (10013662407545041/10000000000000000 : ℝ)^8321 := by
      have hnat : (50278132299435962649 : ℕ)^2048*10000000000000000^8321 ≤ 10013662407545041^8321*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50278132299435962649 50000000000000000000 10013662407545041 10000000000000000 2048 8321 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10013662407545041/10000000000000000 : ℝ)) (X := (50278132299435962649/50000000000000000000 : ℝ)) (by norm_num) 8321 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12639066146772029053/12500000000000000000 : ℝ) ≤ (401092992580401/400000000000000 : ℝ) ^ (8321/2048 : ℝ) := by
    have hpowers : (12639066146772029053/12500000000000000000 : ℝ)^2048 ≤ (401092992580401/400000000000000 : ℝ)^8321 := by
      have hnat : (12639066146772029053 : ℕ)^2048*400000000000000^8321 ≤ 401092992580401^8321*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12639066146772029053 12500000000000000000 401092992580401 400000000000000 2048 8321 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (401092992580401/400000000000000 : ℝ)) (X := (12639066146772029053/12500000000000000000 : ℝ)) (by norm_num) 8321 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5891904543/50000000000000000000 : ℝ) ≤ ((55008032616587935861/55010000000000000000 : ℝ)+2*(1707800870623/343812500000000 : ℝ)*(9/2500 : ℝ))^(8321/2048 : ℝ) := by
    rw [show (55008032616587935861/55010000000000000000 : ℝ)+2*(1707800870623/343812500000000 : ℝ)*(9/2500 : ℝ)=(10000000000580057/10000000000000000 : ℝ) by norm_num, show 1+2*(5891904543/50000000000000000000 : ℝ)=(25000000005891904543/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(139066146772029053/25000000000000000000 : ℝ)+(5891904543/50000000000000000000 : ℝ) ≤ ((55008032616587935861/55010000000000000000 : ℝ)+(1707800870623/343812500000000 : ℝ)*((5573/20000 : ℝ)+(9/2500 : ℝ)))^(8321/2048 : ℝ) := by
    rw [show (55008032616587935861/55010000000000000000 : ℝ)+(1707800870623/343812500000000 : ℝ)*((5573/20000 : ℝ)+(9/2500 : ℝ))=(10013662407545041/10000000000000000 : ℝ) by norm_num, show 1+(139066146772029053/25000000000000000000 : ℝ)+(5891904543/50000000000000000000 : ℝ)=(50278132299435962649/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(139066146772029053/25000000000000000000 : ℝ) ≤ ((55008032616587935861/55010000000000000000 : ℝ)+2*(1707800870623/343812500000000 : ℝ)*(5573/20000 : ℝ))^(8321/2048 : ℝ) := by
    rw [show (55008032616587935861/55010000000000000000 : ℝ)+2*(1707800870623/343812500000000 : ℝ)*(5573/20000 : ℝ)=(401092992580401/400000000000000 : ℝ) by norm_num, show 1+2*(139066146772029053/25000000000000000000 : ℝ)=(12639066146772029053/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (55008032616587935861/55010000000000000000 : ℝ)*(X 1 0+X 2 0)+(1707800870623/343812500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8321/2048 : ℝ)) (lo := (9/2500 : ℝ)) (hi := (5573/20000 : ℝ)) (c := (55008032616587935861/55010000000000000000 : ℝ)) (alpha := (1707800870623/343812500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (55008032616587935861/55010000000000000000 : ℝ)*(X 0 1+X 2 1)+(1707800870623/343812500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8321/2048 : ℝ)) (lo := (9/2500 : ℝ)) (hi := (5573/20000 : ℝ)) (c := (55008032616587935861/55010000000000000000 : ℝ)) (alpha := (1707800870623/343812500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (55008032616587935861/55010000000000000000 : ℝ)*(X 0 2+X 1 2)+(1707800870623/343812500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8321/2048 : ℝ)) (lo := (9/2500 : ℝ)) (hi := (5573/20000 : ℝ)) (c := (55008032616587935861/55010000000000000000 : ℝ)) (alpha := (1707800870623/343812500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1050767689/5000000000 : ℝ)*X 0 0+(2852498111/5000000000 : ℝ)*X 0 1+(249976857/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1354959293/2500000000 : ℝ)*X 1 0+(-620623257/2500000000 : ℝ)*X 1 1+(499953673/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5419838871/10000000000 : ℝ)*X 2 0+(6249419/12500000 : ℝ)*X 2 1+(-62062319/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4318537639/10000000000 : ℝ)*X 0 0+(1837296289/5000000000 : ℝ)*X 0 1+(1014901059/2000000000 : ℝ)*X 0 2+(4318537639/10000000000 : ℝ)*X 1 0+(1837296289/5000000000 : ℝ)*X 1 1+(1014901059/2000000000 : ℝ)*X 1 2+(4318537639/10000000000 : ℝ)*X 2 0+(1837296289/5000000000 : ℝ)*X 2 1+(1014901059/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-525589999/2500000000 : ℝ)*X 0 0+(5009217411/10000000000 : ℝ)*X 0 1+(1139024643/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5239088439/10000000000 : ℝ)*X 1 0+(-223363273/1250000000 : ℝ)*X 1 1+(1139024591/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5239088483/10000000000 : ℝ)*X 2 0+(2847561563/5000000000 : ℝ)*X 2 1+(-893452937/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((864034219/2000000000 : ℝ)*X 0 0+(2527648297/5000000000 : ℝ)*X 0 1+(738836701/2000000000 : ℝ)*X 0 2+(864034219/2000000000 : ℝ)*X 1 0+(2527648297/5000000000 : ℝ)*X 1 1+(738836701/2000000000 : ℝ)*X 1 2+(864034219/2000000000 : ℝ)*X 2 0+(2527648297/5000000000 : ℝ)*X 2 1+(738836701/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (780822174064302974234910099/85953125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (432635891/100000000000000 : ℝ)*(base1) + (163663327/10000000000000 : ℝ)*(base19) + (1040498201/50000000000000 : ℝ)*(base23) + (9909779/25000000000000 : ℝ)*(upper3) + (252605459/100000000000000 : ℝ)*(upper5) + (33310355401703/3125000000000 : ℝ)*(major0) + (33310355401703/3125000000000 : ℝ)*(major1) + (33310355401703/3125000000000 : ℝ)*(major2) + (1417520763769619/100000000000000 : ℝ)*(sp0) + (1417525945030711/100000000000000 : ℝ)*(sp1) + (708762750333789/50000000000000 : ℝ)*(sp2) + (357166271869457/50000000000000 : ℝ)*(sp3) + (1812632563/25000000000000 : ℝ)*(sp4) + (1884860901/100000000000000 : ℝ)*(sp7) + (357167430617853/50000000000000 : ℝ)*(f.failure) + (70876379083199/5000000000000 : ℝ)*(f.sum) + (5102871761111/137525000000000000000000000000 : ℝ)*base66 + (598664305281836283/171906250000000000000000000000000 : ℝ)*base67 + (91812447327507467/171906250000000000000000000000000 : ℝ)*base70 + (169753444560569967/171906250000000000000000000000000 : ℝ)*base72 + (306281036389307/68762500000000000000000000000 : ℝ)*base73 + (917540944520944967/171906250000000000000000000000000 : ℝ)*base76 + (89719936377632467/171906250000000000000000000000000 : ℝ)*base78 + (334659520794023783/171906250000000000000000000000000 : ℝ)*base79 + (60290511153311/137525000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (415133/40000000000000000000 : ℝ)*base89 + (415133/40000000000000000000 : ℝ)*base91 + (415133/40000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3836905736669451154288227759/1375250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9998507/25000000000000 : ℝ)*(base1) + (160400257/25000000000000 : ℝ)*(base19) + (674962963/100000000000000 : ℝ)*(base23) + (51589871/100000000000000 : ℝ)*(upper3) + (29467423/50000000000000 : ℝ)*(upper5) + (1096309602592527/100000000000000 : ℝ)*(major0) + (1096309602592527/100000000000000 : ℝ)*(major1) + (1096309602592527/100000000000000 : ℝ)*(major2) + (471338573/20000000000000 : ℝ)*(sp1) + (185548237/6250000000000 : ℝ)*(sp2) + (1457926293162229/100000000000000 : ℝ)*(sp4) + (364480813718577/25000000000000 : ℝ)*(sp5) + (728961304716723/50000000000000 : ℝ)*(sp6) + (367346409511917/50000000000000 : ℝ)*(sp7) + (367346429508931/50000000000000 : ℝ)*(f.failure) + (1457926253168201/100000000000000 : ℝ)*(f.sum) + (52232875339541/68762500000000000000000000000 : ℝ)*base66 + (36576709895670270747/5501000000000000000000000000000000 : ℝ)*base67 + (1307653313219729253/5501000000000000000000000000000000 : ℝ)*base70 + (7530930916463270747/5501000000000000000000000000000000 : ℝ)*base71 + (61855630735871/17190625000000000000000000000 : ℝ)*base73 + (48817869308925270747/5501000000000000000000000000000000 : ℝ)*base75 + (113238071205270747/5501000000000000000000000000000000 : ℝ)*base77 + (30035022590693270747/5501000000000000000000000000000000 : ℝ)*base79 + (78904700755791/68762500000000000000000000000 : ℝ)*base82 + (179491/40000000000000000000 : ℝ)*base89 + (179491/40000000000000000000 : ℝ)*base91 + (179491/40000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1129_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1193761/800000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5573/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (697/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1281/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1129_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1129_s2_0 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-215547307/1000000000 : ℝ)*x 0 + (5513297669/10000000000 : ℝ)*x 1 + (64461881/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215547307/1000000000 : ℝ)^4161 ≤ (6530752641319/50000000000000 : ℝ)^3137 := by
    have hnat : (215547307 : ℕ)^4161*50000000000000^3137 ≤ 6530752641319^3137*1000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215547307 1000000000 6530752641319 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5513297669/10000000000 : ℝ)^4161 ≤ (22697147582301/50000000000000 : ℝ)^3137 := by
    have hnat : (5513297669 : ℕ)^4161*50000000000000^3137 ≤ 22697147582301^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5513297669 10000000000 22697147582301 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (64461881/125000000 : ℝ)^4161 ≤ (41544199547499/100000000000000 : ℝ)^3137 := by
    have hnat : (64461881 : ℕ)^4161*100000000000000^3137 ≤ 41544199547499^3137*125000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64461881 125000000 41544199547499 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-215547307/1000000000 : ℝ), (5513297669/10000000000 : ℝ), (64461881/125000000 : ℝ)] ![(6530752641319/50000000000000 : ℝ), (22697147582301/50000000000000 : ℝ), (41544199547499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-215547307/1000000000 : ℝ)|^4161 ≤ (6530752641319/50000000000000 : ℝ)^3137
        have hw : |(-215547307/1000000000 : ℝ)|=(215547307/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5513297669/10000000000 : ℝ)|^4161 ≤ (22697147582301/50000000000000 : ℝ)^3137
        have hw : |(5513297669/10000000000 : ℝ)|=(5513297669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(64461881/125000000 : ℝ)|^4161 ≤ (41544199547499/100000000000000 : ℝ)^3137
        have hw : |(64461881/125000000 : ℝ)|=(64461881/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s2_1 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (214976933/400000000 : ℝ)*x 0 + (-2340832877/10000000000 : ℝ)*x 1 + (5156952167/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214976933/400000000 : ℝ)^4161 ≤ (219419411697/500000000000 : ℝ)^3137 := by
    have hnat : (214976933 : ℕ)^4161*500000000000^3137 ≤ 219419411697^3137*400000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214976933 400000000 219419411697 500000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2340832877/10000000000 : ℝ)^4161 ≤ (3642975016289/25000000000000 : ℝ)^3137 := by
    have hnat : (2340832877 : ℕ)^4161*25000000000000^3137 ≤ 3642975016289^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2340832877 10000000000 3642975016289 25000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5156952167/10000000000 : ℝ)^4161 ≤ (41544217574179/100000000000000 : ℝ)^3137 := by
    have hnat : (5156952167 : ℕ)^4161*100000000000000^3137 ≤ 41544217574179^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5156952167 10000000000 41544217574179 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214976933/400000000 : ℝ), (-2340832877/10000000000 : ℝ), (5156952167/10000000000 : ℝ)] ![(219419411697/500000000000 : ℝ), (3642975016289/25000000000000 : ℝ), (41544217574179/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214976933/400000000 : ℝ)|^4161 ≤ (219419411697/500000000000 : ℝ)^3137
        have hw : |(214976933/400000000 : ℝ)|=(214976933/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2340832877/10000000000 : ℝ)|^4161 ≤ (3642975016289/25000000000000 : ℝ)^3137
        have hw : |(-2340832877/10000000000 : ℝ)|=(2340832877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5156952167/10000000000 : ℝ)|^4161 ≤ (41544217574179/100000000000000 : ℝ)^3137
        have hw : |(5156952167/10000000000 : ℝ)|=(5156952167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s2_2 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5374423249/10000000000 : ℝ)*x 0 + (1031390437/2000000000 : ℝ)*x 1 + (-468166591/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5374423249/10000000000 : ℝ)^4161 ≤ (10970970379067/25000000000000 : ℝ)^3137 := by
    have hnat : (5374423249 : ℕ)^4161*25000000000000^3137 ≤ 10970970379067^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374423249 10000000000 10970970379067 25000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1031390437/2000000000 : ℝ)^4161 ≤ (1038605444163/2500000000000 : ℝ)^3137 := by
    have hnat : (1031390437 : ℕ)^4161*2500000000000^3137 ≤ 1038605444163^3137*2000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031390437 2000000000 1038605444163 2500000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (468166591/2000000000 : ℝ)^4161 ≤ (14571900709211/100000000000000 : ℝ)^3137 := by
    have hnat : (468166591 : ℕ)^4161*100000000000000^3137 ≤ 14571900709211^3137*2000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      468166591 2000000000 14571900709211 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5374423249/10000000000 : ℝ), (1031390437/2000000000 : ℝ), (-468166591/2000000000 : ℝ)] ![(10970970379067/25000000000000 : ℝ), (1038605444163/2500000000000 : ℝ), (14571900709211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5374423249/10000000000 : ℝ)|^4161 ≤ (10970970379067/25000000000000 : ℝ)^3137
        have hw : |(5374423249/10000000000 : ℝ)|=(5374423249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1031390437/2000000000 : ℝ)|^4161 ≤ (1038605444163/2500000000000 : ℝ)^3137
        have hw : |(1031390437/2000000000 : ℝ)|=(1031390437/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-468166591/2000000000 : ℝ)|^4161 ≤ (14571900709211/100000000000000 : ℝ)^3137
        have hw : |(-468166591/2000000000 : ℝ)|=(468166591/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s2_3 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2177752683/5000000000 : ℝ)*x 0 + (4016203547/10000000000 : ℝ)*x 1 + (2361667833/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2177752683/5000000000 : ℝ)^4161 ≤ (8301396776813/25000000000000 : ℝ)^3137 := by
    have hnat : (2177752683 : ℕ)^4161*25000000000000^3137 ≤ 8301396776813^3137*5000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177752683 5000000000 8301396776813 25000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4016203547/10000000000 : ℝ)^4161 ≤ (29818833992047/100000000000000 : ℝ)^3137 := by
    have hnat : (4016203547 : ℕ)^4161*100000000000000^3137 ≤ 29818833992047^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4016203547 10000000000 29818833992047 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2361667833/5000000000 : ℝ)^4161 ≤ (36975578884149/100000000000000 : ℝ)^3137 := by
    have hnat : (2361667833 : ℕ)^4161*100000000000000^3137 ≤ 36975578884149^3137*5000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2361667833 5000000000 36975578884149 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2177752683/5000000000 : ℝ), (4016203547/10000000000 : ℝ), (2361667833/5000000000 : ℝ)] ![(8301396776813/25000000000000 : ℝ), (29818833992047/100000000000000 : ℝ), (36975578884149/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2177752683/5000000000 : ℝ)|^4161 ≤ (8301396776813/25000000000000 : ℝ)^3137
        have hw : |(2177752683/5000000000 : ℝ)|=(2177752683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4016203547/10000000000 : ℝ)|^4161 ≤ (29818833992047/100000000000000 : ℝ)^3137
        have hw : |(4016203547/10000000000 : ℝ)|=(4016203547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2361667833/5000000000 : ℝ)|^4161 ≤ (36975578884149/100000000000000 : ℝ)^3137
        have hw : |(2361667833/5000000000 : ℝ)|=(2361667833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s2_4 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2155579357/10000000000 : ℝ)*x 0 + (5159430309/10000000000 : ℝ)*x 1 + (275539637/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2155579357/10000000000 : ℝ)^4161 ≤ (6531179798267/50000000000000 : ℝ)^3137 := by
    have hnat : (2155579357 : ℕ)^4161*50000000000000^3137 ≤ 6531179798267^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155579357 10000000000 6531179798267 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5159430309/10000000000 : ℝ)^4161 ≤ (4157070019263/10000000000000 : ℝ)^3137 := by
    have hnat : (5159430309 : ℕ)^4161*10000000000000^3137 ≤ 4157070019263^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5159430309 10000000000 4157070019263 10000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (275539637/500000000 : ℝ)^4161 ≤ (45366940194507/100000000000000 : ℝ)^3137 := by
    have hnat : (275539637 : ℕ)^4161*100000000000000^3137 ≤ 45366940194507^3137*500000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275539637 500000000 45366940194507 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2155579357/10000000000 : ℝ), (5159430309/10000000000 : ℝ), (275539637/500000000 : ℝ)] ![(6531179798267/50000000000000 : ℝ), (4157070019263/10000000000000 : ℝ), (45366940194507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2155579357/10000000000 : ℝ)|^4161 ≤ (6531179798267/50000000000000 : ℝ)^3137
        have hw : |(-2155579357/10000000000 : ℝ)|=(2155579357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5159430309/10000000000 : ℝ)|^4161 ≤ (4157070019263/10000000000000 : ℝ)^3137
        have hw : |(5159430309/10000000000 : ℝ)|=(5159430309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(275539637/500000000 : ℝ)|^4161 ≤ (45366940194507/100000000000000 : ℝ)^3137
        have hw : |(275539637/500000000 : ℝ)|=(275539637/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s2_5 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5284087477/10000000000 : ℝ)*x 0 + (-993495273/5000000000 : ℝ)*x 1 + (5510793309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5284087477/10000000000 : ℝ)^4161 ≤ (42908176538823/100000000000000 : ℝ)^3137 := by
    have hnat : (5284087477 : ℕ)^4161*100000000000000^3137 ≤ 42908176538823^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5284087477 10000000000 42908176538823 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (993495273/5000000000 : ℝ)^4161 ≤ (2931219259011/25000000000000 : ℝ)^3137 := by
    have hnat : (993495273 : ℕ)^4161*25000000000000^3137 ≤ 2931219259011^3137*5000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      993495273 5000000000 2931219259011 25000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5510793309/10000000000 : ℝ)^4161 ≤ (45366946407787/100000000000000 : ℝ)^3137 := by
    have hnat : (5510793309 : ℕ)^4161*100000000000000^3137 ≤ 45366946407787^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5510793309 10000000000 45366946407787 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5284087477/10000000000 : ℝ), (-993495273/5000000000 : ℝ), (5510793309/10000000000 : ℝ)] ![(42908176538823/100000000000000 : ℝ), (2931219259011/25000000000000 : ℝ), (45366946407787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5284087477/10000000000 : ℝ)|^4161 ≤ (42908176538823/100000000000000 : ℝ)^3137
        have hw : |(5284087477/10000000000 : ℝ)|=(5284087477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-993495273/5000000000 : ℝ)|^4161 ≤ (2931219259011/25000000000000 : ℝ)^3137
        have hw : |(-993495273/5000000000 : ℝ)|=(993495273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5510793309/10000000000 : ℝ)|^4161 ≤ (45366946407787/100000000000000 : ℝ)^3137
        have hw : |(5510793309/10000000000 : ℝ)|=(5510793309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s2_6 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2642043101/5000000000 : ℝ)*x 0 + (5510793171/10000000000 : ℝ)*x 1 + (-1986992493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642043101/5000000000 : ℝ)^4161 ≤ (21454081402943/50000000000000 : ℝ)^3137 := by
    have hnat : (2642043101 : ℕ)^4161*50000000000000^3137 ≤ 21454081402943^3137*5000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642043101 5000000000 21454081402943 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5510793171/10000000000 : ℝ)^4161 ≤ (362935559207/800000000000 : ℝ)^3137 := by
    have hnat : (5510793171 : ℕ)^4161*800000000000^3137 ≤ 362935559207^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5510793171 10000000000 362935559207 800000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1986992493/10000000000 : ℝ)^4161 ≤ (2931223068807/25000000000000 : ℝ)^3137 := by
    have hnat : (1986992493 : ℕ)^4161*25000000000000^3137 ≤ 2931223068807^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1986992493 10000000000 2931223068807 25000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642043101/5000000000 : ℝ), (5510793171/10000000000 : ℝ), (-1986992493/10000000000 : ℝ)] ![(21454081402943/50000000000000 : ℝ), (362935559207/800000000000 : ℝ), (2931223068807/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642043101/5000000000 : ℝ)|^4161 ≤ (21454081402943/50000000000000 : ℝ)^3137
        have hw : |(2642043101/5000000000 : ℝ)|=(2642043101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5510793171/10000000000 : ℝ)|^4161 ≤ (362935559207/800000000000 : ℝ)^3137
        have hw : |(5510793171/10000000000 : ℝ)|=(5510793171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1986992493/10000000000 : ℝ)|^4161 ≤ (2931223068807/25000000000000 : ℝ)^3137
        have hw : |(-1986992493/10000000000 : ℝ)|=(1986992493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s2_7 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (544464469/1250000000 : ℝ)*x 0 + (4718416051/10000000000 : ℝ)*x 1 + (4021172703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (544464469/1250000000 : ℝ)^4161 ≤ (33207714639089/100000000000000 : ℝ)^3137 := by
    have hnat : (544464469 : ℕ)^4161*100000000000000^3137 ≤ 33207714639089^3137*1250000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544464469 1250000000 33207714639089 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4718416051/10000000000 : ℝ)^4161 ≤ (9231126022223/25000000000000 : ℝ)^3137 := by
    have hnat : (4718416051 : ℕ)^4161*25000000000000^3137 ≤ 9231126022223^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4718416051 10000000000 9231126022223 25000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4021172703/10000000000 : ℝ)^4161 ≤ (1194711250319/4000000000000 : ℝ)^3137 := by
    have hnat : (4021172703 : ℕ)^4161*4000000000000^3137 ≤ 1194711250319^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4021172703 10000000000 1194711250319 4000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(544464469/1250000000 : ℝ), (4718416051/10000000000 : ℝ), (4021172703/10000000000 : ℝ)] ![(33207714639089/100000000000000 : ℝ), (9231126022223/25000000000000 : ℝ), (1194711250319/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(544464469/1250000000 : ℝ)|^4161 ≤ (33207714639089/100000000000000 : ℝ)^3137
        have hw : |(544464469/1250000000 : ℝ)|=(544464469/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4718416051/10000000000 : ℝ)|^4161 ≤ (9231126022223/25000000000000 : ℝ)^3137
        have hw : |(4718416051/10000000000 : ℝ)|=(4718416051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4021172703/10000000000 : ℝ)|^4161 ≤ (1194711250319/4000000000000 : ℝ)^3137
        have hw : |(4021172703/10000000000 : ℝ)|=(4021172703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1129_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1193761/800000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1281/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (697/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (9011/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16541/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1281/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (697/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1281/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (697/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1281/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (697/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1281/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (697/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1281/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (697/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1281/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (697/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (697/12500 : ℝ) ^ (8321/2048 : ℝ) ≤ (25186864616429/3125000000000000000 : ℝ) := by
    have hpowers : (697/12500 : ℝ)^8321 ≤ (25186864616429/3125000000000000000 : ℝ)^2048 := by
      have hnat : (697 : ℕ)^8321*3125000000000000000^2048 ≤ 25186864616429^2048*12500^8321 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        697 12500 25186864616429 3125000000000000000 8321 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (697/12500 : ℝ)) (X := (25186864616429/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 8321 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1281/6250 : ℝ) ^ (8321/2048 : ℝ) ≤ (39926356361634019/25000000000000000000 : ℝ) := by
    have hpowers : (1281/6250 : ℝ)^8321 ≤ (39926356361634019/25000000000000000000 : ℝ)^2048 := by
      have hnat : (1281 : ℕ)^8321*25000000000000000000^2048 ≤ 39926356361634019^2048*6250^8321 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1281 6250 39926356361634019 25000000000000000000 8321 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1281/6250 : ℝ)) (X := (39926356361634019/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8321 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562525186864616429/1562500000000000000 : ℝ) ≤ (2500009918497357/2500000000000000 : ℝ) ^ (8321/2048 : ℝ) := by
    have hpowers : (1562525186864616429/1562500000000000000 : ℝ)^2048 ≤ (2500009918497357/2500000000000000 : ℝ)^8321 := by
      have hnat : (1562525186864616429 : ℕ)^2048*2500000000000000^8321 ≤ 2500009918497357^8321*1562500000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562525186864616429 1562500000000000000 2500009918497357 2500000000000000 2048 8321 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500009918497357/2500000000000000 : ℝ)) (X := (1562525186864616429/1562500000000000000 : ℝ)) (by norm_num) 8321 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25040127851278565451/25000000000000000000 : ℝ) ≤ (1250493523396767/1250000000000000 : ℝ) ^ (8321/2048 : ℝ) := by
    have hpowers : (25040127851278565451/25000000000000000000 : ℝ)^2048 ≤ (1250493523396767/1250000000000000 : ℝ)^8321 := by
      have hnat : (25040127851278565451 : ℕ)^2048*1250000000000000^8321 ≤ 1250493523396767^8321*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25040127851278565451 25000000000000000000 1250493523396767 1250000000000000 2048 8321 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250493523396767/1250000000000000 : ℝ)) (X := (25040127851278565451/25000000000000000000 : ℝ)) (by norm_num) 8321 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12539926356361634019/12500000000000000000 : ℝ) ≤ (2501964175089711/2500000000000000 : ℝ) ^ (8321/2048 : ℝ) := by
    have hpowers : (12539926356361634019/12500000000000000000 : ℝ)^2048 ≤ (2501964175089711/2500000000000000 : ℝ)^8321 := by
      have hnat : (12539926356361634019 : ℕ)^2048*2500000000000000^8321 ≤ 2501964175089711^8321*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12539926356361634019 12500000000000000000 2501964175089711 2500000000000000 2048 8321 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501964175089711/2500000000000000 : ℝ)) (X := (12539926356361634019/12500000000000000000 : ℝ)) (by norm_num) 8321 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(25186864616429/3125000000000000000 : ℝ) ≤ ((4661156381152700067/4662500000000000000 : ℝ)+2*(977128296177/373000000000000 : ℝ)*(697/12500 : ℝ))^(8321/2048 : ℝ) := by
    rw [show (4661156381152700067/4662500000000000000 : ℝ)+2*(977128296177/373000000000000 : ℝ)*(697/12500 : ℝ)=(2500009918497357/2500000000000000 : ℝ) by norm_num, show 1+2*(25186864616429/3125000000000000000 : ℝ)=(1562525186864616429/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(39926356361634019/25000000000000000000 : ℝ)+(25186864616429/3125000000000000000 : ℝ) ≤ ((4661156381152700067/4662500000000000000 : ℝ)+(977128296177/373000000000000 : ℝ)*((1281/6250 : ℝ)+(697/12500 : ℝ)))^(8321/2048 : ℝ) := by
    rw [show (4661156381152700067/4662500000000000000 : ℝ)+(977128296177/373000000000000 : ℝ)*((1281/6250 : ℝ)+(697/12500 : ℝ))=(1250493523396767/1250000000000000 : ℝ) by norm_num, show 1+(39926356361634019/25000000000000000000 : ℝ)+(25186864616429/3125000000000000000 : ℝ)=(25040127851278565451/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(39926356361634019/25000000000000000000 : ℝ) ≤ ((4661156381152700067/4662500000000000000 : ℝ)+2*(977128296177/373000000000000 : ℝ)*(1281/6250 : ℝ))^(8321/2048 : ℝ) := by
    rw [show (4661156381152700067/4662500000000000000 : ℝ)+2*(977128296177/373000000000000 : ℝ)*(1281/6250 : ℝ)=(2501964175089711/2500000000000000 : ℝ) by norm_num, show 1+2*(39926356361634019/25000000000000000000 : ℝ)=(12539926356361634019/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4661156381152700067/4662500000000000000 : ℝ)*(X 1 0+X 2 0)+(977128296177/373000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8321/2048 : ℝ)) (lo := (697/12500 : ℝ)) (hi := (1281/6250 : ℝ)) (c := (4661156381152700067/4662500000000000000 : ℝ)) (alpha := (977128296177/373000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4661156381152700067/4662500000000000000 : ℝ)*(X 0 1+X 2 1)+(977128296177/373000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8321/2048 : ℝ)) (lo := (697/12500 : ℝ)) (hi := (1281/6250 : ℝ)) (c := (4661156381152700067/4662500000000000000 : ℝ)) (alpha := (977128296177/373000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4661156381152700067/4662500000000000000 : ℝ)*(X 0 2+X 1 2)+(977128296177/373000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8321/2048 : ℝ)) (lo := (697/12500 : ℝ)) (hi := (1281/6250 : ℝ)) (c := (4661156381152700067/4662500000000000000 : ℝ)) (alpha := (977128296177/373000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-215547307/1000000000 : ℝ)*X 0 0+(5513297669/10000000000 : ℝ)*X 0 1+(64461881/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((214976933/400000000 : ℝ)*X 1 0+(-2340832877/10000000000 : ℝ)*X 1 1+(5156952167/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5374423249/10000000000 : ℝ)*X 2 0+(1031390437/2000000000 : ℝ)*X 2 1+(-468166591/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2177752683/5000000000 : ℝ)*X 0 0+(4016203547/10000000000 : ℝ)*X 0 1+(2361667833/5000000000 : ℝ)*X 0 2+(2177752683/5000000000 : ℝ)*X 1 0+(4016203547/10000000000 : ℝ)*X 1 1+(2361667833/5000000000 : ℝ)*X 1 2+(2177752683/5000000000 : ℝ)*X 2 0+(4016203547/10000000000 : ℝ)*X 2 1+(2361667833/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2155579357/10000000000 : ℝ)*X 0 0+(5159430309/10000000000 : ℝ)*X 0 1+(275539637/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5284087477/10000000000 : ℝ)*X 1 0+(-993495273/5000000000 : ℝ)*X 1 1+(5510793309/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2642043101/5000000000 : ℝ)*X 2 0+(5510793171/10000000000 : ℝ)*X 2 1+(-1986992493/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((544464469/1250000000 : ℝ)*X 0 0+(4718416051/10000000000 : ℝ)*X 0 1+(4021172703/10000000000 : ℝ)*X 0 2+(544464469/1250000000 : ℝ)*X 1 0+(4718416051/10000000000 : ℝ)*X 1 1+(4021172703/10000000000 : ℝ)*X 1 2+(544464469/1250000000 : ℝ)*X 2 0+(4718416051/10000000000 : ℝ)*X 2 1+(4021172703/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (221871833114986817269806609/29140625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (133133463/20000000000000 : ℝ)*(base19) + (97620167/25000000000000 : ℝ)*(base23) + (21853447/100000000000000 : ℝ)*(upper2) + (118602147/50000000000000 : ℝ)*(upper3) + (37105657/25000000000000 : ℝ)*(upper4) + (65944667530557/3125000000000 : ℝ)*(major0) + (65944667530557/3125000000000 : ℝ)*(major1) + (65944667530557/3125000000000 : ℝ)*(major2) + (1403135295514233/50000000000000 : ℝ)*(sp0) + (175392857007217/6250000000000 : ℝ)*(sp1) + (70157149682553/2500000000000 : ℝ)*(sp2) + (1414166382583883/100000000000000 : ℝ)*(sp3) + (7893377161/50000000000000 : ℝ)*(sp4) + (5707794559/100000000000000 : ℝ)*(sp7) + (707086045189221/50000000000000 : ℝ)*(f.failure) + (2806286377782787/100000000000000 : ℝ)*(f.sum) + (5421099162631/2331250000000000000000000000 : ℝ)*base65 + (67297120009946653/7285156250000000000000000000000 : ℝ)*base68 + (245062643427989737/29140625000000000000000000000000 : ℝ)*base70 + (55873289690259153/7285156250000000000000000000000 : ℝ)*base72 + (9536425130737/4662500000000000000000000000 : ℝ)*base73 + (76368785246114737/29140625000000000000000000000000 : ℝ)*base76 + (17296955667602903/7285156250000000000000000000000 : ℝ)*base78 + (57016212090949889/3642578125000000000000000000000 : ℝ)*base80 + (38577925821549/9325000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (50181/40000000000000000000 : ℝ)*base89 + (50181/40000000000000000000 : ℝ)*base91 + (50181/40000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (139239895619591716935425049/58281250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18253701/12500000000000 : ℝ)*(base19) + (330256451/100000000000000 : ℝ)*(upper2) + (43905221/50000000000000 : ℝ)*(upper3) + (676737/1562500000000 : ℝ)*(lower4) + (1070071216943999/50000000000000 : ℝ)*(major0) + (1070071216943999/50000000000000 : ℝ)*(major1) + (1070071216943999/50000000000000 : ℝ)*(major2) + (144447851/2500000000000 : ℝ)*(sp0) + (4862824341/50000000000000 : ℝ)*(sp1) + (258160879/50000000000000 : ℝ)*(sp3) + (1423030323664049/50000000000000 : ℝ)*(sp4) + (355757069195481/12500000000000 : ℝ)*(sp5) + (1423033212621069/50000000000000 : ℝ)*(sp6) + (1434217846575337/100000000000000 : ℝ)*(sp7) + (286843672579419/20000000000000 : ℝ)*(f.failure) + (1423033212621069/50000000000000 : ℝ)*(f.sum) + (64372180273627/9325000000000000000000000000 : ℝ)*base66 + (656874270241539567/233125000000000000000000000000000 : ℝ)*base68 + (520750159174039567/233125000000000000000000000000000 : ℝ)*base70 + (1553402183578414567/233125000000000000000000000000000 : ℝ)*base72 + (2062582175219/1165625000000000000000000000 : ℝ)*base74 + (656498638427210433/233125000000000000000000000000000 : ℝ)*base75 + (1479207991259664567/233125000000000000000000000000000 : ℝ)*base78 + (425834469859039567/233125000000000000000000000000000 : ℝ)*base80 + (9013421491151/4662500000000000000000000000 : ℝ)*base82 + (124859/16000000000000000000 : ℝ)*base89 + (124859/16000000000000000000 : ℝ)*base91 + (124859/16000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1129_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1193761/800000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1281/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (697/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9011/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16541/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1129_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1129_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1193761/800000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9011/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16541/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1129_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1129_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1129_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1193761/800000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9011/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16541/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1129_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
