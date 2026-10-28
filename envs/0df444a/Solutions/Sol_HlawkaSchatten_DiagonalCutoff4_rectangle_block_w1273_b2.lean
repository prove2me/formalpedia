-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1273_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:20:27.183981+00:00
-- url     : https://prove2.me/submissions/2b0723ec-f26c-49d8-914b-5d99e4afdb42

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
theorem support_rectangle_w1273_s6_0 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2105301489/10000000000 : ℝ)*x 0 + (1347689983/2500000000 : ℝ)*x 1 + (1316869409/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2105301489/10000000000 : ℝ)^8467 ≤ (800379282937/6250000000000 : ℝ)^6419 := by
    have hnat : (2105301489 : ℕ)^8467*6250000000000^6419 ≤ 800379282937^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2105301489 10000000000 800379282937 6250000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1347689983/2500000000 : ℝ)^8467 ≤ (44262115486883/100000000000000 : ℝ)^6419 := by
    have hnat : (1347689983 : ℕ)^8467*100000000000000^6419 ≤ 44262115486883^6419*2500000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347689983 2500000000 44262115486883 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316869409/2500000000 : ℝ)^8467 ≤ (42931815977147/100000000000000 : ℝ)^6419 := by
    have hnat : (1316869409 : ℕ)^8467*100000000000000^6419 ≤ 42931815977147^6419*2500000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316869409 2500000000 42931815977147 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2105301489/10000000000 : ℝ), (1347689983/2500000000 : ℝ), (1316869409/2500000000 : ℝ)] ![(800379282937/6250000000000 : ℝ), (44262115486883/100000000000000 : ℝ), (42931815977147/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2105301489/10000000000 : ℝ)|^8467 ≤ (800379282937/6250000000000 : ℝ)^6419
        have hw : |(-2105301489/10000000000 : ℝ)|=(2105301489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1347689983/2500000000 : ℝ)|^8467 ≤ (44262115486883/100000000000000 : ℝ)^6419
        have hw : |(1347689983/2500000000 : ℝ)|=(1347689983/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316869409/2500000000 : ℝ)|^8467 ≤ (42931815977147/100000000000000 : ℝ)^6419
        have hw : |(1316869409/2500000000 : ℝ)|=(1316869409/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1273_s6_1 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344174151/10000000000 : ℝ)*x 0 + (-86712147/400000000 : ℝ)*x 1 + (2633738827/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344174151/10000000000 : ℝ)^8467 ≤ (43758269931879/100000000000000 : ℝ)^6419 := by
    have hnat : (5344174151 : ℕ)^8467*100000000000000^6419 ≤ 43758269931879^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344174151 10000000000 43758269931879 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (86712147/400000000 : ℝ)^8467 ≤ (13309913884287/100000000000000 : ℝ)^6419 := by
    have hnat : (86712147 : ℕ)^8467*100000000000000^6419 ≤ 13309913884287^6419*400000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86712147 400000000 13309913884287 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633738827/5000000000 : ℝ)^8467 ≤ (2146590808533/5000000000000 : ℝ)^6419 := by
    have hnat : (2633738827 : ℕ)^8467*5000000000000^6419 ≤ 2146590808533^6419*5000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633738827 5000000000 2146590808533 5000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344174151/10000000000 : ℝ), (-86712147/400000000 : ℝ), (2633738827/5000000000 : ℝ)] ![(43758269931879/100000000000000 : ℝ), (13309913884287/100000000000000 : ℝ), (2146590808533/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344174151/10000000000 : ℝ)|^8467 ≤ (43758269931879/100000000000000 : ℝ)^6419
        have hw : |(5344174151/10000000000 : ℝ)|=(5344174151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-86712147/400000000 : ℝ)|^8467 ≤ (13309913884287/100000000000000 : ℝ)^6419
        have hw : |(-86712147/400000000 : ℝ)|=(86712147/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633738827/5000000000 : ℝ)|^8467 ≤ (2146590808533/5000000000000 : ℝ)^6419
        have hw : |(2633738827/5000000000 : ℝ)|=(2633738827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1273_s6_2 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (33401089/62500000 : ℝ)*x 0 + (1316869427/2500000000 : ℝ)*x 1 + (-1083901743/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33401089/62500000 : ℝ)^8467 ≤ (43758270893119/100000000000000 : ℝ)^6419 := by
    have hnat : (33401089 : ℕ)^8467*100000000000000^6419 ≤ 43758270893119^6419*62500000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33401089 62500000 43758270893119 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316869427/2500000000 : ℝ)^8467 ≤ (42931816751201/100000000000000 : ℝ)^6419 := by
    have hnat : (1316869427 : ℕ)^8467*100000000000000^6419 ≤ 42931816751201^6419*2500000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316869427 2500000000 42931816751201 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1083901743/5000000000 : ℝ)^8467 ≤ (106479298829/800000000000 : ℝ)^6419 := by
    have hnat : (1083901743 : ℕ)^8467*800000000000^6419 ≤ 106479298829^6419*5000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083901743 5000000000 106479298829 800000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33401089/62500000 : ℝ), (1316869427/2500000000 : ℝ), (-1083901743/5000000000 : ℝ)] ![(43758270893119/100000000000000 : ℝ), (42931816751201/100000000000000 : ℝ), (106479298829/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33401089/62500000 : ℝ)|^8467 ≤ (43758270893119/100000000000000 : ℝ)^6419
        have hw : |(33401089/62500000 : ℝ)|=(33401089/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316869427/2500000000 : ℝ)|^8467 ≤ (42931816751201/100000000000000 : ℝ)^6419
        have hw : |(1316869427/2500000000 : ℝ)|=(1316869427/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1083901743/5000000000 : ℝ)|^8467 ≤ (106479298829/800000000000 : ℝ)^6419
        have hw : |(-1083901743/5000000000 : ℝ)|=(1083901743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1273_s6_3 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4346394989/10000000000 : ℝ)*x 0 + (4222336697/10000000000 : ℝ)*x 1 + (111849221/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4346394989/10000000000 : ℝ)^8467 ≤ (16658783979853/50000000000000 : ℝ)^6419 := by
    have hnat : (4346394989 : ℕ)^8467*50000000000000^6419 ≤ 16658783979853^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4346394989 10000000000 16658783979853 50000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4222336697/10000000000 : ℝ)^8467 ≤ (320689285061/1000000000000 : ℝ)^6419 := by
    have hnat : (4222336697 : ℕ)^8467*1000000000000^6419 ≤ 320689285061^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4222336697 10000000000 320689285061 1000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (111849221/250000000 : ℝ)^8467 ≤ (17306751760779/50000000000000 : ℝ)^6419 := by
    have hnat : (111849221 : ℕ)^8467*50000000000000^6419 ≤ 17306751760779^6419*250000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111849221 250000000 17306751760779 50000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4346394989/10000000000 : ℝ), (4222336697/10000000000 : ℝ), (111849221/250000000 : ℝ)] ![(16658783979853/50000000000000 : ℝ), (320689285061/1000000000000 : ℝ), (17306751760779/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4346394989/10000000000 : ℝ)|^8467 ≤ (16658783979853/50000000000000 : ℝ)^6419
        have hw : |(4346394989/10000000000 : ℝ)|=(4346394989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4222336697/10000000000 : ℝ)|^8467 ≤ (320689285061/1000000000000 : ℝ)^6419
        have hw : |(4222336697/10000000000 : ℝ)|=(4222336697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(111849221/250000000 : ℝ)|^8467 ≤ (17306751760779/50000000000000 : ℝ)^6419
        have hw : |(111849221/250000000 : ℝ)|=(111849221/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1273_s6_4 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2105306013/10000000000 : ℝ)*x 0 + (2633894919/5000000000 : ℝ)*x 1 + (1347611667/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2105306013/10000000000 : ℝ)^8467 ≤ (6403052412653/50000000000000 : ℝ)^6419 := by
    have hnat : (2105306013 : ℕ)^8467*50000000000000^6419 ≤ 6403052412653^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2105306013 10000000000 6403052412653 50000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633894919/5000000000 : ℝ)^8467 ≤ (21467586207189/50000000000000 : ℝ)^6419 := by
    have hnat : (2633894919 : ℕ)^8467*50000000000000^6419 ≤ 21467586207189^6419*5000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633894919 5000000000 21467586207189 50000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347611667/2500000000 : ℝ)^8467 ≤ (44258722744983/100000000000000 : ℝ)^6419 := by
    have hnat : (1347611667 : ℕ)^8467*100000000000000^6419 ≤ 44258722744983^6419*2500000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347611667 2500000000 44258722744983 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2105306013/10000000000 : ℝ), (2633894919/5000000000 : ℝ), (1347611667/2500000000 : ℝ)] ![(6403052412653/50000000000000 : ℝ), (21467586207189/50000000000000 : ℝ), (44258722744983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2105306013/10000000000 : ℝ)|^8467 ≤ (6403052412653/50000000000000 : ℝ)^6419
        have hw : |(-2105306013/10000000000 : ℝ)|=(2105306013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633894919/5000000000 : ℝ)|^8467 ≤ (21467586207189/50000000000000 : ℝ)^6419
        have hw : |(2633894919/5000000000 : ℝ)|=(2633894919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347611667/2500000000 : ℝ)|^8467 ≤ (44258722744983/100000000000000 : ℝ)^6419
        have hw : |(1347611667/2500000000 : ℝ)|=(1347611667/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1273_s6_5 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (664081379/1250000000 : ℝ)*x 0 + (-2044834613/10000000000 : ℝ)*x 1 + (5390446669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664081379/1250000000 : ℝ)^8467 ≤ (43418126960003/100000000000000 : ℝ)^6419 := by
    have hnat : (664081379 : ℕ)^8467*100000000000000^6419 ≤ 43418126960003^6419*1250000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664081379 1250000000 43418126960003 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2044834613/10000000000 : ℝ)^8467 ≤ (770196891769/6250000000000 : ℝ)^6419 := by
    have hnat : (2044834613 : ℕ)^8467*6250000000000^6419 ≤ 770196891769^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2044834613 10000000000 770196891769 6250000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390446669/10000000000 : ℝ)^8467 ≤ (44258722755813/100000000000000 : ℝ)^6419 := by
    have hnat : (5390446669 : ℕ)^8467*100000000000000^6419 ≤ 44258722755813^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390446669 10000000000 44258722755813 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664081379/1250000000 : ℝ), (-2044834613/10000000000 : ℝ), (5390446669/10000000000 : ℝ)] ![(43418126960003/100000000000000 : ℝ), (770196891769/6250000000000 : ℝ), (44258722755813/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664081379/1250000000 : ℝ)|^8467 ≤ (43418126960003/100000000000000 : ℝ)^6419
        have hw : |(664081379/1250000000 : ℝ)|=(664081379/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2044834613/10000000000 : ℝ)|^8467 ≤ (770196891769/6250000000000 : ℝ)^6419
        have hw : |(-2044834613/10000000000 : ℝ)|=(2044834613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390446669/10000000000 : ℝ)|^8467 ≤ (44258722755813/100000000000000 : ℝ)^6419
        have hw : |(5390446669/10000000000 : ℝ)|=(5390446669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1273_s6_6 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312651031/10000000000 : ℝ)*x 0 + (5390446669/10000000000 : ℝ)*x 1 + (-1022417307/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312651031/10000000000 : ℝ)^8467 ≤ (43418126949223/100000000000000 : ℝ)^6419 := by
    have hnat : (5312651031 : ℕ)^8467*100000000000000^6419 ≤ 43418126949223^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312651031 10000000000 43418126949223 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390446669/10000000000 : ℝ)^8467 ≤ (44258722755813/100000000000000 : ℝ)^6419 := by
    have hnat : (5390446669 : ℕ)^8467*100000000000000^6419 ≤ 44258722755813^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390446669 10000000000 44258722755813 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1022417307/5000000000 : ℝ)^8467 ≤ (6161575138127/50000000000000 : ℝ)^6419 := by
    have hnat : (1022417307 : ℕ)^8467*50000000000000^6419 ≤ 6161575138127^6419*5000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1022417307 5000000000 6161575138127 50000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312651031/10000000000 : ℝ), (5390446669/10000000000 : ℝ), (-1022417307/5000000000 : ℝ)] ![(43418126949223/100000000000000 : ℝ), (44258722755813/100000000000000 : ℝ), (6161575138127/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312651031/10000000000 : ℝ)|^8467 ≤ (43418126949223/100000000000000 : ℝ)^6419
        have hw : |(5312651031/10000000000 : ℝ)|=(5312651031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390446669/10000000000 : ℝ)|^8467 ≤ (44258722755813/100000000000000 : ℝ)^6419
        have hw : |(5390446669/10000000000 : ℝ)|=(5390446669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1022417307/5000000000 : ℝ)|^8467 ≤ (6161575138127/50000000000000 : ℝ)^6419
        have hw : |(-1022417307/5000000000 : ℝ)|=(1022417307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1273_s6_7 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2173202291/5000000000 : ℝ)*x 0 + (2236666007/5000000000 : ℝ)*x 1 + (4222975681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2173202291/5000000000 : ℝ)^8467 ≤ (16658832478641/50000000000000 : ℝ)^6419 := by
    have hnat : (2173202291 : ℕ)^8467*50000000000000^6419 ≤ 16658832478641^6419*5000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173202291 5000000000 16658832478641 50000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2236666007/5000000000 : ℝ)^8467 ≤ (8651751208291/25000000000000 : ℝ)^6419 := by
    have hnat : (2236666007 : ℕ)^8467*25000000000000^6419 ≤ 8651751208291^6419*5000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2236666007 5000000000 8651751208291 25000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4222975681/10000000000 : ℝ)^8467 ≤ (16037665095101/50000000000000 : ℝ)^6419 := by
    have hnat : (4222975681 : ℕ)^8467*50000000000000^6419 ≤ 16037665095101^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4222975681 10000000000 16037665095101 50000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2173202291/5000000000 : ℝ), (2236666007/5000000000 : ℝ), (4222975681/10000000000 : ℝ)] ![(16658832478641/50000000000000 : ℝ), (8651751208291/25000000000000 : ℝ), (16037665095101/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2173202291/5000000000 : ℝ)|^8467 ≤ (16658832478641/50000000000000 : ℝ)^6419
        have hw : |(2173202291/5000000000 : ℝ)|=(2173202291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2236666007/5000000000 : ℝ)|^8467 ≤ (8651751208291/25000000000000 : ℝ)^6419
        have hw : |(2236666007/5000000000 : ℝ)|=(2236666007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4222975681/10000000000 : ℝ)|^8467 ≤ (16037665095101/50000000000000 : ℝ)^6419
        have hw : |(4222975681/10000000000 : ℝ)|=(4222975681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1273_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152055603/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (442/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2299/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (11513/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (113/800 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (442/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2299/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (442/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2299/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (442/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2299/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (442/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2299/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (442/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2299/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (442/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2299/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2299/20000 : ℝ) ^ (4233/1024 : ℝ) ≤ (2614401443879803/20000000000000000000 : ℝ) := by
    have hpowers : (2299/20000 : ℝ)^4233 ≤ (2614401443879803/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2299 : ℕ)^4233*20000000000000000000^1024 ≤ 2614401443879803^1024*20000^4233 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2299 20000 2614401443879803 20000000000000000000 4233 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2299/20000 : ℝ)) (X := (2614401443879803/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4233 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (442/3125 : ℝ) ^ (4233/1024 : ℝ) ≤ (30806676495922989/100000000000000000000 : ℝ) := by
    have hpowers : (442/3125 : ℝ)^4233 ≤ (30806676495922989/100000000000000000000 : ℝ)^1024 := by
      have hnat : (442 : ℕ)^4233*100000000000000000000^1024 ≤ 30806676495922989^1024*3125^4233 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        442 3125 30806676495922989 100000000000000000000 4233 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (442/3125 : ℝ)) (X := (30806676495922989/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4233 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002614401443879803/10000000000000000000 : ℝ) ≤ (10000632384082203/10000000000000000 : ℝ) ^ (4233/1024 : ℝ) := by
    have hpowers : (10002614401443879803/10000000000000000000 : ℝ)^1024 ≤ (10000632384082203/10000000000000000 : ℝ)^4233 := by
      have hnat : (10002614401443879803 : ℕ)^1024*10000000000000000^4233 ≤ 10000632384082203^4233*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002614401443879803 10000000000000000000 10000632384082203 10000000000000000 1024 4233 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000632384082203/10000000000000000 : ℝ)) (X := (10002614401443879803/10000000000000000000 : ℝ)) (by norm_num) 4233 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25010969670928830501/25000000000000000000 : ℝ) ≤ (5000530643763093/5000000000000000 : ℝ) ^ (4233/1024 : ℝ) := by
    have hpowers : (25010969670928830501/25000000000000000000 : ℝ)^1024 ≤ (5000530643763093/5000000000000000 : ℝ)^4233 := by
      have hnat : (25010969670928830501 : ℕ)^1024*5000000000000000^4233 ≤ 5000530643763093^4233*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010969670928830501 25000000000000000000 5000530643763093 5000000000000000 1024 4233 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000530643763093/5000000000000000 : ℝ)) (X := (25010969670928830501/25000000000000000000 : ℝ)) (by norm_num) 4233 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50030806676495922989/50000000000000000000 : ℝ) ≤ (10001490190970169/10000000000000000 : ℝ) ^ (4233/1024 : ℝ) := by
    have hpowers : (50030806676495922989/50000000000000000000 : ℝ)^1024 ≤ (10001490190970169/10000000000000000 : ℝ)^4233 := by
      have hnat : (50030806676495922989 : ℕ)^1024*10000000000000000^4233 ≤ 10001490190970169^4233*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030806676495922989 50000000000000000000 10001490190970169 10000000000000000 1024 4233 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001490190970169/10000000000000000 : ℝ)) (X := (50030806676495922989/50000000000000000000 : ℝ)) (by norm_num) 4233 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2614401443879803/20000000000000000000 : ℝ) ≤ ((8827271565085528859/8830000000000000000 : ℝ)+2*(142967814661/88300000000000 : ℝ)*(2299/20000 : ℝ))^(4233/1024 : ℝ) := by
    rw [show (8827271565085528859/8830000000000000000 : ℝ)+2*(142967814661/88300000000000 : ℝ)*(2299/20000 : ℝ)=(10000632384082203/10000000000000000 : ℝ) by norm_num, show 1+2*(2614401443879803/20000000000000000000 : ℝ)=(10002614401443879803/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30806676495922989/100000000000000000000 : ℝ)+(2614401443879803/20000000000000000000 : ℝ) ≤ ((8827271565085528859/8830000000000000000 : ℝ)+(142967814661/88300000000000 : ℝ)*((442/3125 : ℝ)+(2299/20000 : ℝ)))^(4233/1024 : ℝ) := by
    rw [show (8827271565085528859/8830000000000000000 : ℝ)+(142967814661/88300000000000 : ℝ)*((442/3125 : ℝ)+(2299/20000 : ℝ))=(5000530643763093/5000000000000000 : ℝ) by norm_num, show 1+(30806676495922989/100000000000000000000 : ℝ)+(2614401443879803/20000000000000000000 : ℝ)=(25010969670928830501/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30806676495922989/100000000000000000000 : ℝ) ≤ ((8827271565085528859/8830000000000000000 : ℝ)+2*(142967814661/88300000000000 : ℝ)*(442/3125 : ℝ))^(4233/1024 : ℝ) := by
    rw [show (8827271565085528859/8830000000000000000 : ℝ)+2*(142967814661/88300000000000 : ℝ)*(442/3125 : ℝ)=(10001490190970169/10000000000000000 : ℝ) by norm_num, show 1+2*(30806676495922989/100000000000000000000 : ℝ)=(50030806676495922989/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8827271565085528859/8830000000000000000 : ℝ)*(X 1 0+X 2 0)+(142967814661/88300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4233/1024 : ℝ)) (lo := (2299/20000 : ℝ)) (hi := (442/3125 : ℝ)) (c := (8827271565085528859/8830000000000000000 : ℝ)) (alpha := (142967814661/88300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8827271565085528859/8830000000000000000 : ℝ)*(X 0 1+X 2 1)+(142967814661/88300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4233/1024 : ℝ)) (lo := (2299/20000 : ℝ)) (hi := (442/3125 : ℝ)) (c := (8827271565085528859/8830000000000000000 : ℝ)) (alpha := (142967814661/88300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8827271565085528859/8830000000000000000 : ℝ)*(X 0 2+X 1 2)+(142967814661/88300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4233/1024 : ℝ)) (lo := (2299/20000 : ℝ)) (hi := (442/3125 : ℝ)) (c := (8827271565085528859/8830000000000000000 : ℝ)) (alpha := (142967814661/88300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2105301489/10000000000 : ℝ)*X 0 0+(1347689983/2500000000 : ℝ)*X 0 1+(1316869409/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344174151/10000000000 : ℝ)*X 1 0+(-86712147/400000000 : ℝ)*X 1 1+(2633738827/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((33401089/62500000 : ℝ)*X 2 0+(1316869427/2500000000 : ℝ)*X 2 1+(-1083901743/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4346394989/10000000000 : ℝ)*X 0 0+(4222336697/10000000000 : ℝ)*X 0 1+(111849221/250000000 : ℝ)*X 0 2+(4346394989/10000000000 : ℝ)*X 1 0+(4222336697/10000000000 : ℝ)*X 1 1+(111849221/250000000 : ℝ)*X 1 2+(4346394989/10000000000 : ℝ)*X 2 0+(4222336697/10000000000 : ℝ)*X 2 1+(111849221/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2105306013/10000000000 : ℝ)*X 0 0+(2633894919/5000000000 : ℝ)*X 0 1+(1347611667/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((664081379/1250000000 : ℝ)*X 1 0+(-2044834613/10000000000 : ℝ)*X 1 1+(5390446669/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312651031/10000000000 : ℝ)*X 2 0+(5390446669/10000000000 : ℝ)*X 2 1+(-1022417307/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2173202291/5000000000 : ℝ)*X 0 0+(2236666007/5000000000 : ℝ)*X 0 1+(4222975681/10000000000 : ℝ)*X 0 2+(2173202291/5000000000 : ℝ)*X 1 0+(2236666007/5000000000 : ℝ)*X 1 1+(4222975681/10000000000 : ℝ)*X 1 2+(2173202291/5000000000 : ℝ)*X 2 0+(2236666007/5000000000 : ℝ)*X 2 1+(4222975681/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (256046414421786177016085883/44150000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1255425281/100000000000000 : ℝ)*(base19) + (1200471509/100000000000000 : ℝ)*(base23) + (26588959/100000000000000 : ℝ)*(upper3) + (101560987/100000000000000 : ℝ)*(upper4) + (228736029/100000000000000 : ℝ)*(upper5) + (604281267051979/10000000000000 : ℝ)*(major0) + (604281267051979/10000000000000 : ℝ)*(major1) + (604281267051979/10000000000000 : ℝ)*(major2) + (8111496910709839/100000000000000 : ℝ)*(sp0) + (4055771498018119/50000000000000 : ℝ)*(sp1) + (8111543050990009/100000000000000 : ℝ)*(sp2) + (1987034586578537/50000000000000 : ℝ)*(sp3) + (47340751679/100000000000000 : ℝ)*(sp4) + (5861552727/50000000000000 : ℝ)*(sp7) + (31047507002051/781250000000 : ℝ)*(f.failure) + (4055772125730759/50000000000000 : ℝ)*(f.sum) + (206285251879/88300000000000000000000000 : ℝ)*base66 + (348264289687738039/88300000000000000000000000000000 : ℝ)*base68 + (239769781763538039/88300000000000000000000000000000 : ℝ)*base70 + (1321172980412138039/88300000000000000000000000000000 : ℝ)*base72 + (217246382267/441500000000000000000000000 : ℝ)*base74 + (216865598494338039/88300000000000000000000000000000 : ℝ)*base76 + (90189122785261961/88300000000000000000000000000000 : ℝ)*base77 + (1412330830049661961/88300000000000000000000000000000 : ℝ)*base79 + (4490389198721/441500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1104253/78125000000000000000 : ℝ)*base89 + (1104253/78125000000000000000 : ℝ)*base91 + (1104253/78125000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3610218024575388153535887501/441500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11699581/800000000000 : ℝ)*(base19) + (1587221813/100000000000000 : ℝ)*(base23) + (165075669/100000000000000 : ℝ)*(upper3) + (14452617/25000000000000 : ℝ)*(lower4) + (33730487/20000000000000 : ℝ)*(upper5) + (6073566351493987/100000000000000 : ℝ)*(major0) + (6073566351493987/100000000000000 : ℝ)*(major1) + (6073566351493987/100000000000000 : ℝ)*(major2) + (41462692543/100000000000000 : ℝ)*(sp1) + (22205278383/50000000000000 : ℝ)*(sp2) + (1630565249579569/20000000000000 : ℝ)*(sp4) + (2038195830689419/25000000000000 : ℝ)*(sp5) + (1630556050023853/20000000000000 : ℝ)*(sp6) + (1997153091258987/50000000000000 : ℝ)*(sp7) + (1997153091258987/50000000000000 : ℝ)*(f.failure) + (1630565249579569/20000000000000 : ℝ)*(f.sum) + (18724942867481/2207500000000000000000000000 : ℝ)*base65 + (4768014070276170833/883000000000000000000000000000000 : ℝ)*base67 + (4317969402787829167/883000000000000000000000000000000 : ℝ)*base70 + (4038565675170833/883000000000000000000000000000000 : ℝ)*base71 + (8095455445681/2207500000000000000000000000 : ℝ)*base73 + (3780301825214170833/883000000000000000000000000000000 : ℝ)*base75 + (7361720000014829167/883000000000000000000000000000000 : ℝ)*base78 + (16341979393127170833/883000000000000000000000000000000 : ℝ)*base79 + (4531247391413/4415000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (52545839/5000000000000000000000 : ℝ)*base90 + (52545839/5000000000000000000000 : ℝ)*base92 + (52545839/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1273_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152055603/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (442/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2299/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11513/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (113/800 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1273_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1273_s7_0 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-421063257/2000000000 : ℝ)*x 0 + (2695295027/5000000000 : ℝ)*x 1 + (164613679/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (421063257/2000000000 : ℝ)^8467 ≤ (1280618724279/10000000000000 : ℝ)^6419 := by
    have hnat : (421063257 : ℕ)^8467*10000000000000^6419 ≤ 1280618724279^6419*2000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      421063257 2000000000 1280618724279 10000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695295027/5000000000 : ℝ)^8467 ≤ (44260275650023/100000000000000 : ℝ)^6419 := by
    have hnat : (2695295027 : ℕ)^8467*100000000000000^6419 ≤ 44260275650023^6419*5000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695295027 5000000000 44260275650023 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (164613679/312500000 : ℝ)^8467 ≤ (42933537094481/100000000000000 : ℝ)^6419 := by
    have hnat : (164613679 : ℕ)^8467*100000000000000^6419 ≤ 42933537094481^6419*312500000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164613679 312500000 42933537094481 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-421063257/2000000000 : ℝ), (2695295027/5000000000 : ℝ), (164613679/312500000 : ℝ)] ![(1280618724279/10000000000000 : ℝ), (44260275650023/100000000000000 : ℝ), (42933537094481/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-421063257/2000000000 : ℝ)|^8467 ≤ (1280618724279/10000000000000 : ℝ)^6419
        have hw : |(-421063257/2000000000 : ℝ)|=(421063257/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695295027/5000000000 : ℝ)|^8467 ≤ (44260275650023/100000000000000 : ℝ)^6419
        have hw : |(2695295027/5000000000 : ℝ)|=(2695295027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(164613679/312500000 : ℝ)|^8467 ≤ (42933537094481/100000000000000 : ℝ)^6419
        have hw : |(164613679/312500000 : ℝ)|=(164613679/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1273_s7_1 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344130873/10000000000 : ℝ)*x 0 + (-1083824447/5000000000 : ℝ)*x 1 + (5267637729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344130873/10000000000 : ℝ)^8467 ≤ (43757802510743/100000000000000 : ℝ)^6419 := by
    have hnat : (5344130873 : ℕ)^8467*100000000000000^6419 ≤ 43757802510743^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344130873 10000000000 43757802510743 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1083824447/5000000000 : ℝ)^8467 ≤ (6654330183709/50000000000000 : ℝ)^6419 := by
    have hnat : (1083824447 : ℕ)^8467*50000000000000^6419 ≤ 6654330183709^6419*5000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083824447 5000000000 6654330183709 50000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267637729/10000000000 : ℝ)^8467 ≤ (2683346069077/6250000000000 : ℝ)^6419 := by
    have hnat : (5267637729 : ℕ)^8467*6250000000000^6419 ≤ 2683346069077^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267637729 10000000000 2683346069077 6250000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344130873/10000000000 : ℝ), (-1083824447/5000000000 : ℝ), (5267637729/10000000000 : ℝ)] ![(43757802510743/100000000000000 : ℝ), (6654330183709/50000000000000 : ℝ), (2683346069077/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344130873/10000000000 : ℝ)|^8467 ≤ (43757802510743/100000000000000 : ℝ)^6419
        have hw : |(5344130873/10000000000 : ℝ)|=(5344130873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1083824447/5000000000 : ℝ)|^8467 ≤ (6654330183709/50000000000000 : ℝ)^6419
        have hw : |(-1083824447/5000000000 : ℝ)|=(1083824447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267637729/10000000000 : ℝ)|^8467 ≤ (2683346069077/6250000000000 : ℝ)^6419
        have hw : |(5267637729/10000000000 : ℝ)|=(5267637729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1273_s7_2 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672065429/5000000000 : ℝ)*x 0 + (5267637761/10000000000 : ℝ)*x 1 + (-270956109/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672065429/5000000000 : ℝ)^8467 ≤ (43757802348737/100000000000000 : ℝ)^6419 := by
    have hnat : (2672065429 : ℕ)^8467*100000000000000^6419 ≤ 43757802348737^6419*5000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672065429 5000000000 43757802348737 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267637761/10000000000 : ℝ)^8467 ≤ (42933537449259/100000000000000 : ℝ)^6419 := by
    have hnat : (5267637761 : ℕ)^8467*100000000000000^6419 ≤ 42933537449259^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267637761 10000000000 42933537449259 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270956109/1250000000 : ℝ)^8467 ≤ (53234640757/400000000000 : ℝ)^6419 := by
    have hnat : (270956109 : ℕ)^8467*400000000000^6419 ≤ 53234640757^6419*1250000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270956109 1250000000 53234640757 400000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672065429/5000000000 : ℝ), (5267637761/10000000000 : ℝ), (-270956109/1250000000 : ℝ)] ![(43757802348737/100000000000000 : ℝ), (42933537449259/100000000000000 : ℝ), (53234640757/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672065429/5000000000 : ℝ)|^8467 ≤ (43757802348737/100000000000000 : ℝ)^6419
        have hw : |(2672065429/5000000000 : ℝ)|=(2672065429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267637761/10000000000 : ℝ)|^8467 ≤ (42933537449259/100000000000000 : ℝ)^6419
        have hw : |(5267637761/10000000000 : ℝ)|=(5267637761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-270956109/1250000000 : ℝ)|^8467 ≤ (53234640757/400000000000 : ℝ)^6419
        have hw : |(-270956109/1250000000 : ℝ)|=(270956109/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1273_s7_3 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2173201747/5000000000 : ℝ)*x 0 + (527833991/1250000000 : ℝ)*x 1 + (1118407827/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2173201747/5000000000 : ℝ)^8467 ≤ (33317653956199/100000000000000 : ℝ)^6419 := by
    have hnat : (2173201747 : ℕ)^8467*100000000000000^6419 ≤ 33317653956199^6419*5000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173201747 5000000000 33317653956199 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (527833991/1250000000 : ℝ)^8467 ≤ (16036143495673/50000000000000 : ℝ)^6419 := by
    have hnat : (527833991 : ℕ)^8467*50000000000000^6419 ≤ 16036143495673^6419*1250000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527833991 1250000000 16036143495673 50000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1118407827/2500000000 : ℝ)^8467 ≤ (6922011806967/20000000000000 : ℝ)^6419 := by
    have hnat : (1118407827 : ℕ)^8467*20000000000000^6419 ≤ 6922011806967^6419*2500000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1118407827 2500000000 6922011806967 20000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2173201747/5000000000 : ℝ), (527833991/1250000000 : ℝ), (1118407827/2500000000 : ℝ)] ![(33317653956199/100000000000000 : ℝ), (16036143495673/50000000000000 : ℝ), (6922011806967/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2173201747/5000000000 : ℝ)|^8467 ≤ (33317653956199/100000000000000 : ℝ)^6419
        have hw : |(2173201747/5000000000 : ℝ)|=(2173201747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(527833991/1250000000 : ℝ)|^8467 ≤ (16036143495673/50000000000000 : ℝ)^6419
        have hw : |(527833991/1250000000 : ℝ)|=(527833991/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1118407827/2500000000 : ℝ)|^8467 ≤ (6922011806967/20000000000000 : ℝ)^6419
        have hw : |(1118407827/2500000000 : ℝ)|=(1118407827/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1273_s7_4 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-52633019/250000000 : ℝ)*x 0 + (2633974167/5000000000 : ℝ)*x 1 + (1078055681/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (52633019/250000000 : ℝ)^8467 ≤ (12806223148033/100000000000000 : ℝ)^6419 := by
    have hnat : (52633019 : ℕ)^8467*100000000000000^6419 ≤ 12806223148033^6419*250000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52633019 250000000 12806223148033 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633974167/5000000000 : ℝ)^8467 ≤ (10734219101393/25000000000000 : ℝ)^6419 := by
    have hnat : (2633974167 : ℕ)^8467*25000000000000^6419 ≤ 10734219101393^6419*5000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633974167 5000000000 10734219101393 25000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078055681/2000000000 : ℝ)^8467 ≤ (44256900432827/100000000000000 : ℝ)^6419 := by
    have hnat : (1078055681 : ℕ)^8467*100000000000000^6419 ≤ 44256900432827^6419*2000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078055681 2000000000 44256900432827 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-52633019/250000000 : ℝ), (2633974167/5000000000 : ℝ), (1078055681/2000000000 : ℝ)] ![(12806223148033/100000000000000 : ℝ), (10734219101393/25000000000000 : ℝ), (44256900432827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-52633019/250000000 : ℝ)|^8467 ≤ (12806223148033/100000000000000 : ℝ)^6419
        have hw : |(-52633019/250000000 : ℝ)|=(52633019/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633974167/5000000000 : ℝ)|^8467 ≤ (10734219101393/25000000000000 : ℝ)^6419
        have hw : |(2633974167/5000000000 : ℝ)|=(2633974167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078055681/2000000000 : ℝ)|^8467 ≤ (44256900432827/100000000000000 : ℝ)^6419
        have hw : |(1078055681/2000000000 : ℝ)|=(1078055681/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1273_s7_5 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656345963/5000000000 : ℝ)*x 0 + (-2045008237/10000000000 : ℝ)*x 1 + (1347569631/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656345963/5000000000 : ℝ)^8467 ≤ (43418567801131/100000000000000 : ℝ)^6419 := by
    have hnat : (2656345963 : ℕ)^8467*100000000000000^6419 ≤ 43418567801131^6419*5000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656345963 5000000000 43418567801131 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2045008237/10000000000 : ℝ)^8467 ≤ (6162265233131/50000000000000 : ℝ)^6419 := by
    have hnat : (2045008237 : ℕ)^8467*50000000000000^6419 ≤ 6162265233131^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2045008237 10000000000 6162265233131 50000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347569631/2500000000 : ℝ)^8467 ≤ (5532112715201/12500000000000 : ℝ)^6419 := by
    have hnat : (1347569631 : ℕ)^8467*12500000000000^6419 ≤ 5532112715201^6419*2500000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347569631 2500000000 5532112715201 12500000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656345963/5000000000 : ℝ), (-2045008237/10000000000 : ℝ), (1347569631/2500000000 : ℝ)] ![(43418567801131/100000000000000 : ℝ), (6162265233131/50000000000000 : ℝ), (5532112715201/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656345963/5000000000 : ℝ)|^8467 ≤ (43418567801131/100000000000000 : ℝ)^6419
        have hw : |(2656345963/5000000000 : ℝ)|=(2656345963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2045008237/10000000000 : ℝ)|^8467 ≤ (6162265233131/50000000000000 : ℝ)^6419
        have hw : |(-2045008237/10000000000 : ℝ)|=(2045008237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347569631/2500000000 : ℝ)|^8467 ≤ (5532112715201/12500000000000 : ℝ)^6419
        have hw : |(1347569631/2500000000 : ℝ)|=(1347569631/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1273_s7_6 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312691833/10000000000 : ℝ)*x 0 + (1078055743/2000000000 : ℝ)*x 1 + (-1022504051/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312691833/10000000000 : ℝ)^8467 ≤ (43418566798581/100000000000000 : ℝ)^6419 := by
    have hnat : (5312691833 : ℕ)^8467*100000000000000^6419 ≤ 43418566798581^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312691833 10000000000 43418566798581 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078055743/2000000000 : ℝ)^8467 ≤ (22128451895077/50000000000000 : ℝ)^6419 := by
    have hnat : (1078055743 : ℕ)^8467*50000000000000^6419 ≤ 22128451895077^6419*2000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078055743 2000000000 22128451895077 50000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1022504051/5000000000 : ℝ)^8467 ≤ (2464905878617/20000000000000 : ℝ)^6419 := by
    have hnat : (1022504051 : ℕ)^8467*20000000000000^6419 ≤ 2464905878617^6419*5000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1022504051 5000000000 2464905878617 20000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312691833/10000000000 : ℝ), (1078055743/2000000000 : ℝ), (-1022504051/5000000000 : ℝ)] ![(43418566798581/100000000000000 : ℝ), (22128451895077/50000000000000 : ℝ), (2464905878617/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312691833/10000000000 : ℝ)|^8467 ≤ (43418566798581/100000000000000 : ℝ)^6419
        have hw : |(5312691833/10000000000 : ℝ)|=(5312691833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078055743/2000000000 : ℝ)|^8467 ≤ (22128451895077/50000000000000 : ℝ)^6419
        have hw : |(1078055743/2000000000 : ℝ)|=(1078055743/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1022504051/5000000000 : ℝ)|^8467 ≤ (2464905878617/20000000000000 : ℝ)^6419
        have hw : |(-1022504051/5000000000 : ℝ)|=(1022504051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1273_s7_7 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4346412769/10000000000 : ℝ)*x 0 + (2236498921/5000000000 : ℝ)*x 1 + (211165389/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4346412769/10000000000 : ℝ)^8467 ≤ (33317747738443/100000000000000 : ℝ)^6419 := by
    have hnat : (4346412769 : ℕ)^8467*100000000000000^6419 ≤ 33317747738443^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4346412769 10000000000 33317747738443 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2236498921/5000000000 : ℝ)^8467 ≤ (17301797394723/50000000000000 : ℝ)^6419 := by
    have hnat : (2236498921 : ℕ)^8467*50000000000000^6419 ≤ 17301797394723^6419*5000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2236498921 5000000000 17301797394723 50000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (211165389/500000000 : ℝ)^8467 ≤ (3207865745799/10000000000000 : ℝ)^6419 := by
    have hnat : (211165389 : ℕ)^8467*10000000000000^6419 ≤ 3207865745799^6419*500000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211165389 500000000 3207865745799 10000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4346412769/10000000000 : ℝ), (2236498921/5000000000 : ℝ), (211165389/500000000 : ℝ)] ![(33317747738443/100000000000000 : ℝ), (17301797394723/50000000000000 : ℝ), (3207865745799/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4346412769/10000000000 : ℝ)|^8467 ≤ (33317747738443/100000000000000 : ℝ)^6419
        have hw : |(4346412769/10000000000 : ℝ)|=(4346412769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2236498921/5000000000 : ℝ)|^8467 ≤ (17301797394723/50000000000000 : ℝ)^6419
        have hw : |(2236498921/5000000000 : ℝ)|=(2236498921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(211165389/500000000 : ℝ)|^8467 ≤ (3207865745799/10000000000000 : ℝ)^6419
        have hw : |(211165389/500000000 : ℝ)|=(211165389/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1273_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152055603/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (113/800 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11513/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2879/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14121/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (113/800 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11513/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (113/800 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11513/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (113/800 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11513/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (113/800 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11513/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (113/800 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11513/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (113/800 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11513/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11513/100000 : ℝ) ^ (4233/1024 : ℝ) ≤ (526273255300027/4000000000000000000 : ℝ) := by
    have hpowers : (11513/100000 : ℝ)^4233 ≤ (526273255300027/4000000000000000000 : ℝ)^1024 := by
      have hnat : (11513 : ℕ)^4233*4000000000000000000^1024 ≤ 526273255300027^1024*100000^4233 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11513 100000 526273255300027 4000000000000000000 4233 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11513/100000 : ℝ)) (X := (526273255300027/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4233 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (113/800 : ℝ) ^ (4233/1024 : ℝ) ≤ (30635965970125479/100000000000000000000 : ℝ) := by
    have hpowers : (113/800 : ℝ)^4233 ≤ (30635965970125479/100000000000000000000 : ℝ)^1024 := by
      have hnat : (113 : ℕ)^4233*100000000000000000000^1024 ≤ 30635965970125479^1024*800^4233 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        113 800 30635965970125479 100000000000000000000 4233 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (113/800 : ℝ)) (X := (30635965970125479/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4233 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000526273255300027/2000000000000000000 : ℝ) ≤ (10000636487208869/10000000000000000 : ℝ) ^ (4233/1024 : ℝ) := by
    have hpowers : (2000526273255300027/2000000000000000000 : ℝ)^1024 ≤ (10000636487208869/10000000000000000 : ℝ)^4233 := by
      have hnat : (2000526273255300027 : ℕ)^1024*10000000000000000^4233 ≤ 10000636487208869^4233*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000526273255300027 2000000000000000000 10000636487208869 10000000000000000 1024 4233 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000636487208869/10000000000000000 : ℝ)) (X := (2000526273255300027/2000000000000000000 : ℝ)) (by norm_num) 4233 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50021896398676313077/50000000000000000000 : ℝ) ≤ (5000529605274783/5000000000000000 : ℝ) ^ (4233/1024 : ℝ) := by
    have hpowers : (50021896398676313077/50000000000000000000 : ℝ)^1024 ≤ (5000529605274783/5000000000000000 : ℝ)^4233 := by
      have hnat : (50021896398676313077 : ℕ)^1024*5000000000000000^4233 ≤ 5000529605274783^4233*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021896398676313077 50000000000000000000 5000529605274783 5000000000000000 1024 4233 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000529605274783/5000000000000000 : ℝ)) (X := (50021896398676313077/50000000000000000000 : ℝ)) (by norm_num) 4233 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50030635965970125479/50000000000000000000 : ℝ) ≤ (10001481933890263/10000000000000000 : ℝ) ^ (4233/1024 : ℝ) := by
    have hpowers : (50030635965970125479/50000000000000000000 : ℝ)^1024 ≤ (10001481933890263/10000000000000000 : ℝ)^4233 := by
      have hnat : (50030635965970125479 : ℕ)^1024*10000000000000000^4233 ≤ 10001481933890263^4233*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030635965970125479 50000000000000000000 10001481933890263 10000000000000000 1024 4233 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001481933890263/10000000000000000 : ℝ)) (X := (50030635965970125479/50000000000000000000 : ℝ)) (by norm_num) 4233 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(526273255300027/4000000000000000000 : ℝ) ≤ ((13055964438473338353/13060000000000000000 : ℝ)+2*(422723340697/261200000000000 : ℝ)*(11513/100000 : ℝ))^(4233/1024 : ℝ) := by
    rw [show (13055964438473338353/13060000000000000000 : ℝ)+2*(422723340697/261200000000000 : ℝ)*(11513/100000 : ℝ)=(10000636487208869/10000000000000000 : ℝ) by norm_num, show 1+2*(526273255300027/4000000000000000000 : ℝ)=(2000526273255300027/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30635965970125479/100000000000000000000 : ℝ)+(526273255300027/4000000000000000000 : ℝ) ≤ ((13055964438473338353/13060000000000000000 : ℝ)+(422723340697/261200000000000 : ℝ)*((113/800 : ℝ)+(11513/100000 : ℝ)))^(4233/1024 : ℝ) := by
    rw [show (13055964438473338353/13060000000000000000 : ℝ)+(422723340697/261200000000000 : ℝ)*((113/800 : ℝ)+(11513/100000 : ℝ))=(5000529605274783/5000000000000000 : ℝ) by norm_num, show 1+(30635965970125479/100000000000000000000 : ℝ)+(526273255300027/4000000000000000000 : ℝ)=(50021896398676313077/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30635965970125479/100000000000000000000 : ℝ) ≤ ((13055964438473338353/13060000000000000000 : ℝ)+2*(422723340697/261200000000000 : ℝ)*(113/800 : ℝ))^(4233/1024 : ℝ) := by
    rw [show (13055964438473338353/13060000000000000000 : ℝ)+2*(422723340697/261200000000000 : ℝ)*(113/800 : ℝ)=(10001481933890263/10000000000000000 : ℝ) by norm_num, show 1+2*(30635965970125479/100000000000000000000 : ℝ)=(50030635965970125479/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13055964438473338353/13060000000000000000 : ℝ)*(X 1 0+X 2 0)+(422723340697/261200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4233/1024 : ℝ)) (lo := (11513/100000 : ℝ)) (hi := (113/800 : ℝ)) (c := (13055964438473338353/13060000000000000000 : ℝ)) (alpha := (422723340697/261200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13055964438473338353/13060000000000000000 : ℝ)*(X 0 1+X 2 1)+(422723340697/261200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4233/1024 : ℝ)) (lo := (11513/100000 : ℝ)) (hi := (113/800 : ℝ)) (c := (13055964438473338353/13060000000000000000 : ℝ)) (alpha := (422723340697/261200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13055964438473338353/13060000000000000000 : ℝ)*(X 0 2+X 1 2)+(422723340697/261200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4233/1024 : ℝ)) (lo := (11513/100000 : ℝ)) (hi := (113/800 : ℝ)) (c := (13055964438473338353/13060000000000000000 : ℝ)) (alpha := (422723340697/261200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-421063257/2000000000 : ℝ)*X 0 0+(2695295027/5000000000 : ℝ)*X 0 1+(164613679/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344130873/10000000000 : ℝ)*X 1 0+(-1083824447/5000000000 : ℝ)*X 1 1+(5267637729/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672065429/5000000000 : ℝ)*X 2 0+(5267637761/10000000000 : ℝ)*X 2 1+(-270956109/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2173201747/5000000000 : ℝ)*X 0 0+(527833991/1250000000 : ℝ)*X 0 1+(1118407827/2500000000 : ℝ)*X 0 2+(2173201747/5000000000 : ℝ)*X 1 0+(527833991/1250000000 : ℝ)*X 1 1+(1118407827/2500000000 : ℝ)*X 1 2+(2173201747/5000000000 : ℝ)*X 2 0+(527833991/1250000000 : ℝ)*X 2 1+(1118407827/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-52633019/250000000 : ℝ)*X 0 0+(2633974167/5000000000 : ℝ)*X 0 1+(1078055681/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656345963/5000000000 : ℝ)*X 1 0+(-2045008237/10000000000 : ℝ)*X 1 1+(1347569631/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312691833/10000000000 : ℝ)*X 2 0+(1078055743/2000000000 : ℝ)*X 2 1+(-1022504051/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4346412769/10000000000 : ℝ)*X 0 0+(2236498921/5000000000 : ℝ)*X 0 1+(211165389/500000000 : ℝ)*X 0 2+(4346412769/10000000000 : ℝ)*X 1 0+(2236498921/5000000000 : ℝ)*X 1 1+(211165389/500000000 : ℝ)*X 1 2+(4346412769/10000000000 : ℝ)*X 2 0+(2236498921/5000000000 : ℝ)*X 2 1+(211165389/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (128154199044397749465153/13060000000000000000000000000 : ℝ) := by norm_num
    linear_combination (996752093/50000000000000 : ℝ)*(base19) + (922427131/50000000000000 : ℝ)*(base23) + (67240443/100000000000000 : ℝ)*(lower2) + (240221923/100000000000000 : ℝ)*(upper3) + (90470703/50000000000000 : ℝ)*(upper5) + (6059056847332683/100000000000000 : ℝ)*(major0) + (6059056847332683/100000000000000 : ℝ)*(major1) + (6059056847332683/100000000000000 : ℝ)*(major2) + (127082687784451/1562500000000 : ℝ)*(sp0) + (2033336856834127/25000000000000 : ℝ)*(sp1) + (8133347575986433/100000000000000 : ℝ)*(sp2) + (3984735305861693/100000000000000 : ℝ)*(sp3) + (57402635831/100000000000000 : ℝ)*(sp4) + (2864087211/10000000000000 : ℝ)*(sp7) + (996190986683451/25000000000000 : ℝ)*(f.failure) + (1626669884168139/20000000000000 : ℝ)*(f.sum) + (21810770416131/13060000000000000000000000000 : ℝ)*base65 + (3561088144187158901/1306000000000000000000000000000000 : ℝ)*base68 + (4367830277429158901/1306000000000000000000000000000000 : ℝ)*base70 + (9155798906320841099/1306000000000000000000000000000000 : ℝ)*base71 + (30576186450269/13060000000000000000000000000 : ℝ)*base74 + (7174765171360841099/1306000000000000000000000000000000 : ℝ)*base75 + (3671521560859158901/1306000000000000000000000000000000 : ℝ)*base78 + (7727298952094841099/1306000000000000000000000000000000 : ℝ)*base79 + (18996251384029/13060000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (36925953/2500000000000000000000 : ℝ)*base89 + (36925953/2500000000000000000000 : ℝ)*base91 + (36925953/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (357093162424449992477273973/65300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (235869889/100000000000000 : ℝ)*(base19) + (1508419/400000000000 : ℝ)*(base23) + (59082781/50000000000000 : ℝ)*(upper3) + (46611003/50000000000000 : ℝ)*(lower4) + (608978369041847/10000000000000 : ℝ)*(major0) + (608978369041847/10000000000000 : ℝ)*(major1) + (608978369041847/10000000000000 : ℝ)*(major2) + (223828399/3125000000000 : ℝ)*(sp1) + (25558564171/100000000000000 : ℝ)*(sp2) + (128324059/5000000000000 : ℝ)*(sp3) + (1021824451951659/12500000000000 : ℝ)*(sp4) + (4087294108617307/50000000000000 : ℝ)*(sp5) + (8174569679944351/100000000000000 : ℝ)*(sp6) + (250310563528693/6250000000000 : ℝ)*(sp7) + (1001242895735067/25000000000000 : ℝ)*(f.failure) + (1021824451951659/12500000000000 : ℝ)*(f.sum) + (356283451473/1306000000000000000000000000 : ℝ)*base66 + (1710110895695392009/130600000000000000000000000000000 : ℝ)*base68 + (2900711071328992009/130600000000000000000000000000000 : ℝ)*base70 + (587565381643007991/130600000000000000000000000000000 : ℝ)*base71 + (2508853103403/1306000000000000000000000000 : ℝ)*base73 + (203553442562207991/130600000000000000000000000000000 : ℝ)*base75 + (302989889690792009/130600000000000000000000000000000 : ℝ)*base78 + (1848594074684192009/130600000000000000000000000000000 : ℝ)*base80 + (6020156684563/1306000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (9069599/2500000000000000000000 : ℝ)*base90 + (9069599/2500000000000000000000 : ℝ)*base92 + (9069599/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1273_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152055603/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (113/800 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11513/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2879/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14121/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1273_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1273_s8_0 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2105321421/10000000000 : ℝ)*x 0 + (2695278513/5000000000 : ℝ)*x 1 + (5267667167/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2105321421/10000000000 : ℝ)^8467 ≤ (640311422579/5000000000000 : ℝ)^6419 := by
    have hnat : (2105321421 : ℕ)^8467*5000000000000^6419 ≤ 640311422579^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2105321421 10000000000 640311422579 5000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695278513/5000000000 : ℝ)^8467 ≤ (44259917947631/100000000000000 : ℝ)^6419 := by
    have hnat : (2695278513 : ℕ)^8467*100000000000000^6419 ≤ 44259917947631^6419*5000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695278513 5000000000 44259917947631 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267667167/10000000000 : ℝ)^8467 ≤ (42933853589147/100000000000000 : ℝ)^6419 := by
    have hnat : (5267667167 : ℕ)^8467*100000000000000^6419 ≤ 42933853589147^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267667167 10000000000 42933853589147 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2105321421/10000000000 : ℝ), (2695278513/5000000000 : ℝ), (5267667167/10000000000 : ℝ)] ![(640311422579/5000000000000 : ℝ), (44259917947631/100000000000000 : ℝ), (42933853589147/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2105321421/10000000000 : ℝ)|^8467 ≤ (640311422579/5000000000000 : ℝ)^6419
        have hw : |(-2105321421/10000000000 : ℝ)|=(2105321421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695278513/5000000000 : ℝ)|^8467 ≤ (44259917947631/100000000000000 : ℝ)^6419
        have hw : |(2695278513/5000000000 : ℝ)|=(2695278513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267667167/10000000000 : ℝ)|^8467 ≤ (42933853589147/100000000000000 : ℝ)^6419
        have hw : |(5267667167/10000000000 : ℝ)|=(5267667167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1273_s8_1 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068824353/2000000000 : ℝ)*x 0 + (-433524399/2000000000 : ℝ)*x 1 + (2633833571/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068824353/2000000000 : ℝ)^8467 ≤ (21878852070277/50000000000000 : ℝ)^6419 := by
    have hnat : (1068824353 : ℕ)^8467*50000000000000^6419 ≤ 21878852070277^6419*2000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068824353 2000000000 21878852070277 50000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (433524399/2000000000 : ℝ)^8467 ≤ (1663555315599/12500000000000 : ℝ)^6419 := by
    have hnat : (433524399 : ℕ)^8467*12500000000000^6419 ≤ 1663555315599^6419*2000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433524399 2000000000 1663555315599 12500000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633833571/5000000000 : ℝ)^8467 ≤ (343470826563/800000000000 : ℝ)^6419 := by
    have hnat : (2633833571 : ℕ)^8467*800000000000^6419 ≤ 343470826563^6419*5000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633833571 5000000000 343470826563 800000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068824353/2000000000 : ℝ), (-433524399/2000000000 : ℝ), (2633833571/5000000000 : ℝ)] ![(21878852070277/50000000000000 : ℝ), (1663555315599/12500000000000 : ℝ), (343470826563/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068824353/2000000000 : ℝ)|^8467 ≤ (21878852070277/50000000000000 : ℝ)^6419
        have hw : |(1068824353/2000000000 : ℝ)|=(1068824353/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-433524399/2000000000 : ℝ)|^8467 ≤ (1663555315599/12500000000000 : ℝ)^6419
        have hw : |(-433524399/2000000000 : ℝ)|=(433524399/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633833571/5000000000 : ℝ)|^8467 ≤ (343470826563/800000000000 : ℝ)^6419
        have hw : |(2633833571/5000000000 : ℝ)|=(2633833571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1273_s8_2 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344121763/10000000000 : ℝ)*x 0 + (1316916789/2500000000 : ℝ)*x 1 + (-2167621979/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344121763/10000000000 : ℝ)^8467 ≤ (43757704118953/100000000000000 : ℝ)^6419 := by
    have hnat : (5344121763 : ℕ)^8467*100000000000000^6419 ≤ 43757704118953^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344121763 10000000000 43757704118953 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316916789/2500000000 : ℝ)^8467 ≤ (42933853470887/100000000000000 : ℝ)^6419 := by
    have hnat : (1316916789 : ℕ)^8467*100000000000000^6419 ≤ 42933853470887^6419*2500000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316916789 2500000000 42933853470887 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2167621979/10000000000 : ℝ)^8467 ≤ (831777649701/6250000000000 : ℝ)^6419 := by
    have hnat : (2167621979 : ℕ)^8467*6250000000000^6419 ≤ 831777649701^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2167621979 10000000000 831777649701 6250000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344121763/10000000000 : ℝ), (1316916789/2500000000 : ℝ), (-2167621979/10000000000 : ℝ)] ![(43757704118953/100000000000000 : ℝ), (42933853470887/100000000000000 : ℝ), (831777649701/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344121763/10000000000 : ℝ)|^8467 ≤ (43757704118953/100000000000000 : ℝ)^6419
        have hw : |(5344121763/10000000000 : ℝ)|=(5344121763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316916789/2500000000 : ℝ)|^8467 ≤ (42933853470887/100000000000000 : ℝ)^6419
        have hw : |(1316916789/2500000000 : ℝ)|=(1316916789/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2167621979/10000000000 : ℝ)|^8467 ≤ (831777649701/6250000000000 : ℝ)^6419
        have hw : |(-2167621979/10000000000 : ℝ)|=(2167621979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1273_s8_3 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2173202497/5000000000 : ℝ)*x 0 + (4222735481/10000000000 : ℝ)*x 1 + (4473567429/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2173202497/5000000000 : ℝ)^8467 ≤ (16658834561567/50000000000000 : ℝ)^6419 := by
    have hnat : (2173202497 : ℕ)^8467*50000000000000^6419 ≤ 16658834561567^6419*5000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173202497 5000000000 16658834561567 50000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4222735481/10000000000 : ℝ)^8467 ≤ (801823092541/2500000000000 : ℝ)^6419 := by
    have hnat : (4222735481 : ℕ)^8467*2500000000000^6419 ≤ 801823092541^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4222735481 10000000000 801823092541 2500000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4473567429/10000000000 : ℝ)^8467 ≤ (6921881432829/20000000000000 : ℝ)^6419 := by
    have hnat : (4473567429 : ℕ)^8467*20000000000000^6419 ≤ 6921881432829^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4473567429 10000000000 6921881432829 20000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2173202497/5000000000 : ℝ), (4222735481/10000000000 : ℝ), (4473567429/10000000000 : ℝ)] ![(16658834561567/50000000000000 : ℝ), (801823092541/2500000000000 : ℝ), (6921881432829/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2173202497/5000000000 : ℝ)|^8467 ≤ (16658834561567/50000000000000 : ℝ)^6419
        have hw : |(2173202497/5000000000 : ℝ)|=(2173202497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4222735481/10000000000 : ℝ)|^8467 ≤ (801823092541/2500000000000 : ℝ)^6419
        have hw : |(4222735481/10000000000 : ℝ)|=(4222735481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4473567429/10000000000 : ℝ)|^8467 ≤ (6921881432829/20000000000000 : ℝ)^6419
        have hw : |(4473567429/10000000000 : ℝ)|=(4473567429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1273_s8_4 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-526331121/2500000000 : ℝ)*x 0 + (329248679/625000000 : ℝ)*x 1 + (2695122669/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (526331121/2500000000 : ℝ)^8467 ≤ (800390814227/6250000000000 : ℝ)^6419 := by
    have hnat : (526331121 : ℕ)^8467*6250000000000^6419 ≤ 800390814227^6419*2500000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526331121 2500000000 800390814227 6250000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (329248679/625000000 : ℝ)^8467 ≤ (8587440927123/20000000000000 : ℝ)^6419 := by
    have hnat : (329248679 : ℕ)^8467*20000000000000^6419 ≤ 8587440927123^6419*625000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329248679 625000000 8587440927123 20000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695122669/5000000000 : ℝ)^8467 ≤ (44256542314661/100000000000000 : ℝ)^6419 := by
    have hnat : (2695122669 : ℕ)^8467*100000000000000^6419 ≤ 44256542314661^6419*5000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695122669 5000000000 44256542314661 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-526331121/2500000000 : ℝ), (329248679/625000000 : ℝ), (2695122669/5000000000 : ℝ)] ![(800390814227/6250000000000 : ℝ), (8587440927123/20000000000000 : ℝ), (44256542314661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-526331121/2500000000 : ℝ)|^8467 ≤ (800390814227/6250000000000 : ℝ)^6419
        have hw : |(-526331121/2500000000 : ℝ)|=(526331121/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(329248679/625000000 : ℝ)|^8467 ≤ (8587440927123/20000000000000 : ℝ)^6419
        have hw : |(329248679/625000000 : ℝ)|=(329248679/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695122669/5000000000 : ℝ)|^8467 ≤ (44256542314661/100000000000000 : ℝ)^6419
        have hw : |(2695122669/5000000000 : ℝ)|=(2695122669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1273_s8_5 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4346414727/10000000000 : ℝ)*x 0 + (8945869/20000000 : ℝ)*x 1 + (4223370317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4346414727/10000000000 : ℝ)^8467 ≤ (33317767536363/100000000000000 : ℝ)^6419 := by
    have hnat : (4346414727 : ℕ)^8467*100000000000000^6419 ≤ 33317767536363^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4346414727 10000000000 33317767536363 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8945869/20000000 : ℝ)^8467 ≤ (3460294842791/10000000000000 : ℝ)^6419 := by
    have hnat : (8945869 : ℕ)^8467*10000000000000^6419 ≤ 3460294842791^6419*20000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8945869 20000000 3460294842791 10000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4223370317/10000000000 : ℝ)^8467 ≤ (32079284019489/100000000000000 : ℝ)^6419 := by
    have hnat : (4223370317 : ℕ)^8467*100000000000000^6419 ≤ 32079284019489^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4223370317 10000000000 32079284019489 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4346414727/10000000000 : ℝ), (8945869/20000000 : ℝ), (4223370317/10000000000 : ℝ)] ![(33317767536363/100000000000000 : ℝ), (3460294842791/10000000000000 : ℝ), (32079284019489/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4346414727/10000000000 : ℝ)|^8467 ≤ (33317767536363/100000000000000 : ℝ)^6419
        have hw : |(4346414727/10000000000 : ℝ)|=(4346414727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8945869/20000000 : ℝ)|^8467 ≤ (3460294842791/10000000000000 : ℝ)^6419
        have hw : |(8945869/20000000 : ℝ)|=(8945869/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4223370317/10000000000 : ℝ)|^8467 ≤ (32079284019489/100000000000000 : ℝ)^6419
        have hw : |(4223370317/10000000000 : ℝ)|=(4223370317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1273_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152055603/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14121/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2879/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11517/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14121/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14121/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2879/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14121/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2879/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14121/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2879/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14121/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2879/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14121/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2879/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14121/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2879/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2879/25000 : ℝ) ^ (4233/1024 : ℝ) ≤ (13171009209967217/100000000000000000000 : ℝ) := by
    have hpowers : (2879/25000 : ℝ)^4233 ≤ (13171009209967217/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2879 : ℕ)^4233*100000000000000000000^1024 ≤ 13171009209967217^1024*25000^4233 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2879 25000 13171009209967217 100000000000000000000 4233 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2879/25000 : ℝ)) (X := (13171009209967217/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4233 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14121/100000 : ℝ) ^ (4233/1024 : ℝ) ≤ (6120023696640129/20000000000000000000 : ℝ) := by
    have hpowers : (14121/100000 : ℝ)^4233 ≤ (6120023696640129/20000000000000000000 : ℝ)^1024 := by
      have hnat : (14121 : ℕ)^4233*20000000000000000000^1024 ≤ 6120023696640129^1024*100000^4233 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14121 100000 6120023696640129 20000000000000000000 4233 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14121/100000 : ℝ)) (X := (6120023696640129/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4233 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013171009209967217/50000000000000000000 : ℝ) ≤ (625039823313767/625000000000000 : ℝ) ^ (4233/1024 : ℝ) := by
    have hpowers : (50013171009209967217/50000000000000000000 : ℝ)^1024 ≤ (625039823313767/625000000000000 : ℝ)^4233 := by
      have hnat : (50013171009209967217 : ℕ)^1024*625000000000000^4233 ≤ 625039823313767^4233*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013171009209967217 50000000000000000000 625039823313767 625000000000000 1024 4233 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625039823313767/625000000000000 : ℝ)) (X := (50013171009209967217/50000000000000000000 : ℝ)) (by norm_num) 4233 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50021885563846583931/50000000000000000000 : ℝ) ≤ (1000105868651533/1000000000000000 : ℝ) ^ (4233/1024 : ℝ) := by
    have hpowers : (50021885563846583931/50000000000000000000 : ℝ)^1024 ≤ (1000105868651533/1000000000000000 : ℝ)^4233 := by
      have hnat : (50021885563846583931 : ℕ)^1024*1000000000000000^4233 ≤ 1000105868651533^4233*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021885563846583931 50000000000000000000 1000105868651533 1000000000000000 1024 4233 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000105868651533/1000000000000000 : ℝ)) (X := (50021885563846583931/50000000000000000000 : ℝ)) (by norm_num) 4233 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006120023696640129/10000000000000000000 : ℝ) ≤ (2500370050002597/2500000000000000 : ℝ) ^ (4233/1024 : ℝ) := by
    have hpowers : (10006120023696640129/10000000000000000000 : ℝ)^1024 ≤ (2500370050002597/2500000000000000 : ℝ)^4233 := by
      have hnat : (10006120023696640129 : ℕ)^1024*2500000000000000^4233 ≤ 2500370050002597^4233*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006120023696640129 10000000000000000000 2500370050002597 2500000000000000 1024 4233 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500370050002597/2500000000000000 : ℝ)) (X := (10006120023696640129/10000000000000000000 : ℝ)) (by norm_num) 4233 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13171009209967217/100000000000000000000 : ℝ) ≤ ((406905492764056761/407031250000000000 : ℝ)+2*(210756747529/130250000000000 : ℝ)*(2879/25000 : ℝ))^(4233/1024 : ℝ) := by
    rw [show (406905492764056761/407031250000000000 : ℝ)+2*(210756747529/130250000000000 : ℝ)*(2879/25000 : ℝ)=(625039823313767/625000000000000 : ℝ) by norm_num, show 1+2*(13171009209967217/100000000000000000000 : ℝ)=(50013171009209967217/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6120023696640129/20000000000000000000 : ℝ)+(13171009209967217/100000000000000000000 : ℝ) ≤ ((406905492764056761/407031250000000000 : ℝ)+(210756747529/130250000000000 : ℝ)*((14121/100000 : ℝ)+(2879/25000 : ℝ)))^(4233/1024 : ℝ) := by
    rw [show (406905492764056761/407031250000000000 : ℝ)+(210756747529/130250000000000 : ℝ)*((14121/100000 : ℝ)+(2879/25000 : ℝ))=(1000105868651533/1000000000000000 : ℝ) by norm_num, show 1+(6120023696640129/20000000000000000000 : ℝ)+(13171009209967217/100000000000000000000 : ℝ)=(50021885563846583931/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6120023696640129/20000000000000000000 : ℝ) ≤ ((406905492764056761/407031250000000000 : ℝ)+2*(210756747529/130250000000000 : ℝ)*(14121/100000 : ℝ))^(4233/1024 : ℝ) := by
    rw [show (406905492764056761/407031250000000000 : ℝ)+2*(210756747529/130250000000000 : ℝ)*(14121/100000 : ℝ)=(2500370050002597/2500000000000000 : ℝ) by norm_num, show 1+2*(6120023696640129/20000000000000000000 : ℝ)=(10006120023696640129/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (406905492764056761/407031250000000000 : ℝ)*(X 1 0+X 2 0)+(210756747529/130250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4233/1024 : ℝ)) (lo := (2879/25000 : ℝ)) (hi := (14121/100000 : ℝ)) (c := (406905492764056761/407031250000000000 : ℝ)) (alpha := (210756747529/130250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (406905492764056761/407031250000000000 : ℝ)*(X 0 1+X 2 1)+(210756747529/130250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4233/1024 : ℝ)) (lo := (2879/25000 : ℝ)) (hi := (14121/100000 : ℝ)) (c := (406905492764056761/407031250000000000 : ℝ)) (alpha := (210756747529/130250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (406905492764056761/407031250000000000 : ℝ)*(X 0 2+X 1 2)+(210756747529/130250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4233/1024 : ℝ)) (lo := (2879/25000 : ℝ)) (hi := (14121/100000 : ℝ)) (c := (406905492764056761/407031250000000000 : ℝ)) (alpha := (210756747529/130250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2105321421/10000000000 : ℝ)*X 0 0+(2695278513/5000000000 : ℝ)*X 0 1+(5267667167/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1068824353/2000000000 : ℝ)*X 1 0+(-433524399/2000000000 : ℝ)*X 1 1+(2633833571/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344121763/10000000000 : ℝ)*X 2 0+(1316916789/2500000000 : ℝ)*X 2 1+(-2167621979/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2173202497/5000000000 : ℝ)*X 0 0+(4222735481/10000000000 : ℝ)*X 0 1+(4473567429/10000000000 : ℝ)*X 0 2+(2173202497/5000000000 : ℝ)*X 1 0+(4222735481/10000000000 : ℝ)*X 1 1+(4473567429/10000000000 : ℝ)*X 1 2+(2173202497/5000000000 : ℝ)*X 2 0+(4222735481/10000000000 : ℝ)*X 2 1+(4473567429/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-526331121/2500000000 : ℝ)*X 0 0+(329248679/625000000 : ℝ)*X 0 1+(2695122669/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4346414727/10000000000 : ℝ)*X 0 0+(8945869/20000000 : ℝ)*X 0 1+(4223370317/10000000000 : ℝ)*X 0 2+(4346414727/10000000000 : ℝ)*X 1 0+(8945869/20000000 : ℝ)*X 1 1+(4223370317/10000000000 : ℝ)*X 1 2+(4346414727/10000000000 : ℝ)*X 2 0+(8945869/20000000 : ℝ)*X 2 1+(4223370317/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s8_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (136006617745576462197259857/20351562500000000000000000000000 : ℝ) := by norm_num
    linear_combination (30226837/2500000000000 : ℝ)*(base19) + (1119225927/100000000000000 : ℝ)*(base23) + (46388141/100000000000000 : ℝ)*(lower2) + (5413367/4000000000000 : ℝ)*(upper3) + (48896467/50000000000000 : ℝ)*(upper5) + (6062101316412773/100000000000000 : ℝ)*(major0) + (6062101316412773/100000000000000 : ℝ)*(major1) + (6062101316412773/100000000000000 : ℝ)*(major2) + (8137402277576341/100000000000000 : ℝ)*(sp0) + (508589690406129/6250000000000 : ℝ)*(sp1) + (8137435136345617/100000000000000 : ℝ)*(sp2) + (3986748904943107/100000000000000 : ℝ)*(sp3) + (33977995203/100000000000000 : ℝ)*(sp4) + (17249548927/100000000000000 : ℝ)*(sp5) + (1993383077246017/50000000000000 : ℝ)*(f.failure) + (1017179531946443/12500000000000 : ℝ)*(f.sum) + (8207897615377/1628125000000000000000000000 : ℝ)*base66 + (683524850343945753/40703125000000000000000000000000 : ℝ)*base67 + (432561629245664503/40703125000000000000000000000000 : ℝ)*base69 + (179679143910897997/40703125000000000000000000000000 : ℝ)*base72 + (28243554762659/13025000000000000000000000000 : ℝ)*base73 + (163897547202685657/10175781250000000000000000000000 : ℝ)*base75 + (125559149539248157/10175781250000000000000000000000 : ℝ)*base77 + (650590161213164503/40703125000000000000000000000000 : ℝ)*base79 + (10340660585859/13025000000000000000000000000 : ℝ)*base81 + (44283251/5000000000000000000000 : ℝ)*base89 + (44283251/5000000000000000000000 : ℝ)*base91 + (44283251/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1273_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152055603/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14121/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2879/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11517/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14121/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1273_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1273_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152055603/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (442/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2299/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11517/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14121/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1273_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1273_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1273_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152055603/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (442/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2299/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11517/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14121/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1273_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
