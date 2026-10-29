-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1379_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:22:48.990431+00:00
-- url     : https://prove2.me/submissions/1fd54ffc-e277-4ca1-8343-fc34a75c842f

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
theorem support_rectangle_w1379_s0_0 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1787473503/10000000000 : ℝ)*x 0 + (5981089303/10000000000 : ℝ)*x 1 + (4819659823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1787473503/10000000000 : ℝ)^4339 ≤ (2625410556583/25000000000000 : ℝ)^3315 := by
    have hnat : (1787473503 : ℕ)^4339*25000000000000^3315 ≤ 2625410556583^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1787473503 10000000000 2625410556583 25000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5981089303/10000000000 : ℝ)^4339 ≤ (79734812843/156250000000 : ℝ)^3315 := by
    have hnat : (5981089303 : ℕ)^4339*156250000000^3315 ≤ 79734812843^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5981089303 10000000000 79734812843 156250000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4819659823/10000000000 : ℝ)^4339 ≤ (19234038768131/50000000000000 : ℝ)^3315 := by
    have hnat : (4819659823 : ℕ)^4339*50000000000000^3315 ≤ 19234038768131^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4819659823 10000000000 19234038768131 50000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1787473503/10000000000 : ℝ), (5981089303/10000000000 : ℝ), (4819659823/10000000000 : ℝ)] ![(2625410556583/25000000000000 : ℝ), (79734812843/156250000000 : ℝ), (19234038768131/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1787473503/10000000000 : ℝ)|^4339 ≤ (2625410556583/25000000000000 : ℝ)^3315
        have hw : |(-1787473503/10000000000 : ℝ)|=(1787473503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5981089303/10000000000 : ℝ)|^4339 ≤ (79734812843/156250000000 : ℝ)^3315
        have hw : |(5981089303/10000000000 : ℝ)|=(5981089303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4819659823/10000000000 : ℝ)|^4339 ≤ (19234038768131/50000000000000 : ℝ)^3315
        have hw : |(4819659823/10000000000 : ℝ)|=(4819659823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_s0_1 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5497674017/10000000000 : ℝ)*x 0 + (-1222934639/5000000000 : ℝ)*x 1 + (2409830239/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5497674017/10000000000 : ℝ)^4339 ≤ (45700457491349/100000000000000 : ℝ)^3315 := by
    have hnat : (5497674017 : ℕ)^4339*100000000000000^3315 ≤ 45700457491349^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5497674017 10000000000 45700457491349 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1222934639/5000000000 : ℝ)^4339 ≤ (7915729055609/50000000000000 : ℝ)^3315 := by
    have hnat : (1222934639 : ℕ)^4339*50000000000000^3315 ≤ 7915729055609^3315*5000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1222934639 5000000000 7915729055609 50000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2409830239/5000000000 : ℝ)^4339 ≤ (19234042189513/50000000000000 : ℝ)^3315 := by
    have hnat : (2409830239 : ℕ)^4339*50000000000000^3315 ≤ 19234042189513^3315*5000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2409830239 5000000000 19234042189513 50000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5497674017/10000000000 : ℝ), (-1222934639/5000000000 : ℝ), (2409830239/5000000000 : ℝ)] ![(45700457491349/100000000000000 : ℝ), (7915729055609/50000000000000 : ℝ), (19234042189513/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5497674017/10000000000 : ℝ)|^4339 ≤ (45700457491349/100000000000000 : ℝ)^3315
        have hw : |(5497674017/10000000000 : ℝ)|=(5497674017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1222934639/5000000000 : ℝ)|^4339 ≤ (7915729055609/50000000000000 : ℝ)^3315
        have hw : |(-1222934639/5000000000 : ℝ)|=(1222934639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2409830239/5000000000 : ℝ)|^4339 ≤ (19234042189513/50000000000000 : ℝ)^3315
        have hw : |(2409830239/5000000000 : ℝ)|=(2409830239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_s0_2 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (549767389/1000000000 : ℝ)*x 0 + (4819659723/10000000000 : ℝ)*x 1 + (-2445870373/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (549767389/1000000000 : ℝ)^4339 ≤ (45700456109529/100000000000000 : ℝ)^3315 := by
    have hnat : (549767389 : ℕ)^4339*100000000000000^3315 ≤ 45700456109529^3315*1000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549767389 1000000000 45700456109529 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4819659723/10000000000 : ℝ)^4339 ≤ (19234038245783/50000000000000 : ℝ)^3315 := by
    have hnat : (4819659723 : ℕ)^4339*50000000000000^3315 ≤ 19234038245783^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4819659723 10000000000 19234038245783 50000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2445870373/10000000000 : ℝ)^4339 ≤ (7915733694113/50000000000000 : ℝ)^3315 := by
    have hnat : (2445870373 : ℕ)^4339*50000000000000^3315 ≤ 7915733694113^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2445870373 10000000000 7915733694113 50000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(549767389/1000000000 : ℝ), (4819659723/10000000000 : ℝ), (-2445870373/10000000000 : ℝ)] ![(45700456109529/100000000000000 : ℝ), (19234038245783/50000000000000 : ℝ), (7915733694113/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(549767389/1000000000 : ℝ)|^4339 ≤ (45700456109529/100000000000000 : ℝ)^3315
        have hw : |(549767389/1000000000 : ℝ)|=(549767389/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4819659723/10000000000 : ℝ)|^4339 ≤ (19234038245783/50000000000000 : ℝ)^3315
        have hw : |(4819659723/10000000000 : ℝ)|=(4819659723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2445870373/10000000000 : ℝ)|^4339 ≤ (7915733694113/50000000000000 : ℝ)^3315
        have hw : |(-2445870373/10000000000 : ℝ)|=(2445870373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_s0_3 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4173260201/10000000000 : ℝ)*x 0 + (3104934219/10000000000 : ℝ)*x 1 + (5571539963/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4173260201/10000000000 : ℝ)^4339 ≤ (31859630529127/100000000000000 : ℝ)^3315 := by
    have hnat : (4173260201 : ℕ)^4339*100000000000000^3315 ≤ 31859630529127^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4173260201 10000000000 31859630529127 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3104934219/10000000000 : ℝ)^4339 ≤ (10817276523783/50000000000000 : ℝ)^3315 := by
    have hnat : (3104934219 : ℕ)^4339*50000000000000^3315 ≤ 10817276523783^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3104934219 10000000000 10817276523783 50000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5571539963/10000000000 : ℝ)^4339 ≤ (46505816411563/100000000000000 : ℝ)^3315 := by
    have hnat : (5571539963 : ℕ)^4339*100000000000000^3315 ≤ 46505816411563^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5571539963 10000000000 46505816411563 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4173260201/10000000000 : ℝ), (3104934219/10000000000 : ℝ), (5571539963/10000000000 : ℝ)] ![(31859630529127/100000000000000 : ℝ), (10817276523783/50000000000000 : ℝ), (46505816411563/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4173260201/10000000000 : ℝ)|^4339 ≤ (31859630529127/100000000000000 : ℝ)^3315
        have hw : |(4173260201/10000000000 : ℝ)|=(4173260201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3104934219/10000000000 : ℝ)|^4339 ≤ (10817276523783/50000000000000 : ℝ)^3315
        have hw : |(3104934219/10000000000 : ℝ)|=(3104934219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5571539963/10000000000 : ℝ)|^4339 ≤ (46505816411563/100000000000000 : ℝ)^3315
        have hw : |(5571539963/10000000000 : ℝ)|=(5571539963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_s0_4 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1791739873/10000000000 : ℝ)*x 0 + (4849482497/10000000000 : ℝ)*x 1 + (5950200447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1791739873/10000000000 : ℝ)^4339 ≤ (10534462501813/100000000000000 : ℝ)^3315 := by
    have hnat : (1791739873 : ℕ)^4339*100000000000000^3315 ≤ 10534462501813^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1791739873 10000000000 10534462501813 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4849482497/10000000000 : ℝ)^4339 ≤ (7755986269741/20000000000000 : ℝ)^3315 := by
    have hnat : (4849482497 : ℕ)^4339*20000000000000^3315 ≤ 7755986269741^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4849482497 10000000000 7755986269741 20000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5950200447/10000000000 : ℝ)^4339 ≤ (50685606123949/100000000000000 : ℝ)^3315 := by
    have hnat : (5950200447 : ℕ)^4339*100000000000000^3315 ≤ 50685606123949^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5950200447 10000000000 50685606123949 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1791739873/10000000000 : ℝ), (4849482497/10000000000 : ℝ), (5950200447/10000000000 : ℝ)] ![(10534462501813/100000000000000 : ℝ), (7755986269741/20000000000000 : ℝ), (50685606123949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1791739873/10000000000 : ℝ)|^4339 ≤ (10534462501813/100000000000000 : ℝ)^3315
        have hw : |(-1791739873/10000000000 : ℝ)|=(1791739873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4849482497/10000000000 : ℝ)|^4339 ≤ (7755986269741/20000000000000 : ℝ)^3315
        have hw : |(4849482497/10000000000 : ℝ)|=(4849482497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5950200447/10000000000 : ℝ)|^4339 ≤ (50685606123949/100000000000000 : ℝ)^3315
        have hw : |(5950200447/10000000000 : ℝ)|=(5950200447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_s0_5 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5180928761/10000000000 : ℝ)*x 0 + (-164416477/1250000000 : ℝ)*x 1 + (743774869/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5180928761/10000000000 : ℝ)^4339 ≤ (42285204593749/100000000000000 : ℝ)^3315 := by
    have hnat : (5180928761 : ℕ)^4339*100000000000000^3315 ≤ 42285204593749^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180928761 10000000000 42285204593749 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (164416477/1250000000 : ℝ)^4339 ≤ (3514602969443/50000000000000 : ℝ)^3315 := by
    have hnat : (164416477 : ℕ)^4339*50000000000000^3315 ≤ 3514602969443^3315*1250000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164416477 1250000000 3514602969443 50000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (743774869/1250000000 : ℝ)^4339 ≤ (25342794727651/50000000000000 : ℝ)^3315 := by
    have hnat : (743774869 : ℕ)^4339*50000000000000^3315 ≤ 25342794727651^3315*1250000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      743774869 1250000000 25342794727651 50000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5180928761/10000000000 : ℝ), (-164416477/1250000000 : ℝ), (743774869/1250000000 : ℝ)] ![(42285204593749/100000000000000 : ℝ), (3514602969443/50000000000000 : ℝ), (25342794727651/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5180928761/10000000000 : ℝ)|^4339 ≤ (42285204593749/100000000000000 : ℝ)^3315
        have hw : |(5180928761/10000000000 : ℝ)|=(5180928761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-164416477/1250000000 : ℝ)|^4339 ≤ (3514602969443/50000000000000 : ℝ)^3315
        have hw : |(-164416477/1250000000 : ℝ)|=(164416477/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(743774869/1250000000 : ℝ)|^4339 ≤ (25342794727651/50000000000000 : ℝ)^3315
        have hw : |(743774869/1250000000 : ℝ)|=(743774869/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_s0_6 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (647615853/1250000000 : ℝ)*x 0 + (5950202419/10000000000 : ℝ)*x 1 + (-1315329249/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (647615853/1250000000 : ℝ)^4339 ≤ (42285183901079/100000000000000 : ℝ)^3315 := by
    have hnat : (647615853 : ℕ)^4339*100000000000000^3315 ≤ 42285183901079^3315*1250000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647615853 1250000000 42285183901079 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5950202419/10000000000 : ℝ)^4339 ≤ (10137125622191/20000000000000 : ℝ)^3315 := by
    have hnat : (5950202419 : ℕ)^4339*20000000000000^3315 ≤ 10137125622191^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5950202419 10000000000 10137125622191 20000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1315329249/10000000000 : ℝ)^4339 ≤ (109831062237/1562500000000 : ℝ)^3315 := by
    have hnat : (1315329249 : ℕ)^4339*1562500000000^3315 ≤ 109831062237^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315329249 10000000000 109831062237 1562500000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(647615853/1250000000 : ℝ), (5950202419/10000000000 : ℝ), (-1315329249/10000000000 : ℝ)] ![(42285183901079/100000000000000 : ℝ), (10137125622191/20000000000000 : ℝ), (109831062237/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(647615853/1250000000 : ℝ)|^4339 ≤ (42285183901079/100000000000000 : ℝ)^3315
        have hw : |(647615853/1250000000 : ℝ)|=(647615853/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5950202419/10000000000 : ℝ)|^4339 ≤ (10137125622191/20000000000000 : ℝ)^3315
        have hw : |(5950202419/10000000000 : ℝ)|=(5950202419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1315329249/10000000000 : ℝ)|^4339 ≤ (109831062237/1562500000000 : ℝ)^3315
        have hw : |(-1315329249/10000000000 : ℝ)|=(1315329249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_s0_7 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (836462221/2000000000 : ℝ)*x 0 + (688525861/1250000000 : ℝ)*x 1 + (792634299/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (836462221/2000000000 : ℝ)^4339 ≤ (15975050695221/50000000000000 : ℝ)^3315 := by
    have hnat : (836462221 : ℕ)^4339*50000000000000^3315 ≤ 15975050695221^3315*2000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      836462221 2000000000 15975050695221 50000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (688525861/1250000000 : ℝ)^4339 ≤ (22907546990683/50000000000000 : ℝ)^3315 := by
    have hnat : (688525861 : ℕ)^4339*50000000000000^3315 ≤ 22907546990683^3315*1250000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      688525861 1250000000 22907546990683 50000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (792634299/2500000000 : ℝ)^4339 ≤ (2779350576641/12500000000000 : ℝ)^3315 := by
    have hnat : (792634299 : ℕ)^4339*12500000000000^3315 ≤ 2779350576641^3315*2500000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      792634299 2500000000 2779350576641 12500000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(836462221/2000000000 : ℝ), (688525861/1250000000 : ℝ), (792634299/2500000000 : ℝ)] ![(15975050695221/50000000000000 : ℝ), (22907546990683/50000000000000 : ℝ), (2779350576641/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(836462221/2000000000 : ℝ)|^4339 ≤ (15975050695221/50000000000000 : ℝ)^3315
        have hw : |(836462221/2000000000 : ℝ)|=(836462221/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(688525861/1250000000 : ℝ)|^4339 ≤ (22907546990683/50000000000000 : ℝ)^3315
        have hw : |(688525861/1250000000 : ℝ)|=(688525861/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(792634299/2500000000 : ℝ)|^4339 ≤ (2779350576641/12500000000000 : ℝ)^3315
        have hw : |(792634299/2500000000 : ℝ)|=(792634299/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1379_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156188383/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (211/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (26607/100000 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (2169/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2169 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2169*1^512 ≤ 0^512*1^2169 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2169 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2169 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2169/512 : ℝ) ≤ (257694744910650377/12500000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2169 ≤ (257694744910650377/12500000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2169*12500000000000000000^512 ≤ 257694744910650377^512*5^2169 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 257694744910650377 12500000000000000000 2169 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (257694744910650377/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2169 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2169/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2169 := by
      have hnat : (1 : ℕ)^512*1^2169 ≤ 1^2169*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2169 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2169 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (12757694744910650377/12500000000000000000 : ℝ) ≤ (2009657033049631/2000000000000000 : ℝ) ^ (2169/512 : ℝ) := by
    have hpowers : (12757694744910650377/12500000000000000000 : ℝ)^512 ≤ (2009657033049631/2000000000000000 : ℝ)^2169 := by
      have hnat : (12757694744910650377 : ℕ)^512*2000000000000000^2169 ≤ 2009657033049631^2169*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12757694744910650377 12500000000000000000 2009657033049631 2000000000000000 512 2169 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2009657033049631/2000000000000000 : ℝ)) (X := (12757694744910650377/12500000000000000000 : ℝ)) (by norm_num) 2169 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (6507694744910650377/6250000000000000000 : ℝ) ≤ (1009657033049631/1000000000000000 : ℝ) ^ (2169/512 : ℝ) := by
    have hpowers : (6507694744910650377/6250000000000000000 : ℝ)^512 ≤ (1009657033049631/1000000000000000 : ℝ)^2169 := by
      have hnat : (6507694744910650377 : ℕ)^512*1000000000000000^2169 ≤ 1009657033049631^2169*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6507694744910650377 6250000000000000000 1009657033049631 1000000000000000 512 2169 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1009657033049631/1000000000000000 : ℝ)) (X := (6507694744910650377/6250000000000000000 : ℝ)) (by norm_num) 2169 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(9657033049631/800000000000000 : ℝ)*(0 : ℝ))^(2169/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(9657033049631/800000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(257694744910650377/12500000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(9657033049631/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2169/512 : ℝ) := by
    rw [show (1 : ℝ)+(9657033049631/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2009657033049631/2000000000000000 : ℝ) by norm_num, show 1+(257694744910650377/12500000000000000000 : ℝ)+(0 : ℝ)=(12757694744910650377/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(257694744910650377/12500000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(9657033049631/800000000000000 : ℝ)*(2/5 : ℝ))^(2169/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(9657033049631/800000000000000 : ℝ)*(2/5 : ℝ)=(1009657033049631/1000000000000000 : ℝ) by norm_num, show 1+2*(257694744910650377/12500000000000000000 : ℝ)=(6507694744910650377/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(9657033049631/800000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2169/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (9657033049631/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(9657033049631/800000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2169/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (9657033049631/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(9657033049631/800000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2169/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (9657033049631/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1787473503/10000000000 : ℝ)*X 0 0+(5981089303/10000000000 : ℝ)*X 0 1+(4819659823/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5497674017/10000000000 : ℝ)*X 1 0+(-1222934639/5000000000 : ℝ)*X 1 1+(2409830239/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((549767389/1000000000 : ℝ)*X 2 0+(4819659723/10000000000 : ℝ)*X 2 1+(-2445870373/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4173260201/10000000000 : ℝ)*X 0 0+(3104934219/10000000000 : ℝ)*X 0 1+(5571539963/10000000000 : ℝ)*X 0 2+(4173260201/10000000000 : ℝ)*X 1 0+(3104934219/10000000000 : ℝ)*X 1 1+(5571539963/10000000000 : ℝ)*X 1 2+(4173260201/10000000000 : ℝ)*X 2 0+(3104934219/10000000000 : ℝ)*X 2 1+(5571539963/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1791739873/10000000000 : ℝ)*X 0 0+(4849482497/10000000000 : ℝ)*X 0 1+(5950200447/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5180928761/10000000000 : ℝ)*X 1 0+(-164416477/1250000000 : ℝ)*X 1 1+(743774869/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((647615853/1250000000 : ℝ)*X 2 0+(5950202419/10000000000 : ℝ)*X 2 1+(-1315329249/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((836462221/2000000000 : ℝ)*X 0 0+(688525861/1250000000 : ℝ)*X 0 1+(792634299/2500000000 : ℝ)*X 0 2+(836462221/2000000000 : ℝ)*X 1 0+(688525861/1250000000 : ℝ)*X 1 1+(792634299/2500000000 : ℝ)*X 1 2+(836462221/2000000000 : ℝ)*X 2 0+(688525861/1250000000 : ℝ)*X 2 1+(792634299/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (145434200305163460976431/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (256514237/100000000000000 : ℝ)*(base1) + (846527563/50000000000000 : ℝ)*(base19) + (1673165061/100000000000000 : ℝ)*(base23) + (311747859/100000000000000 : ℝ)*(upper3) + (10493413/50000000000000 : ℝ)*(upper5) + (633219290774267/100000000000000 : ℝ)*(major0) + (633219290774267/100000000000000 : ℝ)*(major1) + (633219290774267/100000000000000 : ℝ)*(major2) + (430506983469359/50000000000000 : ℝ)*(sp0) + (430508211514537/50000000000000 : ℝ)*(sp1) + (430508221459569/50000000000000 : ℝ)*(sp2) + (50677154082761/12500000000000 : ℝ)*(sp3) + (4405659719/100000000000000 : ℝ)*(sp4) + (2733897671/100000000000000 : ℝ)*(sp7) + (101355055768499/25000000000000 : ℝ)*(f.failure) + (4305090580421/500000000000 : ℝ)*(f.sum) + (66883023434523/40000000000000000000000000000 : ℝ)*base66 + (593355292714523/80000000000000000000000000000 : ℝ)*base68 + (366453063285477/80000000000000000000000000000 : ℝ)*base69 + (125751083434523/80000000000000000000000000000 : ℝ)*base72 + (208896113274523/40000000000000000000000000000 : ℝ)*base74 + (292052221914523/80000000000000000000000000000 : ℝ)*base76 + (109634008394523/80000000000000000000000000000 : ℝ)*base78 + (122668157125477/80000000000000000000000000000 : ℝ)*base79 + (84134437205477/40000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (6147117/2500000000000000000000 : ℝ)*base89 + (6147117/2500000000000000000000 : ℝ)*base91 + (6147117/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7677915672881008018371/1600000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9024109/2500000000000 : ℝ)*(base19) + (729978343/100000000000000 : ℝ)*(base23) + (19065289/100000000000000 : ℝ)*(base39) + (137558823/50000000000000 : ℝ)*(upper2) + (15622917/25000000000000 : ℝ)*(upper5) + (26725462949451/4000000000000 : ℝ)*(major0) + (26725462949451/4000000000000 : ℝ)*(major1) + (334068277335493/50000000000000 : ℝ)*(major2) + (91665189/100000000000000 : ℝ)*(sp1) + (2692924047/100000000000000 : ℝ)*(sp2) + (90849686826769/10000000000000 : ℝ)*(sp4) + (908496415638141/100000000000000 : ℝ)*(sp5) + (908493464430589/100000000000000 : ℝ)*(sp6) + (26736006261437/6250000000000 : ℝ)*(sp7) + (26736006261437/6250000000000 : ℝ)*(f.failure) + (908496887332979/100000000000000 : ℝ)*(f.sum) + (219502770570691/80000000000000000000000000000 : ℝ)*base65 + (167774126186917/40000000000000000000000000000 : ℝ)*base68 + (14862598044181/3200000000000000000000000000 : ℝ)*base69 + (43528959893083/40000000000000000000000000000 : ℝ)*base71 + (324030710069309/80000000000000000000000000000 : ℝ)*base74 + (6966690383381/3200000000000000000000000000 : ℝ)*base75 + (3154596559381/3200000000000000000000000000 : ℝ)*base77 + (7028758664981/3200000000000000000000000000 : ℝ)*base79 + (444106018581/1600000000000000000000000000 : ℝ)*base81 + (1536371/625000000000000000000 : ℝ)*base89 + (1536371/625000000000000000000 : ℝ)*base91 + (1536371/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1379_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156188383/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (211/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (26607/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1379_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1379_s1_0 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-983483373/5000000000 : ℝ)*x 0 + (2812961479/5000000000 : ℝ)*x 1 + (158119813/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (983483373/5000000000 : ℝ)^4339 ≤ (11902869224473/100000000000000 : ℝ)^3315 := by
    have hnat : (983483373 : ℕ)^4339*100000000000000^3315 ≤ 11902869224473^3315*5000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      983483373 5000000000 11902869224473 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2812961479/5000000000 : ℝ)^4339 ≤ (23550433596173/50000000000000 : ℝ)^3315 := by
    have hnat : (2812961479 : ℕ)^4339*50000000000000^3315 ≤ 23550433596173^3315*5000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2812961479 5000000000 23550433596173 50000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (158119813/312500000 : ℝ)^4339 ≤ (40996263576281/100000000000000 : ℝ)^3315 := by
    have hnat : (158119813 : ℕ)^4339*100000000000000^3315 ≤ 40996263576281^3315*312500000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      158119813 312500000 40996263576281 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-983483373/5000000000 : ℝ), (2812961479/5000000000 : ℝ), (158119813/312500000 : ℝ)] ![(11902869224473/100000000000000 : ℝ), (23550433596173/50000000000000 : ℝ), (40996263576281/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-983483373/5000000000 : ℝ)|^4339 ≤ (11902869224473/100000000000000 : ℝ)^3315
        have hw : |(-983483373/5000000000 : ℝ)|=(983483373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2812961479/5000000000 : ℝ)|^4339 ≤ (23550433596173/50000000000000 : ℝ)^3315
        have hw : |(2812961479/5000000000 : ℝ)|=(2812961479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(158119813/312500000 : ℝ)|^4339 ≤ (40996263576281/100000000000000 : ℝ)^3315
        have hw : |(158119813/312500000 : ℝ)|=(158119813/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_s1_1 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1080377093/2000000000 : ℝ)*x 0 + (-1134056277/5000000000 : ℝ)*x 1 + (2529917717/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1080377093/2000000000 : ℝ)^4339 ≤ (22330524490707/50000000000000 : ℝ)^3315 := by
    have hnat : (1080377093 : ℕ)^4339*50000000000000^3315 ≤ 22330524490707^3315*2000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080377093 2000000000 22330524490707 50000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1134056277/5000000000 : ℝ)^4339 ≤ (3585668096301/25000000000000 : ℝ)^3315 := by
    have hnat : (1134056277 : ℕ)^4339*25000000000000^3315 ≤ 3585668096301^3315*5000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1134056277 5000000000 3585668096301 25000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2529917717/5000000000 : ℝ)^4339 ≤ (40996278614291/100000000000000 : ℝ)^3315 := by
    have hnat : (2529917717 : ℕ)^4339*100000000000000^3315 ≤ 40996278614291^3315*5000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2529917717 5000000000 40996278614291 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1080377093/2000000000 : ℝ), (-1134056277/5000000000 : ℝ), (2529917717/5000000000 : ℝ)] ![(22330524490707/50000000000000 : ℝ), (3585668096301/25000000000000 : ℝ), (40996278614291/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1080377093/2000000000 : ℝ)|^4339 ≤ (22330524490707/50000000000000 : ℝ)^3315
        have hw : |(1080377093/2000000000 : ℝ)|=(1080377093/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1134056277/5000000000 : ℝ)|^4339 ≤ (3585668096301/25000000000000 : ℝ)^3315
        have hw : |(-1134056277/5000000000 : ℝ)|=(1134056277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2529917717/5000000000 : ℝ)|^4339 ≤ (40996278614291/100000000000000 : ℝ)^3315
        have hw : |(2529917717/5000000000 : ℝ)|=(2529917717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_s1_2 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2700943057/5000000000 : ℝ)*x 0 + (5059834203/10000000000 : ℝ)*x 1 + (-1134056641/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2700943057/5000000000 : ℝ)^4339 ≤ (44661056004603/100000000000000 : ℝ)^3315 := by
    have hnat : (2700943057 : ℕ)^4339*100000000000000^3315 ≤ 44661056004603^3315*5000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700943057 5000000000 44661056004603 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5059834203/10000000000 : ℝ)^4339 ≤ (40996265559431/100000000000000 : ℝ)^3315 := by
    have hnat : (5059834203 : ℕ)^4339*100000000000000^3315 ≤ 40996265559431^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5059834203 10000000000 40996265559431 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1134056641/5000000000 : ℝ)^4339 ≤ (7171339205421/50000000000000 : ℝ)^3315 := by
    have hnat : (1134056641 : ℕ)^4339*50000000000000^3315 ≤ 7171339205421^3315*5000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1134056641 5000000000 7171339205421 50000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2700943057/5000000000 : ℝ), (5059834203/10000000000 : ℝ), (-1134056641/5000000000 : ℝ)] ![(44661056004603/100000000000000 : ℝ), (40996265559431/100000000000000 : ℝ), (7171339205421/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2700943057/5000000000 : ℝ)|^4339 ≤ (44661056004603/100000000000000 : ℝ)^3315
        have hw : |(2700943057/5000000000 : ℝ)|=(2700943057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5059834203/10000000000 : ℝ)|^4339 ≤ (40996265559431/100000000000000 : ℝ)^3315
        have hw : |(5059834203/10000000000 : ℝ)|=(5059834203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1134056641/5000000000 : ℝ)|^4339 ≤ (7171339205421/50000000000000 : ℝ)^3315
        have hw : |(-1134056641/5000000000 : ℝ)|=(1134056641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_s1_3 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2142841457/5000000000 : ℝ)*x 0 + (1861505941/5000000000 : ℝ)*x 1 + (2462624169/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2142841457/5000000000 : ℝ)^4339 ≤ (1030864145847/3125000000000 : ℝ)^3315 := by
    have hnat : (2142841457 : ℕ)^4339*3125000000000^3315 ≤ 1030864145847^3315*5000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2142841457 5000000000 1030864145847 3125000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1861505941/5000000000 : ℝ)^4339 ≤ (6859369073647/25000000000000 : ℝ)^3315 := by
    have hnat : (1861505941 : ℕ)^4339*25000000000000^3315 ≤ 6859369073647^3315*5000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1861505941 5000000000 6859369073647 25000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2462624169/5000000000 : ℝ)^4339 ≤ (19787435513563/50000000000000 : ℝ)^3315 := by
    have hnat : (2462624169 : ℕ)^4339*50000000000000^3315 ≤ 19787435513563^3315*5000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2462624169 5000000000 19787435513563 50000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2142841457/5000000000 : ℝ), (1861505941/5000000000 : ℝ), (2462624169/5000000000 : ℝ)] ![(1030864145847/3125000000000 : ℝ), (6859369073647/25000000000000 : ℝ), (19787435513563/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2142841457/5000000000 : ℝ)|^4339 ≤ (1030864145847/3125000000000 : ℝ)^3315
        have hw : |(2142841457/5000000000 : ℝ)|=(2142841457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1861505941/5000000000 : ℝ)|^4339 ≤ (6859369073647/25000000000000 : ℝ)^3315
        have hw : |(1861505941/5000000000 : ℝ)|=(1861505941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2462624169/5000000000 : ℝ)|^4339 ≤ (19787435513563/50000000000000 : ℝ)^3315
        have hw : |(2462624169/5000000000 : ℝ)|=(2462624169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_s1_4 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1967439479/10000000000 : ℝ)*x 0 + (1266684311/2500000000 : ℝ)*x 1 + (5618897741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1967439479/10000000000 : ℝ)^4339 ≤ (11906613715563/100000000000000 : ℝ)^3315 := by
    have hnat : (1967439479 : ℕ)^4339*100000000000000^3315 ≤ 11906613715563^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1967439479 10000000000 11906613715563 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1266684311/2500000000 : ℝ)^4339 ≤ (10267372078157/25000000000000 : ℝ)^3315 := by
    have hnat : (1266684311 : ℕ)^4339*25000000000000^3315 ≤ 10267372078157^3315*2500000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1266684311 2500000000 10267372078157 25000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5618897741/10000000000 : ℝ)^4339 ≤ (23511948976791/50000000000000 : ℝ)^3315 := by
    have hnat : (5618897741 : ℕ)^4339*50000000000000^3315 ≤ 23511948976791^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5618897741 10000000000 23511948976791 50000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1967439479/10000000000 : ℝ), (1266684311/2500000000 : ℝ), (5618897741/10000000000 : ℝ)] ![(11906613715563/100000000000000 : ℝ), (10267372078157/25000000000000 : ℝ), (23511948976791/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1967439479/10000000000 : ℝ)|^4339 ≤ (11906613715563/100000000000000 : ℝ)^3315
        have hw : |(-1967439479/10000000000 : ℝ)|=(1967439479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1266684311/2500000000 : ℝ)|^4339 ≤ (10267372078157/25000000000000 : ℝ)^3315
        have hw : |(1266684311/2500000000 : ℝ)|=(1266684311/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5618897741/10000000000 : ℝ)|^4339 ≤ (23511948976791/50000000000000 : ℝ)^3315
        have hw : |(5618897741/10000000000 : ℝ)|=(5618897741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_s1_5 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1050909883/2000000000 : ℝ)*x 0 + (-427262503/2500000000 : ℝ)*x 1 + (702362229/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050909883/2000000000 : ℝ)^4339 ≤ (4307340311957/10000000000000 : ℝ)^3315 := by
    have hnat : (1050909883 : ℕ)^4339*10000000000000^3315 ≤ 4307340311957^3315*2000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050909883 2000000000 4307340311957 10000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (427262503/2500000000 : ℝ)^4339 ≤ (1980539581911/20000000000000 : ℝ)^3315 := by
    have hnat : (427262503 : ℕ)^4339*20000000000000^3315 ≤ 1980539581911^3315*2500000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427262503 2500000000 1980539581911 20000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (702362229/1250000000 : ℝ)^4339 ≤ (23511949475199/50000000000000 : ℝ)^3315 := by
    have hnat : (702362229 : ℕ)^4339*50000000000000^3315 ≤ 23511949475199^3315*1250000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      702362229 1250000000 23511949475199 50000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050909883/2000000000 : ℝ), (-427262503/2500000000 : ℝ), (702362229/1250000000 : ℝ)] ![(4307340311957/10000000000000 : ℝ), (1980539581911/20000000000000 : ℝ), (23511949475199/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050909883/2000000000 : ℝ)|^4339 ≤ (4307340311957/10000000000000 : ℝ)^3315
        have hw : |(1050909883/2000000000 : ℝ)|=(1050909883/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-427262503/2500000000 : ℝ)|^4339 ≤ (1980539581911/20000000000000 : ℝ)^3315
        have hw : |(-427262503/2500000000 : ℝ)|=(427262503/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(702362229/1250000000 : ℝ)|^4339 ≤ (23511949475199/50000000000000 : ℝ)^3315
        have hw : |(702362229/1250000000 : ℝ)|=(702362229/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_s1_6 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5254549717/10000000000 : ℝ)*x 0 + (5618898123/10000000000 : ℝ)*x 1 + (-341809833/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5254549717/10000000000 : ℝ)^4339 ≤ (43073406359881/100000000000000 : ℝ)^3315 := by
    have hnat : (5254549717 : ℕ)^4339*100000000000000^3315 ≤ 43073406359881^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254549717 10000000000 43073406359881 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5618898123/10000000000 : ℝ)^4339 ≤ (23511951069009/50000000000000 : ℝ)^3315 := by
    have hnat : (5618898123 : ℕ)^4339*50000000000000^3315 ≤ 23511951069009^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5618898123 10000000000 23511951069009 50000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (341809833/2000000000 : ℝ)^4339 ≤ (9902691485811/100000000000000 : ℝ)^3315 := by
    have hnat : (341809833 : ℕ)^4339*100000000000000^3315 ≤ 9902691485811^3315*2000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341809833 2000000000 9902691485811 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5254549717/10000000000 : ℝ), (5618898123/10000000000 : ℝ), (-341809833/2000000000 : ℝ)] ![(43073406359881/100000000000000 : ℝ), (23511951069009/50000000000000 : ℝ), (9902691485811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5254549717/10000000000 : ℝ)|^4339 ≤ (43073406359881/100000000000000 : ℝ)^3315
        have hw : |(5254549717/10000000000 : ℝ)|=(5254549717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5618898123/10000000000 : ℝ)|^4339 ≤ (23511951069009/50000000000000 : ℝ)^3315
        have hw : |(5618898123/10000000000 : ℝ)|=(5618898123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-341809833/2000000000 : ℝ)|^4339 ≤ (9902691485811/100000000000000 : ℝ)^3315
        have hw : |(-341809833/2000000000 : ℝ)|=(341809833/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_s1_7 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (857337673/2000000000 : ℝ)*x 0 + (982117729/2000000000 : ℝ)*x 1 + (1868964221/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (857337673/2000000000 : ℝ)^4339 ≤ (16498891388313/50000000000000 : ℝ)^3315 := by
    have hnat : (857337673 : ℕ)^4339*50000000000000^3315 ≤ 16498891388313^3315*2000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      857337673 2000000000 16498891388313 50000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (982117729/2000000000 : ℝ)^4339 ≤ (39420763966929/100000000000000 : ℝ)^3315 := by
    have hnat : (982117729 : ℕ)^4339*100000000000000^3315 ≤ 39420763966929^3315*2000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      982117729 2000000000 39420763966929 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1868964221/5000000000 : ℝ)^4339 ≤ (27581453239559/100000000000000 : ℝ)^3315 := by
    have hnat : (1868964221 : ℕ)^4339*100000000000000^3315 ≤ 27581453239559^3315*5000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1868964221 5000000000 27581453239559 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(857337673/2000000000 : ℝ), (982117729/2000000000 : ℝ), (1868964221/5000000000 : ℝ)] ![(16498891388313/50000000000000 : ℝ), (39420763966929/100000000000000 : ℝ), (27581453239559/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(857337673/2000000000 : ℝ)|^4339 ≤ (16498891388313/50000000000000 : ℝ)^3315
        have hw : |(857337673/2000000000 : ℝ)|=(857337673/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(982117729/2000000000 : ℝ)|^4339 ≤ (39420763966929/100000000000000 : ℝ)^3315
        have hw : |(982117729/2000000000 : ℝ)|=(982117729/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1868964221/5000000000 : ℝ)|^4339 ≤ (27581453239559/100000000000000 : ℝ)^3315
        have hw : |(1868964221/5000000000 : ℝ)|=(1868964221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1379_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156188383/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26607/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (211/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (289/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (19191/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (26607/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (211/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (26607/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (211/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (26607/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (211/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (26607/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (211/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (26607/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (211/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (26607/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (211/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (211/12500 : ℝ) ^ (2169/512 : ℝ) ≤ (3094339933823/100000000000000000000 : ℝ) := by
    have hpowers : (211/12500 : ℝ)^2169 ≤ (3094339933823/100000000000000000000 : ℝ)^512 := by
      have hnat : (211 : ℕ)^2169*100000000000000000000^512 ≤ 3094339933823^512*12500^2169 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        211 12500 3094339933823 100000000000000000000 2169 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (211/12500 : ℝ)) (X := (3094339933823/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2169 512 (by norm_num) hpowers
    exact h
  have hpowhi : (26607/100000 : ℝ) ^ (2169/512 : ℝ) ≤ (366516896013474567/100000000000000000000 : ℝ) := by
    have hpowers : (26607/100000 : ℝ)^2169 ≤ (366516896013474567/100000000000000000000 : ℝ)^512 := by
      have hnat : (26607 : ℕ)^2169*100000000000000000000^512 ≤ 366516896013474567^512*100000^2169 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26607 100000 366516896013474567 100000000000000000000 2169 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26607/100000 : ℝ)) (X := (366516896013474567/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2169 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000003094339933823/50000000000000000000 : ℝ) ≤ (500000007304297/500000000000000 : ℝ) ^ (2169/512 : ℝ) := by
    have hpowers : (50000003094339933823/50000000000000000000 : ℝ)^512 ≤ (500000007304297/500000000000000 : ℝ)^2169 := by
      have hnat : (50000003094339933823 : ℕ)^512*500000000000000^2169 ≤ 500000007304297^2169*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000003094339933823 50000000000000000000 500000007304297 500000000000000 512 2169 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500000007304297/500000000000000 : ℝ)) (X := (50000003094339933823/50000000000000000000 : ℝ)) (by norm_num) 2169 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (10036651999035340839/10000000000000000000 : ℝ) ≤ (2502159936338421/2500000000000000 : ℝ) ^ (2169/512 : ℝ) := by
    have hpowers : (10036651999035340839/10000000000000000000 : ℝ)^512 ≤ (2502159936338421/2500000000000000 : ℝ)^2169 := by
      have hnat : (10036651999035340839 : ℕ)^512*2500000000000000^2169 ≤ 2502159936338421^2169*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10036651999035340839 10000000000000000000 2502159936338421 2500000000000000 512 2169 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2502159936338421/2500000000000000 : ℝ)) (X := (10036651999035340839/10000000000000000000 : ℝ)) (by norm_num) 2169 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50366516896013474567/50000000000000000000 : ℝ) ≤ (2504319836155357/2500000000000000 : ℝ) ^ (2169/512 : ℝ) := by
    have hpowers : (50366516896013474567/50000000000000000000 : ℝ)^512 ≤ (2504319836155357/2500000000000000 : ℝ)^2169 := by
      have hnat : (50366516896013474567 : ℕ)^512*2500000000000000^2169 ≤ 2504319836155357^2169*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50366516896013474567 50000000000000000000 2504319836155357 2500000000000000 512 2169 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2504319836155357/2500000000000000 : ℝ)) (X := (50366516896013474567/50000000000000000000 : ℝ)) (by norm_num) 2169 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3094339933823/100000000000000000000 : ℝ) ≤ ((62290209088296908779/62297500000000000000 : ℝ)+2*(269987477117/77871875000000 : ℝ)*(211/12500 : ℝ))^(2169/512 : ℝ) := by
    rw [show (62290209088296908779/62297500000000000000 : ℝ)+2*(269987477117/77871875000000 : ℝ)*(211/12500 : ℝ)=(500000007304297/500000000000000 : ℝ) by norm_num, show 1+2*(3094339933823/100000000000000000000 : ℝ)=(50000003094339933823/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(366516896013474567/100000000000000000000 : ℝ)+(3094339933823/100000000000000000000 : ℝ) ≤ ((62290209088296908779/62297500000000000000 : ℝ)+(269987477117/77871875000000 : ℝ)*((26607/100000 : ℝ)+(211/12500 : ℝ)))^(2169/512 : ℝ) := by
    rw [show (62290209088296908779/62297500000000000000 : ℝ)+(269987477117/77871875000000 : ℝ)*((26607/100000 : ℝ)+(211/12500 : ℝ))=(2502159936338421/2500000000000000 : ℝ) by norm_num, show 1+(366516896013474567/100000000000000000000 : ℝ)+(3094339933823/100000000000000000000 : ℝ)=(10036651999035340839/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(366516896013474567/100000000000000000000 : ℝ) ≤ ((62290209088296908779/62297500000000000000 : ℝ)+2*(269987477117/77871875000000 : ℝ)*(26607/100000 : ℝ))^(2169/512 : ℝ) := by
    rw [show (62290209088296908779/62297500000000000000 : ℝ)+2*(269987477117/77871875000000 : ℝ)*(26607/100000 : ℝ)=(2504319836155357/2500000000000000 : ℝ) by norm_num, show 1+2*(366516896013474567/100000000000000000000 : ℝ)=(50366516896013474567/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (62290209088296908779/62297500000000000000 : ℝ)*(X 1 0+X 2 0)+(269987477117/77871875000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2169/512 : ℝ)) (lo := (211/12500 : ℝ)) (hi := (26607/100000 : ℝ)) (c := (62290209088296908779/62297500000000000000 : ℝ)) (alpha := (269987477117/77871875000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (62290209088296908779/62297500000000000000 : ℝ)*(X 0 1+X 2 1)+(269987477117/77871875000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2169/512 : ℝ)) (lo := (211/12500 : ℝ)) (hi := (26607/100000 : ℝ)) (c := (62290209088296908779/62297500000000000000 : ℝ)) (alpha := (269987477117/77871875000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (62290209088296908779/62297500000000000000 : ℝ)*(X 0 2+X 1 2)+(269987477117/77871875000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2169/512 : ℝ)) (lo := (211/12500 : ℝ)) (hi := (26607/100000 : ℝ)) (c := (62290209088296908779/62297500000000000000 : ℝ)) (alpha := (269987477117/77871875000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-983483373/5000000000 : ℝ)*X 0 0+(2812961479/5000000000 : ℝ)*X 0 1+(158119813/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1080377093/2000000000 : ℝ)*X 1 0+(-1134056277/5000000000 : ℝ)*X 1 1+(2529917717/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2700943057/5000000000 : ℝ)*X 2 0+(5059834203/10000000000 : ℝ)*X 2 1+(-1134056641/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2142841457/5000000000 : ℝ)*X 0 0+(1861505941/5000000000 : ℝ)*X 0 1+(2462624169/5000000000 : ℝ)*X 0 2+(2142841457/5000000000 : ℝ)*X 1 0+(1861505941/5000000000 : ℝ)*X 1 1+(2462624169/5000000000 : ℝ)*X 1 2+(2142841457/5000000000 : ℝ)*X 2 0+(1861505941/5000000000 : ℝ)*X 2 1+(2462624169/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1967439479/10000000000 : ℝ)*X 0 0+(1266684311/2500000000 : ℝ)*X 0 1+(5618897741/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1050909883/2000000000 : ℝ)*X 1 0+(-427262503/2500000000 : ℝ)*X 1 1+(702362229/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5254549717/10000000000 : ℝ)*X 2 0+(5618898123/10000000000 : ℝ)*X 2 1+(-341809833/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((857337673/2000000000 : ℝ)*X 0 0+(982117729/2000000000 : ℝ)*X 0 1+(1868964221/5000000000 : ℝ)*X 0 2+(857337673/2000000000 : ℝ)*X 1 0+(982117729/2000000000 : ℝ)*X 1 1+(1868964221/5000000000 : ℝ)*X 1 2+(857337673/2000000000 : ℝ)*X 2 0+(982117729/2000000000 : ℝ)*X 2 1+(1868964221/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12096773430896480558684184009/1557437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (628580897/50000000000000 : ℝ)*(base19) + (186237573/12500000000000 : ℝ)*(base23) + (11938447/100000000000000 : ℝ)*(upper2) + (29792121/12500000000000 : ℝ)*(upper3) + (649580870484819/50000000000000 : ℝ)*(major0) + (649580870484819/50000000000000 : ℝ)*(major1) + (649580870484819/50000000000000 : ℝ)*(major2) + (70660814658443/4000000000000 : ℝ)*(sp0) + (1766530435661771/100000000000000 : ℝ)*(sp1) + (1766530144320483/100000000000000 : ℝ)*(sp2) + (831786578675079/100000000000000 : ℝ)*(sp3) + (1132636249/10000000000000 : ℝ)*(sp4) + (29301249/50000000000000 : ℝ)*(sp6) + (4951537279/100000000000000 : ℝ)*(sp7) + (415895765106179/50000000000000 : ℝ)*(f.failure) + (353306338564713/20000000000000 : ℝ)*(f.sum) + (227523819905977/124595000000000000000000000000 : ℝ)*base65 + (27648967239858898999/3114875000000000000000000000000000 : ℝ)*base68 + (19981382426905523999/3114875000000000000000000000000000 : ℝ)*base70 + (9031965248539773999/3114875000000000000000000000000000 : ℝ)*base72 + (62920353943767/124595000000000000000000000000 : ℝ)*base73 + (34035484509750023999/3114875000000000000000000000000000 : ℝ)*base76 + (21316432987083148999/3114875000000000000000000000000000 : ℝ)*base78 + (58513497022317273999/3114875000000000000000000000000000 : ℝ)*base80 + (50913344664373/31148750000000000000000000000 : ℝ)*base81 + (21318557/5000000000000000000000 : ℝ)*base89 + (21318557/5000000000000000000000 : ℝ)*base91 + (21318557/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2721345632669513585885564811/311487500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (189872099/100000000000000 : ℝ)*(base1) + (2062501337/100000000000000 : ℝ)*(base19) + (2237587651/100000000000000 : ℝ)*(base23) + (220540827/100000000000000 : ℝ)*(upper3) + (260895569/100000000000000 : ℝ)*(upper5) + (133191541401597/10000000000000 : ℝ)*(major0) + (133191541401597/10000000000000 : ℝ)*(major1) + (133191541401597/10000000000000 : ℝ)*(major2) + (5302231147/50000000000000 : ℝ)*(sp1) + (3284112663/25000000000000 : ℝ)*(sp2) + (1811068575982577/100000000000000 : ℝ)*(sp4) + (1811055719146847/100000000000000 : ℝ)*(sp5) + (72442120482887/4000000000000 : ℝ)*(sp6) + (170552392165787/20000000000000 : ℝ)*(sp7) + (170552430140207/20000000000000 : ℝ)*(f.failure) + (905534193055239/50000000000000 : ℝ)*(f.sum) + (9564872917397/6229750000000000000000000000 : ℝ)*base65 + (5402017572665695063/622975000000000000000000000000000 : ℝ)*base67 + (3548737366267795063/622975000000000000000000000000000 : ℝ)*base69 + (5812307894085370063/622975000000000000000000000000000 : ℝ)*base71 + (42037009154171/24919000000000000000000000000 : ℝ)*base73 + (785592342447370063/622975000000000000000000000000000 : ℝ)*base75 + (238504739998929937/622975000000000000000000000000000 : ℝ)*base78 + (4333968270979937/622975000000000000000000000000000 : ℝ)*base80 + (36342182967347/24919000000000000000000000000 : ℝ)*base81 + (5384719/2000000000000000000000 : ℝ)*base90 + (5384719/2000000000000000000000 : ℝ)*base92 + (5384719/2000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1379_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156188383/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26607/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (211/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (289/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (19191/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1379_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1379_s2_0 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1001998667/5000000000 : ℝ)*x 0 + (273502329/500000000 : ℝ)*x 1 + (5191940859/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1001998667/5000000000 : ℝ)^4339 ≤ (6098512343941/50000000000000 : ℝ)^3315 := by
    have hnat : (1001998667 : ℕ)^4339*50000000000000^3315 ≤ 6098512343941^3315*5000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1001998667 5000000000 6098512343941 50000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (273502329/500000000 : ℝ)^4339 ≤ (22700045778667/50000000000000 : ℝ)^3315 := by
    have hnat : (273502329 : ℕ)^4339*50000000000000^3315 ≤ 22700045778667^3315*500000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273502329 500000000 22700045778667 50000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5191940859/10000000000 : ℝ)^4339 ≤ (8480576746383/20000000000000 : ℝ)^3315 := by
    have hnat : (5191940859 : ℕ)^4339*20000000000000^3315 ≤ 8480576746383^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5191940859 10000000000 8480576746383 20000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1001998667/5000000000 : ℝ), (273502329/500000000 : ℝ), (5191940859/10000000000 : ℝ)] ![(6098512343941/50000000000000 : ℝ), (22700045778667/50000000000000 : ℝ), (8480576746383/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1001998667/5000000000 : ℝ)|^4339 ≤ (6098512343941/50000000000000 : ℝ)^3315
        have hw : |(-1001998667/5000000000 : ℝ)|=(1001998667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(273502329/500000000 : ℝ)|^4339 ≤ (22700045778667/50000000000000 : ℝ)^3315
        have hw : |(273502329/500000000 : ℝ)|=(273502329/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5191940859/10000000000 : ℝ)|^4339 ≤ (8480576746383/20000000000000 : ℝ)^3315
        have hw : |(5191940859/10000000000 : ℝ)|=(5191940859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_s2_1 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1340851833/2500000000 : ℝ)*x 0 + (-2147418159/10000000000 : ℝ)*x 1 + (5191940877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1340851833/2500000000 : ℝ)^4339 ≤ (22122557303447/50000000000000 : ℝ)^3315 := by
    have hnat : (1340851833 : ℕ)^4339*50000000000000^3315 ≤ 22122557303447^3315*2500000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1340851833 2500000000 22122557303447 50000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2147418159/10000000000 : ℝ)^4339 ≤ (13352001453493/100000000000000 : ℝ)^3315 := by
    have hnat : (2147418159 : ℕ)^4339*100000000000000^3315 ≤ 13352001453493^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2147418159 10000000000 13352001453493 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5191940877/10000000000 : ℝ)^4339 ≤ (10600720981083/25000000000000 : ℝ)^3315 := by
    have hnat : (5191940877 : ℕ)^4339*25000000000000^3315 ≤ 10600720981083^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5191940877 10000000000 10600720981083 25000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1340851833/2500000000 : ℝ), (-2147418159/10000000000 : ℝ), (5191940877/10000000000 : ℝ)] ![(22122557303447/50000000000000 : ℝ), (13352001453493/100000000000000 : ℝ), (10600720981083/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1340851833/2500000000 : ℝ)|^4339 ≤ (22122557303447/50000000000000 : ℝ)^3315
        have hw : |(1340851833/2500000000 : ℝ)|=(1340851833/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2147418159/10000000000 : ℝ)|^4339 ≤ (13352001453493/100000000000000 : ℝ)^3315
        have hw : |(-2147418159/10000000000 : ℝ)|=(2147418159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5191940877/10000000000 : ℝ)|^4339 ≤ (10600720981083/25000000000000 : ℝ)^3315
        have hw : |(5191940877/10000000000 : ℝ)|=(5191940877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_s2_2 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5363407241/10000000000 : ℝ)*x 0 + (5191940959/10000000000 : ℝ)*x 1 + (-536854543/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363407241/10000000000 : ℝ)^4339 ≤ (8849022724861/20000000000000 : ℝ)^3315 := by
    have hnat : (5363407241 : ℕ)^4339*20000000000000^3315 ≤ 8849022724861^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363407241 10000000000 8849022724861 20000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5191940959/10000000000 : ℝ)^4339 ≤ (424028848009/1000000000000 : ℝ)^3315 := by
    have hnat : (5191940959 : ℕ)^4339*1000000000000^3315 ≤ 424028848009^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5191940959 10000000000 424028848009 1000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (536854543/2500000000 : ℝ)^4339 ≤ (13352001559291/100000000000000 : ℝ)^3315 := by
    have hnat : (536854543 : ℕ)^4339*100000000000000^3315 ≤ 13352001559291^3315*2500000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536854543 2500000000 13352001559291 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363407241/10000000000 : ℝ), (5191940959/10000000000 : ℝ), (-536854543/2500000000 : ℝ)] ![(8849022724861/20000000000000 : ℝ), (424028848009/1000000000000 : ℝ), (13352001559291/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363407241/10000000000 : ℝ)|^4339 ≤ (8849022724861/20000000000000 : ℝ)^3315
        have hw : |(5363407241/10000000000 : ℝ)|=(5363407241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5191940959/10000000000 : ℝ)|^4339 ≤ (424028848009/1000000000000 : ℝ)^3315
        have hw : |(5191940959/10000000000 : ℝ)|=(5191940959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-536854543/2500000000 : ℝ)|^4339 ≤ (13352001559291/100000000000000 : ℝ)^3315
        have hw : |(-536854543/2500000000 : ℝ)|=(536854543/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_s2_3 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4311687569/10000000000 : ℝ)*x 0 + (4025648089/10000000000 : ℝ)*x 1 + (4616279927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4311687569/10000000000 : ℝ)^4339 ≤ (8312472548533/25000000000000 : ℝ)^3315 := by
    have hnat : (4311687569 : ℕ)^4339*25000000000000^3315 ≤ 8312472548533^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4311687569 10000000000 8312472548533 25000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4025648089/10000000000 : ℝ)^4339 ≤ (1899546909009/6250000000000 : ℝ)^3315 := by
    have hnat : (4025648089 : ℕ)^4339*6250000000000^3315 ≤ 1899546909009^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4025648089 10000000000 1899546909009 6250000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4616279927/10000000000 : ℝ)^4339 ≤ (18178679623249/50000000000000 : ℝ)^3315 := by
    have hnat : (4616279927 : ℕ)^4339*50000000000000^3315 ≤ 18178679623249^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4616279927 10000000000 18178679623249 50000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4311687569/10000000000 : ℝ), (4025648089/10000000000 : ℝ), (4616279927/10000000000 : ℝ)] ![(8312472548533/25000000000000 : ℝ), (1899546909009/6250000000000 : ℝ), (18178679623249/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4311687569/10000000000 : ℝ)|^4339 ≤ (8312472548533/25000000000000 : ℝ)^3315
        have hw : |(4311687569/10000000000 : ℝ)|=(4311687569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4025648089/10000000000 : ℝ)|^4339 ≤ (1899546909009/6250000000000 : ℝ)^3315
        have hw : |(4025648089/10000000000 : ℝ)|=(4025648089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4616279927/10000000000 : ℝ)|^4339 ≤ (18178679623249/50000000000000 : ℝ)^3315
        have hw : |(4616279927/10000000000 : ℝ)|=(4616279927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_s2_4 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1002026603/5000000000 : ℝ)*x 0 + (5193616741/10000000000 : ℝ)*x 1 + (136708909/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1002026603/5000000000 : ℝ)^4339 ≤ (1219746978929/10000000000000 : ℝ)^3315 := by
    have hnat : (1002026603 : ℕ)^4339*10000000000000^3315 ≤ 1219746978929^3315*5000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1002026603 5000000000 1219746978929 10000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5193616741/10000000000 : ℝ)^4339 ≤ (42420799558877/100000000000000 : ℝ)^3315 := by
    have hnat : (5193616741 : ℕ)^4339*100000000000000^3315 ≤ 42420799558877^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5193616741 10000000000 42420799558877 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (136708909/250000000 : ℝ)^4339 ≤ (2836358165121/6250000000000 : ℝ)^3315 := by
    have hnat : (136708909 : ℕ)^4339*6250000000000^3315 ≤ 2836358165121^3315*250000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136708909 250000000 2836358165121 6250000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1002026603/5000000000 : ℝ), (5193616741/10000000000 : ℝ), (136708909/250000000 : ℝ)] ![(1219746978929/10000000000000 : ℝ), (42420799558877/100000000000000 : ℝ), (2836358165121/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1002026603/5000000000 : ℝ)|^4339 ≤ (1219746978929/10000000000000 : ℝ)^3315
        have hw : |(-1002026603/5000000000 : ℝ)|=(1002026603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5193616741/10000000000 : ℝ)|^4339 ≤ (42420799558877/100000000000000 : ℝ)^3315
        have hw : |(5193616741/10000000000 : ℝ)|=(5193616741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(136708909/250000000 : ℝ)|^4339 ≤ (2836358165121/6250000000000 : ℝ)^3315
        have hw : |(136708909/250000000 : ℝ)|=(136708909/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_s2_5 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5291444991/10000000000 : ℝ)*x 0 + (-935501641/5000000000 : ℝ)*x 1 + (1093671211/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5291444991/10000000000 : ℝ)^4339 ≤ (43469703136503/100000000000000 : ℝ)^3315 := by
    have hnat : (5291444991 : ℕ)^4339*100000000000000^3315 ≤ 43469703136503^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5291444991 10000000000 43469703136503 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (935501641/5000000000 : ℝ)^4339 ≤ (11148569514503/100000000000000 : ℝ)^3315 := by
    have hnat : (935501641 : ℕ)^4339*100000000000000^3315 ≤ 11148569514503^3315*5000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      935501641 5000000000 11148569514503 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1093671211/2000000000 : ℝ)^4339 ≤ (45381727328869/100000000000000 : ℝ)^3315 := by
    have hnat : (1093671211 : ℕ)^4339*100000000000000^3315 ≤ 45381727328869^3315*2000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093671211 2000000000 45381727328869 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5291444991/10000000000 : ℝ), (-935501641/5000000000 : ℝ), (1093671211/2000000000 : ℝ)] ![(43469703136503/100000000000000 : ℝ), (11148569514503/100000000000000 : ℝ), (45381727328869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5291444991/10000000000 : ℝ)|^4339 ≤ (43469703136503/100000000000000 : ℝ)^3315
        have hw : |(5291444991/10000000000 : ℝ)|=(5291444991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-935501641/5000000000 : ℝ)|^4339 ≤ (11148569514503/100000000000000 : ℝ)^3315
        have hw : |(-935501641/5000000000 : ℝ)|=(935501641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1093671211/2000000000 : ℝ)|^4339 ≤ (45381727328869/100000000000000 : ℝ)^3315
        have hw : |(1093671211/2000000000 : ℝ)|=(1093671211/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_s2_6 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5291446477/10000000000 : ℝ)*x 0 + (2734178073/5000000000 : ℝ)*x 1 + (-1871001107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5291446477/10000000000 : ℝ)^4339 ≤ (10867429778763/25000000000000 : ℝ)^3315 := by
    have hnat : (5291446477 : ℕ)^4339*25000000000000^3315 ≤ 10867429778763^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5291446477 10000000000 10867429778763 25000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2734178073/5000000000 : ℝ)^4339 ≤ (22690864158679/50000000000000 : ℝ)^3315 := by
    have hnat : (2734178073 : ℕ)^4339*50000000000000^3315 ≤ 22690864158679^3315*5000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2734178073 5000000000 22690864158679 50000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1871001107/10000000000 : ℝ)^4339 ≤ (557427627561/5000000000000 : ℝ)^3315 := by
    have hnat : (1871001107 : ℕ)^4339*5000000000000^3315 ≤ 557427627561^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1871001107 10000000000 557427627561 5000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5291446477/10000000000 : ℝ), (2734178073/5000000000 : ℝ), (-1871001107/10000000000 : ℝ)] ![(10867429778763/25000000000000 : ℝ), (22690864158679/50000000000000 : ℝ), (557427627561/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5291446477/10000000000 : ℝ)|^4339 ≤ (10867429778763/25000000000000 : ℝ)^3315
        have hw : |(5291446477/10000000000 : ℝ)|=(5291446477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2734178073/5000000000 : ℝ)|^4339 ≤ (22690864158679/50000000000000 : ℝ)^3315
        have hw : |(2734178073/5000000000 : ℝ)|=(2734178073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1871001107/10000000000 : ℝ)|^4339 ≤ (557427627561/5000000000000 : ℝ)^3315
        have hw : |(-1871001107/10000000000 : ℝ)|=(1871001107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1379_s2_7 (p : ℝ) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4311807883/10000000000 : ℝ)*x 0 + (2306360709/5000000000 : ℝ)*x 1 + (1007309121/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4311807883/10000000000 : ℝ)^4339 ≤ (3325110460903/10000000000000 : ℝ)^3315 := by
    have hnat : (4311807883 : ℕ)^4339*10000000000000^3315 ≤ 3325110460903^3315*10000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4311807883 10000000000 3325110460903 10000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2306360709/5000000000 : ℝ)^4339 ≤ (18160339904693/50000000000000 : ℝ)^3315 := by
    have hnat : (2306360709 : ℕ)^4339*50000000000000^3315 ≤ 18160339904693^3315*5000000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2306360709 5000000000 18160339904693 50000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1007309121/2500000000 : ℝ)^4339 ≤ (30428215574253/100000000000000 : ℝ)^3315 := by
    have hnat : (1007309121 : ℕ)^4339*100000000000000^3315 ≤ 30428215574253^3315*2500000000^4339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1007309121 2500000000 30428215574253 100000000000000 4339 3315 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4339/1024 : ℝ)) 4339 3315 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4311807883/10000000000 : ℝ), (2306360709/5000000000 : ℝ), (1007309121/2500000000 : ℝ)] ![(3325110460903/10000000000000 : ℝ), (18160339904693/50000000000000 : ℝ), (30428215574253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4311807883/10000000000 : ℝ)|^4339 ≤ (3325110460903/10000000000000 : ℝ)^3315
        have hw : |(4311807883/10000000000 : ℝ)|=(4311807883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2306360709/5000000000 : ℝ)|^4339 ≤ (18160339904693/50000000000000 : ℝ)^3315
        have hw : |(2306360709/5000000000 : ℝ)|=(2306360709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1007309121/2500000000 : ℝ)|^4339 ≤ (30428215574253/100000000000000 : ℝ)^3315
        have hw : |(1007309121/2500000000 : ℝ)|=(1007309121/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1379_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156188383/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19191/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (289/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (2521/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3193/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (19191/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (289/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (19191/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (289/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (19191/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (289/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (19191/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (289/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (19191/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (289/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (19191/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (289/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (289/4000 : ℝ) ^ (2169/512 : ℝ) ≤ (1464410030145223/100000000000000000000 : ℝ) := by
    have hpowers : (289/4000 : ℝ)^2169 ≤ (1464410030145223/100000000000000000000 : ℝ)^512 := by
      have hnat : (289 : ℕ)^2169*100000000000000000000^512 ≤ 1464410030145223^512*4000^2169 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        289 4000 1464410030145223 100000000000000000000 2169 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (289/4000 : ℝ)) (X := (1464410030145223/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2169 512 (by norm_num) hpowers
    exact h
  have hpowhi : (19191/100000 : ℝ) ^ (2169/512 : ℝ) ≤ (91826117655053911/100000000000000000000 : ℝ) := by
    have hpowers : (19191/100000 : ℝ)^2169 ≤ (91826117655053911/100000000000000000000 : ℝ)^512 := by
      have hnat : (19191 : ℕ)^2169*100000000000000000000^512 ≤ 91826117655053911^512*100000^2169 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19191 100000 91826117655053911 100000000000000000000 2169 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19191/100000 : ℝ)) (X := (91826117655053911/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2169 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001464410030145223/50000000000000000000 : ℝ) ≤ (1250008641880447/1250000000000000 : ℝ) ^ (2169/512 : ℝ) := by
    have hpowers : (50001464410030145223/50000000000000000000 : ℝ)^512 ≤ (1250008641880447/1250000000000000 : ℝ)^2169 := by
      have hnat : (50001464410030145223 : ℕ)^512*1250000000000000^2169 ≤ 1250008641880447^2169*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001464410030145223 50000000000000000000 1250008641880447 1250000000000000 512 2169 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250008641880447/1250000000000000 : ℝ)) (X := (50001464410030145223/50000000000000000000 : ℝ)) (by norm_num) 2169 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50046645263842599567/50000000000000000000 : ℝ) ≤ (5001100685541299/5000000000000000 : ℝ) ^ (2169/512 : ℝ) := by
    have hpowers : (50046645263842599567/50000000000000000000 : ℝ)^512 ≤ (5001100685541299/5000000000000000 : ℝ)^2169 := by
      have hnat : (50046645263842599567 : ℕ)^512*5000000000000000^2169 ≤ 5001100685541299^2169*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50046645263842599567 50000000000000000000 5001100685541299 5000000000000000 512 2169 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001100685541299/5000000000000000 : ℝ)) (X := (50046645263842599567/50000000000000000000 : ℝ)) (by norm_num) 2169 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50091826117655053911/50000000000000000000 : ℝ) ≤ (500216680356081/500000000000000 : ℝ) ^ (2169/512 : ℝ) := by
    have hpowers : (50091826117655053911/50000000000000000000 : ℝ)^512 ≤ (500216680356081/500000000000000 : ℝ)^2169 := by
      have hnat : (50091826117655053911 : ℕ)^512*500000000000000^2169 ≤ 500216680356081^2169*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50091826117655053911 50000000000000000000 500216680356081 500000000000000 512 2169 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500216680356081/500000000000000 : ℝ)) (X := (50091826117655053911/50000000000000000000 : ℝ)) (by norm_num) 2169 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1464410030145223/100000000000000000000 : ℝ) ≤ ((29907504114791890629/29915000000000000000 : ℝ)+2*(1066118019511/598300000000000 : ℝ)*(289/4000 : ℝ))^(2169/512 : ℝ) := by
    rw [show (29907504114791890629/29915000000000000000 : ℝ)+2*(1066118019511/598300000000000 : ℝ)*(289/4000 : ℝ)=(1250008641880447/1250000000000000 : ℝ) by norm_num, show 1+2*(1464410030145223/100000000000000000000 : ℝ)=(50001464410030145223/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(91826117655053911/100000000000000000000 : ℝ)+(1464410030145223/100000000000000000000 : ℝ) ≤ ((29907504114791890629/29915000000000000000 : ℝ)+(1066118019511/598300000000000 : ℝ)*((19191/100000 : ℝ)+(289/4000 : ℝ)))^(2169/512 : ℝ) := by
    rw [show (29907504114791890629/29915000000000000000 : ℝ)+(1066118019511/598300000000000 : ℝ)*((19191/100000 : ℝ)+(289/4000 : ℝ))=(5001100685541299/5000000000000000 : ℝ) by norm_num, show 1+(91826117655053911/100000000000000000000 : ℝ)+(1464410030145223/100000000000000000000 : ℝ)=(50046645263842599567/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(91826117655053911/100000000000000000000 : ℝ) ≤ ((29907504114791890629/29915000000000000000 : ℝ)+2*(1066118019511/598300000000000 : ℝ)*(19191/100000 : ℝ))^(2169/512 : ℝ) := by
    rw [show (29907504114791890629/29915000000000000000 : ℝ)+2*(1066118019511/598300000000000 : ℝ)*(19191/100000 : ℝ)=(500216680356081/500000000000000 : ℝ) by norm_num, show 1+2*(91826117655053911/100000000000000000000 : ℝ)=(50091826117655053911/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (29907504114791890629/29915000000000000000 : ℝ)*(X 1 0+X 2 0)+(1066118019511/598300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2169/512 : ℝ)) (lo := (289/4000 : ℝ)) (hi := (19191/100000 : ℝ)) (c := (29907504114791890629/29915000000000000000 : ℝ)) (alpha := (1066118019511/598300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (29907504114791890629/29915000000000000000 : ℝ)*(X 0 1+X 2 1)+(1066118019511/598300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2169/512 : ℝ)) (lo := (289/4000 : ℝ)) (hi := (19191/100000 : ℝ)) (c := (29907504114791890629/29915000000000000000 : ℝ)) (alpha := (1066118019511/598300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (29907504114791890629/29915000000000000000 : ℝ)*(X 0 2+X 1 2)+(1066118019511/598300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2169/512 : ℝ)) (lo := (289/4000 : ℝ)) (hi := (19191/100000 : ℝ)) (c := (29907504114791890629/29915000000000000000 : ℝ)) (alpha := (1066118019511/598300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1001998667/5000000000 : ℝ)*X 0 0+(273502329/500000000 : ℝ)*X 0 1+(5191940859/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1340851833/2500000000 : ℝ)*X 1 0+(-2147418159/10000000000 : ℝ)*X 1 1+(5191940877/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5363407241/10000000000 : ℝ)*X 2 0+(5191940959/10000000000 : ℝ)*X 2 1+(-536854543/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4311687569/10000000000 : ℝ)*X 0 0+(4025648089/10000000000 : ℝ)*X 0 1+(4616279927/10000000000 : ℝ)*X 0 2+(4311687569/10000000000 : ℝ)*X 1 0+(4025648089/10000000000 : ℝ)*X 1 1+(4616279927/10000000000 : ℝ)*X 1 2+(4311687569/10000000000 : ℝ)*X 2 0+(4025648089/10000000000 : ℝ)*X 2 1+(4616279927/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1002026603/5000000000 : ℝ)*X 0 0+(5193616741/10000000000 : ℝ)*X 0 1+(136708909/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5291444991/10000000000 : ℝ)*X 1 0+(-935501641/5000000000 : ℝ)*X 1 1+(1093671211/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5291446477/10000000000 : ℝ)*X 2 0+(2734178073/5000000000 : ℝ)*X 2 1+(-1871001107/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4311807883/10000000000 : ℝ)*X 0 0+(2306360709/5000000000 : ℝ)*X 0 1+(1007309121/2500000000 : ℝ)*X 0 2+(4311807883/10000000000 : ℝ)*X 1 0+(2306360709/5000000000 : ℝ)*X 1 1+(1007309121/2500000000 : ℝ)*X 1 2+(4311807883/10000000000 : ℝ)*X 2 0+(2306360709/5000000000 : ℝ)*X 2 1+(1007309121/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1379_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1677318850482603068261824377/299150000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (963010393/100000000000000 : ℝ)*(base19) + (408831391/50000000000000 : ℝ)*(base23) + (9046853/20000000000000 : ℝ)*(lower2) + (161443011/100000000000000 : ℝ)*(upper3) + (17771327/25000000000000 : ℝ)*(upper5) + (528889217960729/20000000000000 : ℝ)*(major0) + (528889217960729/20000000000000 : ℝ)*(major1) + (528889217960729/20000000000000 : ℝ)*(major2) + (1797883836807/50000000000 : ℝ)*(sp0) + (898944463768893/25000000000000 : ℝ)*(sp1) + (224736125026449/6250000000000 : ℝ)*(sp2) + (846553567603587/50000000000000 : ℝ)*(sp3) + (5572235983/50000000000000 : ℝ)*(sp4) + (1207883167/20000000000000 : ℝ)*(sp7) + (1693113174623009/100000000000000 : ℝ)*(f.failure) + (1797889409042983/50000000000000 : ℝ)*(f.sum) + (9946083007437/2991500000000000000000000000 : ℝ)*base65 + (2540531767791541459/598300000000000000000000000000000 : ℝ)*base68 + (5284632211497658541/598300000000000000000000000000000 : ℝ)*base69 + (713027286026558541/598300000000000000000000000000000 : ℝ)*base71 + (557903510833/239320000000000000000000000 : ℝ)*base74 + (929769916800458541/598300000000000000000000000000000 : ℝ)*base75 + (802185090474558541/598300000000000000000000000000000 : ℝ)*base77 + (2049860343686541459/598300000000000000000000000000000 : ℝ)*base80 + (31371912796949/5983000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (89695553/10000000000000000000000 : ℝ)*base90 + (89695553/10000000000000000000000 : ℝ)*base92 + (89695553/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (319671450034169088707975211/74787500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (162868587/20000000000000 : ℝ)*(base19) + (2963820123/100000000000000 : ℝ)*(base23) + (8329273/50000000000000 : ℝ)*(lower2) + (258017091/100000000000000 : ℝ)*(upper3) + (75843989/25000000000000 : ℝ)*(lower4) + (273877/2500000000000 : ℝ)*(upper5) + (267682618334653/10000000000000 : ℝ)*(major0) + (267682618334653/10000000000000 : ℝ)*(major1) + (267682618334653/10000000000000 : ℝ)*(major2) + (43050078001/100000000000000 : ℝ)*(sp2) + (3639807614306077/100000000000000 : ℝ)*(sp4) + (1819903399981571/50000000000000 : ℝ)*(sp5) + (1819880800203977/50000000000000 : ℝ)*(sp6) + (1713844609907083/100000000000000 : ℝ)*(sp7) + (1713844609907083/100000000000000 : ℝ)*(f.failure) + (3639807614306077/100000000000000 : ℝ)*(f.sum) + (161024359269/47864000000000000000000000 : ℝ)*base65 + (673832999330833263/299150000000000000000000000000000 : ℝ)*base68 + (2022723426060983263/299150000000000000000000000000000 : ℝ)*base70 + (43732643190166737/299150000000000000000000000000000 : ℝ)*base71 + (1435144569073/747875000000000000000000000 : ℝ)*base74 + (1479145466734483263/299150000000000000000000000000000 : ℝ)*base76 + (5763894132569383263/299150000000000000000000000000000 : ℝ)*base78 + (3753490465922733263/299150000000000000000000000000000 : ℝ)*base80 + (70362441313/74787500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (74016789/10000000000000000000000 : ℝ)*base89 + (74016789/10000000000000000000000 : ℝ)*base91 + (74016789/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1379_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156188383/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19191/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (289/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2521/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3193/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1379_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1379_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156188383/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2521/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3193/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1379_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1379_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1379_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2169/512 : ℝ) ≤ p) (hpb : p ≤ (4339/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156188383/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2521/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3193/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1379_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
