-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1090_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:57:00.048996+00:00
-- url     : https://prove2.me/submissions/b152b15b-f1f7-42ba-b0af-60b9b27854b5

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
theorem support_rectangle_w1090_s0_0 (p : ℝ) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1908378153/10000000000 : ℝ)*x 0 + (6066427281/10000000000 : ℝ)*x 1 + (2386930257/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1908378153/10000000000 : ℝ)^8283 ≤ (2215212966111/20000000000000 : ℝ)^6235 := by
    have hnat : (1908378153 : ℕ)^8283*20000000000000^6235 ≤ 2215212966111^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1908378153 10000000000 2215212966111 20000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6066427281/10000000000 : ℝ)^8283 ≤ (51479386314211/100000000000000 : ℝ)^6235 := by
    have hnat : (6066427281 : ℕ)^8283*100000000000000^6235 ≤ 51479386314211^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6066427281 10000000000 51479386314211 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2386930257/5000000000 : ℝ)^8283 ≤ (37444548839127/100000000000000 : ℝ)^6235 := by
    have hnat : (2386930257 : ℕ)^8283*100000000000000^6235 ≤ 37444548839127^6235*5000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2386930257 5000000000 37444548839127 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8283/2048 : ℝ)) 8283 6235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1908378153/10000000000 : ℝ), (6066427281/10000000000 : ℝ), (2386930257/5000000000 : ℝ)] ![(2215212966111/20000000000000 : ℝ), (51479386314211/100000000000000 : ℝ), (37444548839127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1908378153/10000000000 : ℝ)|^8283 ≤ (2215212966111/20000000000000 : ℝ)^6235
        have hw : |(-1908378153/10000000000 : ℝ)|=(1908378153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6066427281/10000000000 : ℝ)|^8283 ≤ (51479386314211/100000000000000 : ℝ)^6235
        have hw : |(6066427281/10000000000 : ℝ)|=(6066427281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2386930257/5000000000 : ℝ)|^8283 ≤ (37444548839127/100000000000000 : ℝ)^6235
        have hw : |(2386930257/5000000000 : ℝ)|=(2386930257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1090_s0_1 (p : ℝ) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5519722243/10000000000 : ℝ)*x 0 + (-2651677627/10000000000 : ℝ)*x 1 + (1193465171/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5519722243/10000000000 : ℝ)^8283 ≤ (45409341850647/100000000000000 : ℝ)^6235 := by
    have hnat : (5519722243 : ℕ)^8283*100000000000000^6235 ≤ 45409341850647^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5519722243 10000000000 45409341850647 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2651677627/10000000000 : ℝ)^8283 ≤ (1071631720263/6250000000000 : ℝ)^6235 := by
    have hnat : (2651677627 : ℕ)^8283*6250000000000^6235 ≤ 1071631720263^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651677627 10000000000 1071631720263 6250000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1193465171/2500000000 : ℝ)^8283 ≤ (37444550610537/100000000000000 : ℝ)^6235 := by
    have hnat : (1193465171 : ℕ)^8283*100000000000000^6235 ≤ 37444550610537^6235*2500000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1193465171 2500000000 37444550610537 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8283/2048 : ℝ)) 8283 6235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5519722243/10000000000 : ℝ), (-2651677627/10000000000 : ℝ), (1193465171/2500000000 : ℝ)] ![(45409341850647/100000000000000 : ℝ), (1071631720263/6250000000000 : ℝ), (37444550610537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5519722243/10000000000 : ℝ)|^8283 ≤ (45409341850647/100000000000000 : ℝ)^6235
        have hw : |(5519722243/10000000000 : ℝ)|=(5519722243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2651677627/10000000000 : ℝ)|^8283 ≤ (1071631720263/6250000000000 : ℝ)^6235
        have hw : |(-2651677627/10000000000 : ℝ)|=(2651677627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1193465171/2500000000 : ℝ)|^8283 ≤ (37444550610537/100000000000000 : ℝ)^6235
        have hw : |(1193465171/2500000000 : ℝ)|=(1193465171/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1090_s0_2 (p : ℝ) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2759860697/5000000000 : ℝ)*x 0 + (2386930637/5000000000 : ℝ)*x 1 + (-331459749/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2759860697/5000000000 : ℝ)^8283 ≤ (2838083285747/6250000000000 : ℝ)^6235 := by
    have hnat : (2759860697 : ℕ)^8283*6250000000000^6235 ≤ 2838083285747^6235*5000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2759860697 5000000000 2838083285747 6250000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2386930637/5000000000 : ℝ)^8283 ≤ (37444556758371/100000000000000 : ℝ)^6235 := by
    have hnat : (2386930637 : ℕ)^8283*100000000000000^6235 ≤ 37444556758371^6235*5000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2386930637 5000000000 37444556758371 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (331459749/1250000000 : ℝ)^8283 ≤ (17146110659579/100000000000000 : ℝ)^6235 := by
    have hnat : (331459749 : ℕ)^8283*100000000000000^6235 ≤ 17146110659579^6235*1250000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331459749 1250000000 17146110659579 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8283/2048 : ℝ)) 8283 6235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2759860697/5000000000 : ℝ), (2386930637/5000000000 : ℝ), (-331459749/1250000000 : ℝ)] ![(2838083285747/6250000000000 : ℝ), (37444556758371/100000000000000 : ℝ), (17146110659579/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2759860697/5000000000 : ℝ)|^8283 ≤ (2838083285747/6250000000000 : ℝ)^6235
        have hw : |(2759860697/5000000000 : ℝ)|=(2759860697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2386930637/5000000000 : ℝ)|^8283 ≤ (37444556758371/100000000000000 : ℝ)^6235
        have hw : |(2386930637/5000000000 : ℝ)|=(2386930637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-331459749/1250000000 : ℝ)|^8283 ≤ (17146110659579/100000000000000 : ℝ)^6235
        have hw : |(-331459749/1250000000 : ℝ)|=(331459749/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1090_s0_3 (p : ℝ) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (841046083/2000000000 : ℝ)*x 0 + (31236117/100000000 : ℝ)*x 1 + (2834468397/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (841046083/2000000000 : ℝ)^8283 ≤ (15819278295543/50000000000000 : ℝ)^6235 := by
    have hnat : (841046083 : ℕ)^8283*50000000000000^6235 ≤ 15819278295543^6235*2000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      841046083 2000000000 15819278295543 50000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (31236117/100000000 : ℝ)^8283 ≤ (2664267941641/12500000000000 : ℝ)^6235 := by
    have hnat : (31236117 : ℕ)^8283*12500000000000^6235 ≤ 2664267941641^6235*100000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31236117 100000000 2664267941641 12500000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2834468397/5000000000 : ℝ)^8283 ≤ (47047299855943/100000000000000 : ℝ)^6235 := by
    have hnat : (2834468397 : ℕ)^8283*100000000000000^6235 ≤ 47047299855943^6235*5000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2834468397 5000000000 47047299855943 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8283/2048 : ℝ)) 8283 6235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(841046083/2000000000 : ℝ), (31236117/100000000 : ℝ), (2834468397/5000000000 : ℝ)] ![(15819278295543/50000000000000 : ℝ), (2664267941641/12500000000000 : ℝ), (47047299855943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(841046083/2000000000 : ℝ)|^8283 ≤ (15819278295543/50000000000000 : ℝ)^6235
        have hw : |(841046083/2000000000 : ℝ)|=(841046083/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(31236117/100000000 : ℝ)|^8283 ≤ (2664267941641/12500000000000 : ℝ)^6235
        have hw : |(31236117/100000000 : ℝ)|=(31236117/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2834468397/5000000000 : ℝ)|^8283 ≤ (47047299855943/100000000000000 : ℝ)^6235
        have hw : |(2834468397/5000000000 : ℝ)|=(2834468397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1090_s0_4 (p : ℝ) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-956839703/5000000000 : ℝ)*x 0 + (4807227479/10000000000 : ℝ)*x 1 + (1206378141/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (956839703/5000000000 : ℝ)^8283 ≤ (5558478905031/50000000000000 : ℝ)^6235 := by
    have hnat : (956839703 : ℕ)^8283*50000000000000^6235 ≤ 5558478905031^6235*5000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      956839703 5000000000 5558478905031 50000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4807227479/10000000000 : ℝ)^8283 ≤ (18896316498313/50000000000000 : ℝ)^6235 := by
    have hnat : (4807227479 : ℕ)^8283*50000000000000^6235 ≤ 18896316498313^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4807227479 10000000000 18896316498313 50000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1206378141/2000000000 : ℝ)^8283 ≤ (51090409177931/100000000000000 : ℝ)^6235 := by
    have hnat : (1206378141 : ℕ)^8283*100000000000000^6235 ≤ 51090409177931^6235*2000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1206378141 2000000000 51090409177931 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8283/2048 : ℝ)) 8283 6235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-956839703/5000000000 : ℝ), (4807227479/10000000000 : ℝ), (1206378141/2000000000 : ℝ)] ![(5558478905031/50000000000000 : ℝ), (18896316498313/50000000000000 : ℝ), (51090409177931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-956839703/5000000000 : ℝ)|^8283 ≤ (5558478905031/50000000000000 : ℝ)^6235
        have hw : |(-956839703/5000000000 : ℝ)|=(956839703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4807227479/10000000000 : ℝ)|^8283 ≤ (18896316498313/50000000000000 : ℝ)^6235
        have hw : |(4807227479/10000000000 : ℝ)|=(4807227479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1206378141/2000000000 : ℝ)|^8283 ≤ (51090409177931/100000000000000 : ℝ)^6235
        have hw : |(1206378141/2000000000 : ℝ)|=(1206378141/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1090_s0_5 (p : ℝ) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5168769719/10000000000 : ℝ)*x 0 + (-34841251/250000000 : ℝ)*x 1 + (3015944991/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5168769719/10000000000 : ℝ)^8283 ≤ (41614430187433/100000000000000 : ℝ)^6235 := by
    have hnat : (5168769719 : ℕ)^8283*100000000000000^6235 ≤ 41614430187433^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5168769719 10000000000 41614430187433 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (34841251/250000000 : ℝ)^8283 ≤ (7295168748261/100000000000000 : ℝ)^6235 := by
    have hnat : (34841251 : ℕ)^8283*100000000000000^6235 ≤ 7295168748261^6235*250000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34841251 250000000 7295168748261 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3015944991/5000000000 : ℝ)^8283 ≤ (51090401042597/100000000000000 : ℝ)^6235 := by
    have hnat : (3015944991 : ℕ)^8283*100000000000000^6235 ≤ 51090401042597^6235*5000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3015944991 5000000000 51090401042597 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8283/2048 : ℝ)) 8283 6235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5168769719/10000000000 : ℝ), (-34841251/250000000 : ℝ), (3015944991/5000000000 : ℝ)] ![(41614430187433/100000000000000 : ℝ), (7295168748261/100000000000000 : ℝ), (51090401042597/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5168769719/10000000000 : ℝ)|^8283 ≤ (41614430187433/100000000000000 : ℝ)^6235
        have hw : |(5168769719/10000000000 : ℝ)|=(5168769719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-34841251/250000000 : ℝ)|^8283 ≤ (7295168748261/100000000000000 : ℝ)^6235
        have hw : |(-34841251/250000000 : ℝ)|=(34841251/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3015944991/5000000000 : ℝ)|^8283 ≤ (51090401042597/100000000000000 : ℝ)^6235
        have hw : |(3015944991/5000000000 : ℝ)|=(3015944991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1090_s0_6 (p : ℝ) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5168770189/10000000000 : ℝ)*x 0 + (1206378163/2000000000 : ℝ)*x 1 + (-139364797/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5168770189/10000000000 : ℝ)^8283 ≤ (20807217607199/50000000000000 : ℝ)^6235 := by
    have hnat : (5168770189 : ℕ)^8283*50000000000000^6235 ≤ 20807217607199^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5168770189 10000000000 20807217607199 50000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1206378163/2000000000 : ℝ)^8283 ≤ (51090410415673/100000000000000 : ℝ)^6235 := by
    have hnat : (1206378163 : ℕ)^8283*100000000000000^6235 ≤ 51090410415673^6235*2000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1206378163 2000000000 51090410415673 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (139364797/1000000000 : ℝ)^8283 ≤ (7295154353547/100000000000000 : ℝ)^6235 := by
    have hnat : (139364797 : ℕ)^8283*100000000000000^6235 ≤ 7295154353547^6235*1000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      139364797 1000000000 7295154353547 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8283/2048 : ℝ)) 8283 6235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5168770189/10000000000 : ℝ), (1206378163/2000000000 : ℝ), (-139364797/1000000000 : ℝ)] ![(20807217607199/50000000000000 : ℝ), (51090410415673/100000000000000 : ℝ), (7295154353547/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5168770189/10000000000 : ℝ)|^8283 ≤ (20807217607199/50000000000000 : ℝ)^6235
        have hw : |(5168770189/10000000000 : ℝ)|=(5168770189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1206378163/2000000000 : ℝ)|^8283 ≤ (51090410415673/100000000000000 : ℝ)^6235
        have hw : |(1206378163/2000000000 : ℝ)|=(1206378163/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-139364797/1000000000 : ℝ)|^8283 ≤ (7295154353547/100000000000000 : ℝ)^6235
        have hw : |(-139364797/1000000000 : ℝ)|=(139364797/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1090_s0_7 (p : ℝ) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4215666277/10000000000 : ℝ)*x 0 + (2801615143/5000000000 : ℝ)*x 1 + (1595810687/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4215666277/10000000000 : ℝ)^8283 ≤ (3174290438391/10000000000000 : ℝ)^6235 := by
    have hnat : (4215666277 : ℕ)^8283*10000000000000^6235 ≤ 3174290438391^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4215666277 10000000000 3174290438391 10000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2801615143/5000000000 : ℝ)^8283 ≤ (46324258698549/100000000000000 : ℝ)^6235 := by
    have hnat : (2801615143 : ℕ)^8283*100000000000000^6235 ≤ 46324258698549^6235*5000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2801615143 5000000000 46324258698549 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1595810687/5000000000 : ℝ)^8283 ≤ (5483209225809/25000000000000 : ℝ)^6235 := by
    have hnat : (1595810687 : ℕ)^8283*25000000000000^6235 ≤ 5483209225809^6235*5000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1595810687 5000000000 5483209225809 25000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8283/2048 : ℝ)) 8283 6235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4215666277/10000000000 : ℝ), (2801615143/5000000000 : ℝ), (1595810687/5000000000 : ℝ)] ![(3174290438391/10000000000000 : ℝ), (46324258698549/100000000000000 : ℝ), (5483209225809/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4215666277/10000000000 : ℝ)|^8283 ≤ (3174290438391/10000000000000 : ℝ)^6235
        have hw : |(4215666277/10000000000 : ℝ)|=(4215666277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2801615143/5000000000 : ℝ)|^8283 ≤ (46324258698549/100000000000000 : ℝ)^6235
        have hw : |(2801615143/5000000000 : ℝ)|=(2801615143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1595810687/5000000000 : ℝ)|^8283 ≤ (5483209225809/25000000000000 : ℝ)^6235
        have hw : |(1595810687/5000000000 : ℝ)|=(1595810687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1090_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148460143/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (99/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1751/6250 : ℝ)*pair X 0 0 := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
  have base45 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [sign1]
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
  have hpowlo : (0 : ℝ) ^ (4141/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4141 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4141*1^1024 ≤ 0^1024*1^4141 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4141 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4141 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4141/1024 : ℝ) ≤ (245896511368747371/10000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4141 ≤ (245896511368747371/10000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4141*10000000000000000000^1024 ≤ 245896511368747371^1024*5^4141 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 245896511368747371 10000000000000000000 4141 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (245896511368747371/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4141 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4141/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4141 := by
      have hnat : (1 : ℕ)^1024*1^4141 ≤ 1^4141*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4141 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4141 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10245896511368747371/10000000000000000000 : ℝ) ≤ (1257531413863423/1250000000000000 : ℝ) ^ (4141/1024 : ℝ) := by
    have hpowers : (10245896511368747371/10000000000000000000 : ℝ)^1024 ≤ (1257531413863423/1250000000000000 : ℝ)^4141 := by
      have hnat : (10245896511368747371 : ℕ)^1024*1250000000000000^4141 ≤ 1257531413863423^4141*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10245896511368747371 10000000000000000000 1257531413863423 1250000000000000 1024 4141 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1257531413863423/1250000000000000 : ℝ)) (X := (10245896511368747371/10000000000000000000 : ℝ)) (by norm_num) 4141 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5245896511368747371/5000000000000000000 : ℝ) ≤ (632531413863423/625000000000000 : ℝ) ^ (4141/1024 : ℝ) := by
    have hpowers : (5245896511368747371/5000000000000000000 : ℝ)^1024 ≤ (632531413863423/625000000000000 : ℝ)^4141 := by
      have hnat : (5245896511368747371 : ℕ)^1024*625000000000000^4141 ≤ 632531413863423^4141*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5245896511368747371 5000000000000000000 632531413863423 625000000000000 1024 4141 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (632531413863423/625000000000000 : ℝ)) (X := (5245896511368747371/5000000000000000000 : ℝ)) (by norm_num) 4141 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(7531413863423/500000000000000 : ℝ)*(0 : ℝ))^(4141/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(7531413863423/500000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(245896511368747371/10000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(7531413863423/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4141/1024 : ℝ) := by
    rw [show (1 : ℝ)+(7531413863423/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(1257531413863423/1250000000000000 : ℝ) by norm_num, show 1+(245896511368747371/10000000000000000000 : ℝ)+(0 : ℝ)=(10245896511368747371/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(245896511368747371/10000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(7531413863423/500000000000000 : ℝ)*(2/5 : ℝ))^(4141/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(7531413863423/500000000000000 : ℝ)*(2/5 : ℝ)=(632531413863423/625000000000000 : ℝ) by norm_num, show 1+2*(245896511368747371/10000000000000000000 : ℝ)=(5245896511368747371/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(7531413863423/500000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4141/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (7531413863423/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(7531413863423/500000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4141/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (7531413863423/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(7531413863423/500000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4141/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (7531413863423/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1908378153/10000000000 : ℝ)*X 0 0+(6066427281/10000000000 : ℝ)*X 0 1+(2386930257/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1090_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5519722243/10000000000 : ℝ)*X 1 0+(-2651677627/10000000000 : ℝ)*X 1 1+(1193465171/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1090_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2759860697/5000000000 : ℝ)*X 2 0+(2386930637/5000000000 : ℝ)*X 2 1+(-331459749/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1090_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((841046083/2000000000 : ℝ)*X 0 0+(31236117/100000000 : ℝ)*X 0 1+(2834468397/5000000000 : ℝ)*X 0 2+(841046083/2000000000 : ℝ)*X 1 0+(31236117/100000000 : ℝ)*X 1 1+(2834468397/5000000000 : ℝ)*X 1 2+(841046083/2000000000 : ℝ)*X 2 0+(31236117/100000000 : ℝ)*X 2 1+(2834468397/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1090_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-956839703/5000000000 : ℝ)*X 0 0+(4807227479/10000000000 : ℝ)*X 0 1+(1206378141/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1090_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5168769719/10000000000 : ℝ)*X 1 0+(-34841251/250000000 : ℝ)*X 1 1+(3015944991/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1090_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5168770189/10000000000 : ℝ)*X 2 0+(1206378163/2000000000 : ℝ)*X 2 1+(-139364797/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1090_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4215666277/10000000000 : ℝ)*X 0 0+(2801615143/5000000000 : ℝ)*X 0 1+(1595810687/5000000000 : ℝ)*X 0 2+(4215666277/10000000000 : ℝ)*X 1 0+(2801615143/5000000000 : ℝ)*X 1 1+(1595810687/5000000000 : ℝ)*X 1 2+(4215666277/10000000000 : ℝ)*X 2 0+(2801615143/5000000000 : ℝ)*X 2 1+(1595810687/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1090_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1635841543345594101/1000000000000000000000000 : ℝ) := by norm_num
    linear_combination (108489/160000000000 : ℝ)*(base1) + (9904473/100000000000000 : ℝ)*(base16) + (329478679/100000000000000 : ℝ)*(base19) + (220385561/100000000000000 : ℝ)*(base23) + (94213209/100000000000000 : ℝ)*(upper3) + (291633411204057/50000000000000 : ℝ)*(major0) + (291633411204057/50000000000000 : ℝ)*(major1) + (291633411204057/50000000000000 : ℝ)*(major2) + (193413877574679/25000000000000 : ℝ)*(sp0) + (77365553260179/10000000000000 : ℝ)*(sp1) + (773655651599381/100000000000000 : ℝ)*(sp2) + (392877290207843/100000000000000 : ℝ)*(sp3) + (429491851/100000000000000 : ℝ)*(sp4) + (90072441/25000000000000 : ℝ)*(sp7) + (392877718303231/100000000000000 : ℝ)*(f.failure) + (386827935992471/50000000000000 : ℝ)*(f.sum) + (16890063769611/12500000000000000000000000000 : ℝ)*base65 + (188220429217889/25000000000000000000000000000 : ℝ)*base68 + (6738819917889/25000000000000000000000000000 : ℝ)*base70 + (226629567889/25000000000000000000000000000 : ℝ)*base72 + (5794540582111/12500000000000000000000000000 : ℝ)*base73 + (30028304442889/25000000000000000000000000000 : ℝ)*base76 + (42682683167889/25000000000000000000000000000 : ℝ)*base78 + (82791093442889/25000000000000000000000000000 : ℝ)*base80 + (69002479932111/12500000000000000000000000000 : ℝ)*base81 + (8377967/10000000000000000000000 : ℝ)*base90 + (8377967/10000000000000000000000 : ℝ)*base92 + (8377967/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11806666616421409763043/1562500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1442513141/100000000000000 : ℝ)*(base19) + (230403007/12500000000000 : ℝ)*(base23) + (287578201/100000000000000 : ℝ)*(base39) + (178345977/50000000000000 : ℝ)*(base45) + (4896149/3125000000000 : ℝ)*(upper3) + (176860917/50000000000000 : ℝ)*(upper5) + (38475211010701/6250000000000 : ℝ)*(major0) + (38475211010701/6250000000000 : ℝ)*(major1) + (76950386074127/12500000000000 : ℝ)*(major2) + (34805111/5000000000000 : ℝ)*(sp2) + (102068398932853/12500000000000 : ℝ)*(sp4) + (816545748949683/100000000000000 : ℝ)*(sp5) + (204136234928687/25000000000000 : ℝ)*(sp6) + (414659021425849/100000000000000 : ℝ)*(sp7) + (414659021425849/100000000000000 : ℝ)*(f.failure) + (797409647501/97656250000 : ℝ)*(f.sum) + (2393295254517/6250000000000000000000000000 : ℝ)*base65 + (3752039980779/6250000000000000000000000000 : ℝ)*base68 + (21694669720773/3125000000000000000000000000 : ℝ)*base69 + (2943538355779/6250000000000000000000000000 : ℝ)*base72 + (17598708598267/6250000000000000000000000000 : ℝ)*base73 + (1472404764523/3125000000000000000000000000 : ℝ)*base75 + (2892022606801/1562500000000000000000000000 : ℝ)*base78 + (6252222008273/3125000000000000000000000000 : ℝ)*base79 + (106246401287/390625000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (6436407/10000000000000000000000 : ℝ)*base89 + (6436407/10000000000000000000000 : ℝ)*base91 + (93563593/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1090_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148460143/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (99/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1751/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1090_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1090_s1_0 (p : ℝ) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2116786083/10000000000 : ℝ)*x 0 + (357227681/625000000 : ℝ)*x 1 + (4991196049/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2116786083/10000000000 : ℝ)^8283 ≤ (794443898499/6250000000000 : ℝ)^6235 := by
    have hnat : (2116786083 : ℕ)^8283*6250000000000^6235 ≤ 794443898499^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116786083 10000000000 794443898499 6250000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (357227681/625000000 : ℝ)^8283 ≤ (23781468438767/50000000000000 : ℝ)^6235 := by
    have hnat : (357227681 : ℕ)^8283*50000000000000^6235 ≤ 23781468438767^6235*625000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      357227681 625000000 23781468438767 50000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4991196049/10000000000 : ℝ)^8283 ≤ (39725960742107/100000000000000 : ℝ)^6235 := by
    have hnat : (4991196049 : ℕ)^8283*100000000000000^6235 ≤ 39725960742107^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4991196049 10000000000 39725960742107 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8283/2048 : ℝ)) 8283 6235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2116786083/10000000000 : ℝ), (357227681/625000000 : ℝ), (4991196049/10000000000 : ℝ)] ![(794443898499/6250000000000 : ℝ), (23781468438767/50000000000000 : ℝ), (39725960742107/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2116786083/10000000000 : ℝ)|^8283 ≤ (794443898499/6250000000000 : ℝ)^6235
        have hw : |(-2116786083/10000000000 : ℝ)|=(2116786083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(357227681/625000000 : ℝ)|^8283 ≤ (23781468438767/50000000000000 : ℝ)^6235
        have hw : |(357227681/625000000 : ℝ)|=(357227681/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4991196049/10000000000 : ℝ)|^8283 ≤ (39725960742107/100000000000000 : ℝ)^6235
        have hw : |(4991196049/10000000000 : ℝ)|=(4991196049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1090_s1_1 (p : ℝ) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5421988361/10000000000 : ℝ)*x 0 + (-2508791883/10000000000 : ℝ)*x 1 + (4991196267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5421988361/10000000000 : ℝ)^8283 ≤ (4434432980727/10000000000000 : ℝ)^6235 := by
    have hnat : (5421988361 : ℕ)^8283*10000000000000^6235 ≤ 4434432980727^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5421988361 10000000000 4434432980727 10000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2508791883/10000000000 : ℝ)^8283 ≤ (15929707131191/100000000000000 : ℝ)^6235 := by
    have hnat : (2508791883 : ℕ)^8283*100000000000000^6235 ≤ 15929707131191^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2508791883 10000000000 15929707131191 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4991196267/10000000000 : ℝ)^8283 ≤ (39725963047141/100000000000000 : ℝ)^6235 := by
    have hnat : (4991196267 : ℕ)^8283*100000000000000^6235 ≤ 39725963047141^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4991196267 10000000000 39725963047141 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8283/2048 : ℝ)) 8283 6235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5421988361/10000000000 : ℝ), (-2508791883/10000000000 : ℝ), (4991196267/10000000000 : ℝ)] ![(4434432980727/10000000000000 : ℝ), (15929707131191/100000000000000 : ℝ), (39725963047141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5421988361/10000000000 : ℝ)|^8283 ≤ (4434432980727/10000000000000 : ℝ)^6235
        have hw : |(5421988361/10000000000 : ℝ)|=(5421988361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2508791883/10000000000 : ℝ)|^8283 ≤ (15929707131191/100000000000000 : ℝ)^6235
        have hw : |(-2508791883/10000000000 : ℝ)|=(2508791883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4991196267/10000000000 : ℝ)|^8283 ≤ (39725963047141/100000000000000 : ℝ)^6235
        have hw : |(4991196267/10000000000 : ℝ)|=(4991196267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1090_s1_2 (p : ℝ) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (677748657/1250000000 : ℝ)*x 0 + (4991195349/10000000000 : ℝ)*x 1 + (-2508791881/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (677748657/1250000000 : ℝ)^8283 ≤ (44344339531467/100000000000000 : ℝ)^6235 := by
    have hnat : (677748657 : ℕ)^8283*100000000000000^6235 ≤ 44344339531467^6235*1250000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677748657 1250000000 44344339531467 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4991195349/10000000000 : ℝ)^8283 ≤ (39725953340619/100000000000000 : ℝ)^6235 := by
    have hnat : (4991195349 : ℕ)^8283*100000000000000^6235 ≤ 39725953340619^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4991195349 10000000000 39725953340619 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2508791881/10000000000 : ℝ)^8283 ≤ (199121338929/1250000000000 : ℝ)^6235 := by
    have hnat : (2508791881 : ℕ)^8283*1250000000000^6235 ≤ 199121338929^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2508791881 10000000000 199121338929 1250000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8283/2048 : ℝ)) 8283 6235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(677748657/1250000000 : ℝ), (4991195349/10000000000 : ℝ), (-2508791881/10000000000 : ℝ)] ![(44344339531467/100000000000000 : ℝ), (39725953340619/100000000000000 : ℝ), (199121338929/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(677748657/1250000000 : ℝ)|^8283 ≤ (44344339531467/100000000000000 : ℝ)^6235
        have hw : |(677748657/1250000000 : ℝ)|=(677748657/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4991195349/10000000000 : ℝ)|^8283 ≤ (39725953340619/100000000000000 : ℝ)^6235
        have hw : |(4991195349/10000000000 : ℝ)|=(4991195349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2508791881/10000000000 : ℝ)|^8283 ≤ (199121338929/1250000000000 : ℝ)^6235
        have hw : |(-2508791881/10000000000 : ℝ)|=(2508791881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1090_s1_3 (p : ℝ) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4321808193/10000000000 : ℝ)*x 0 + (3667163989/10000000000 : ℝ)*x 1 + (5093745313/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4321808193/10000000000 : ℝ)^8283 ≤ (32809011223309/100000000000000 : ℝ)^6235 := by
    have hnat : (4321808193 : ℕ)^8283*100000000000000^6235 ≤ 32809011223309^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4321808193 10000000000 32809011223309 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3667163989/10000000000 : ℝ)^8283 ≤ (26377075677999/100000000000000 : ℝ)^6235 := by
    have hnat : (3667163989 : ℕ)^8283*100000000000000^6235 ≤ 26377075677999^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3667163989 10000000000 26377075677999 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5093745313/10000000000 : ℝ)^8283 ≤ (510173913519/1250000000000 : ℝ)^6235 := by
    have hnat : (5093745313 : ℕ)^8283*1250000000000^6235 ≤ 510173913519^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5093745313 10000000000 510173913519 1250000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8283/2048 : ℝ)) 8283 6235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4321808193/10000000000 : ℝ), (3667163989/10000000000 : ℝ), (5093745313/10000000000 : ℝ)] ![(32809011223309/100000000000000 : ℝ), (26377075677999/100000000000000 : ℝ), (510173913519/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4321808193/10000000000 : ℝ)|^8283 ≤ (32809011223309/100000000000000 : ℝ)^6235
        have hw : |(4321808193/10000000000 : ℝ)|=(4321808193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3667163989/10000000000 : ℝ)|^8283 ≤ (26377075677999/100000000000000 : ℝ)^6235
        have hw : |(3667163989/10000000000 : ℝ)|=(3667163989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5093745313/10000000000 : ℝ)|^8283 ≤ (510173913519/1250000000000 : ℝ)^6235
        have hw : |(5093745313/10000000000 : ℝ)|=(5093745313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1090_s1_4 (p : ℝ) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1058833879/5000000000 : ℝ)*x 0 + (500128591/1000000000 : ℝ)*x 1 + (5705349843/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058833879/5000000000 : ℝ)^8283 ≤ (12718136267723/100000000000000 : ℝ)^6235 := by
    have hnat : (1058833879 : ℕ)^8283*100000000000000^6235 ≤ 12718136267723^6235*5000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058833879 5000000000 12718136267723 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (500128591/1000000000 : ℝ)^8283 ≤ (39832681835427/100000000000000 : ℝ)^6235 := by
    have hnat : (500128591 : ℕ)^8283*100000000000000^6235 ≤ 39832681835427^6235*1000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      500128591 1000000000 39832681835427 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5705349843/10000000000 : ℝ)^8283 ≤ (5931147735499/12500000000000 : ℝ)^6235 := by
    have hnat : (5705349843 : ℕ)^8283*12500000000000^6235 ≤ 5931147735499^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5705349843 10000000000 5931147735499 12500000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8283/2048 : ℝ)) 8283 6235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1058833879/5000000000 : ℝ), (500128591/1000000000 : ℝ), (5705349843/10000000000 : ℝ)] ![(12718136267723/100000000000000 : ℝ), (39832681835427/100000000000000 : ℝ), (5931147735499/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1058833879/5000000000 : ℝ)|^8283 ≤ (12718136267723/100000000000000 : ℝ)^6235
        have hw : |(-1058833879/5000000000 : ℝ)|=(1058833879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(500128591/1000000000 : ℝ)|^8283 ≤ (39832681835427/100000000000000 : ℝ)^6235
        have hw : |(500128591/1000000000 : ℝ)|=(500128591/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5705349843/10000000000 : ℝ)|^8283 ≤ (5931147735499/12500000000000 : ℝ)^6235
        have hw : |(5705349843/10000000000 : ℝ)|=(5705349843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1090_s1_5 (p : ℝ) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5236743933/10000000000 : ℝ)*x 0 + (-89731903/500000000 : ℝ)*x 1 + (5705349687/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5236743933/10000000000 : ℝ)^8283 ≤ (8468605115511/20000000000000 : ℝ)^6235 := by
    have hnat : (5236743933 : ℕ)^8283*20000000000000^6235 ≤ 8468605115511^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5236743933 10000000000 8468605115511 20000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (89731903/500000000 : ℝ)^8283 ≤ (10207794255191/100000000000000 : ℝ)^6235 := by
    have hnat : (89731903 : ℕ)^8283*100000000000000^6235 ≤ 10207794255191^6235*500000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89731903 500000000 10207794255191 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5705349687/10000000000 : ℝ)^8283 ≤ (741393440007/1562500000000 : ℝ)^6235 := by
    have hnat : (5705349687 : ℕ)^8283*1562500000000^6235 ≤ 741393440007^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5705349687 10000000000 741393440007 1562500000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8283/2048 : ℝ)) 8283 6235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5236743933/10000000000 : ℝ), (-89731903/500000000 : ℝ), (5705349687/10000000000 : ℝ)] ![(8468605115511/20000000000000 : ℝ), (10207794255191/100000000000000 : ℝ), (741393440007/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5236743933/10000000000 : ℝ)|^8283 ≤ (8468605115511/20000000000000 : ℝ)^6235
        have hw : |(5236743933/10000000000 : ℝ)|=(5236743933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-89731903/500000000 : ℝ)|^8283 ≤ (10207794255191/100000000000000 : ℝ)^6235
        have hw : |(-89731903/500000000 : ℝ)|=(89731903/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5705349687/10000000000 : ℝ)|^8283 ≤ (741393440007/1562500000000 : ℝ)^6235
        have hw : |(5705349687/10000000000 : ℝ)|=(5705349687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1090_s1_6 (p : ℝ) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (327296497/625000000 : ℝ)*x 0 + (5705349807/10000000000 : ℝ)*x 1 + (-1794637857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (327296497/625000000 : ℝ)^8283 ≤ (42343025781647/100000000000000 : ℝ)^6235 := by
    have hnat : (327296497 : ℕ)^8283*100000000000000^6235 ≤ 42343025781647^6235*625000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327296497 625000000 42343025781647 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5705349807/10000000000 : ℝ)^8283 ≤ (47449181486251/100000000000000 : ℝ)^6235 := by
    have hnat : (5705349807 : ℕ)^8283*100000000000000^6235 ≤ 47449181486251^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5705349807 10000000000 47449181486251 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1794637857/10000000000 : ℝ)^8283 ≤ (1275974090159/12500000000000 : ℝ)^6235 := by
    have hnat : (1794637857 : ℕ)^8283*12500000000000^6235 ≤ 1275974090159^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1794637857 10000000000 1275974090159 12500000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8283/2048 : ℝ)) 8283 6235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(327296497/625000000 : ℝ), (5705349807/10000000000 : ℝ), (-1794637857/10000000000 : ℝ)] ![(42343025781647/100000000000000 : ℝ), (47449181486251/100000000000000 : ℝ), (1275974090159/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(327296497/625000000 : ℝ)|^8283 ≤ (42343025781647/100000000000000 : ℝ)^6235
        have hw : |(327296497/625000000 : ℝ)|=(327296497/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5705349807/10000000000 : ℝ)|^8283 ≤ (47449181486251/100000000000000 : ℝ)^6235
        have hw : |(5705349807/10000000000 : ℝ)|=(5705349807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1794637857/10000000000 : ℝ)|^8283 ≤ (1275974090159/12500000000000 : ℝ)^6235
        have hw : |(-1794637857/10000000000 : ℝ)|=(1794637857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1090_s1_7 (p : ℝ) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4323543573/10000000000 : ℝ)*x 0 + (5073877101/10000000000 : ℝ)*x 1 + (460929047/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4323543573/10000000000 : ℝ)^8283 ≤ (8206628450933/25000000000000 : ℝ)^6235 := by
    have hnat : (4323543573 : ℕ)^8283*25000000000000^6235 ≤ 8206628450933^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4323543573 10000000000 8206628450933 25000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5073877101/10000000000 : ℝ)^8283 ≤ (8120512596339/20000000000000 : ℝ)^6235 := by
    have hnat : (5073877101 : ℕ)^8283*20000000000000^6235 ≤ 8120512596339^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5073877101 10000000000 8120512596339 20000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (460929047/1250000000 : ℝ)^8283 ≤ (26570923202323/100000000000000 : ℝ)^6235 := by
    have hnat : (460929047 : ℕ)^8283*100000000000000^6235 ≤ 26570923202323^6235*1250000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      460929047 1250000000 26570923202323 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8283/2048 : ℝ)) 8283 6235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4323543573/10000000000 : ℝ), (5073877101/10000000000 : ℝ), (460929047/1250000000 : ℝ)] ![(8206628450933/25000000000000 : ℝ), (8120512596339/20000000000000 : ℝ), (26570923202323/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4323543573/10000000000 : ℝ)|^8283 ≤ (8206628450933/25000000000000 : ℝ)^6235
        have hw : |(4323543573/10000000000 : ℝ)|=(4323543573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5073877101/10000000000 : ℝ)|^8283 ≤ (8120512596339/20000000000000 : ℝ)^6235
        have hw : |(5073877101/10000000000 : ℝ)|=(5073877101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(460929047/1250000000 : ℝ)|^8283 ≤ (26570923202323/100000000000000 : ℝ)^6235
        have hw : |(460929047/1250000000 : ℝ)|=(460929047/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1090_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148460143/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1751/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (99/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5353/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20677/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1751/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (99/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1751/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (99/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1751/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (99/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1751/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (99/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1751/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (99/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1751/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (99/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (99/50000 : ℝ) ^ (4141/1024 : ℝ) ≤ (1169127479/100000000000000000000 : ℝ) := by
    have hpowers : (99/50000 : ℝ)^4141 ≤ (1169127479/100000000000000000000 : ℝ)^1024 := by
      have hnat : (99 : ℕ)^4141*100000000000000000000^1024 ≤ 1169127479^1024*50000^4141 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        99 50000 1169127479 100000000000000000000 4141 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (99/50000 : ℝ)) (X := (1169127479/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4141 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1751/6250 : ℝ) ^ (4141/1024 : ℝ) ≤ (582559923553267701/100000000000000000000 : ℝ) := by
    have hpowers : (1751/6250 : ℝ)^4141 ≤ (582559923553267701/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1751 : ℕ)^4141*100000000000000000000^1024 ≤ 582559923553267701^1024*6250^4141 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1751 6250 582559923553267701 100000000000000000000 4141 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1751/6250 : ℝ)) (X := (582559923553267701/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4141 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000001169127479/50000000000000000000 : ℝ) ≤ (5000000000028911/5000000000000000 : ℝ) ^ (4141/1024 : ℝ) := by
    have hpowers : (50000000001169127479/50000000000000000000 : ℝ)^1024 ≤ (5000000000028911/5000000000000000 : ℝ)^4141 := by
      have hnat : (50000000001169127479 : ℕ)^1024*5000000000000000^4141 ≤ 5000000000028911^4141*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000001169127479 50000000000000000000 5000000000028911 5000000000000000 1024 4141 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000000028911/5000000000000000 : ℝ)) (X := (50000000001169127479/50000000000000000000 : ℝ)) (by norm_num) 4141 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (5029127996236119759/5000000000000000000 : ℝ) ≤ (5007187127167549/5000000000000000 : ℝ) ^ (4141/1024 : ℝ) := by
    have hpowers : (5029127996236119759/5000000000000000000 : ℝ)^1024 ≤ (5007187127167549/5000000000000000 : ℝ)^4141 := by
      have hnat : (5029127996236119759 : ℕ)^1024*5000000000000000^4141 ≤ 5007187127167549^4141*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5029127996236119759 5000000000000000000 5007187127167549 5000000000000000 1024 4141 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5007187127167549/5000000000000000 : ℝ)) (X := (5029127996236119759/5000000000000000000 : ℝ)) (by norm_num) 4141 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50582559923553267701/50000000000000000000 : ℝ) ≤ (5014374254306187/5000000000000000 : ℝ) ^ (4141/1024 : ℝ) := by
    have hpowers : (50582559923553267701/50000000000000000000 : ℝ)^1024 ≤ (5014374254306187/5000000000000000 : ℝ)^4141 := by
      have hnat : (50582559923553267701 : ℕ)^1024*5000000000000000^4141 ≤ 5014374254306187^4141*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50582559923553267701 50000000000000000000 5014374254306187 5000000000000000 1024 4141 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5014374254306187/5000000000000000 : ℝ)) (X := (50582559923553267701/50000000000000000000 : ℝ)) (by norm_num) 4141 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1169127479/100000000000000000000 : ℝ) ≤ ((2781743077969146911/2781800000000000000 : ℝ)+2*(3593563569319/695450000000000 : ℝ)*(99/50000 : ℝ))^(4141/1024 : ℝ) := by
    rw [show (2781743077969146911/2781800000000000000 : ℝ)+2*(3593563569319/695450000000000 : ℝ)*(99/50000 : ℝ)=(5000000000028911/5000000000000000 : ℝ) by norm_num, show 1+2*(1169127479/100000000000000000000 : ℝ)=(50000000001169127479/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(582559923553267701/100000000000000000000 : ℝ)+(1169127479/100000000000000000000 : ℝ) ≤ ((2781743077969146911/2781800000000000000 : ℝ)+(3593563569319/695450000000000 : ℝ)*((1751/6250 : ℝ)+(99/50000 : ℝ)))^(4141/1024 : ℝ) := by
    rw [show (2781743077969146911/2781800000000000000 : ℝ)+(3593563569319/695450000000000 : ℝ)*((1751/6250 : ℝ)+(99/50000 : ℝ))=(5007187127167549/5000000000000000 : ℝ) by norm_num, show 1+(582559923553267701/100000000000000000000 : ℝ)+(1169127479/100000000000000000000 : ℝ)=(5029127996236119759/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(582559923553267701/100000000000000000000 : ℝ) ≤ ((2781743077969146911/2781800000000000000 : ℝ)+2*(3593563569319/695450000000000 : ℝ)*(1751/6250 : ℝ))^(4141/1024 : ℝ) := by
    rw [show (2781743077969146911/2781800000000000000 : ℝ)+2*(3593563569319/695450000000000 : ℝ)*(1751/6250 : ℝ)=(5014374254306187/5000000000000000 : ℝ) by norm_num, show 1+2*(582559923553267701/100000000000000000000 : ℝ)=(50582559923553267701/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2781743077969146911/2781800000000000000 : ℝ)*(X 1 0+X 2 0)+(3593563569319/695450000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4141/1024 : ℝ)) (lo := (99/50000 : ℝ)) (hi := (1751/6250 : ℝ)) (c := (2781743077969146911/2781800000000000000 : ℝ)) (alpha := (3593563569319/695450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2781743077969146911/2781800000000000000 : ℝ)*(X 0 1+X 2 1)+(3593563569319/695450000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4141/1024 : ℝ)) (lo := (99/50000 : ℝ)) (hi := (1751/6250 : ℝ)) (c := (2781743077969146911/2781800000000000000 : ℝ)) (alpha := (3593563569319/695450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2781743077969146911/2781800000000000000 : ℝ)*(X 0 2+X 1 2)+(3593563569319/695450000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4141/1024 : ℝ)) (lo := (99/50000 : ℝ)) (hi := (1751/6250 : ℝ)) (c := (2781743077969146911/2781800000000000000 : ℝ)) (alpha := (3593563569319/695450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2116786083/10000000000 : ℝ)*X 0 0+(357227681/625000000 : ℝ)*X 0 1+(4991196049/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1090_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5421988361/10000000000 : ℝ)*X 1 0+(-2508791883/10000000000 : ℝ)*X 1 1+(4991196267/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1090_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((677748657/1250000000 : ℝ)*X 2 0+(4991195349/10000000000 : ℝ)*X 2 1+(-2508791881/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1090_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4321808193/10000000000 : ℝ)*X 0 0+(3667163989/10000000000 : ℝ)*X 0 1+(5093745313/10000000000 : ℝ)*X 0 2+(4321808193/10000000000 : ℝ)*X 1 0+(3667163989/10000000000 : ℝ)*X 1 1+(5093745313/10000000000 : ℝ)*X 1 2+(4321808193/10000000000 : ℝ)*X 2 0+(3667163989/10000000000 : ℝ)*X 2 1+(5093745313/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1090_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1058833879/5000000000 : ℝ)*X 0 0+(500128591/1000000000 : ℝ)*X 0 1+(5705349843/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1090_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5236743933/10000000000 : ℝ)*X 1 0+(-89731903/500000000 : ℝ)*X 1 1+(5705349687/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1090_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((327296497/625000000 : ℝ)*X 2 0+(5705349807/10000000000 : ℝ)*X 2 1+(-1794637857/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1090_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4323543573/10000000000 : ℝ)*X 0 0+(5073877101/10000000000 : ℝ)*X 0 1+(460929047/1250000000 : ℝ)*X 0 2+(4323543573/10000000000 : ℝ)*X 1 0+(5073877101/10000000000 : ℝ)*X 1 1+(460929047/1250000000 : ℝ)*X 1 2+(4323543573/10000000000 : ℝ)*X 2 0+(5073877101/10000000000 : ℝ)*X 2 1+(460929047/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1090_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (544118979801228873927529491/69545000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (90050241/50000000000000 : ℝ)*(base1) + (1600655597/100000000000000 : ℝ)*(base19) + (1828512517/100000000000000 : ℝ)*(base23) + (68620157/50000000000000 : ℝ)*(upper3) + (199547313/100000000000000 : ℝ)*(upper5) + (520340760790691/50000000000000 : ℝ)*(major0) + (520340760790691/50000000000000 : ℝ)*(major1) + (520340760790691/50000000000000 : ℝ)*(major2) + (345092678887947/25000000000000 : ℝ)*(sp0) + (1380377402120879/100000000000000 : ℝ)*(sp1) + (690188587131979/50000000000000 : ℝ)*(sp2) + (14019600445463/2000000000000 : ℝ)*(sp3) + (846732517/10000000000000 : ℝ)*(sp4) + (3577213177/100000000000000 : ℝ)*(sp7) + (700983779586809/100000000000000 : ℝ)*(f.failure) + (345094750694119/25000000000000 : ℝ)*(f.sum) + (27163631716401/69545000000000000000000000000 : ℝ)*base65 + (66465105495171501/139090000000000000000000000000000 : ℝ)*base67 + (558233037943761501/139090000000000000000000000000000 : ℝ)*base69 + (137448196645821501/139090000000000000000000000000000 : ℝ)*base71 + (64628003040217/34772500000000000000000000000 : ℝ)*base74 + (177456808545371501/139090000000000000000000000000000 : ℝ)*base75 + (508686927381211501/139090000000000000000000000000000 : ℝ)*base77 + (1769444315855711501/139090000000000000000000000000000 : ℝ)*base79 + (8029051541991/17386250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (54946313/10000000000000000000000 : ℝ)*base90 + (54946313/10000000000000000000000 : ℝ)*base92 + (54946313/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8924563644897525650686281/2483750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (45150461/100000000000000 : ℝ)*(base1) + (163711153/20000000000000 : ℝ)*(base19) + (26187849/3125000000000 : ℝ)*(base23) + (79271971/100000000000000 : ℝ)*(upper3) + (79240069/100000000000000 : ℝ)*(upper5) + (267699380269601/25000000000000 : ℝ)*(major0) + (267699380269601/25000000000000 : ℝ)*(major1) + (267699380269601/25000000000000 : ℝ)*(major2) + (98172231/3125000000000 : ℝ)*(sp1) + (177290397/5000000000000 : ℝ)*(sp2) + (710162804505787/50000000000000 : ℝ)*(sp4) + (355080400948489/25000000000000 : ℝ)*(sp5) + (710160590021003/50000000000000 : ℝ)*(sp6) + (360634656686261/50000000000000 : ℝ)*(sp7) + (721269358522983/100000000000000 : ℝ)*(f.failure) + (1420325563861113/100000000000000 : ℝ)*(f.sum) + (8286711239277/4967500000000000000000000000 : ℝ)*base66 + (18385793126634073/9935000000000000000000000000000 : ℝ)*base67 + (12530957622614073/9935000000000000000000000000000 : ℝ)*base69 + (17313434024394073/9935000000000000000000000000000 : ℝ)*base71 + (18628808852387/4967500000000000000000000000 : ℝ)*base74 + (69563991948624073/9935000000000000000000000000000 : ℝ)*base75 + (14253822692374073/9935000000000000000000000000000 : ℝ)*base77 + (38106023291835927/9935000000000000000000000000000 : ℝ)*base80 + (23969833875057/4967500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (75033431/10000000000000000000000 : ℝ)*base90 + (75033431/10000000000000000000000 : ℝ)*base92 + (75033431/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1090_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148460143/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1751/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (99/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5353/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20677/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1090_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1090_s2_0 (p : ℝ) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2172867893/10000000000 : ℝ)*x 0 + (5520996937/10000000000 : ℝ)*x 1 + (515023501/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2172867893/10000000000 : ℝ)^8283 ≤ (13160420600741/100000000000000 : ℝ)^6235 := by
    have hnat : (2172867893 : ℕ)^8283*100000000000000^6235 ≤ 13160420600741^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2172867893 10000000000 13160420600741 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5520996937/10000000000 : ℝ)^8283 ≤ (45423273469963/100000000000000 : ℝ)^6235 := by
    have hnat : (5520996937 : ℕ)^8283*100000000000000^6235 ≤ 45423273469963^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5520996937 10000000000 45423273469963 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (515023501/1000000000 : ℝ)^8283 ≤ (41416305910377/100000000000000 : ℝ)^6235 := by
    have hnat : (515023501 : ℕ)^8283*100000000000000^6235 ≤ 41416305910377^6235*1000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515023501 1000000000 41416305910377 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8283/2048 : ℝ)) 8283 6235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2172867893/10000000000 : ℝ), (5520996937/10000000000 : ℝ), (515023501/1000000000 : ℝ)] ![(13160420600741/100000000000000 : ℝ), (45423273469963/100000000000000 : ℝ), (41416305910377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2172867893/10000000000 : ℝ)|^8283 ≤ (13160420600741/100000000000000 : ℝ)^6235
        have hw : |(-2172867893/10000000000 : ℝ)|=(2172867893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5520996937/10000000000 : ℝ)|^8283 ≤ (45423273469963/100000000000000 : ℝ)^6235
        have hw : |(5520996937/10000000000 : ℝ)|=(5520996937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(515023501/1000000000 : ℝ)|^8283 ≤ (41416305910377/100000000000000 : ℝ)^6235
        have hw : |(515023501/1000000000 : ℝ)|=(515023501/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1090_s2_1 (p : ℝ) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2688066057/5000000000 : ℝ)*x 0 + (-2366030917/10000000000 : ℝ)*x 1 + (5150235617/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2688066057/5000000000 : ℝ)^8283 ≤ (1370212309619/3125000000000 : ℝ)^6235 := by
    have hnat : (2688066057 : ℕ)^8283*3125000000000^6235 ≤ 1370212309619^6235*5000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688066057 5000000000 1370212309619 3125000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2366030917/10000000000 : ℝ)^8283 ≤ (14736893677773/100000000000000 : ℝ)^6235 := by
    have hnat : (2366030917 : ℕ)^8283*100000000000000^6235 ≤ 14736893677773^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2366030917 10000000000 14736893677773 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5150235617/10000000000 : ℝ)^8283 ≤ (41416312394993/100000000000000 : ℝ)^6235 := by
    have hnat : (5150235617 : ℕ)^8283*100000000000000^6235 ≤ 41416312394993^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5150235617 10000000000 41416312394993 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8283/2048 : ℝ)) 8283 6235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2688066057/5000000000 : ℝ), (-2366030917/10000000000 : ℝ), (5150235617/10000000000 : ℝ)] ![(1370212309619/3125000000000 : ℝ), (14736893677773/100000000000000 : ℝ), (41416312394993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2688066057/5000000000 : ℝ)|^8283 ≤ (1370212309619/3125000000000 : ℝ)^6235
        have hw : |(2688066057/5000000000 : ℝ)|=(2688066057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2366030917/10000000000 : ℝ)|^8283 ≤ (14736893677773/100000000000000 : ℝ)^6235
        have hw : |(-2366030917/10000000000 : ℝ)|=(2366030917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5150235617/10000000000 : ℝ)|^8283 ≤ (41416312394993/100000000000000 : ℝ)^6235
        have hw : |(5150235617/10000000000 : ℝ)|=(5150235617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1090_s2_2 (p : ℝ) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5376132229/10000000000 : ℝ)*x 0 + (5150235483/10000000000 : ℝ)*x 1 + (-118301547/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5376132229/10000000000 : ℝ)^8283 ≤ (8769359030761/20000000000000 : ℝ)^6235 := by
    have hnat : (5376132229 : ℕ)^8283*20000000000000^6235 ≤ 8769359030761^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376132229 10000000000 8769359030761 20000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5150235483/10000000000 : ℝ)^8283 ≤ (41416310963463/100000000000000 : ℝ)^6235 := by
    have hnat : (5150235483 : ℕ)^8283*100000000000000^6235 ≤ 41416310963463^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5150235483 10000000000 41416310963463 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (118301547/500000000 : ℝ)^8283 ≤ (3684223467021/25000000000000 : ℝ)^6235 := by
    have hnat : (118301547 : ℕ)^8283*25000000000000^6235 ≤ 3684223467021^6235*500000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      118301547 500000000 3684223467021 25000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8283/2048 : ℝ)) 8283 6235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5376132229/10000000000 : ℝ), (5150235483/10000000000 : ℝ), (-118301547/500000000 : ℝ)] ![(8769359030761/20000000000000 : ℝ), (41416310963463/100000000000000 : ℝ), (3684223467021/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5376132229/10000000000 : ℝ)|^8283 ≤ (8769359030761/20000000000000 : ℝ)^6235
        have hw : |(5376132229/10000000000 : ℝ)|=(5376132229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5150235483/10000000000 : ℝ)|^8283 ≤ (41416310963463/100000000000000 : ℝ)^6235
        have hw : |(5150235483/10000000000 : ℝ)|=(5150235483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-118301547/500000000 : ℝ)|^8283 ≤ (3684223467021/25000000000000 : ℝ)^6235
        have hw : |(-118301547/500000000 : ℝ)|=(118301547/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1090_s2_3 (p : ℝ) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2180069589/5000000000 : ℝ)*x 0 + (4010412961/10000000000 : ℝ)*x 1 + (2370258511/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2180069589/5000000000 : ℝ)^8283 ≤ (16598071905953/50000000000000 : ℝ)^6235 := by
    have hnat : (2180069589 : ℕ)^8283*50000000000000^6235 ≤ 16598071905953^6235*5000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180069589 5000000000 16598071905953 50000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4010412961/10000000000 : ℝ)^8283 ≤ (29706349229317/100000000000000 : ℝ)^6235 := by
    have hnat : (4010412961 : ℕ)^8283*100000000000000^6235 ≤ 29706349229317^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4010412961 10000000000 29706349229317 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2370258511/5000000000 : ℝ)^8283 ≤ (37097506941161/100000000000000 : ℝ)^6235 := by
    have hnat : (2370258511 : ℕ)^8283*100000000000000^6235 ≤ 37097506941161^6235*5000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2370258511 5000000000 37097506941161 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8283/2048 : ℝ)) 8283 6235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2180069589/5000000000 : ℝ), (4010412961/10000000000 : ℝ), (2370258511/5000000000 : ℝ)] ![(16598071905953/50000000000000 : ℝ), (29706349229317/100000000000000 : ℝ), (37097506941161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2180069589/5000000000 : ℝ)|^8283 ≤ (16598071905953/50000000000000 : ℝ)^6235
        have hw : |(2180069589/5000000000 : ℝ)|=(2180069589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4010412961/10000000000 : ℝ)|^8283 ≤ (29706349229317/100000000000000 : ℝ)^6235
        have hw : |(4010412961/10000000000 : ℝ)|=(4010412961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2370258511/5000000000 : ℝ)|^8283 ≤ (37097506941161/100000000000000 : ℝ)^6235
        have hw : |(2370258511/5000000000 : ℝ)|=(2370258511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1090_s2_4 (p : ℝ) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1086492951/5000000000 : ℝ)*x 0 + (5152886743/10000000000 : ℝ)*x 1 + (17244743/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1086492951/5000000000 : ℝ)^8283 ≤ (13161370126289/100000000000000 : ℝ)^6235 := by
    have hnat : (1086492951 : ℕ)^8283*100000000000000^6235 ≤ 13161370126289^6235*5000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086492951 5000000000 13161370126289 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5152886743/10000000000 : ℝ)^8283 ≤ (4144463691847/10000000000000 : ℝ)^6235 := by
    have hnat : (5152886743 : ℕ)^8283*10000000000000^6235 ≤ 4144463691847^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152886743 10000000000 4144463691847 10000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (17244743/31250000 : ℝ)^8283 ≤ (22696996470609/50000000000000 : ℝ)^6235 := by
    have hnat : (17244743 : ℕ)^8283*50000000000000^6235 ≤ 22696996470609^6235*31250000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17244743 31250000 22696996470609 50000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8283/2048 : ℝ)) 8283 6235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1086492951/5000000000 : ℝ), (5152886743/10000000000 : ℝ), (17244743/31250000 : ℝ)] ![(13161370126289/100000000000000 : ℝ), (4144463691847/10000000000000 : ℝ), (22696996470609/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1086492951/5000000000 : ℝ)|^8283 ≤ (13161370126289/100000000000000 : ℝ)^6235
        have hw : |(-1086492951/5000000000 : ℝ)|=(1086492951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5152886743/10000000000 : ℝ)|^8283 ≤ (4144463691847/10000000000000 : ℝ)^6235
        have hw : |(5152886743/10000000000 : ℝ)|=(5152886743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(17244743/31250000 : ℝ)|^8283 ≤ (22696996470609/50000000000000 : ℝ)^6235
        have hw : |(17244743/31250000 : ℝ)|=(17244743/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1090_s2_5 (p : ℝ) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5282391353/10000000000 : ℝ)*x 0 + (-1997948643/10000000000 : ℝ)*x 1 + (5518317851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5282391353/10000000000 : ℝ)^8283 ≤ (42834055624349/100000000000000 : ℝ)^6235 := by
    have hnat : (5282391353 : ℕ)^8283*100000000000000^6235 ≤ 42834055624349^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282391353 10000000000 42834055624349 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1997948643/10000000000 : ℝ)^8283 ≤ (11771950426781/100000000000000 : ℝ)^6235 := by
    have hnat : (1997948643 : ℕ)^8283*100000000000000^6235 ≤ 11771950426781^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1997948643 10000000000 11771950426781 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5518317851/10000000000 : ℝ)^8283 ≤ (45393993935671/100000000000000 : ℝ)^6235 := by
    have hnat : (5518317851 : ℕ)^8283*100000000000000^6235 ≤ 45393993935671^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5518317851 10000000000 45393993935671 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8283/2048 : ℝ)) 8283 6235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5282391353/10000000000 : ℝ), (-1997948643/10000000000 : ℝ), (5518317851/10000000000 : ℝ)] ![(42834055624349/100000000000000 : ℝ), (11771950426781/100000000000000 : ℝ), (45393993935671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5282391353/10000000000 : ℝ)|^8283 ≤ (42834055624349/100000000000000 : ℝ)^6235
        have hw : |(5282391353/10000000000 : ℝ)|=(5282391353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1997948643/10000000000 : ℝ)|^8283 ≤ (11771950426781/100000000000000 : ℝ)^6235
        have hw : |(-1997948643/10000000000 : ℝ)|=(1997948643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5518317851/10000000000 : ℝ)|^8283 ≤ (45393993935671/100000000000000 : ℝ)^6235
        have hw : |(5518317851/10000000000 : ℝ)|=(5518317851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1090_s2_6 (p : ℝ) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (660298943/1250000000 : ℝ)*x 0 + (689789721/1250000000 : ℝ)*x 1 + (-1997948497/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (660298943/1250000000 : ℝ)^8283 ≤ (8566811536373/20000000000000 : ℝ)^6235 := by
    have hnat : (660298943 : ℕ)^8283*20000000000000^6235 ≤ 8566811536373^6235*1250000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660298943 1250000000 8566811536373 20000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (689789721/1250000000 : ℝ)^8283 ≤ (45393993028643/100000000000000 : ℝ)^6235 := by
    have hnat : (689789721 : ℕ)^8283*100000000000000^6235 ≤ 45393993028643^6235*1250000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      689789721 1250000000 45393993028643 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1997948497/10000000000 : ℝ)^8283 ≤ (11771949283987/100000000000000 : ℝ)^6235 := by
    have hnat : (1997948497 : ℕ)^8283*100000000000000^6235 ≤ 11771949283987^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1997948497 10000000000 11771949283987 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8283/2048 : ℝ)) 8283 6235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(660298943/1250000000 : ℝ), (689789721/1250000000 : ℝ), (-1997948497/10000000000 : ℝ)] ![(8566811536373/20000000000000 : ℝ), (45393993028643/100000000000000 : ℝ), (11771949283987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(660298943/1250000000 : ℝ)|^8283 ≤ (8566811536373/20000000000000 : ℝ)^6235
        have hw : |(660298943/1250000000 : ℝ)|=(660298943/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(689789721/1250000000 : ℝ)|^8283 ≤ (45393993028643/100000000000000 : ℝ)^6235
        have hw : |(689789721/1250000000 : ℝ)|=(689789721/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1997948497/10000000000 : ℝ)|^8283 ≤ (11771949283987/100000000000000 : ℝ)^6235
        have hw : |(-1997948497/10000000000 : ℝ)|=(1997948497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1090_s2_7 (p : ℝ) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2180185909/5000000000 : ℝ)*x 0 + (947059183/2000000000 : ℝ)*x 1 + (4015687669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2180185909/5000000000 : ℝ)^8283 ≤ (16599248418837/50000000000000 : ℝ)^6235 := by
    have hnat : (2180185909 : ℕ)^8283*50000000000000^6235 ≤ 16599248418837^6235*5000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180185909 5000000000 16599248418837 50000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (947059183/2000000000 : ℝ)^8283 ≤ (37043237640123/100000000000000 : ℝ)^6235 := by
    have hnat : (947059183 : ℕ)^8283*100000000000000^6235 ≤ 37043237640123^6235*2000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      947059183 2000000000 37043237640123 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4015687669/10000000000 : ℝ)^8283 ≤ (14879132755937/50000000000000 : ℝ)^6235 := by
    have hnat : (4015687669 : ℕ)^8283*50000000000000^6235 ≤ 14879132755937^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4015687669 10000000000 14879132755937 50000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8283/2048 : ℝ)) 8283 6235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2180185909/5000000000 : ℝ), (947059183/2000000000 : ℝ), (4015687669/10000000000 : ℝ)] ![(16599248418837/50000000000000 : ℝ), (37043237640123/100000000000000 : ℝ), (14879132755937/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2180185909/5000000000 : ℝ)|^8283 ≤ (16599248418837/50000000000000 : ℝ)^6235
        have hw : |(2180185909/5000000000 : ℝ)|=(2180185909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(947059183/2000000000 : ℝ)|^8283 ≤ (37043237640123/100000000000000 : ℝ)^6235
        have hw : |(947059183/2000000000 : ℝ)|=(947059183/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4015687669/10000000000 : ℝ)|^8283 ≤ (14879132755937/50000000000000 : ℝ)^6235
        have hw : |(4015687669/10000000000 : ℝ)|=(4015687669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1090_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148460143/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20677/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5353/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2207/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16663/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20677/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5353/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20677/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5353/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20677/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5353/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20677/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5353/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20677/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5353/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20677/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5353/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5353/100000 : ℝ) ^ (4141/1024 : ℝ) ≤ (180491515183203/25000000000000000000 : ℝ) := by
    have hpowers : (5353/100000 : ℝ)^4141 ≤ (180491515183203/25000000000000000000 : ℝ)^1024 := by
      have hnat : (5353 : ℕ)^4141*25000000000000000000^1024 ≤ 180491515183203^1024*100000^4141 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5353 100000 180491515183203 25000000000000000000 4141 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5353/100000 : ℝ)) (X := (180491515183203/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4141 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (20677/100000 : ℝ) ^ (4141/1024 : ℝ) ≤ (170556783248154997/100000000000000000000 : ℝ) := by
    have hpowers : (20677/100000 : ℝ)^4141 ≤ (170556783248154997/100000000000000000000 : ℝ)^1024 := by
      have hnat : (20677 : ℕ)^4141*100000000000000000000^1024 ≤ 170556783248154997^1024*100000^4141 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20677 100000 170556783248154997 100000000000000000000 4141 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20677/100000 : ℝ)) (X := (170556783248154997/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4141 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500180491515183203/12500000000000000000 : ℝ) ≤ (10000035705830893/10000000000000000 : ℝ) ^ (4141/1024 : ℝ) := by
    have hpowers : (12500180491515183203/12500000000000000000 : ℝ)^1024 ≤ (10000035705830893/10000000000000000 : ℝ)^4141 := by
      have hnat : (12500180491515183203 : ℕ)^1024*10000000000000000^4141 ≤ 10000035705830893^4141*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500180491515183203 12500000000000000000 10000035705830893 10000000000000000 1024 4141 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000035705830893/10000000000000000 : ℝ)) (X := (12500180491515183203/12500000000000000000 : ℝ)) (by norm_num) 4141 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100171278749308887809/100000000000000000000 : ℝ) ≤ (10004232709307441/10000000000000000 : ℝ) ^ (4141/1024 : ℝ) := by
    have hpowers : (100171278749308887809/100000000000000000000 : ℝ)^1024 ≤ (10004232709307441/10000000000000000 : ℝ)^4141 := by
      have hnat : (100171278749308887809 : ℕ)^1024*10000000000000000^4141 ≤ 10004232709307441^4141*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100171278749308887809 100000000000000000000 10004232709307441 10000000000000000 1024 4141 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004232709307441/10000000000000000 : ℝ)) (X := (100171278749308887809/100000000000000000000 : ℝ)) (by norm_num) 4141 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50170556783248154997/50000000000000000000 : ℝ) ≤ (10008429712783989/10000000000000000 : ℝ) ^ (4141/1024 : ℝ) := by
    have hpowers : (50170556783248154997/50000000000000000000 : ℝ)^1024 ≤ (10008429712783989/10000000000000000 : ℝ)^4141 := by
      have hnat : (50170556783248154997 : ℕ)^1024*10000000000000000^4141 ≤ 10008429712783989^4141*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50170556783248154997 50000000000000000000 10008429712783989 10000000000000000 1024 4141 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10008429712783989/10000000000000000 : ℝ)) (X := (50170556783248154997/50000000000000000000 : ℝ)) (by norm_num) 4141 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(180491515183203/25000000000000000000 : ℝ) ≤ ((38298903509233170361/38310000000000000000 : ℝ)+2*(1049250869137/383100000000000 : ℝ)*(5353/100000 : ℝ))^(4141/1024 : ℝ) := by
    rw [show (38298903509233170361/38310000000000000000 : ℝ)+2*(1049250869137/383100000000000 : ℝ)*(5353/100000 : ℝ)=(10000035705830893/10000000000000000 : ℝ) by norm_num, show 1+2*(180491515183203/25000000000000000000 : ℝ)=(12500180491515183203/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(170556783248154997/100000000000000000000 : ℝ)+(180491515183203/25000000000000000000 : ℝ) ≤ ((38298903509233170361/38310000000000000000 : ℝ)+(1049250869137/383100000000000 : ℝ)*((20677/100000 : ℝ)+(5353/100000 : ℝ)))^(4141/1024 : ℝ) := by
    rw [show (38298903509233170361/38310000000000000000 : ℝ)+(1049250869137/383100000000000 : ℝ)*((20677/100000 : ℝ)+(5353/100000 : ℝ))=(10004232709307441/10000000000000000 : ℝ) by norm_num, show 1+(170556783248154997/100000000000000000000 : ℝ)+(180491515183203/25000000000000000000 : ℝ)=(100171278749308887809/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(170556783248154997/100000000000000000000 : ℝ) ≤ ((38298903509233170361/38310000000000000000 : ℝ)+2*(1049250869137/383100000000000 : ℝ)*(20677/100000 : ℝ))^(4141/1024 : ℝ) := by
    rw [show (38298903509233170361/38310000000000000000 : ℝ)+2*(1049250869137/383100000000000 : ℝ)*(20677/100000 : ℝ)=(10008429712783989/10000000000000000 : ℝ) by norm_num, show 1+2*(170556783248154997/100000000000000000000 : ℝ)=(50170556783248154997/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (38298903509233170361/38310000000000000000 : ℝ)*(X 1 0+X 2 0)+(1049250869137/383100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4141/1024 : ℝ)) (lo := (5353/100000 : ℝ)) (hi := (20677/100000 : ℝ)) (c := (38298903509233170361/38310000000000000000 : ℝ)) (alpha := (1049250869137/383100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (38298903509233170361/38310000000000000000 : ℝ)*(X 0 1+X 2 1)+(1049250869137/383100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4141/1024 : ℝ)) (lo := (5353/100000 : ℝ)) (hi := (20677/100000 : ℝ)) (c := (38298903509233170361/38310000000000000000 : ℝ)) (alpha := (1049250869137/383100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (38298903509233170361/38310000000000000000 : ℝ)*(X 0 2+X 1 2)+(1049250869137/383100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4141/1024 : ℝ)) (lo := (5353/100000 : ℝ)) (hi := (20677/100000 : ℝ)) (c := (38298903509233170361/38310000000000000000 : ℝ)) (alpha := (1049250869137/383100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2172867893/10000000000 : ℝ)*X 0 0+(5520996937/10000000000 : ℝ)*X 0 1+(515023501/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1090_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2688066057/5000000000 : ℝ)*X 1 0+(-2366030917/10000000000 : ℝ)*X 1 1+(5150235617/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1090_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5376132229/10000000000 : ℝ)*X 2 0+(5150235483/10000000000 : ℝ)*X 2 1+(-118301547/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1090_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2180069589/5000000000 : ℝ)*X 0 0+(4010412961/10000000000 : ℝ)*X 0 1+(2370258511/5000000000 : ℝ)*X 0 2+(2180069589/5000000000 : ℝ)*X 1 0+(4010412961/10000000000 : ℝ)*X 1 1+(2370258511/5000000000 : ℝ)*X 1 2+(2180069589/5000000000 : ℝ)*X 2 0+(4010412961/10000000000 : ℝ)*X 2 1+(2370258511/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1090_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1086492951/5000000000 : ℝ)*X 0 0+(5152886743/10000000000 : ℝ)*X 0 1+(17244743/31250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1090_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5282391353/10000000000 : ℝ)*X 1 0+(-1997948643/10000000000 : ℝ)*X 1 1+(5518317851/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1090_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((660298943/1250000000 : ℝ)*X 2 0+(689789721/1250000000 : ℝ)*X 2 1+(-1997948497/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1090_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2180185909/5000000000 : ℝ)*X 0 0+(947059183/2000000000 : ℝ)*X 0 1+(4015687669/10000000000 : ℝ)*X 0 2+(2180185909/5000000000 : ℝ)*X 1 0+(947059183/2000000000 : ℝ)*X 1 1+(4015687669/10000000000 : ℝ)*X 1 2+(2180185909/5000000000 : ℝ)*X 2 0+(947059183/2000000000 : ℝ)*X 2 1+(4015687669/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1090_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (235537031669725752780838107/31925000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1275824187/100000000000000 : ℝ)*(base19) + (327966259/25000000000000 : ℝ)*(base23) + (727597/6250000000000 : ℝ)*(lower2) + (73025379/50000000000000 : ℝ)*(upper3) + (12623779/10000000000000 : ℝ)*(upper5) + (101671647949929/5000000000000 : ℝ)*(major0) + (101671647949929/5000000000000 : ℝ)*(major1) + (101671647949929/5000000000000 : ℝ)*(major2) + (1348582819532359/50000000000000 : ℝ)*(sp0) + (674295413295469/25000000000000 : ℝ)*(sp1) + (1348590808570513/50000000000000 : ℝ)*(sp2) + (684837524437261/50000000000000 : ℝ)*(sp3) + (3457988269/20000000000000 : ℝ)*(sp4) + (7694189103/100000000000000 : ℝ)*(sp7) + (10957461944509/800000000000 : ℝ)*(f.failure) + (1348591464503031/50000000000000 : ℝ)*(f.sum) + (623342424449/638500000000000000000000000 : ℝ)*base66 + (517045062773081877/63850000000000000000000000000000 : ℝ)*base68 + (299175887367631877/63850000000000000000000000000000 : ℝ)*base70 + (450241109310181877/63850000000000000000000000000000 : ℝ)*base72 + (3547264087549/1277000000000000000000000000 : ℝ)*base73 + (387474889568831877/63850000000000000000000000000000 : ℝ)*base76 + (122713664906681877/63850000000000000000000000000000 : ℝ)*base78 + (108364674902531877/63850000000000000000000000000000 : ℝ)*base80 + (3310489429063/1277000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (204787/80000000000000000000 : ℝ)*base89 + (204787/80000000000000000000 : ℝ)*base91 + (204787/80000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (412756785892465033941848463/63850000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1275873637/100000000000000 : ℝ)*(base19) + (299990719/20000000000000 : ℝ)*(base23) + (45203641/25000000000000 : ℝ)*(upper3) + (40067193/100000000000000 : ℝ)*(lower4) + (31286643/25000000000000 : ℝ)*(upper5) + (412613947901417/20000000000000 : ℝ)*(major0) + (412613947901417/20000000000000 : ℝ)*(major1) + (412613947901417/20000000000000 : ℝ)*(major2) + (2824732497/25000000000000 : ℝ)*(sp1) + (175951667/1250000000000 : ℝ)*(sp2) + (1368246867279093/50000000000000 : ℝ)*(sp4) + (8551503624233/312500000000 : ℝ)*(sp5) + (273647815847123/10000000000000 : ℝ)*(sp6) + (694822764486723/50000000000000 : ℝ)*(sp7) + (694822764486723/50000000000000 : ℝ)*(f.failure) + (1368246867279093/50000000000000 : ℝ)*(f.sum) + (15243656271593/3831000000000000000000000000 : ℝ)*base65 + (798515738558398463/766200000000000000000000000000000 : ℝ)*base68 + (909865501916401537/766200000000000000000000000000000 : ℝ)*base69 + (5734490207239201537/766200000000000000000000000000000 : ℝ)*base71 + (754471743701/766200000000000000000000000 : ℝ)*base74 + (4084653668221201537/766200000000000000000000000000000 : ℝ)*base75 + (4166397356421601537/766200000000000000000000000000000 : ℝ)*base77 + (3234531720925201537/766200000000000000000000000000000 : ℝ)*base79 + (151062924731/766200000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (31818611/5000000000000000000000 : ℝ)*base90 + (31818611/5000000000000000000000 : ℝ)*base92 + (31818611/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1090_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148460143/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20677/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5353/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2207/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16663/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1090_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1090_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148460143/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2207/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16663/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1090_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1090_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1090_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148460143/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2207/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16663/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1090_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
