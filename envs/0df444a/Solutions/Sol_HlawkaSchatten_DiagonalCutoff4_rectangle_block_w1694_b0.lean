-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1694_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:39:34.184944+00:00
-- url     : https://prove2.me/submissions/ea488cef-ce02-41f5-96db-b1abb8878d7f

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
theorem support_rectangle_w1694_s0_0 (p : ℝ) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-55402241/400000000 : ℝ)*x 0 + (5731035941/10000000000 : ℝ)*x 1 + (1235630957/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (55402241/400000000 : ℝ)^5175 ≤ (2126268157457/25000000000000 : ℝ)^4151 := by
    have hnat : (55402241 : ℕ)^5175*25000000000000^4151 ≤ 2126268157457^4151*400000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55402241 400000000 2126268157457 25000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5731035941/10000000000 : ℝ)^5175 ≤ (24978264563501/50000000000000 : ℝ)^4151 := by
    have hnat : (5731035941 : ℕ)^5175*50000000000000^4151 ≤ 24978264563501^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5731035941 10000000000 24978264563501 50000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1235630957/2500000000 : ℝ)^5175 ≤ (5192299777847/12500000000000 : ℝ)^4151 := by
    have hnat : (1235630957 : ℕ)^5175*12500000000000^4151 ≤ 5192299777847^4151*2500000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1235630957 2500000000 5192299777847 12500000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5175/1024 : ℝ)) 5175 4151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-55402241/400000000 : ℝ), (5731035941/10000000000 : ℝ), (1235630957/2500000000 : ℝ)] ![(2126268157457/25000000000000 : ℝ), (24978264563501/50000000000000 : ℝ), (5192299777847/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-55402241/400000000 : ℝ)|^5175 ≤ (2126268157457/25000000000000 : ℝ)^4151
        have hw : |(-55402241/400000000 : ℝ)|=(55402241/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5731035941/10000000000 : ℝ)|^5175 ≤ (24978264563501/50000000000000 : ℝ)^4151
        have hw : |(5731035941/10000000000 : ℝ)|=(5731035941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1235630957/2500000000 : ℝ)|^5175 ≤ (5192299777847/12500000000000 : ℝ)^4151
        have hw : |(1235630957/2500000000 : ℝ)|=(1235630957/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1694_s0_1 (p : ℝ) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2707839343/5000000000 : ℝ)*x 0 + (-226794099/1250000000 : ℝ)*x 1 + (988504979/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2707839343/5000000000 : ℝ)^5175 ≤ (9310615038271/20000000000000 : ℝ)^4151 := by
    have hnat : (2707839343 : ℕ)^5175*20000000000000^4151 ≤ 9310615038271^4151*5000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707839343 5000000000 9310615038271 20000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (226794099/1250000000 : ℝ)^5175 ≤ (2381703079141/20000000000000 : ℝ)^4151 := by
    have hnat : (226794099 : ℕ)^5175*20000000000000^4151 ≤ 2381703079141^4151*1250000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226794099 1250000000 2381703079141 20000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (988504979/2000000000 : ℝ)^5175 ≤ (41538409402293/100000000000000 : ℝ)^4151 := by
    have hnat : (988504979 : ℕ)^5175*100000000000000^4151 ≤ 41538409402293^4151*2000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      988504979 2000000000 41538409402293 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5175/1024 : ℝ)) 5175 4151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2707839343/5000000000 : ℝ), (-226794099/1250000000 : ℝ), (988504979/2000000000 : ℝ)] ![(9310615038271/20000000000000 : ℝ), (2381703079141/20000000000000 : ℝ), (41538409402293/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2707839343/5000000000 : ℝ)|^5175 ≤ (9310615038271/20000000000000 : ℝ)^4151
        have hw : |(2707839343/5000000000 : ℝ)|=(2707839343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-226794099/1250000000 : ℝ)|^5175 ≤ (2381703079141/20000000000000 : ℝ)^4151
        have hw : |(-226794099/1250000000 : ℝ)|=(226794099/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(988504979/2000000000 : ℝ)|^5175 ≤ (41538409402293/100000000000000 : ℝ)^4151
        have hw : |(988504979/2000000000 : ℝ)|=(988504979/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1694_s0_2 (p : ℝ) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (676960147/1250000000 : ℝ)*x 0 + (4942523971/10000000000 : ℝ)*x 1 + (-907175357/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (676960147/1250000000 : ℝ)^5175 ≤ (931062037509/2000000000000 : ℝ)^4151 := by
    have hnat : (676960147 : ℕ)^5175*2000000000000^4151 ≤ 931062037509^4151*1250000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676960147 1250000000 931062037509 2000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4942523971/10000000000 : ℝ)^5175 ≤ (20769199860531/50000000000000 : ℝ)^4151 := by
    have hnat : (4942523971 : ℕ)^5175*50000000000000^4151 ≤ 20769199860531^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4942523971 10000000000 20769199860531 50000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (907175357/5000000000 : ℝ)^5175 ≤ (11908498392179/100000000000000 : ℝ)^4151 := by
    have hnat : (907175357 : ℕ)^5175*100000000000000^4151 ≤ 11908498392179^4151*5000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      907175357 5000000000 11908498392179 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5175/1024 : ℝ)) 5175 4151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(676960147/1250000000 : ℝ), (4942523971/10000000000 : ℝ), (-907175357/5000000000 : ℝ)] ![(931062037509/2000000000000 : ℝ), (20769199860531/50000000000000 : ℝ), (11908498392179/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(676960147/1250000000 : ℝ)|^5175 ≤ (931062037509/2000000000000 : ℝ)^4151
        have hw : |(676960147/1250000000 : ℝ)|=(676960147/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4942523971/10000000000 : ℝ)|^5175 ≤ (20769199860531/50000000000000 : ℝ)^4151
        have hw : |(4942523971/10000000000 : ℝ)|=(4942523971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-907175357/5000000000 : ℝ)|^5175 ≤ (11908498392179/100000000000000 : ℝ)^4151
        have hw : |(-907175357/5000000000 : ℝ)|=(907175357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1694_s0_3 (p : ℝ) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4053173343/10000000000 : ℝ)*x 0 + (381206853/1250000000 : ℝ)*x 1 + (1313119919/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4053173343/10000000000 : ℝ)^5175 ≤ (32437183144057/100000000000000 : ℝ)^4151 := by
    have hnat : (4053173343 : ℕ)^5175*100000000000000^4151 ≤ 32437183144057^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4053173343 10000000000 32437183144057 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (381206853/1250000000 : ℝ)^5175 ≤ (1422007122367/6250000000000 : ℝ)^4151 := by
    have hnat : (381206853 : ℕ)^5175*6250000000000^4151 ≤ 1422007122367^4151*1250000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      381206853 1250000000 1422007122367 6250000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1313119919/2500000000 : ℝ)^5175 ≤ (11202675720539/25000000000000 : ℝ)^4151 := by
    have hnat : (1313119919 : ℕ)^5175*25000000000000^4151 ≤ 11202675720539^4151*2500000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313119919 2500000000 11202675720539 25000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5175/1024 : ℝ)) 5175 4151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4053173343/10000000000 : ℝ), (381206853/1250000000 : ℝ), (1313119919/2500000000 : ℝ)] ![(32437183144057/100000000000000 : ℝ), (1422007122367/6250000000000 : ℝ), (11202675720539/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4053173343/10000000000 : ℝ)|^5175 ≤ (32437183144057/100000000000000 : ℝ)^4151
        have hw : |(4053173343/10000000000 : ℝ)|=(4053173343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(381206853/1250000000 : ℝ)|^5175 ≤ (1422007122367/6250000000000 : ℝ)^4151
        have hw : |(381206853/1250000000 : ℝ)|=(381206853/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1313119919/2500000000 : ℝ)|^5175 ≤ (11202675720539/25000000000000 : ℝ)^4151
        have hw : |(1313119919/2500000000 : ℝ)|=(1313119919/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1694_s0_4 (p : ℝ) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-277398591/2000000000 : ℝ)*x 0 + (4962234881/10000000000 : ℝ)*x 1 + (713831081/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (277398591/2000000000 : ℝ)^5175 ≤ (851990317483/10000000000000 : ℝ)^4151 := by
    have hnat : (277398591 : ℕ)^5175*10000000000000^4151 ≤ 851990317483^4151*2000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277398591 2000000000 851990317483 10000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4962234881/10000000000 : ℝ)^5175 ≤ (1669800908317/4000000000000 : ℝ)^4151 := by
    have hnat : (4962234881 : ℕ)^5175*4000000000000^4151 ≤ 1669800908317^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4962234881 10000000000 1669800908317 4000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (713831081/1250000000 : ℝ)^5175 ≤ (6216884262741/12500000000000 : ℝ)^4151 := by
    have hnat : (713831081 : ℕ)^5175*12500000000000^4151 ≤ 6216884262741^4151*1250000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      713831081 1250000000 6216884262741 12500000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5175/1024 : ℝ)) 5175 4151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-277398591/2000000000 : ℝ), (4962234881/10000000000 : ℝ), (713831081/1250000000 : ℝ)] ![(851990317483/10000000000000 : ℝ), (1669800908317/4000000000000 : ℝ), (6216884262741/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-277398591/2000000000 : ℝ)|^5175 ≤ (851990317483/10000000000000 : ℝ)^4151
        have hw : |(-277398591/2000000000 : ℝ)|=(277398591/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4962234881/10000000000 : ℝ)|^5175 ≤ (1669800908317/4000000000000 : ℝ)^4151
        have hw : |(4962234881/10000000000 : ℝ)|=(4962234881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(713831081/1250000000 : ℝ)|^5175 ≤ (6216884262741/12500000000000 : ℝ)^4151
        have hw : |(713831081/1250000000 : ℝ)|=(713831081/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1694_s0_5 (p : ℝ) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5201585721/10000000000 : ℝ)*x 0 + (-1046228043/10000000000 : ℝ)*x 1 + (5710648637/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5201585721/10000000000 : ℝ)^5175 ≤ (885400948909/2000000000000 : ℝ)^4151 := by
    have hnat : (5201585721 : ℕ)^5175*2000000000000^4151 ≤ 885400948909^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5201585721 10000000000 885400948909 2000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1046228043/10000000000 : ℝ)^5175 ≤ (5994878550503/100000000000000 : ℝ)^4151 := by
    have hnat : (1046228043 : ℕ)^5175*100000000000000^4151 ≤ 5994878550503^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046228043 10000000000 5994878550503 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5710648637/10000000000 : ℝ)^5175 ≤ (24867536991247/50000000000000 : ℝ)^4151 := by
    have hnat : (5710648637 : ℕ)^5175*50000000000000^4151 ≤ 24867536991247^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5710648637 10000000000 24867536991247 50000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5175/1024 : ℝ)) 5175 4151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5201585721/10000000000 : ℝ), (-1046228043/10000000000 : ℝ), (5710648637/10000000000 : ℝ)] ![(885400948909/2000000000000 : ℝ), (5994878550503/100000000000000 : ℝ), (24867536991247/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5201585721/10000000000 : ℝ)|^5175 ≤ (885400948909/2000000000000 : ℝ)^4151
        have hw : |(5201585721/10000000000 : ℝ)|=(5201585721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1046228043/10000000000 : ℝ)|^5175 ≤ (5994878550503/100000000000000 : ℝ)^4151
        have hw : |(-1046228043/10000000000 : ℝ)|=(1046228043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5710648637/10000000000 : ℝ)|^5175 ≤ (24867536991247/50000000000000 : ℝ)^4151
        have hw : |(5710648637/10000000000 : ℝ)|=(5710648637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1694_s0_6 (p : ℝ) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5201585709/10000000000 : ℝ)*x 0 + (5710648813/10000000000 : ℝ)*x 1 + (-523113897/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5201585709/10000000000 : ℝ)^5175 ≤ (70832075709/160000000000 : ℝ)^4151 := by
    have hnat : (5201585709 : ℕ)^5175*160000000000^4151 ≤ 70832075709^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5201585709 10000000000 70832075709 160000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5710648813/10000000000 : ℝ)^5175 ≤ (12433768973359/25000000000000 : ℝ)^4151 := by
    have hnat : (5710648813 : ℕ)^5175*25000000000000^4151 ≤ 12433768973359^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5710648813 10000000000 12433768973359 25000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (523113897/5000000000 : ℝ)^5175 ≤ (5994876771769/100000000000000 : ℝ)^4151 := by
    have hnat : (523113897 : ℕ)^5175*100000000000000^4151 ≤ 5994876771769^4151*5000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523113897 5000000000 5994876771769 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5175/1024 : ℝ)) 5175 4151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5201585709/10000000000 : ℝ), (5710648813/10000000000 : ℝ), (-523113897/5000000000 : ℝ)] ![(70832075709/160000000000 : ℝ), (12433768973359/25000000000000 : ℝ), (5994876771769/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5201585709/10000000000 : ℝ)|^5175 ≤ (70832075709/160000000000 : ℝ)^4151
        have hw : |(5201585709/10000000000 : ℝ)|=(5201585709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5710648813/10000000000 : ℝ)|^5175 ≤ (12433768973359/25000000000000 : ℝ)^4151
        have hw : |(5710648813/10000000000 : ℝ)|=(5710648813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-523113897/5000000000 : ℝ)|^5175 ≤ (5994876771769/100000000000000 : ℝ)^4151
        have hw : |(-523113897/5000000000 : ℝ)|=(523113897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1694_s0_7 (p : ℝ) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4058584627/10000000000 : ℝ)*x 0 + (103948233/200000000 : ℝ)*x 1 + (3106608729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4058584627/10000000000 : ℝ)^5175 ≤ (8122795277177/25000000000000 : ℝ)^4151 := by
    have hnat : (4058584627 : ℕ)^5175*25000000000000^4151 ≤ 8122795277177^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4058584627 10000000000 8122795277177 25000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (103948233/200000000 : ℝ)^5175 ≤ (1769030530307/4000000000000 : ℝ)^4151 := by
    have hnat : (103948233 : ℕ)^5175*4000000000000^4151 ≤ 1769030530307^4151*200000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103948233 200000000 1769030530307 4000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3106608729/10000000000 : ℝ)^5175 ≤ (23283055618161/100000000000000 : ℝ)^4151 := by
    have hnat : (3106608729 : ℕ)^5175*100000000000000^4151 ≤ 23283055618161^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3106608729 10000000000 23283055618161 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5175/1024 : ℝ)) 5175 4151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4058584627/10000000000 : ℝ), (103948233/200000000 : ℝ), (3106608729/10000000000 : ℝ)] ![(8122795277177/25000000000000 : ℝ), (1769030530307/4000000000000 : ℝ), (23283055618161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4058584627/10000000000 : ℝ)|^5175 ≤ (8122795277177/25000000000000 : ℝ)^4151
        have hw : |(4058584627/10000000000 : ℝ)|=(4058584627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(103948233/200000000 : ℝ)|^5175 ≤ (1769030530307/4000000000000 : ℝ)^4151
        have hw : |(103948233/200000000 : ℝ)|=(103948233/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3106608729/10000000000 : ℝ)|^5175 ≤ (23283055618161/100000000000000 : ℝ)^4151
        have hw : |(3106608729/10000000000 : ℝ)|=(3106608729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1694_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9484113/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (2781/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2811/12500 : ℝ)*pair X 0 0 := by
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
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base53 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [sign3]
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
  have hpowlo : (0 : ℝ) ^ (5167/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5167 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5167*1^1024 ≤ 0^1024*1^5167 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5167 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5167 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5167/1024 : ℝ) ≤ (981827364214300463/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5167 ≤ (981827364214300463/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5167*100000000000000000000^1024 ≤ 981827364214300463^1024*5^5167 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 981827364214300463 100000000000000000000 5167 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (981827364214300463/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5167 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5167/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5167 := by
      have hnat : (1 : ℕ)^1024*1^5167 ≤ 1^5167*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5167 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100981827364214300463/100000000000000000000 : ℝ) ≤ (10019381787052319/10000000000000000 : ℝ) ^ (5167/1024 : ℝ) := by
    have hpowers : (100981827364214300463/100000000000000000000 : ℝ)^1024 ≤ (10019381787052319/10000000000000000 : ℝ)^5167 := by
      have hnat : (100981827364214300463 : ℕ)^1024*10000000000000000^5167 ≤ 10019381787052319^5167*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100981827364214300463 100000000000000000000 10019381787052319 10000000000000000 1024 5167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10019381787052319/10000000000000000 : ℝ)) (X := (100981827364214300463/100000000000000000000 : ℝ)) (by norm_num) 5167 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50981827364214300463/50000000000000000000 : ℝ) ≤ (5019381787052319/5000000000000000 : ℝ) ^ (5167/1024 : ℝ) := by
    have hpowers : (50981827364214300463/50000000000000000000 : ℝ)^1024 ≤ (5019381787052319/5000000000000000 : ℝ)^5167 := by
      have hnat : (50981827364214300463 : ℕ)^1024*5000000000000000^5167 ≤ 5019381787052319^5167*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50981827364214300463 50000000000000000000 5019381787052319 5000000000000000 1024 5167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5019381787052319/5000000000000000 : ℝ)) (X := (50981827364214300463/50000000000000000000 : ℝ)) (by norm_num) 5167 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(19381787052319/4000000000000000 : ℝ)*(0 : ℝ))^(5167/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(19381787052319/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(981827364214300463/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(19381787052319/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5167/1024 : ℝ) := by
    rw [show (1 : ℝ)+(19381787052319/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10019381787052319/10000000000000000 : ℝ) by norm_num, show 1+(981827364214300463/100000000000000000000 : ℝ)+(0 : ℝ)=(100981827364214300463/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(981827364214300463/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(19381787052319/4000000000000000 : ℝ)*(2/5 : ℝ))^(5167/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(19381787052319/4000000000000000 : ℝ)*(2/5 : ℝ)=(5019381787052319/5000000000000000 : ℝ) by norm_num, show 1+2*(981827364214300463/100000000000000000000 : ℝ)=(50981827364214300463/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(19381787052319/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5167/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (19381787052319/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(19381787052319/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5167/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (19381787052319/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(19381787052319/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5167/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (19381787052319/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-55402241/400000000 : ℝ)*X 0 0+(5731035941/10000000000 : ℝ)*X 0 1+(1235630957/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1694_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2707839343/5000000000 : ℝ)*X 1 0+(-226794099/1250000000 : ℝ)*X 1 1+(988504979/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1694_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((676960147/1250000000 : ℝ)*X 2 0+(4942523971/10000000000 : ℝ)*X 2 1+(-907175357/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1694_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4053173343/10000000000 : ℝ)*X 0 0+(381206853/1250000000 : ℝ)*X 0 1+(1313119919/2500000000 : ℝ)*X 0 2+(4053173343/10000000000 : ℝ)*X 1 0+(381206853/1250000000 : ℝ)*X 1 1+(1313119919/2500000000 : ℝ)*X 1 2+(4053173343/10000000000 : ℝ)*X 2 0+(381206853/1250000000 : ℝ)*X 2 1+(1313119919/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1694_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-277398591/2000000000 : ℝ)*X 0 0+(4962234881/10000000000 : ℝ)*X 0 1+(713831081/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1694_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5201585721/10000000000 : ℝ)*X 1 0+(-1046228043/10000000000 : ℝ)*X 1 1+(5710648637/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1694_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5201585709/10000000000 : ℝ)*X 2 0+(5710648813/10000000000 : ℝ)*X 2 1+(-523113897/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1694_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4058584627/10000000000 : ℝ)*X 0 0+(103948233/200000000 : ℝ)*X 0 1+(3106608729/10000000000 : ℝ)*X 0 2+(4058584627/10000000000 : ℝ)*X 1 0+(103948233/200000000 : ℝ)*X 1 1+(3106608729/10000000000 : ℝ)*X 1 2+(4058584627/10000000000 : ℝ)*X 2 0+(103948233/200000000 : ℝ)*X 2 1+(3106608729/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1694_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (47765304723718308539043/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2705517/2000000000000 : ℝ)*(base19) + (83038331/20000000000000 : ℝ)*(base23) + (1984201/781250000000 : ℝ)*(base24) + (15937331/100000000000000 : ℝ)*(base53) + (6661473/25000000000000 : ℝ)*(upper4) + (172217991810667/20000000000000 : ℝ)*(major0) + (172217991810667/20000000000000 : ℝ)*(major1) + (172217991810667/20000000000000 : ℝ)*(major2) + (634106282597591/50000000000000 : ℝ)*(sp0) + (158526911219807/12500000000000 : ℝ)*(sp1) + (317053688966231/25000000000000 : ℝ)*(sp2) + (113490812424733/25000000000000 : ℝ)*(sp3) + (22878713/800000000000 : ℝ)*(sp4) + (58188229/5000000000000 : ℝ)*(sp7) + (56745551682939/12500000000000 : ℝ)*(f.failure) + (634107712517153/50000000000000 : ℝ)*(f.sum) + (91049654846773/40000000000000000000000000000 : ℝ)*base65 + (19926642886773/80000000000000000000000000000 : ℝ)*base67 + (256237507446773/80000000000000000000000000000 : ℝ)*base69 + (201991459126773/80000000000000000000000000000 : ℝ)*base71 + (92371638646773/40000000000000000000000000000 : ℝ)*base73 + (725660513526773/80000000000000000000000000000 : ℝ)*base75 + (181351314486773/80000000000000000000000000000 : ℝ)*base77 + (350923617526773/80000000000000000000000000000 : ℝ)*base79 + (139996706646773/40000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (726893/62500000000000000000 : ℝ)*base90 + (726893/62500000000000000000 : ℝ)*base92 + (726893/62500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5357540537646401001/1000000000000000000000000 : ℝ) := by norm_num
    linear_combination (317001411/25000000000000 : ℝ)*(base19) + (162350053/12500000000000 : ℝ)*(base23) + (1492643/25000000000000 : ℝ)*(upper2) + (204885739/100000000000000 : ℝ)*(upper3) + (22951451/12500000000000 : ℝ)*(upper5) + (907222236908641/100000000000000 : ℝ)*(major0) + (907222236908641/100000000000000 : ℝ)*(major1) + (907222236908641/100000000000000 : ℝ)*(major2) + (175772023/4000000000000 : ℝ)*(sp1) + (4938445059/100000000000000 : ℝ)*(sp2) + (66807953172047/5000000000000 : ℝ)*(sp4) + (1336153401134721/100000000000000 : ℝ)*(sp5) + (1336152826195457/100000000000000 : ℝ)*(sp6) + (9565704635833/2000000000000 : ℝ)*(sp7) + (9565704635833/2000000000000 : ℝ)*(f.failure) + (66807953172047/5000000000000 : ℝ)*(f.sum) + (325143079811521/200000000000000000000000000000 : ℝ)*base66 + (2804874034188479/400000000000000000000000000000 : ℝ)*base67 + (1203269502188479/400000000000000000000000000000 : ℝ)*base69 + (1293363153788479/400000000000000000000000000000 : ℝ)*base71 + (584082929211521/200000000000000000000000000000 : ℝ)*base74 + (2585873189388479/400000000000000000000000000000 : ℝ)*base75 + (952375111388479/400000000000000000000000000000 : ℝ)*base77 + (2386624558188479/400000000000000000000000000000 : ℝ)*base79 + (414057483011521/200000000000000000000000000000 : ℝ)*base82 + (78871/10000000000000000000 : ℝ)*base90 + (78871/10000000000000000000 : ℝ)*base92 + (78871/10000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1694_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9484113/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2781/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2811/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1694_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1694_s1_0 (p : ℝ) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-366727319/2500000000 : ℝ)*x 0 + (5501174203/10000000000 : ℝ)*x 1 + (5118738657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (366727319/2500000000 : ℝ)^5175 ≤ (4568097075883/50000000000000 : ℝ)^4151 := by
    have hnat : (366727319 : ℕ)^5175*50000000000000^4151 ≤ 4568097075883^4151*2500000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      366727319 2500000000 4568097075883 50000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5501174203/10000000000 : ℝ)^5175 ≤ (23735532602083/50000000000000 : ℝ)^4151 := by
    have hnat : (5501174203 : ℕ)^5175*50000000000000^4151 ≤ 23735532602083^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5501174203 10000000000 23735532602083 50000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5118738657/10000000000 : ℝ)^5175 ≤ (21696370314441/50000000000000 : ℝ)^4151 := by
    have hnat : (5118738657 : ℕ)^5175*50000000000000^4151 ≤ 21696370314441^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5118738657 10000000000 21696370314441 50000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5175/1024 : ℝ)) 5175 4151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-366727319/2500000000 : ℝ), (5501174203/10000000000 : ℝ), (5118738657/10000000000 : ℝ)] ![(4568097075883/50000000000000 : ℝ), (23735532602083/50000000000000 : ℝ), (21696370314441/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-366727319/2500000000 : ℝ)|^5175 ≤ (4568097075883/50000000000000 : ℝ)^4151
        have hw : |(-366727319/2500000000 : ℝ)|=(366727319/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5501174203/10000000000 : ℝ)|^5175 ≤ (23735532602083/50000000000000 : ℝ)^4151
        have hw : |(5501174203/10000000000 : ℝ)|=(5501174203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5118738657/10000000000 : ℝ)|^5175 ≤ (21696370314441/50000000000000 : ℝ)^4151
        have hw : |(5118738657/10000000000 : ℝ)|=(5118738657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1694_s1_1 (p : ℝ) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677221509/5000000000 : ℝ)*x 0 + (-416574939/2500000000 : ℝ)*x 1 + (1279684557/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677221509/5000000000 : ℝ)^5175 ≤ (11474440195151/25000000000000 : ℝ)^4151 := by
    have hnat : (2677221509 : ℕ)^5175*25000000000000^4151 ≤ 11474440195151^4151*5000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677221509 5000000000 11474440195151 25000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (416574939/2500000000 : ℝ)^5175 ≤ (5354751551501/50000000000000 : ℝ)^4151 := by
    have hnat : (416574939 : ℕ)^5175*50000000000000^4151 ≤ 5354751551501^4151*2500000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416574939 2500000000 5354751551501 50000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1279684557/2500000000 : ℝ)^5175 ≤ (10848184023753/25000000000000 : ℝ)^4151 := by
    have hnat : (1279684557 : ℕ)^5175*25000000000000^4151 ≤ 10848184023753^4151*2500000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1279684557 2500000000 10848184023753 25000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5175/1024 : ℝ)) 5175 4151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677221509/5000000000 : ℝ), (-416574939/2500000000 : ℝ), (1279684557/2500000000 : ℝ)] ![(11474440195151/25000000000000 : ℝ), (5354751551501/50000000000000 : ℝ), (10848184023753/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677221509/5000000000 : ℝ)|^5175 ≤ (11474440195151/25000000000000 : ℝ)^4151
        have hw : |(2677221509/5000000000 : ℝ)|=(2677221509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-416574939/2500000000 : ℝ)|^5175 ≤ (5354751551501/50000000000000 : ℝ)^4151
        have hw : |(-416574939/2500000000 : ℝ)|=(416574939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1279684557/2500000000 : ℝ)|^5175 ≤ (10848184023753/25000000000000 : ℝ)^4151
        have hw : |(1279684557/2500000000 : ℝ)|=(1279684557/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1694_s1_2 (p : ℝ) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354442061/10000000000 : ℝ)*x 0 + (2559369529/5000000000 : ℝ)*x 1 + (-833149969/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354442061/10000000000 : ℝ)^5175 ≤ (45897750553639/100000000000000 : ℝ)^4151 := by
    have hnat : (5354442061 : ℕ)^5175*100000000000000^4151 ≤ 45897750553639^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354442061 10000000000 45897750553639 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2559369529/5000000000 : ℝ)^5175 ≤ (8678548973367/20000000000000 : ℝ)^4151 := by
    have hnat : (2559369529 : ℕ)^5175*20000000000000^4151 ≤ 8678548973367^4151*5000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2559369529 5000000000 8678548973367 20000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (833149969/5000000000 : ℝ)^5175 ≤ (10709504561297/100000000000000 : ℝ)^4151 := by
    have hnat : (833149969 : ℕ)^5175*100000000000000^4151 ≤ 10709504561297^4151*5000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      833149969 5000000000 10709504561297 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5175/1024 : ℝ)) 5175 4151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354442061/10000000000 : ℝ), (2559369529/5000000000 : ℝ), (-833149969/5000000000 : ℝ)] ![(45897750553639/100000000000000 : ℝ), (8678548973367/20000000000000 : ℝ), (10709504561297/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354442061/10000000000 : ℝ)|^5175 ≤ (45897750553639/100000000000000 : ℝ)^4151
        have hw : |(5354442061/10000000000 : ℝ)|=(5354442061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2559369529/5000000000 : ℝ)|^5175 ≤ (8678548973367/20000000000000 : ℝ)^4151
        have hw : |(2559369529/5000000000 : ℝ)|=(2559369529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-833149969/5000000000 : ℝ)|^5175 ≤ (10709504561297/100000000000000 : ℝ)^4151
        have hw : |(-833149969/5000000000 : ℝ)|=(833149969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1694_s1_3 (p : ℝ) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2060926163/5000000000 : ℝ)*x 0 + (902622547/2500000000 : ℝ)*x 1 + (4678879321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2060926163/5000000000 : ℝ)^5175 ≤ (33123828256831/100000000000000 : ℝ)^4151 := by
    have hnat : (2060926163 : ℕ)^5175*100000000000000^4151 ≤ 33123828256831^4151*5000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2060926163 5000000000 33123828256831 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (902622547/2500000000 : ℝ)^5175 ≤ (28081690818759/100000000000000 : ℝ)^4151 := by
    have hnat : (902622547 : ℕ)^5175*100000000000000^4151 ≤ 28081690818759^4151*2500000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      902622547 2500000000 28081690818759 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4678879321/10000000000 : ℝ)^5175 ≤ (19397240452433/50000000000000 : ℝ)^4151 := by
    have hnat : (4678879321 : ℕ)^5175*50000000000000^4151 ≤ 19397240452433^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4678879321 10000000000 19397240452433 50000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5175/1024 : ℝ)) 5175 4151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2060926163/5000000000 : ℝ), (902622547/2500000000 : ℝ), (4678879321/10000000000 : ℝ)] ![(33123828256831/100000000000000 : ℝ), (28081690818759/100000000000000 : ℝ), (19397240452433/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2060926163/5000000000 : ℝ)|^5175 ≤ (33123828256831/100000000000000 : ℝ)^4151
        have hw : |(2060926163/5000000000 : ℝ)|=(2060926163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(902622547/2500000000 : ℝ)|^5175 ≤ (28081690818759/100000000000000 : ℝ)^4151
        have hw : |(902622547/2500000000 : ℝ)|=(902622547/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4678879321/10000000000 : ℝ)|^5175 ≤ (19397240452433/50000000000000 : ℝ)^4151
        have hw : |(4678879321/10000000000 : ℝ)|=(4678879321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1694_s1_4 (p : ℝ) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-733563527/5000000000 : ℝ)*x 0 + (5123372303/10000000000 : ℝ)*x 1 + (5496464001/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (733563527/5000000000 : ℝ)^5175 ≤ (4568942572059/50000000000000 : ℝ)^4151 := by
    have hnat : (733563527 : ℕ)^5175*50000000000000^4151 ≤ 4568942572059^4151*5000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      733563527 5000000000 4568942572059 50000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5123372303/10000000000 : ℝ)^5175 ≤ (10860429150487/25000000000000 : ℝ)^4151 := by
    have hnat : (5123372303 : ℕ)^5175*25000000000000^4151 ≤ 10860429150487^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5123372303 10000000000 10860429150487 25000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5496464001/10000000000 : ℝ)^5175 ≤ (92617965319/195312500000 : ℝ)^4151 := by
    have hnat : (5496464001 : ℕ)^5175*195312500000^4151 ≤ 92617965319^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5496464001 10000000000 92617965319 195312500000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5175/1024 : ℝ)) 5175 4151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-733563527/5000000000 : ℝ), (5123372303/10000000000 : ℝ), (5496464001/10000000000 : ℝ)] ![(4568942572059/50000000000000 : ℝ), (10860429150487/25000000000000 : ℝ), (92617965319/195312500000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-733563527/5000000000 : ℝ)|^5175 ≤ (4568942572059/50000000000000 : ℝ)^4151
        have hw : |(-733563527/5000000000 : ℝ)|=(733563527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5123372303/10000000000 : ℝ)|^5175 ≤ (10860429150487/25000000000000 : ℝ)^4151
        have hw : |(5123372303/10000000000 : ℝ)|=(5123372303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5496464001/10000000000 : ℝ)|^5175 ≤ (92617965319/195312500000 : ℝ)^4151
        have hw : |(5496464001/10000000000 : ℝ)|=(5496464001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1694_s1_5 (p : ℝ) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (656512791/1250000000 : ℝ)*x 0 + (-128857203/1000000000 : ℝ)*x 1 + (5496464277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (656512791/1250000000 : ℝ)^5175 ≤ (11201672368797/25000000000000 : ℝ)^4151 := by
    have hnat : (656512791 : ℕ)^5175*25000000000000^4151 ≤ 11201672368797^4151*1250000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656512791 1250000000 11201672368797 25000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (128857203/1000000000 : ℝ)^5175 ≤ (242903415599/3125000000000 : ℝ)^4151 := by
    have hnat : (128857203 : ℕ)^5175*3125000000000^4151 ≤ 242903415599^4151*1000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128857203 1000000000 242903415599 3125000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5496464277/10000000000 : ℝ)^5175 ≤ (23710200605953/50000000000000 : ℝ)^4151 := by
    have hnat : (5496464277 : ℕ)^5175*50000000000000^4151 ≤ 23710200605953^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5496464277 10000000000 23710200605953 50000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5175/1024 : ℝ)) 5175 4151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(656512791/1250000000 : ℝ), (-128857203/1000000000 : ℝ), (5496464277/10000000000 : ℝ)] ![(11201672368797/25000000000000 : ℝ), (242903415599/3125000000000 : ℝ), (23710200605953/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(656512791/1250000000 : ℝ)|^5175 ≤ (11201672368797/25000000000000 : ℝ)^4151
        have hw : |(656512791/1250000000 : ℝ)|=(656512791/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-128857203/1000000000 : ℝ)|^5175 ≤ (242903415599/3125000000000 : ℝ)^4151
        have hw : |(-128857203/1000000000 : ℝ)|=(128857203/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5496464277/10000000000 : ℝ)|^5175 ≤ (23710200605953/50000000000000 : ℝ)^4151
        have hw : |(5496464277/10000000000 : ℝ)|=(5496464277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1694_s1_6 (p : ℝ) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5252100583/10000000000 : ℝ)*x 0 + (5496466087/10000000000 : ℝ)*x 1 + (-322142977/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5252100583/10000000000 : ℝ)^5175 ≤ (44806670915841/100000000000000 : ℝ)^4151 := by
    have hnat : (5252100583 : ℕ)^5175*100000000000000^4151 ≤ 44806670915841^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252100583 10000000000 44806670915841 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5496466087/10000000000 : ℝ)^5175 ≤ (23710210339879/50000000000000 : ℝ)^4151 := by
    have hnat : (5496466087 : ℕ)^5175*50000000000000^4151 ≤ 23710210339879^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5496466087 10000000000 23710210339879 50000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (322142977/2500000000 : ℝ)^5175 ≤ (7772908381697/100000000000000 : ℝ)^4151 := by
    have hnat : (322142977 : ℕ)^5175*100000000000000^4151 ≤ 7772908381697^4151*2500000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      322142977 2500000000 7772908381697 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5175/1024 : ℝ)) 5175 4151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5252100583/10000000000 : ℝ), (5496466087/10000000000 : ℝ), (-322142977/2500000000 : ℝ)] ![(44806670915841/100000000000000 : ℝ), (23710210339879/50000000000000 : ℝ), (7772908381697/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5252100583/10000000000 : ℝ)|^5175 ≤ (44806670915841/100000000000000 : ℝ)^4151
        have hw : |(5252100583/10000000000 : ℝ)|=(5252100583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5496466087/10000000000 : ℝ)|^5175 ≤ (23710210339879/50000000000000 : ℝ)^4151
        have hw : |(5496466087/10000000000 : ℝ)|=(5496466087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-322142977/2500000000 : ℝ)|^5175 ≤ (7772908381697/100000000000000 : ℝ)^4151
        have hw : |(-322142977/2500000000 : ℝ)|=(322142977/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1694_s1_7 (p : ℝ) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (515307651/1250000000 : ℝ)*x 0 + (933187769/2000000000 : ℝ)*x 1 + (3623645441/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (515307651/1250000000 : ℝ)^5175 ≤ (33129928494629/100000000000000 : ℝ)^4151 := by
    have hnat : (515307651 : ℕ)^5175*100000000000000^4151 ≤ 33129928494629^4151*1250000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515307651 1250000000 33129928494629 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (933187769/2000000000 : ℝ)^5175 ≤ (19330381788017/50000000000000 : ℝ)^4151 := by
    have hnat : (933187769 : ℕ)^5175*50000000000000^4151 ≤ 19330381788017^4151*2000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      933187769 2000000000 19330381788017 50000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3623645441/10000000000 : ℝ)^5175 ≤ (28209307917617/100000000000000 : ℝ)^4151 := by
    have hnat : (3623645441 : ℕ)^5175*100000000000000^4151 ≤ 28209307917617^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3623645441 10000000000 28209307917617 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5175/1024 : ℝ)) 5175 4151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(515307651/1250000000 : ℝ), (933187769/2000000000 : ℝ), (3623645441/10000000000 : ℝ)] ![(33129928494629/100000000000000 : ℝ), (19330381788017/50000000000000 : ℝ), (28209307917617/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(515307651/1250000000 : ℝ)|^5175 ≤ (33129928494629/100000000000000 : ℝ)^4151
        have hw : |(515307651/1250000000 : ℝ)|=(515307651/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(933187769/2000000000 : ℝ)|^5175 ≤ (19330381788017/50000000000000 : ℝ)^4151
        have hw : |(933187769/2000000000 : ℝ)|=(933187769/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3623645441/10000000000 : ℝ)|^5175 ≤ (28209307917617/100000000000000 : ℝ)^4151
        have hw : |(3623645441/10000000000 : ℝ)|=(3623645441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1694_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9484113/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2811/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2781/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1899/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (441/2500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2811/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2781/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2811/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2781/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2811/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2781/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2811/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2781/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2811/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2781/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2811/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2781/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2781/50000 : ℝ) ^ (5167/1024 : ℝ) ≤ (46619003429481/100000000000000000000 : ℝ) := by
    have hpowers : (2781/50000 : ℝ)^5167 ≤ (46619003429481/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2781 : ℕ)^5167*100000000000000000000^1024 ≤ 46619003429481^1024*50000^5167 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2781 50000 46619003429481 100000000000000000000 5167 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2781/50000 : ℝ)) (X := (46619003429481/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5167 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2811/12500 : ℝ) ^ (5167/1024 : ℝ) ≤ (6713047679818109/12500000000000000000 : ℝ) := by
    have hpowers : (2811/12500 : ℝ)^5167 ≤ (6713047679818109/12500000000000000000 : ℝ)^1024 := by
      have hnat : (2811 : ℕ)^5167*12500000000000000000^1024 ≤ 6713047679818109^1024*12500^5167 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2811 12500 6713047679818109 12500000000000000000 5167 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2811/12500 : ℝ)) (X := (6713047679818109/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 5167 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000046619003429481/50000000000000000000 : ℝ) ≤ (10000001847797239/10000000000000000 : ℝ) ^ (5167/1024 : ℝ) := by
    have hpowers : (50000046619003429481/50000000000000000000 : ℝ)^1024 ≤ (10000001847797239/10000000000000000 : ℝ)^5167 := by
      have hnat : (50000046619003429481 : ℕ)^1024*10000000000000000^5167 ≤ 10000001847797239^5167*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000046619003429481 50000000000000000000 10000001847797239 10000000000000000 1024 5167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001847797239/10000000000000000 : ℝ)) (X := (50000046619003429481/50000000000000000000 : ℝ)) (by norm_num) 5167 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100053751000441974353/100000000000000000000 : ℝ) ≤ (2500266252986881/2500000000000000 : ℝ) ^ (5167/1024 : ℝ) := by
    have hpowers : (100053751000441974353/100000000000000000000 : ℝ)^1024 ≤ (2500266252986881/2500000000000000 : ℝ)^5167 := by
      have hnat : (100053751000441974353 : ℕ)^1024*2500000000000000^5167 ≤ 2500266252986881^5167*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100053751000441974353 100000000000000000000 2500266252986881 2500000000000000 1024 5167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500266252986881/2500000000000000 : ℝ)) (X := (100053751000441974353/100000000000000000000 : ℝ)) (by norm_num) 5167 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6256713047679818109/6250000000000000000 : ℝ) ≤ (10002128176097809/10000000000000000 : ℝ) ^ (5167/1024 : ℝ) := by
    have hpowers : (6256713047679818109/6250000000000000000 : ℝ)^1024 ≤ (10002128176097809/10000000000000000 : ℝ)^5167 := by
      have hnat : (6256713047679818109 : ℕ)^1024*10000000000000000^5167 ≤ 10002128176097809^5167*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6256713047679818109 6250000000000000000 10002128176097809 10000000000000000 1024 5167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002128176097809/10000000000000000 : ℝ)) (X := (6256713047679818109/6250000000000000000 : ℝ)) (by norm_num) 5167 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(46619003429481/100000000000000000000 : ℝ) ≤ ((28208034106301382829/28210000000000000000 : ℝ)+2*(70877610019/112840000000000 : ℝ)*(2781/50000 : ℝ))^(5167/1024 : ℝ) := by
    rw [show (28208034106301382829/28210000000000000000 : ℝ)+2*(70877610019/112840000000000 : ℝ)*(2781/50000 : ℝ)=(10000001847797239/10000000000000000 : ℝ) by norm_num, show 1+2*(46619003429481/100000000000000000000 : ℝ)=(50000046619003429481/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6713047679818109/12500000000000000000 : ℝ)+(46619003429481/100000000000000000000 : ℝ) ≤ ((28208034106301382829/28210000000000000000 : ℝ)+(70877610019/112840000000000 : ℝ)*((2811/12500 : ℝ)+(2781/50000 : ℝ)))^(5167/1024 : ℝ) := by
    rw [show (28208034106301382829/28210000000000000000 : ℝ)+(70877610019/112840000000000 : ℝ)*((2811/12500 : ℝ)+(2781/50000 : ℝ))=(2500266252986881/2500000000000000 : ℝ) by norm_num, show 1+(6713047679818109/12500000000000000000 : ℝ)+(46619003429481/100000000000000000000 : ℝ)=(100053751000441974353/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6713047679818109/12500000000000000000 : ℝ) ≤ ((28208034106301382829/28210000000000000000 : ℝ)+2*(70877610019/112840000000000 : ℝ)*(2811/12500 : ℝ))^(5167/1024 : ℝ) := by
    rw [show (28208034106301382829/28210000000000000000 : ℝ)+2*(70877610019/112840000000000 : ℝ)*(2811/12500 : ℝ)=(10002128176097809/10000000000000000 : ℝ) by norm_num, show 1+2*(6713047679818109/12500000000000000000 : ℝ)=(6256713047679818109/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (28208034106301382829/28210000000000000000 : ℝ)*(X 1 0+X 2 0)+(70877610019/112840000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5167/1024 : ℝ)) (lo := (2781/50000 : ℝ)) (hi := (2811/12500 : ℝ)) (c := (28208034106301382829/28210000000000000000 : ℝ)) (alpha := (70877610019/112840000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (28208034106301382829/28210000000000000000 : ℝ)*(X 0 1+X 2 1)+(70877610019/112840000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5167/1024 : ℝ)) (lo := (2781/50000 : ℝ)) (hi := (2811/12500 : ℝ)) (c := (28208034106301382829/28210000000000000000 : ℝ)) (alpha := (70877610019/112840000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (28208034106301382829/28210000000000000000 : ℝ)*(X 0 2+X 1 2)+(70877610019/112840000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5167/1024 : ℝ)) (lo := (2781/50000 : ℝ)) (hi := (2811/12500 : ℝ)) (c := (28208034106301382829/28210000000000000000 : ℝ)) (alpha := (70877610019/112840000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-366727319/2500000000 : ℝ)*X 0 0+(5501174203/10000000000 : ℝ)*X 0 1+(5118738657/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1694_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2677221509/5000000000 : ℝ)*X 1 0+(-416574939/2500000000 : ℝ)*X 1 1+(1279684557/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1694_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5354442061/10000000000 : ℝ)*X 2 0+(2559369529/5000000000 : ℝ)*X 2 1+(-833149969/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1694_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2060926163/5000000000 : ℝ)*X 0 0+(902622547/2500000000 : ℝ)*X 0 1+(4678879321/10000000000 : ℝ)*X 0 2+(2060926163/5000000000 : ℝ)*X 1 0+(902622547/2500000000 : ℝ)*X 1 1+(4678879321/10000000000 : ℝ)*X 1 2+(2060926163/5000000000 : ℝ)*X 2 0+(902622547/2500000000 : ℝ)*X 2 1+(4678879321/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1694_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-733563527/5000000000 : ℝ)*X 0 0+(5123372303/10000000000 : ℝ)*X 0 1+(5496464001/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1694_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((656512791/1250000000 : ℝ)*X 1 0+(-128857203/1000000000 : ℝ)*X 1 1+(5496464277/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1694_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5252100583/10000000000 : ℝ)*X 2 0+(5496466087/10000000000 : ℝ)*X 2 1+(-322142977/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1694_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((515307651/1250000000 : ℝ)*X 0 0+(933187769/2000000000 : ℝ)*X 0 1+(3623645441/10000000000 : ℝ)*X 0 2+(515307651/1250000000 : ℝ)*X 1 0+(933187769/2000000000 : ℝ)*X 1 1+(3623645441/10000000000 : ℝ)*X 1 2+(515307651/1250000000 : ℝ)*X 2 0+(933187769/2000000000 : ℝ)*X 2 1+(3623645441/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1694_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3423831313097657994185037249/705250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5090109/800000000000 : ℝ)*(base19) + (216171603/100000000000000 : ℝ)*(base23) + (5738659/20000000000000 : ℝ)*(upper2) + (22459557/20000000000000 : ℝ)*(upper3) + (887704841113673/50000000000000 : ℝ)*(major0) + (887704841113673/50000000000000 : ℝ)*(major1) + (887704841113673/50000000000000 : ℝ)*(major2) + (261482550134031/10000000000000 : ℝ)*(sp0) + (2614827144591017/100000000000000 : ℝ)*(sp1) + (261482723342179/10000000000000 : ℝ)*(sp2) + (467994968044103/50000000000000 : ℝ)*(sp3) + (569878583/25000000000000 : ℝ)*(sp4) + (331261249/100000000000000 : ℝ)*(sp6) + (1485685947/100000000000000 : ℝ)*(sp7) + (467995710887077/50000000000000 : ℝ)*(f.failure) + (1307413890427321/50000000000000 : ℝ)*(f.sum) + (190933276063/2821000000000000000000000000 : ℝ)*base65 + (1581368051701570917/1410500000000000000000000000000000 : ℝ)*base67 + (2844007754298570917/1410500000000000000000000000000000 : ℝ)*base69 + (783198586927070917/1410500000000000000000000000000000 : ℝ)*base71 + (960549362769/705250000000000000000000000 : ℝ)*base73 + (6228852773978429083/1410500000000000000000000000000000 : ℝ)*base76 + (2353158360991570917/1410500000000000000000000000000000 : ℝ)*base77 + (1762457691146929083/1410500000000000000000000000000000 : ℝ)*base80 + (2883170379263/1410500000000000000000000000 : ℝ)*base81 + (3507701/250000000000000000000 : ℝ)*base89 + (3507701/250000000000000000000 : ℝ)*base91 + (3507701/250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3414128129430469689625673919/352625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (484102479/20000000000000 : ℝ)*(base19) + (1668438337/100000000000000 : ℝ)*(base23) + (51612871/25000000000000 : ℝ)*(upper3) + (40198947/100000000000000 : ℝ)*(lower4) + (454965987777263/25000000000000 : ℝ)*(major0) + (454965987777263/25000000000000 : ℝ)*(major1) + (454965987777263/25000000000000 : ℝ)*(major2) + (25352003179/100000000000000 : ℝ)*(sp1) + (14264512953/50000000000000 : ℝ)*(sp2) + (2290608283/100000000000000 : ℝ)*(sp3) + (670074995349939/25000000000000 : ℝ)*(sp4) + (1340136104442091/50000000000000 : ℝ)*(sp5) + (335033722991939/12500000000000 : ℝ)*(sp6) + (239856326868877/25000000000000 : ℝ)*(sp7) + (959427598083791/100000000000000 : ℝ)*(f.failure) + (670074995349939/25000000000000 : ℝ)*(f.sum) + (1235743398567/352625000000000000000000000 : ℝ)*base65 + (1515330794998932973/705250000000000000000000000000000 : ℝ)*base68 + (500098803247682973/705250000000000000000000000000000 : ℝ)*base70 + (3968025821284067027/705250000000000000000000000000000 : ℝ)*base71 + (2529790638357/1410500000000000000000000000 : ℝ)*base73 + (435056018034817027/705250000000000000000000000000000 : ℝ)*base75 + (5110738274803067027/705250000000000000000000000000000 : ℝ)*base77 + (1462474473075067027/705250000000000000000000000000000 : ℝ)*base79 + (3548646717307/2821000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (2687617/500000000000000000000 : ℝ)*base90 + (2687617/500000000000000000000 : ℝ)*base92 + (2687617/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1694_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9484113/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2811/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2781/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1899/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (441/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1694_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1694_s2_0 (p : ℝ) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-735903579/5000000000 : ℝ)*x 0 + (2740720101/5000000000 : ℝ)*x 1 + (5135211193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (735903579/5000000000 : ℝ)^5175 ≤ (1834847989549/20000000000000 : ℝ)^4151 := by
    have hnat : (735903579 : ℕ)^5175*20000000000000^4151 ≤ 1834847989549^4151*5000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      735903579 5000000000 1834847989549 20000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2740720101/5000000000 : ℝ)^5175 ≤ (2362943050323/5000000000000 : ℝ)^4151 := by
    have hnat : (2740720101 : ℕ)^5175*5000000000000^4151 ≤ 2362943050323^4151*5000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2740720101 5000000000 2362943050323 5000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5135211193/10000000000 : ℝ)^5175 ≤ (43566899026981/100000000000000 : ℝ)^4151 := by
    have hnat : (5135211193 : ℕ)^5175*100000000000000^4151 ≤ 43566899026981^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5135211193 10000000000 43566899026981 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5175/1024 : ℝ)) 5175 4151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-735903579/5000000000 : ℝ), (2740720101/5000000000 : ℝ), (5135211193/10000000000 : ℝ)] ![(1834847989549/20000000000000 : ℝ), (2362943050323/5000000000000 : ℝ), (43566899026981/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-735903579/5000000000 : ℝ)|^5175 ≤ (1834847989549/20000000000000 : ℝ)^4151
        have hw : |(-735903579/5000000000 : ℝ)|=(735903579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2740720101/5000000000 : ℝ)|^5175 ≤ (2362943050323/5000000000000 : ℝ)^4151
        have hw : |(2740720101/5000000000 : ℝ)|=(2740720101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5135211193/10000000000 : ℝ)|^5175 ≤ (43566899026981/100000000000000 : ℝ)^4151
        have hw : |(5135211193/10000000000 : ℝ)|=(5135211193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1694_s2_1 (p : ℝ) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674569997/5000000000 : ℝ)*x 0 + (-165161953/1000000000 : ℝ)*x 1 + (1027042231/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674569997/5000000000 : ℝ)^5175 ≤ (9168219405389/20000000000000 : ℝ)^4151 := by
    have hnat : (2674569997 : ℕ)^5175*20000000000000^4151 ≤ 9168219405389^4151*5000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674569997 5000000000 9168219405389 20000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (165161953/1000000000 : ℝ)^5175 ≤ (2648001083757/25000000000000 : ℝ)^4151 := by
    have hnat : (165161953 : ℕ)^5175*25000000000000^4151 ≤ 2648001083757^4151*1000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165161953 1000000000 2648001083757 25000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1027042231/2000000000 : ℝ)^5175 ≤ (43566898625061/100000000000000 : ℝ)^4151 := by
    have hnat : (1027042231 : ℕ)^5175*100000000000000^4151 ≤ 43566898625061^4151*2000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027042231 2000000000 43566898625061 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5175/1024 : ℝ)) 5175 4151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674569997/5000000000 : ℝ), (-165161953/1000000000 : ℝ), (1027042231/2000000000 : ℝ)] ![(9168219405389/20000000000000 : ℝ), (2648001083757/25000000000000 : ℝ), (43566898625061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674569997/5000000000 : ℝ)|^5175 ≤ (9168219405389/20000000000000 : ℝ)^4151
        have hw : |(2674569997/5000000000 : ℝ)|=(2674569997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-165161953/1000000000 : ℝ)|^5175 ≤ (2648001083757/25000000000000 : ℝ)^4151
        have hw : |(-165161953/1000000000 : ℝ)|=(165161953/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1027042231/2000000000 : ℝ)|^5175 ≤ (43566898625061/100000000000000 : ℝ)^4151
        have hw : |(1027042231/2000000000 : ℝ)|=(1027042231/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1694_s2_2 (p : ℝ) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349139931/10000000000 : ℝ)*x 0 + (2567605541/5000000000 : ℝ)*x 1 + (-12903279/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349139931/10000000000 : ℝ)^5175 ≤ (45841096353861/100000000000000 : ℝ)^4151 := by
    have hnat : (5349139931 : ℕ)^5175*100000000000000^4151 ≤ 45841096353861^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349139931 10000000000 45841096353861 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2567605541/5000000000 : ℝ)^5175 ≤ (43566897852951/100000000000000 : ℝ)^4151 := by
    have hnat : (2567605541 : ℕ)^5175*100000000000000^4151 ≤ 43566897852951^4151*5000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2567605541 5000000000 43566897852951 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (12903279/78125000 : ℝ)^5175 ≤ (10592005790143/100000000000000 : ℝ)^4151 := by
    have hnat : (12903279 : ℕ)^5175*100000000000000^4151 ≤ 10592005790143^4151*78125000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12903279 78125000 10592005790143 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5175/1024 : ℝ)) 5175 4151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349139931/10000000000 : ℝ), (2567605541/5000000000 : ℝ), (-12903279/78125000 : ℝ)] ![(45841096353861/100000000000000 : ℝ), (43566897852951/100000000000000 : ℝ), (10592005790143/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349139931/10000000000 : ℝ)|^5175 ≤ (45841096353861/100000000000000 : ℝ)^4151
        have hw : |(5349139931/10000000000 : ℝ)|=(5349139931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2567605541/5000000000 : ℝ)|^5175 ≤ (43566897852951/100000000000000 : ℝ)^4151
        have hw : |(2567605541/5000000000 : ℝ)|=(2567605541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-12903279/78125000 : ℝ)|^5175 ≤ (10592005790143/100000000000000 : ℝ)^4151
        have hw : |(-12903279/78125000 : ℝ)|=(12903279/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1694_s2_3 (p : ℝ) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4125625403/10000000000 : ℝ)*x 0 + (3660716179/10000000000 : ℝ)*x 1 + (2313979033/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4125625403/10000000000 : ℝ)^5175 ≤ (16580816679053/50000000000000 : ℝ)^4151 := by
    have hnat : (4125625403 : ℕ)^5175*50000000000000^4151 ≤ 16580816679053^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4125625403 10000000000 16580816679053 50000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3660716179/10000000000 : ℝ)^5175 ≤ (7142384888321/25000000000000 : ℝ)^4151 := by
    have hnat : (3660716179 : ℕ)^5175*25000000000000^4151 ≤ 7142384888321^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3660716179 10000000000 7142384888321 25000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2313979033/5000000000 : ℝ)^5175 ≤ (38268827067589/100000000000000 : ℝ)^4151 := by
    have hnat : (2313979033 : ℕ)^5175*100000000000000^4151 ≤ 38268827067589^4151*5000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2313979033 5000000000 38268827067589 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5175/1024 : ℝ)) 5175 4151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4125625403/10000000000 : ℝ), (3660716179/10000000000 : ℝ), (2313979033/5000000000 : ℝ)] ![(16580816679053/50000000000000 : ℝ), (7142384888321/25000000000000 : ℝ), (38268827067589/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4125625403/10000000000 : ℝ)|^5175 ≤ (16580816679053/50000000000000 : ℝ)^4151
        have hw : |(4125625403/10000000000 : ℝ)|=(4125625403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3660716179/10000000000 : ℝ)|^5175 ≤ (7142384888321/25000000000000 : ℝ)^4151
        have hw : |(3660716179/10000000000 : ℝ)|=(3660716179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2313979033/5000000000 : ℝ)|^5175 ≤ (38268827067589/100000000000000 : ℝ)^4151
        have hw : |(2313979033/5000000000 : ℝ)|=(2313979033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1694_s2_4 (p : ℝ) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1471968817/10000000000 : ℝ)*x 0 + (1284752731/2500000000 : ℝ)*x 1 + (2738791793/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1471968817/10000000000 : ℝ)^5175 ≤ (1146937027069/12500000000000 : ℝ)^4151 := by
    have hnat : (1471968817 : ℕ)^5175*12500000000000^4151 ≤ 1146937027069^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1471968817 10000000000 1146937027069 12500000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1284752731/2500000000 : ℝ)^5175 ≤ (340680405027/781250000000 : ℝ)^4151 := by
    have hnat : (1284752731 : ℕ)^5175*781250000000^4151 ≤ 340680405027^4151*2500000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1284752731 2500000000 340680405027 781250000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2738791793/5000000000 : ℝ)^5175 ≤ (11804352981697/25000000000000 : ℝ)^4151 := by
    have hnat : (2738791793 : ℕ)^5175*25000000000000^4151 ≤ 11804352981697^4151*5000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2738791793 5000000000 11804352981697 25000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5175/1024 : ℝ)) 5175 4151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1471968817/10000000000 : ℝ), (1284752731/2500000000 : ℝ), (2738791793/5000000000 : ℝ)] ![(1146937027069/12500000000000 : ℝ), (340680405027/781250000000 : ℝ), (11804352981697/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1471968817/10000000000 : ℝ)|^5175 ≤ (1146937027069/12500000000000 : ℝ)^4151
        have hw : |(-1471968817/10000000000 : ℝ)|=(1471968817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1284752731/2500000000 : ℝ)|^5175 ≤ (340680405027/781250000000 : ℝ)^4151
        have hw : |(1284752731/2500000000 : ℝ)|=(1284752731/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2738791793/5000000000 : ℝ)|^5175 ≤ (11804352981697/25000000000000 : ℝ)^4151
        have hw : |(2738791793/5000000000 : ℝ)|=(2738791793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1694_s2_5 (p : ℝ) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1314134923/2500000000 : ℝ)*x 0 + (-261849433/2000000000 : ℝ)*x 1 + (17117449/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1314134923/2500000000 : ℝ)^5175 ≤ (22426944498607/50000000000000 : ℝ)^4151 := by
    have hnat : (1314134923 : ℕ)^5175*50000000000000^4151 ≤ 22426944498607^4151*2500000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314134923 2500000000 22426944498607 50000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (261849433/2000000000 : ℝ)^5175 ≤ (1585739609207/20000000000000 : ℝ)^4151 := by
    have hnat : (261849433 : ℕ)^5175*20000000000000^4151 ≤ 1585739609207^4151*2000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261849433 2000000000 1585739609207 20000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (17117449/31250000 : ℝ)^5175 ≤ (47217412936967/100000000000000 : ℝ)^4151 := by
    have hnat : (17117449 : ℕ)^5175*100000000000000^4151 ≤ 47217412936967^4151*31250000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17117449 31250000 47217412936967 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5175/1024 : ℝ)) 5175 4151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1314134923/2500000000 : ℝ), (-261849433/2000000000 : ℝ), (17117449/31250000 : ℝ)] ![(22426944498607/50000000000000 : ℝ), (1585739609207/20000000000000 : ℝ), (47217412936967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1314134923/2500000000 : ℝ)|^5175 ≤ (22426944498607/50000000000000 : ℝ)^4151
        have hw : |(1314134923/2500000000 : ℝ)|=(1314134923/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-261849433/2000000000 : ℝ)|^5175 ≤ (1585739609207/20000000000000 : ℝ)^4151
        have hw : |(-261849433/2000000000 : ℝ)|=(261849433/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(17117449/31250000 : ℝ)|^5175 ≤ (47217412936967/100000000000000 : ℝ)^4151
        have hw : |(17117449/31250000 : ℝ)|=(17117449/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1694_s2_6 (p : ℝ) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5256539699/10000000000 : ℝ)*x 0 + (547758369/1000000000 : ℝ)*x 1 + (-1309247141/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256539699/10000000000 : ℝ)^5175 ≤ (140168403349/312500000000 : ℝ)^4151 := by
    have hnat : (5256539699 : ℕ)^5175*312500000000^4151 ≤ 140168403349^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256539699 10000000000 140168403349 312500000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (547758369/1000000000 : ℝ)^5175 ≤ (47217413044433/100000000000000 : ℝ)^4151 := by
    have hnat : (547758369 : ℕ)^5175*100000000000000^4151 ≤ 47217413044433^4151*1000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547758369 1000000000 47217413044433 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1309247141/10000000000 : ℝ)^5175 ≤ (7928697864839/100000000000000 : ℝ)^4151 := by
    have hnat : (1309247141 : ℕ)^5175*100000000000000^4151 ≤ 7928697864839^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309247141 10000000000 7928697864839 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5175/1024 : ℝ)) 5175 4151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256539699/10000000000 : ℝ), (547758369/1000000000 : ℝ), (-1309247141/10000000000 : ℝ)] ![(140168403349/312500000000 : ℝ), (47217413044433/100000000000000 : ℝ), (7928697864839/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256539699/10000000000 : ℝ)|^5175 ≤ (140168403349/312500000000 : ℝ)^4151
        have hw : |(5256539699/10000000000 : ℝ)|=(5256539699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(547758369/1000000000 : ℝ)|^5175 ≤ (47217413044433/100000000000000 : ℝ)^4151
        have hw : |(547758369/1000000000 : ℝ)|=(547758369/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1309247141/10000000000 : ℝ)|^5175 ≤ (7928697864839/100000000000000 : ℝ)^4151
        have hw : |(-1309247141/10000000000 : ℝ)|=(1309247141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1694_s2_7 (p : ℝ) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2063038827/5000000000 : ℝ)*x 0 + (1154335661/2500000000 : ℝ)*x 1 + (917872697/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2063038827/5000000000 : ℝ)^5175 ≤ (1658308267513/5000000000000 : ℝ)^4151 := by
    have hnat : (2063038827 : ℕ)^5175*5000000000000^4151 ≤ 1658308267513^4151*5000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063038827 5000000000 1658308267513 5000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1154335661/2500000000 : ℝ)^5175 ≤ (19079712231529/50000000000000 : ℝ)^4151 := by
    have hnat : (1154335661 : ℕ)^5175*50000000000000^4151 ≤ 19079712231529^4151*2500000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1154335661 2500000000 19079712231529 50000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (917872697/2500000000 : ℝ)^5175 ≤ (28674410175027/100000000000000 : ℝ)^4151 := by
    have hnat : (917872697 : ℕ)^5175*100000000000000^4151 ≤ 28674410175027^4151*2500000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      917872697 2500000000 28674410175027 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5175/1024 : ℝ)) 5175 4151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2063038827/5000000000 : ℝ), (1154335661/2500000000 : ℝ), (917872697/2500000000 : ℝ)] ![(1658308267513/5000000000000 : ℝ), (19079712231529/50000000000000 : ℝ), (28674410175027/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2063038827/5000000000 : ℝ)|^5175 ≤ (1658308267513/5000000000000 : ℝ)^4151
        have hw : |(2063038827/5000000000 : ℝ)|=(2063038827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1154335661/2500000000 : ℝ)|^5175 ≤ (19079712231529/50000000000000 : ℝ)^4151
        have hw : |(1154335661/2500000000 : ℝ)|=(1154335661/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(917872697/2500000000 : ℝ)|^5175 ≤ (28674410175027/100000000000000 : ℝ)^4151
        have hw : |(917872697/2500000000 : ℝ)|=(917872697/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1694_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9484113/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (441/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1899/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (9853/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17227/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (441/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1899/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (441/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1899/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (441/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1899/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (441/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1899/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (441/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1899/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (441/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1899/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1899/20000 : ℝ) ^ (5167/1024 : ℝ) ≤ (173174311947139/25000000000000000000 : ℝ) := by
    have hpowers : (1899/20000 : ℝ)^5167 ≤ (173174311947139/25000000000000000000 : ℝ)^1024 := by
      have hnat : (1899 : ℕ)^5167*25000000000000000000^1024 ≤ 173174311947139^1024*20000^5167 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1899 20000 173174311947139 25000000000000000000 5167 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1899/20000 : ℝ)) (X := (173174311947139/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5167 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (441/2500 : ℝ) ^ (5167/1024 : ℝ) ≤ (15772784372602307/100000000000000000000 : ℝ) := by
    have hpowers : (441/2500 : ℝ)^5167 ≤ (15772784372602307/100000000000000000000 : ℝ)^1024 := by
      have hnat : (441 : ℕ)^5167*100000000000000000000^1024 ≤ 15772784372602307^1024*2500^5167 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        441 2500 15772784372602307 100000000000000000000 5167 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (441/2500 : ℝ)) (X := (15772784372602307/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5167 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500173174311947139/12500000000000000000 : ℝ) ≤ (10000027455701261/10000000000000000 : ℝ) ^ (5167/1024 : ℝ) := by
    have hpowers : (12500173174311947139/12500000000000000000 : ℝ)^1024 ≤ (10000027455701261/10000000000000000 : ℝ)^5167 := by
      have hnat : (12500173174311947139 : ℕ)^1024*10000000000000000^5167 ≤ 10000027455701261^5167*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500173174311947139 12500000000000000000 10000027455701261 10000000000000000 1024 5167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000027455701261/10000000000000000 : ℝ)) (X := (12500173174311947139/12500000000000000000 : ℝ)) (by norm_num) 5167 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100016465481620390863/100000000000000000000 : ℝ) ≤ (16000522068211/16000000000000 : ℝ) ^ (5167/1024 : ℝ) := by
    have hpowers : (100016465481620390863/100000000000000000000 : ℝ)^1024 ≤ (16000522068211/16000000000000 : ℝ)^5167 := by
      have hnat : (100016465481620390863 : ℕ)^1024*16000000000000^5167 ≤ 16000522068211^5167*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100016465481620390863 100000000000000000000 16000522068211 16000000000000 1024 5167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (16000522068211/16000000000000 : ℝ)) (X := (100016465481620390863/100000000000000000000 : ℝ)) (by norm_num) 5167 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50015772784372602307/50000000000000000000 : ℝ) ≤ (10000625129562489/10000000000000000 : ℝ) ^ (5167/1024 : ℝ) := by
    have hpowers : (50015772784372602307/50000000000000000000 : ℝ)^1024 ≤ (10000625129562489/10000000000000000 : ℝ)^5167 := by
      have hnat : (50015772784372602307 : ℕ)^1024*10000000000000000^5167 ≤ 10000625129562489^5167*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015772784372602307 50000000000000000000 10000625129562489 10000000000000000 1024 5167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000625129562489/10000000000000000 : ℝ)) (X := (50015772784372602307/50000000000000000000 : ℝ)) (by norm_num) 5167 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(173174311947139/25000000000000000000 : ℝ) ≤ ((1809878860297209133/1810000000000000000 : ℝ)+2*(149418465307/407250000000000 : ℝ)*(1899/20000 : ℝ))^(5167/1024 : ℝ) := by
    rw [show (1809878860297209133/1810000000000000000 : ℝ)+2*(149418465307/407250000000000 : ℝ)*(1899/20000 : ℝ)=(10000027455701261/10000000000000000 : ℝ) by norm_num, show 1+2*(173174311947139/25000000000000000000 : ℝ)=(12500173174311947139/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15772784372602307/100000000000000000000 : ℝ)+(173174311947139/25000000000000000000 : ℝ) ≤ ((1809878860297209133/1810000000000000000 : ℝ)+(149418465307/407250000000000 : ℝ)*((441/2500 : ℝ)+(1899/20000 : ℝ)))^(5167/1024 : ℝ) := by
    rw [show (1809878860297209133/1810000000000000000 : ℝ)+(149418465307/407250000000000 : ℝ)*((441/2500 : ℝ)+(1899/20000 : ℝ))=(16000522068211/16000000000000 : ℝ) by norm_num, show 1+(15772784372602307/100000000000000000000 : ℝ)+(173174311947139/25000000000000000000 : ℝ)=(100016465481620390863/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15772784372602307/100000000000000000000 : ℝ) ≤ ((1809878860297209133/1810000000000000000 : ℝ)+2*(149418465307/407250000000000 : ℝ)*(441/2500 : ℝ))^(5167/1024 : ℝ) := by
    rw [show (1809878860297209133/1810000000000000000 : ℝ)+2*(149418465307/407250000000000 : ℝ)*(441/2500 : ℝ)=(10000625129562489/10000000000000000 : ℝ) by norm_num, show 1+2*(15772784372602307/100000000000000000000 : ℝ)=(50015772784372602307/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1809878860297209133/1810000000000000000 : ℝ)*(X 1 0+X 2 0)+(149418465307/407250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5167/1024 : ℝ)) (lo := (1899/20000 : ℝ)) (hi := (441/2500 : ℝ)) (c := (1809878860297209133/1810000000000000000 : ℝ)) (alpha := (149418465307/407250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1809878860297209133/1810000000000000000 : ℝ)*(X 0 1+X 2 1)+(149418465307/407250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5167/1024 : ℝ)) (lo := (1899/20000 : ℝ)) (hi := (441/2500 : ℝ)) (c := (1809878860297209133/1810000000000000000 : ℝ)) (alpha := (149418465307/407250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1809878860297209133/1810000000000000000 : ℝ)*(X 0 2+X 1 2)+(149418465307/407250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5167/1024 : ℝ)) (lo := (1899/20000 : ℝ)) (hi := (441/2500 : ℝ)) (c := (1809878860297209133/1810000000000000000 : ℝ)) (alpha := (149418465307/407250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-735903579/5000000000 : ℝ)*X 0 0+(2740720101/5000000000 : ℝ)*X 0 1+(5135211193/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1694_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674569997/5000000000 : ℝ)*X 1 0+(-165161953/1000000000 : ℝ)*X 1 1+(1027042231/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1694_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349139931/10000000000 : ℝ)*X 2 0+(2567605541/5000000000 : ℝ)*X 2 1+(-12903279/78125000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1694_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4125625403/10000000000 : ℝ)*X 0 0+(3660716179/10000000000 : ℝ)*X 0 1+(2313979033/5000000000 : ℝ)*X 0 2+(4125625403/10000000000 : ℝ)*X 1 0+(3660716179/10000000000 : ℝ)*X 1 1+(2313979033/5000000000 : ℝ)*X 1 2+(4125625403/10000000000 : ℝ)*X 2 0+(3660716179/10000000000 : ℝ)*X 2 1+(2313979033/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1694_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1471968817/10000000000 : ℝ)*X 0 0+(1284752731/2500000000 : ℝ)*X 0 1+(2738791793/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1694_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1314134923/2500000000 : ℝ)*X 1 0+(-261849433/2000000000 : ℝ)*X 1 1+(17117449/31250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1694_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5256539699/10000000000 : ℝ)*X 2 0+(547758369/1000000000 : ℝ)*X 2 1+(-1309247141/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1694_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2063038827/5000000000 : ℝ)*X 0 0+(1154335661/2500000000 : ℝ)*X 0 1+(917872697/2500000000 : ℝ)*X 0 2+(2063038827/5000000000 : ℝ)*X 1 0+(1154335661/2500000000 : ℝ)*X 1 1+(917872697/2500000000 : ℝ)*X 1 2+(2063038827/5000000000 : ℝ)*X 2 0+(1154335661/2500000000 : ℝ)*X 2 1+(917872697/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1694_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16366222298910089141381/2262500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1160299069/100000000000000 : ℝ)*(base19) + (562601739/50000000000000 : ℝ)*(base23) + (576949/100000000000000 : ℝ)*(lower2) + (231057289/100000000000000 : ℝ)*(upper3) + (1139299/1000000000000 : ℝ)*(upper5) + (980539736856963/50000000000000 : ℝ)*(major0) + (980539736856963/50000000000000 : ℝ)*(major1) + (980539736856963/50000000000000 : ℝ)*(major2) + (1444136615073723/50000000000000 : ℝ)*(sp0) + (722070371830029/25000000000000 : ℝ)*(sp1) + (722070380603927/25000000000000 : ℝ)*(sp2) + (1033871449622801/100000000000000 : ℝ)*(sp3) + (470873587/5000000000000 : ℝ)*(sp4) + (28806643/625000000000 : ℝ)*(sp7) + (1033876058685681/100000000000000 : ℝ)*(f.failure) + (1444141323809593/50000000000000 : ℝ)*(f.sum) + (15361178252063/13575000000000000000000000000 : ℝ)*base65 + (2045038379239890763/271500000000000000000000000000000 : ℝ)*base68 + (45953874440609237/271500000000000000000000000000000 : ℝ)*base69 + (1827487569226109237/271500000000000000000000000000000 : ℝ)*base71 + (64411485842737/13575000000000000000000000000 : ℝ)*base74 + (1035117626807609237/271500000000000000000000000000000 : ℝ)*base75 + (580206153919890763/271500000000000000000000000000000 : ℝ)*base78 + (1480091460625890763/271500000000000000000000000000000 : ℝ)*base80 + (23689390229719/6787500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (85953/500000000000000000000 : ℝ)*base89 + (85953/500000000000000000000 : ℝ)*base91 + (85953/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3669963454876112022863588651/271500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (890132737/50000000000000 : ℝ)*(base19) + (2003818297/100000000000000 : ℝ)*(base23) + (285872027/100000000000000 : ℝ)*(upper3) + (97500867/100000000000000 : ℝ)*(lower4) + (284013357/100000000000000 : ℝ)*(upper5) + (2005411370147339/100000000000000 : ℝ)*(major0) + (2005411370147339/100000000000000 : ℝ)*(major1) + (2005411370147339/100000000000000 : ℝ)*(major2) + (798840003/5000000000000 : ℝ)*(sp1) + (17914502807/100000000000000 : ℝ)*(sp2) + (295357456916091/10000000000000 : ℝ)*(sp4) + (184597300755961/6250000000000 : ℝ)*(sp5) + (1476777325419903/50000000000000 : ℝ)*(sp6) + (1057247720555069/100000000000000 : ℝ)*(sp7) + (1057247720555069/100000000000000 : ℝ)*(f.failure) + (295357456916091/10000000000000 : ℝ)*(f.sum) + (1821187310273/20362500000000000000000000000 : ℝ)*base65 + (12217639652476943783/1629000000000000000000000000000000 : ℝ)*base67 + (15251351836552943783/1629000000000000000000000000000000 : ℝ)*base69 + (6387858049498943783/1629000000000000000000000000000000 : ℝ)*base71 + (67478446630477/20362500000000000000000000000 : ℝ)*base74 + (23251517902672943783/1629000000000000000000000000000000 : ℝ)*base75 + (12671756697607943783/1629000000000000000000000000000000 : ℝ)*base77 + (13567933270330943783/1629000000000000000000000000000000 : ℝ)*base79 + (7266920024201/10181250000000000000000000000 : ℝ)*base82 + (2118797/500000000000000000000 : ℝ)*base89 + (2118797/500000000000000000000 : ℝ)*base91 + (2118797/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1694_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9484113/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (441/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1899/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9853/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17227/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1694_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1694_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9484113/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9853/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17227/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1694_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1694_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1694_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9484113/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9853/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17227/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1694_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
