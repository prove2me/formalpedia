-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1617_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:53:09.236709+00:00
-- url     : https://prove2.me/submissions/f1a4876e-3e67-44c4-86ad-75819d63f969

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
theorem support_rectangle_w1617_box_0 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-708186147/5000000000 : ℝ)*x 0 + (33851953/62500000 : ℝ)*x 1 + (1083262489/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (708186147/5000000000 : ℝ)^4787 ≤ (8321335208039/100000000000000 : ℝ)^3763 := by
    have hnat : (708186147 : ℕ)^4787*100000000000000^3763 ≤ 8321335208039^3763*5000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      708186147 5000000000 8321335208039 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (33851953/62500000 : ℝ)^4787 ≤ (45839332573451/100000000000000 : ℝ)^3763 := by
    have hnat : (33851953 : ℕ)^4787*100000000000000^3763 ≤ 45839332573451^3763*62500000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33851953 62500000 45839332573451 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1083262489/2000000000 : ℝ)^4787 ≤ (45839332196633/100000000000000 : ℝ)^3763 := by
    have hnat : (1083262489 : ℕ)^4787*100000000000000^3763 ≤ 45839332196633^3763*2000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083262489 2000000000 45839332196633 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-708186147/5000000000 : ℝ), (33851953/62500000 : ℝ), (1083262489/2000000000 : ℝ)] ![(8321335208039/100000000000000 : ℝ), (45839332573451/100000000000000 : ℝ), (45839332196633/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-708186147/5000000000 : ℝ)|^4787 ≤ (8321335208039/100000000000000 : ℝ)^3763
        have hw : |(-708186147/5000000000 : ℝ)|=(708186147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(33851953/62500000 : ℝ)|^4787 ≤ (45839332573451/100000000000000 : ℝ)^3763
        have hw : |(33851953/62500000 : ℝ)|=(33851953/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1083262489/2000000000 : ℝ)|^4787 ≤ (45839332196633/100000000000000 : ℝ)^3763
        have hw : |(1083262489/2000000000 : ℝ)|=(1083262489/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1617_box_1 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (164100729/312500000 : ℝ)*x 0 + (-1648220677/10000000000 : ℝ)*x 1 + (5416312459/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (164100729/312500000 : ℝ)^4787 ≤ (11017342653389/25000000000000 : ℝ)^3763 := by
    have hnat : (164100729 : ℕ)^4787*25000000000000^3763 ≤ 11017342653389^3763*312500000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164100729 312500000 11017342653389 25000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1648220677/10000000000 : ℝ)^4787 ≤ (1009129701537/10000000000000 : ℝ)^3763 := by
    have hnat : (1648220677 : ℕ)^4787*10000000000000^3763 ≤ 1009129701537^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1648220677 10000000000 1009129701537 10000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5416312459/10000000000 : ℝ)^4787 ≤ (45839332347361/100000000000000 : ℝ)^3763 := by
    have hnat : (5416312459 : ℕ)^4787*100000000000000^3763 ≤ 45839332347361^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416312459 10000000000 45839332347361 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(164100729/312500000 : ℝ), (-1648220677/10000000000 : ℝ), (5416312459/10000000000 : ℝ)] ![(11017342653389/25000000000000 : ℝ), (1009129701537/10000000000000 : ℝ), (45839332347361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(164100729/312500000 : ℝ)|^4787 ≤ (11017342653389/25000000000000 : ℝ)^3763
        have hw : |(164100729/312500000 : ℝ)|=(164100729/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1648220677/10000000000 : ℝ)|^4787 ≤ (1009129701537/10000000000000 : ℝ)^3763
        have hw : |(-1648220677/10000000000 : ℝ)|=(1648220677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5416312459/10000000000 : ℝ)|^4787 ≤ (45839332347361/100000000000000 : ℝ)^3763
        have hw : |(5416312459/10000000000 : ℝ)|=(5416312459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1617_box_2 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2625611611/5000000000 : ℝ)*x 0 + (5416312511/10000000000 : ℝ)*x 1 + (-103013797/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2625611611/5000000000 : ℝ)^4787 ≤ (11017342370477/25000000000000 : ℝ)^3763 := by
    have hnat : (2625611611 : ℕ)^4787*25000000000000^3763 ≤ 11017342370477^3763*5000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2625611611 5000000000 11017342370477 25000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5416312511/10000000000 : ℝ)^4787 ≤ (9167866581441/20000000000000 : ℝ)^3763 := by
    have hnat : (5416312511 : ℕ)^4787*20000000000000^3763 ≤ 9167866581441^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416312511 10000000000 9167866581441 20000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (103013797/625000000 : ℝ)^4787 ≤ (10091297599517/100000000000000 : ℝ)^3763 := by
    have hnat : (103013797 : ℕ)^4787*100000000000000^3763 ≤ 10091297599517^3763*625000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103013797 625000000 10091297599517 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2625611611/5000000000 : ℝ), (5416312511/10000000000 : ℝ), (-103013797/625000000 : ℝ)] ![(11017342370477/25000000000000 : ℝ), (9167866581441/20000000000000 : ℝ), (10091297599517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2625611611/5000000000 : ℝ)|^4787 ≤ (11017342370477/25000000000000 : ℝ)^3763
        have hw : |(2625611611/5000000000 : ℝ)|=(2625611611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5416312511/10000000000 : ℝ)|^4787 ≤ (9167866581441/20000000000000 : ℝ)^3763
        have hw : |(5416312511/10000000000 : ℝ)|=(5416312511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-103013797/625000000 : ℝ)|^4787 ≤ (10091297599517/100000000000000 : ℝ)^3763
        have hw : |(-103013797/625000000 : ℝ)|=(103013797/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1617_box_3 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (448607693/1000000000 : ℝ)*x 0 + (4079787623/10000000000 : ℝ)*x 1 + (81595749/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (448607693/1000000000 : ℝ)^4787 ≤ (9017196745981/25000000000000 : ℝ)^3763 := by
    have hnat : (448607693 : ℕ)^4787*25000000000000^3763 ≤ 9017196745981^3763*1000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448607693 1000000000 9017196745981 25000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4079787623/10000000000 : ℝ)^4787 ≤ (31965607363241/100000000000000 : ℝ)^3763 := by
    have hnat : (4079787623 : ℕ)^4787*100000000000000^3763 ≤ 31965607363241^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4079787623 10000000000 31965607363241 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (81595749/200000000 : ℝ)^4787 ≤ (3196560563891/10000000000000 : ℝ)^3763 := by
    have hnat : (81595749 : ℕ)^4787*10000000000000^3763 ≤ 3196560563891^3763*200000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81595749 200000000 3196560563891 10000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(448607693/1000000000 : ℝ), (4079787623/10000000000 : ℝ), (81595749/200000000 : ℝ)] ![(9017196745981/25000000000000 : ℝ), (31965607363241/100000000000000 : ℝ), (3196560563891/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(448607693/1000000000 : ℝ)|^4787 ≤ (9017196745981/25000000000000 : ℝ)^3763
        have hw : |(448607693/1000000000 : ℝ)|=(448607693/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4079787623/10000000000 : ℝ)|^4787 ≤ (31965607363241/100000000000000 : ℝ)^3763
        have hw : |(4079787623/10000000000 : ℝ)|=(4079787623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(81595749/200000000 : ℝ)|^4787 ≤ (3196560563891/10000000000000 : ℝ)^3763
        have hw : |(81595749/200000000 : ℝ)|=(81595749/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1617_box_4 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1968010591/10000000000 : ℝ)*x 0 + (1629527/3125000 : ℝ)*x 1 + (1042897269/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1968010591/10000000000 : ℝ)^4787 ≤ (395153527971/3125000000000 : ℝ)^3763 := by
    have hnat : (1968010591 : ℕ)^4787*3125000000000^3763 ≤ 395153527971^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1968010591 10000000000 395153527971 3125000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1629527/3125000 : ℝ)^4787 ≤ (21838771918227/50000000000000 : ℝ)^3763 := by
    have hnat : (1629527 : ℕ)^4787*50000000000000^3763 ≤ 21838771918227^3763*3125000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1629527 3125000 21838771918227 50000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1042897269/2000000000 : ℝ)^4787 ≤ (21838771625199/50000000000000 : ℝ)^3763 := by
    have hnat : (1042897269 : ℕ)^4787*50000000000000^3763 ≤ 21838771625199^3763*2000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042897269 2000000000 21838771625199 50000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1968010591/10000000000 : ℝ), (1629527/3125000 : ℝ), (1042897269/2000000000 : ℝ)] ![(395153527971/3125000000000 : ℝ), (21838771918227/50000000000000 : ℝ), (21838771625199/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1968010591/10000000000 : ℝ)|^4787 ≤ (395153527971/3125000000000 : ℝ)^3763
        have hw : |(-1968010591/10000000000 : ℝ)|=(1968010591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1629527/3125000 : ℝ)|^4787 ≤ (21838771918227/50000000000000 : ℝ)^3763
        have hw : |(1629527/3125000 : ℝ)|=(1629527/3125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1042897269/2000000000 : ℝ)|^4787 ≤ (21838771625199/50000000000000 : ℝ)^3763
        have hw : |(1042897269/2000000000 : ℝ)|=(1042897269/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1617_box_5 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5390381203/10000000000 : ℝ)*x 0 + (-866876629/5000000000 : ℝ)*x 1 + (130362159/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5390381203/10000000000 : ℝ)^4787 ≤ (5695041559031/12500000000000 : ℝ)^3763 := by
    have hnat : (5390381203 : ℕ)^4787*12500000000000^3763 ≤ 5695041559031^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390381203 10000000000 5695041559031 12500000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (866876629/5000000000 : ℝ)^4787 ≤ (2152424820589/20000000000000 : ℝ)^3763 := by
    have hnat : (866876629 : ℕ)^4787*20000000000000^3763 ≤ 2152424820589^3763*5000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      866876629 5000000000 2152424820589 20000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (130362159/250000000 : ℝ)^4787 ≤ (5459692926279/12500000000000 : ℝ)^3763 := by
    have hnat : (130362159 : ℕ)^4787*12500000000000^3763 ≤ 5459692926279^3763*250000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130362159 250000000 5459692926279 12500000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5390381203/10000000000 : ℝ), (-866876629/5000000000 : ℝ), (130362159/250000000 : ℝ)] ![(5695041559031/12500000000000 : ℝ), (2152424820589/20000000000000 : ℝ), (5459692926279/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5390381203/10000000000 : ℝ)|^4787 ≤ (5695041559031/12500000000000 : ℝ)^3763
        have hw : |(5390381203/10000000000 : ℝ)|=(5390381203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-866876629/5000000000 : ℝ)|^4787 ≤ (2152424820589/20000000000000 : ℝ)^3763
        have hw : |(-866876629/5000000000 : ℝ)|=(866876629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(130362159/250000000 : ℝ)|^4787 ≤ (5459692926279/12500000000000 : ℝ)^3763
        have hw : |(130362159/250000000 : ℝ)|=(130362159/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1617_box_6 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (336898829/625000000 : ℝ)*x 0 + (5214486347/10000000000 : ℝ)*x 1 + (-1733753193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (336898829/625000000 : ℝ)^4787 ≤ (45560333128131/100000000000000 : ℝ)^3763 := by
    have hnat : (336898829 : ℕ)^4787*100000000000000^3763 ≤ 45560333128131^3763*625000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336898829 625000000 45560333128131 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5214486347/10000000000 : ℝ)^4787 ≤ (4367754327171/10000000000000 : ℝ)^3763 := by
    have hnat : (5214486347 : ℕ)^4787*10000000000000^3763 ≤ 4367754327171^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5214486347 10000000000 4367754327171 10000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1733753193/10000000000 : ℝ)^4787 ≤ (5381061794833/50000000000000 : ℝ)^3763 := by
    have hnat : (1733753193 : ℕ)^4787*50000000000000^3763 ≤ 5381061794833^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1733753193 10000000000 5381061794833 50000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(336898829/625000000 : ℝ), (5214486347/10000000000 : ℝ), (-1733753193/10000000000 : ℝ)] ![(45560333128131/100000000000000 : ℝ), (4367754327171/10000000000000 : ℝ), (5381061794833/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(336898829/625000000 : ℝ)|^4787 ≤ (45560333128131/100000000000000 : ℝ)^3763
        have hw : |(336898829/625000000 : ℝ)|=(336898829/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5214486347/10000000000 : ℝ)|^4787 ≤ (4367754327171/10000000000000 : ℝ)^3763
        have hw : |(5214486347/10000000000 : ℝ)|=(5214486347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1733753193/10000000000 : ℝ)|^4787 ≤ (5381061794833/50000000000000 : ℝ)^3763
        have hw : |(-1733753193/10000000000 : ℝ)|=(1733753193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1617_box_7 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1960786003/5000000000 : ℝ)*x 0 + (2180849997/5000000000 : ℝ)*x 1 + (2180850039/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1960786003/5000000000 : ℝ)^4787 ≤ (15198517994343/50000000000000 : ℝ)^3763 := by
    have hnat : (1960786003 : ℕ)^4787*50000000000000^3763 ≤ 15198517994343^3763*5000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1960786003 5000000000 15198517994343 50000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2180849997/5000000000 : ℝ)^4787 ≤ (8700370393213/25000000000000 : ℝ)^3763 := by
    have hnat : (2180849997 : ℕ)^4787*25000000000000^3763 ≤ 8700370393213^3763*5000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180849997 5000000000 8700370393213 25000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2180850039/5000000000 : ℝ)^4787 ≤ (17400741212731/50000000000000 : ℝ)^3763 := by
    have hnat : (2180850039 : ℕ)^4787*50000000000000^3763 ≤ 17400741212731^3763*5000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180850039 5000000000 17400741212731 50000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1960786003/5000000000 : ℝ), (2180849997/5000000000 : ℝ), (2180850039/5000000000 : ℝ)] ![(15198517994343/50000000000000 : ℝ), (8700370393213/25000000000000 : ℝ), (17400741212731/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1960786003/5000000000 : ℝ)|^4787 ≤ (15198517994343/50000000000000 : ℝ)^3763
        have hw : |(1960786003/5000000000 : ℝ)|=(1960786003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2180849997/5000000000 : ℝ)|^4787 ≤ (8700370393213/25000000000000 : ℝ)^3763
        have hw : |(2180849997/5000000000 : ℝ)|=(2180849997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2180850039/5000000000 : ℝ)|^4787 ≤ (17400741212731/50000000000000 : ℝ)^3763
        have hw : |(2180850039/5000000000 : ℝ)|=(2180850039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1617_box_8 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1850651133/10000000000 : ℝ)*x 0 + (2535074743/5000000000 : ℝ)*x 1 + (1089234633/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1850651133/10000000000 : ℝ)^4787 ≤ (11693553147617/100000000000000 : ℝ)^3763 := by
    have hnat : (1850651133 : ℕ)^4787*100000000000000^3763 ≤ 11693553147617^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1850651133 10000000000 11693553147617 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2535074743/5000000000 : ℝ)^4787 ≤ (10536346583039/25000000000000 : ℝ)^3763 := by
    have hnat : (2535074743 : ℕ)^4787*25000000000000^3763 ≤ 10536346583039^3763*5000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2535074743 5000000000 10536346583039 25000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1089234633/2000000000 : ℝ)^4787 ≤ (46161060504621/100000000000000 : ℝ)^3763 := by
    have hnat : (1089234633 : ℕ)^4787*100000000000000^3763 ≤ 46161060504621^3763*2000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089234633 2000000000 46161060504621 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1850651133/10000000000 : ℝ), (2535074743/5000000000 : ℝ), (1089234633/2000000000 : ℝ)] ![(11693553147617/100000000000000 : ℝ), (10536346583039/25000000000000 : ℝ), (46161060504621/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1850651133/10000000000 : ℝ)|^4787 ≤ (11693553147617/100000000000000 : ℝ)^3763
        have hw : |(-1850651133/10000000000 : ℝ)|=(1850651133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2535074743/5000000000 : ℝ)|^4787 ≤ (10536346583039/25000000000000 : ℝ)^3763
        have hw : |(2535074743/5000000000 : ℝ)|=(2535074743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1089234633/2000000000 : ℝ)|^4787 ≤ (46161060504621/100000000000000 : ℝ)^3763
        have hw : |(1089234633/2000000000 : ℝ)|=(1089234633/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1617_box_9 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (65382893/125000000 : ℝ)*x 0 + (-104647/640000 : ℝ)*x 1 + (10637057/19531250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (65382893/125000000 : ℝ)^4787 ≤ (8769930107837/20000000000000 : ℝ)^3763 := by
    have hnat : (65382893 : ℕ)^4787*20000000000000^3763 ≤ 8769930107837^3763*125000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65382893 125000000 8769930107837 20000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (104647/640000 : ℝ)^4787 ≤ (4994644366149/50000000000000 : ℝ)^3763 := by
    have hnat : (104647 : ℕ)^4787*50000000000000^3763 ≤ 4994644366149^3763*640000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104647 640000 4994644366149 50000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (10637057/19531250 : ℝ)^4787 ≤ (9232212141897/20000000000000 : ℝ)^3763 := by
    have hnat : (10637057 : ℕ)^4787*20000000000000^3763 ≤ 9232212141897^3763*19531250^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10637057 19531250 9232212141897 20000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(65382893/125000000 : ℝ), (-104647/640000 : ℝ), (10637057/19531250 : ℝ)] ![(8769930107837/20000000000000 : ℝ), (4994644366149/50000000000000 : ℝ), (9232212141897/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(65382893/125000000 : ℝ)|^4787 ≤ (8769930107837/20000000000000 : ℝ)^3763
        have hw : |(65382893/125000000 : ℝ)|=(65382893/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-104647/640000 : ℝ)|^4787 ≤ (4994644366149/50000000000000 : ℝ)^3763
        have hw : |(-104647/640000 : ℝ)|=(104647/640000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(10637057/19531250 : ℝ)|^4787 ≤ (9232212141897/20000000000000 : ℝ)^3763
        have hw : |(10637057/19531250 : ℝ)|=(10637057/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1617_box_10 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5230631077/10000000000 : ℝ)*x 0 + (5446173/10000000 : ℝ)*x 1 + (-1635110129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5230631077/10000000000 : ℝ)^4787 ≤ (8769929333593/20000000000000 : ℝ)^3763 := by
    have hnat : (5230631077 : ℕ)^4787*20000000000000^3763 ≤ 8769929333593^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230631077 10000000000 8769929333593 20000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5446173/10000000 : ℝ)^4787 ≤ (11540264681383/25000000000000 : ℝ)^3763 := by
    have hnat : (5446173 : ℕ)^4787*25000000000000^3763 ≤ 11540264681383^3763*10000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5446173 10000000 11540264681383 25000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1635110129/10000000000 : ℝ)^4787 ≤ (9989294592173/100000000000000 : ℝ)^3763 := by
    have hnat : (1635110129 : ℕ)^4787*100000000000000^3763 ≤ 9989294592173^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1635110129 10000000000 9989294592173 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5230631077/10000000000 : ℝ), (5446173/10000000 : ℝ), (-1635110129/10000000000 : ℝ)] ![(8769929333593/20000000000000 : ℝ), (11540264681383/25000000000000 : ℝ), (9989294592173/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5230631077/10000000000 : ℝ)|^4787 ≤ (8769929333593/20000000000000 : ℝ)^3763
        have hw : |(5230631077/10000000000 : ℝ)|=(5230631077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5446173/10000000 : ℝ)|^4787 ≤ (11540264681383/25000000000000 : ℝ)^3763
        have hw : |(5446173/10000000 : ℝ)|=(5446173/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1635110129/10000000000 : ℝ)|^4787 ≤ (9989294592173/100000000000000 : ℝ)^3763
        have hw : |(-1635110129/10000000000 : ℝ)|=(1635110129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1617_box_11 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4567202847/10000000000 : ℝ)*x 0 + (2019001299/5000000000 : ℝ)*x 1 + (201900139/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4567202847/10000000000 : ℝ)^4787 ≤ (36900581952873/100000000000000 : ℝ)^3763 := by
    have hnat : (4567202847 : ℕ)^4787*100000000000000^3763 ≤ 36900581952873^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4567202847 10000000000 36900581952873 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2019001299/5000000000 : ℝ)^4787 ≤ (15774854055577/50000000000000 : ℝ)^3763 := by
    have hnat : (2019001299 : ℕ)^4787*50000000000000^3763 ≤ 15774854055577^3763*5000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2019001299 5000000000 15774854055577 50000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (201900139/500000000 : ℝ)^4787 ≤ (6309941984023/20000000000000 : ℝ)^3763 := by
    have hnat : (201900139 : ℕ)^4787*20000000000000^3763 ≤ 6309941984023^3763*500000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201900139 500000000 6309941984023 20000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4567202847/10000000000 : ℝ), (2019001299/5000000000 : ℝ), (201900139/500000000 : ℝ)] ![(36900581952873/100000000000000 : ℝ), (15774854055577/50000000000000 : ℝ), (6309941984023/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4567202847/10000000000 : ℝ)|^4787 ≤ (36900581952873/100000000000000 : ℝ)^3763
        have hw : |(4567202847/10000000000 : ℝ)|=(4567202847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2019001299/5000000000 : ℝ)|^4787 ≤ (15774854055577/50000000000000 : ℝ)^3763
        have hw : |(2019001299/5000000000 : ℝ)|=(2019001299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(201900139/500000000 : ℝ)|^4787 ≤ (6309941984023/20000000000000 : ℝ)^3763
        have hw : |(201900139/500000000 : ℝ)|=(201900139/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1617_box_12 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-153240613/1000000000 : ℝ)*x 0 + (2777424527/5000000000 : ℝ)*x 1 + (5194618947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (153240613/1000000000 : ℝ)^4787 ≤ (459901824271/5000000000000 : ℝ)^3763 := by
    have hnat : (153240613 : ℕ)^4787*5000000000000^3763 ≤ 459901824271^3763*1000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      153240613 1000000000 459901824271 5000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2777424527/5000000000 : ℝ)^4787 ≤ (23668004230559/50000000000000 : ℝ)^3763 := by
    have hnat : (2777424527 : ℕ)^4787*50000000000000^3763 ≤ 23668004230559^3763*5000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2777424527 5000000000 23668004230559 50000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5194618947/10000000000 : ℝ)^4787 ≤ (21732977520383/50000000000000 : ℝ)^3763 := by
    have hnat : (5194618947 : ℕ)^4787*50000000000000^3763 ≤ 21732977520383^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5194618947 10000000000 21732977520383 50000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-153240613/1000000000 : ℝ), (2777424527/5000000000 : ℝ), (5194618947/10000000000 : ℝ)] ![(459901824271/5000000000000 : ℝ), (23668004230559/50000000000000 : ℝ), (21732977520383/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-153240613/1000000000 : ℝ)|^4787 ≤ (459901824271/5000000000000 : ℝ)^3763
        have hw : |(-153240613/1000000000 : ℝ)|=(153240613/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2777424527/5000000000 : ℝ)|^4787 ≤ (23668004230559/50000000000000 : ℝ)^3763
        have hw : |(2777424527/5000000000 : ℝ)|=(2777424527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5194618947/10000000000 : ℝ)|^4787 ≤ (21732977520383/50000000000000 : ℝ)^3763
        have hw : |(5194618947/10000000000 : ℝ)|=(5194618947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1617_box_13 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1080817421/2000000000 : ℝ)*x 0 + (-1741874293/10000000000 : ℝ)*x 1 + (5194618919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1080817421/2000000000 : ℝ)^4787 ≤ (11426937944879/25000000000000 : ℝ)^3763 := by
    have hnat : (1080817421 : ℕ)^4787*25000000000000^3763 ≤ 11426937944879^3763*2000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080817421 2000000000 11426937944879 25000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1741874293/10000000000 : ℝ)^4787 ≤ (2165258691799/20000000000000 : ℝ)^3763 := by
    have hnat : (1741874293 : ℕ)^4787*20000000000000^3763 ≤ 2165258691799^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1741874293 10000000000 2165258691799 20000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5194618919/10000000000 : ℝ)^4787 ≤ (135831108571/312500000000 : ℝ)^3763 := by
    have hnat : (5194618919 : ℕ)^4787*312500000000^3763 ≤ 135831108571^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5194618919 10000000000 135831108571 312500000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1080817421/2000000000 : ℝ), (-1741874293/10000000000 : ℝ), (5194618919/10000000000 : ℝ)] ![(11426937944879/25000000000000 : ℝ), (2165258691799/20000000000000 : ℝ), (135831108571/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1080817421/2000000000 : ℝ)|^4787 ≤ (11426937944879/25000000000000 : ℝ)^3763
        have hw : |(1080817421/2000000000 : ℝ)|=(1080817421/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1741874293/10000000000 : ℝ)|^4787 ≤ (2165258691799/20000000000000 : ℝ)^3763
        have hw : |(-1741874293/10000000000 : ℝ)|=(1741874293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5194618919/10000000000 : ℝ)|^4787 ≤ (135831108571/312500000000 : ℝ)^3763
        have hw : |(5194618919/10000000000 : ℝ)|=(5194618919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1617_box_14 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5404087077/10000000000 : ℝ)*x 0 + (103892377/200000000 : ℝ)*x 1 + (-69674977/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5404087077/10000000000 : ℝ)^4787 ≤ (22853875739123/50000000000000 : ℝ)^3763 := by
    have hnat : (5404087077 : ℕ)^4787*50000000000000^3763 ≤ 22853875739123^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404087077 10000000000 22853875739123 50000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (103892377/200000000 : ℝ)^4787 ≤ (43465954008251/100000000000000 : ℝ)^3763 := by
    have hnat : (103892377 : ℕ)^4787*100000000000000^3763 ≤ 43465954008251^3763*200000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103892377 200000000 43465954008251 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (69674977/400000000 : ℝ)^4787 ≤ (676643406417/6250000000000 : ℝ)^3763 := by
    have hnat : (69674977 : ℕ)^4787*6250000000000^3763 ≤ 676643406417^3763*400000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69674977 400000000 676643406417 6250000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5404087077/10000000000 : ℝ), (103892377/200000000 : ℝ), (-69674977/400000000 : ℝ)] ![(22853875739123/50000000000000 : ℝ), (43465954008251/100000000000000 : ℝ), (676643406417/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5404087077/10000000000 : ℝ)|^4787 ≤ (22853875739123/50000000000000 : ℝ)^3763
        have hw : |(5404087077/10000000000 : ℝ)|=(5404087077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(103892377/200000000 : ℝ)|^4787 ≤ (43465954008251/100000000000000 : ℝ)^3763
        have hw : |(103892377/200000000 : ℝ)|=(103892377/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-69674977/400000000 : ℝ)|^4787 ≤ (676643406417/6250000000000 : ℝ)^3763
        have hw : |(-69674977/400000000 : ℝ)|=(69674977/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1617_box_15 (p : ℝ) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1932189041/5000000000 : ℝ)*x 0 + (438940189/1000000000 : ℝ)*x 1 + (4389401873/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1932189041/5000000000 : ℝ)^4787 ≤ (14917098347521/50000000000000 : ℝ)^3763 := by
    have hnat : (1932189041 : ℕ)^4787*50000000000000^3763 ≤ 14917098347521^3763*5000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1932189041 5000000000 14917098347521 50000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (438940189/1000000000 : ℝ)^4787 ≤ (35082901731609/100000000000000 : ℝ)^3763 := by
    have hnat : (438940189 : ℕ)^4787*100000000000000^3763 ≤ 35082901731609^3763*1000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438940189 1000000000 35082901731609 100000000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4389401873/10000000000 : ℝ)^4787 ≤ (877072538969/2500000000000 : ℝ)^3763 := by
    have hnat : (4389401873 : ℕ)^4787*2500000000000^3763 ≤ 877072538969^3763*10000000000^4787 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4389401873 10000000000 877072538969 2500000000000 4787 3763 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4787/1024 : ℝ)) 4787 3763 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1932189041/5000000000 : ℝ), (438940189/1000000000 : ℝ), (4389401873/10000000000 : ℝ)] ![(14917098347521/50000000000000 : ℝ), (35082901731609/100000000000000 : ℝ), (877072538969/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1932189041/5000000000 : ℝ)|^4787 ≤ (14917098347521/50000000000000 : ℝ)^3763
        have hw : |(1932189041/5000000000 : ℝ)|=(1932189041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(438940189/1000000000 : ℝ)|^4787 ≤ (35082901731609/100000000000000 : ℝ)^3763
        have hw : |(438940189/1000000000 : ℝ)|=(438940189/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4389401873/10000000000 : ℝ)|^4787 ≤ (877072538969/2500000000000 : ℝ)^3763
        have hw : |(4389401873/10000000000 : ℝ)|=(4389401873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1617_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (17400031/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16329/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10481/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(32471/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(5827/10000 : ℝ) ∧ (20143/25000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (10987/12500 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16329/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10481/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16329/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10481/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16329/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10481/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16329/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10481/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16329/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10481/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16329/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10481/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10481/100000 : ℝ) ^ (4783/1024 : ℝ) ≤ (332131917700477/12500000000000000000 : ℝ) := by
    have hpowers : (10481/100000 : ℝ)^4783 ≤ (332131917700477/12500000000000000000 : ℝ)^1024 := by
      have hnat : (10481 : ℕ)^4783*12500000000000000000^1024 ≤ 332131917700477^1024*100000^4783 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10481 100000 332131917700477 12500000000000000000 4783 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10481/100000 : ℝ)) (X := (332131917700477/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4783 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16329/100000 : ℝ) ^ (4783/1024 : ℝ) ≤ (10538630518144777/50000000000000000000 : ℝ) := by
    have hpowers : (16329/100000 : ℝ)^4783 ≤ (10538630518144777/50000000000000000000 : ℝ)^1024 := by
      have hnat : (16329 : ℕ)^4783*50000000000000000000^1024 ≤ 10538630518144777^1024*100000^4783 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16329 100000 10538630518144777 50000000000000000000 4783 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16329/100000 : ℝ)) (X := (10538630518144777/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4783 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250332131917700477/6250000000000000000 : ℝ) ≤ (5000056884128273/5000000000000000 : ℝ) ^ (4783/1024 : ℝ) := by
    have hpowers : (6250332131917700477/6250000000000000000 : ℝ)^1024 ≤ (5000056884128273/5000000000000000 : ℝ)^4783 := by
      have hnat : (6250332131917700477 : ℕ)^1024*5000000000000000^4783 ≤ 5000056884128273^4783*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250332131917700477 6250000000000000000 5000056884128273 5000000000000000 1024 4783 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000056884128273/5000000000000000 : ℝ)) (X := (6250332131917700477/6250000000000000000 : ℝ)) (by norm_num) 4783 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10002373431637789337/10000000000000000000 : ℝ) ≤ (5000254042165841/5000000000000000 : ℝ) ^ (4783/1024 : ℝ) := by
    have hpowers : (10002373431637789337/10000000000000000000 : ℝ)^1024 ≤ (5000254042165841/5000000000000000 : ℝ)^4783 := by
      have hnat : (10002373431637789337 : ℕ)^1024*5000000000000000^4783 ≤ 5000254042165841^4783*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002373431637789337 10000000000000000000 5000254042165841 5000000000000000 1024 4783 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000254042165841/5000000000000000 : ℝ)) (X := (10002373431637789337/10000000000000000000 : ℝ)) (by norm_num) 4783 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25010538630518144777/25000000000000000000 : ℝ) ≤ (5000451200203409/5000000000000000 : ℝ) ^ (4783/1024 : ℝ) := by
    have hpowers : (25010538630518144777/25000000000000000000 : ℝ)^1024 ≤ (5000451200203409/5000000000000000 : ℝ)^4783 := by
      have hnat : (25010538630518144777 : ℕ)^1024*5000000000000000^4783 ≤ 5000451200203409^4783*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010538630518144777 25000000000000000000 5000451200203409 5000000000000000 1024 4783 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000451200203409/5000000000000000 : ℝ)) (X := (25010538630518144777/25000000000000000000 : ℝ)) (by norm_num) 4783 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(332131917700477/12500000000000000000 : ℝ) ≤ ((3654524978949830011/3655000000000000000 : ℝ)+2*(3080594337/4568750000000 : ℝ)*(10481/100000 : ℝ))^(4783/1024 : ℝ) := by
    rw [show (3654524978949830011/3655000000000000000 : ℝ)+2*(3080594337/4568750000000 : ℝ)*(10481/100000 : ℝ)=(5000056884128273/5000000000000000 : ℝ) by norm_num, show 1+2*(332131917700477/12500000000000000000 : ℝ)=(6250332131917700477/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10538630518144777/50000000000000000000 : ℝ)+(332131917700477/12500000000000000000 : ℝ) ≤ ((3654524978949830011/3655000000000000000 : ℝ)+(3080594337/4568750000000 : ℝ)*((16329/100000 : ℝ)+(10481/100000 : ℝ)))^(4783/1024 : ℝ) := by
    rw [show (3654524978949830011/3655000000000000000 : ℝ)+(3080594337/4568750000000 : ℝ)*((16329/100000 : ℝ)+(10481/100000 : ℝ))=(5000254042165841/5000000000000000 : ℝ) by norm_num, show 1+(10538630518144777/50000000000000000000 : ℝ)+(332131917700477/12500000000000000000 : ℝ)=(10002373431637789337/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10538630518144777/50000000000000000000 : ℝ) ≤ ((3654524978949830011/3655000000000000000 : ℝ)+2*(3080594337/4568750000000 : ℝ)*(16329/100000 : ℝ))^(4783/1024 : ℝ) := by
    rw [show (3654524978949830011/3655000000000000000 : ℝ)+2*(3080594337/4568750000000 : ℝ)*(16329/100000 : ℝ)=(5000451200203409/5000000000000000 : ℝ) by norm_num, show 1+2*(10538630518144777/50000000000000000000 : ℝ)=(25010538630518144777/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3654524978949830011/3655000000000000000 : ℝ)*(X 1 0+X 2 0)+(3080594337/4568750000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4783/1024 : ℝ)) (lo := (10481/100000 : ℝ)) (hi := (16329/100000 : ℝ)) (c := (3654524978949830011/3655000000000000000 : ℝ)) (alpha := (3080594337/4568750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3654524978949830011/3655000000000000000 : ℝ)*(X 0 1+X 2 1)+(3080594337/4568750000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4783/1024 : ℝ)) (lo := (10481/100000 : ℝ)) (hi := (16329/100000 : ℝ)) (c := (3654524978949830011/3655000000000000000 : ℝ)) (alpha := (3080594337/4568750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3654524978949830011/3655000000000000000 : ℝ)*(X 0 2+X 1 2)+(3080594337/4568750000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4783/1024 : ℝ)) (lo := (10481/100000 : ℝ)) (hi := (16329/100000 : ℝ)) (c := (3654524978949830011/3655000000000000000 : ℝ)) (alpha := (3080594337/4568750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-708186147/5000000000 : ℝ)*X 0 0+(33851953/62500000 : ℝ)*X 0 1+(1083262489/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((164100729/312500000 : ℝ)*X 1 0+(-1648220677/10000000000 : ℝ)*X 1 1+(5416312459/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2625611611/5000000000 : ℝ)*X 2 0+(5416312511/10000000000 : ℝ)*X 2 1+(-103013797/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((448607693/1000000000 : ℝ)*X 0 0+(4079787623/10000000000 : ℝ)*X 0 1+(81595749/200000000 : ℝ)*X 0 2+(448607693/1000000000 : ℝ)*X 1 0+(4079787623/10000000000 : ℝ)*X 1 1+(81595749/200000000 : ℝ)*X 1 2+(448607693/1000000000 : ℝ)*X 2 0+(4079787623/10000000000 : ℝ)*X 2 1+(81595749/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1968010591/10000000000 : ℝ)*X 0 0+(1629527/3125000 : ℝ)*X 0 1+(1042897269/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5390381203/10000000000 : ℝ)*X 1 0+(-866876629/5000000000 : ℝ)*X 1 1+(130362159/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((336898829/625000000 : ℝ)*X 2 0+(5214486347/10000000000 : ℝ)*X 2 1+(-1733753193/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1960786003/5000000000 : ℝ)*X 0 0+(2180849997/5000000000 : ℝ)*X 0 1+(2180850039/5000000000 : ℝ)*X 0 2+(1960786003/5000000000 : ℝ)*X 1 0+(2180849997/5000000000 : ℝ)*X 1 1+(2180850039/5000000000 : ℝ)*X 1 2+(1960786003/5000000000 : ℝ)*X 2 0+(2180849997/5000000000 : ℝ)*X 2 1+(2180850039/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1850651133/10000000000 : ℝ)*X 0 0+(2535074743/5000000000 : ℝ)*X 0 1+(1089234633/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((65382893/125000000 : ℝ)*X 1 0+(-104647/640000 : ℝ)*X 1 1+(10637057/19531250 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5230631077/10000000000 : ℝ)*X 2 0+(5446173/10000000 : ℝ)*X 2 1+(-1635110129/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4567202847/10000000000 : ℝ)*X 0 0+(2019001299/5000000000 : ℝ)*X 0 1+(201900139/500000000 : ℝ)*X 0 2+(4567202847/10000000000 : ℝ)*X 1 0+(2019001299/5000000000 : ℝ)*X 1 1+(201900139/500000000 : ℝ)*X 1 2+(4567202847/10000000000 : ℝ)*X 2 0+(2019001299/5000000000 : ℝ)*X 2 1+(201900139/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-153240613/1000000000 : ℝ)*X 0 0+(2777424527/5000000000 : ℝ)*X 0 1+(5194618947/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1080817421/2000000000 : ℝ)*X 1 0+(-1741874293/10000000000 : ℝ)*X 1 1+(5194618919/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5404087077/10000000000 : ℝ)*X 2 0+(103892377/200000000 : ℝ)*X 2 1+(-69674977/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1932189041/5000000000 : ℝ)*X 0 0+(438940189/1000000000 : ℝ)*X 0 1+(4389401873/10000000000 : ℝ)*X 0 2+(1932189041/5000000000 : ℝ)*X 1 0+(438940189/1000000000 : ℝ)*X 1 1+(4389401873/10000000000 : ℝ)*X 1 2+(1932189041/5000000000 : ℝ)*X 2 0+(438940189/1000000000 : ℝ)*X 2 1+(4389401873/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1617_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-32471/50000 : ℝ) ≤ (-118677315286280566265263253600247/182750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7011537/50000000000000 : ℝ)*(upper0) + (2875681/25000000000000 : ℝ)*(lower2) + (3868469/50000000000000 : ℝ)*(upper4) + (7325267/100000000000000 : ℝ)*(upper5) + (1695427138215053/100000000000000 : ℝ)*(major0) + (1695427138215053/100000000000000 : ℝ)*(major1) + (1695427138215053/100000000000000 : ℝ)*(major2) + (31382593/10000000000000 : ℝ)*(sp1) + (24860683/12500000000000 : ℝ)*(sp3) + (48762374750739/2000000000000 : ℝ)*(sp4) + (304764856867489/12500000000000 : ℝ)*(sp5) + (1219059584382921/50000000000000 : ℝ)*(sp6) + (243595369478613/25000000000000 : ℝ)*(sp7) + (107807223/25000000000000 : ℝ)*(sp8) + (243595419199979/25000000000000 : ℝ)*(f.failure) + (1219059584382921/50000000000000 : ℝ)*(f.sum) + (14924180062073/1827500000000000000000000000 : ℝ)*base65 + (3919610894484155583/365500000000000000000000000000000 : ℝ)*base67 + (2433805837817155583/365500000000000000000000000000000 : ℝ)*base69 + (3890739853576155583/365500000000000000000000000000000 : ℝ)*base71 + (10097874441703/1827500000000000000000000000 : ℝ)*base73 + (2408648012287155583/365500000000000000000000000000000 : ℝ)*base75 + (4317126630140155583/365500000000000000000000000000000 : ℝ)*base77 + (3351503403023155583/365500000000000000000000000000000 : ℝ)*base79 + (2916195833763/1827500000000000000000000000 : ℝ)*base81 + (2700651/250000000000000000000 : ℝ)*base90 + (2700651/250000000000000000000 : ℝ)*base92 + (2700651/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (5827/10000 : ℝ) ≤ (26623106685004990952745265946613/45687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4800523/100000000000000 : ℝ)*(lower0) + (2848769/20000000000000 : ℝ)*(upper1) + (5839033/25000000000000 : ℝ)*(upper2) + (4442711/25000000000000 : ℝ)*(upper3) + (46173/2500000000000 : ℝ)*(lower5) + (445297876431239/25000000000000 : ℝ)*(major0) + (445297876431239/25000000000000 : ℝ)*(major1) + (445297876431239/25000000000000 : ℝ)*(major2) + (78727734151101/3125000000000 : ℝ)*(sp0) + (78727734151101/3125000000000 : ℝ)*(sp1) + (157455453263927/6250000000000 : ℝ)*(sp2) + (511834904973763/50000000000000 : ℝ)*(sp3) + (240612401/100000000000000 : ℝ)*(sp6) + (1645422269/100000000000000 : ℝ)*(sp11) + (255917863842449/25000000000000 : ℝ)*(f.failure) + (78727734151101/3125000000000 : ℝ)*(f.sum) + (24282332447927/3655000000000000000000000000 : ℝ)*base65 + (153070900649513629/91375000000000000000000000000000 : ℝ)*base67 + (513170835519513629/91375000000000000000000000000000 : ℝ)*base69 + (632840254215888629/91375000000000000000000000000000 : ℝ)*base71 + (2639856794859/456875000000000000000000000 : ℝ)*base73 + (2675788635016486371/91375000000000000000000000000000 : ℝ)*base76 + (485290876461888629/91375000000000000000000000000000 : ℝ)*base77 + (741448768151611371/91375000000000000000000000000000 : ℝ)*base80 + (25455593405513/3655000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (1715919/250000000000000000000 : ℝ)*base89 + (1715919/250000000000000000000 : ℝ)*base91 + (1715919/250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (20143/25000 : ℝ) ≤ (920316825417618499223529996651/1142187500000000000000000000000 : ℝ) := by norm_num
    linear_combination (4741507/10000000000000 : ℝ)*(upper1) + (204255099/100000000000000 : ℝ)*(upper2) + (32401643/50000000000000 : ℝ)*(lower5) + (23558994574747/1250000000000 : ℝ)*(major0) + (23558994574747/1250000000000 : ℝ)*(major1) + (23558994574747/1250000000000 : ℝ)*(major2) + (17800448069/25000000000000 : ℝ)*(sp1) + (4722606383/25000000000000 : ℝ)*(sp2) + (22274768443/100000000000000 : ℝ)*(sp3) + (6912165479/100000000000000 : ℝ)*(sp4) + (1329701836928701/50000000000000 : ℝ)*(sp8) + (1329669692115303/50000000000000 : ℝ)*(sp9) + (53187833911947/2000000000000 : ℝ)*(sp10) + (1083147959801691/100000000000000 : ℝ)*(sp11) + (541585117285067/50000000000000 : ℝ)*(f.failure) + (1329705293011441/50000000000000 : ℝ)*(f.sum) + (14481167607/45687500000000000000000000 : ℝ)*base65 + (9096967225475967/4568750000000000000000000000000 : ℝ)*base67 + (21125257993374033/4568750000000000000000000000000 : ℝ)*base70 + (56814315981624033/4568750000000000000000000000000 : ℝ)*base72 + (6113366792429/731000000000000000000000000 : ℝ)*base73 + (53394954210830283/4568750000000000000000000000000 : ℝ)*base76 + (43079204667036533/4568750000000000000000000000000 : ℝ)*base78 + (38164009726274033/4568750000000000000000000000000 : ℝ)*base80 + (194268340847/182750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1637077/500000000000000000000 : ℝ)*base89 + (1637077/500000000000000000000 : ℝ)*base91 + (1637077/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-10987/12500 : ℝ) ≤ (-40156199296099559494541097799383/45687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (62977/100000000000000 : ℝ)*(lower0) + (15706219/100000000000000 : ℝ)*(upper1) + (3656423/50000000000000 : ℝ)*(upper3) + (33836771/100000000000000 : ℝ)*(lower4) + (963561584841951/50000000000000 : ℝ)*(major0) + (963561584841951/50000000000000 : ℝ)*(major1) + (963561584841951/50000000000000 : ℝ)*(major2) + (312351679/100000000000000 : ℝ)*(sp4) + (4754179877/25000000000000 : ℝ)*(sp6) + (5459918041/50000000000000 : ℝ)*(sp7) + (1388001838650917/50000000000000 : ℝ)*(sp12) + (1388001994826757/50000000000000 : ℝ)*(sp13) + (555196994586801/20000000000000 : ℝ)*(sp14) + (553764579251401/50000000000000 : ℝ)*(sp15) + (276885019584721/25000000000000 : ℝ)*(f.failure) + (1388001994826757/50000000000000 : ℝ)*(f.sum) + (4703154096701/3655000000000000000000000000 : ℝ)*base66 + (1072347602330191461/182750000000000000000000000000000 : ℝ)*base67 + (1588118418704941461/182750000000000000000000000000000 : ℝ)*base69 + (585584758610308539/182750000000000000000000000000000 : ℝ)*base72 + (13361391967627/1827500000000000000000000000 : ℝ)*base73 + (60025179254191461/182750000000000000000000000000000 : ℝ)*base75 + (979574961580441461/182750000000000000000000000000000 : ℝ)*base77 + (1923319159682691461/182750000000000000000000000000000 : ℝ)*base79 + (1357439560731/3655000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (2473649/250000000000000000000 : ℝ)*base90 + (2473649/250000000000000000000 : ℝ)*base92 + (2473649/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1617_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (17400031/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16329/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10481/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(32471/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(5827/10000 : ℝ) else (20143/25000 : ℝ) ≤ X j i ∧ X j i ≤ (10987/12500 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1617_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1617_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (17400031/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16329/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10481/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(32471/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(5827/10000 : ℝ) else (20143/25000 : ℝ) ≤ X j i ∧ X j i ≤ (10987/12500 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1617_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4783/1024 : ℝ) ≤ p) (hpb : p ≤ (4787/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (17400031/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16329/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10481/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(32471/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(5827/10000 : ℝ) else (20143/25000 : ℝ) ≤ X j i ∧ X j i ≤ (10987/12500 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1617_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
