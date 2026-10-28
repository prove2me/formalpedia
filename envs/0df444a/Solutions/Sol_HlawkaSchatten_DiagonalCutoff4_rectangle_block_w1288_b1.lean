-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1288_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:25:06.576997+00:00
-- url     : https://prove2.me/submissions/1cf8c0b2-76a9-407e-8b1d-c4a563f030e8

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
theorem support_rectangle_w1288_s3_0 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-261143557/1250000000 : ℝ)*x 0 + (2717340419/5000000000 : ℝ)*x 1 + (5225183111/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (261143557/1250000000 : ℝ)^531 ≤ (12705138486651/100000000000000 : ℝ)^403 := by
    have hnat : (261143557 : ℕ)^531*100000000000000^403 ≤ 12705138486651^403*1250000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261143557 1250000000 12705138486651 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2717340419/5000000000 : ℝ)^531 ≤ (223887885073/500000000000 : ℝ)^403 := by
    have hnat : (2717340419 : ℕ)^531*500000000000^403 ≤ 223887885073^403*5000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717340419 5000000000 223887885073 500000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5225183111/10000000000 : ℝ)^531 ≤ (10629321121829/25000000000000 : ℝ)^403 := by
    have hnat : (5225183111 : ℕ)^531*25000000000000^403 ≤ 10629321121829^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5225183111 10000000000 10629321121829 25000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-261143557/1250000000 : ℝ), (2717340419/5000000000 : ℝ), (5225183111/10000000000 : ℝ)] ![(12705138486651/100000000000000 : ℝ), (223887885073/500000000000 : ℝ), (10629321121829/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-261143557/1250000000 : ℝ)|^531 ≤ (12705138486651/100000000000000 : ℝ)^403
        have hw : |(-261143557/1250000000 : ℝ)|=(261143557/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2717340419/5000000000 : ℝ)|^531 ≤ (223887885073/500000000000 : ℝ)^403
        have hw : |(2717340419/5000000000 : ℝ)|=(2717340419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5225183111/10000000000 : ℝ)|^531 ≤ (10629321121829/25000000000000 : ℝ)^403
        have hw : |(5225183111/10000000000 : ℝ)|=(5225183111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1288_s3_1 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5354706389/10000000000 : ℝ)*x 0 + (-2196380027/10000000000 : ℝ)*x 1 + (1306295773/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354706389/10000000000 : ℝ)^531 ≤ (43911397852393/100000000000000 : ℝ)^403 := by
    have hnat : (5354706389 : ℕ)^531*100000000000000^403 ≤ 43911397852393^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354706389 10000000000 43911397852393 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2196380027/10000000000 : ℝ)^531 ≤ (13571317852217/100000000000000 : ℝ)^403 := by
    have hnat : (2196380027 : ℕ)^531*100000000000000^403 ≤ 13571317852217^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2196380027 10000000000 13571317852217 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1306295773/2500000000 : ℝ)^531 ≤ (5314660535451/12500000000000 : ℝ)^403 := by
    have hnat : (1306295773 : ℕ)^531*12500000000000^403 ≤ 5314660535451^403*2500000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1306295773 2500000000 5314660535451 12500000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354706389/10000000000 : ℝ), (-2196380027/10000000000 : ℝ), (1306295773/2500000000 : ℝ)] ![(43911397852393/100000000000000 : ℝ), (13571317852217/100000000000000 : ℝ), (5314660535451/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354706389/10000000000 : ℝ)|^531 ≤ (43911397852393/100000000000000 : ℝ)^403
        have hw : |(5354706389/10000000000 : ℝ)|=(5354706389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2196380027/10000000000 : ℝ)|^531 ≤ (13571317852217/100000000000000 : ℝ)^403
        have hw : |(-2196380027/10000000000 : ℝ)|=(2196380027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1306295773/2500000000 : ℝ)|^531 ≤ (5314660535451/12500000000000 : ℝ)^403
        have hw : |(1306295773/2500000000 : ℝ)|=(1306295773/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1288_s3_2 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2677353147/5000000000 : ℝ)*x 0 + (5225183441/10000000000 : ℝ)*x 1 + (-2196379693/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677353147/5000000000 : ℝ)^531 ≤ (43911396825903/100000000000000 : ℝ)^403 := by
    have hnat : (2677353147 : ℕ)^531*100000000000000^403 ≤ 43911396825903^403*5000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677353147 5000000000 43911396825903 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5225183441/10000000000 : ℝ)^531 ≤ (21258644012697/50000000000000 : ℝ)^403 := by
    have hnat : (5225183441 : ℕ)^531*50000000000000^403 ≤ 21258644012697^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5225183441 10000000000 21258644012697 50000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2196379693/10000000000 : ℝ)^531 ≤ (13571315132959/100000000000000 : ℝ)^403 := by
    have hnat : (2196379693 : ℕ)^531*100000000000000^403 ≤ 13571315132959^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2196379693 10000000000 13571315132959 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677353147/5000000000 : ℝ), (5225183441/10000000000 : ℝ), (-2196379693/10000000000 : ℝ)] ![(43911396825903/100000000000000 : ℝ), (21258644012697/50000000000000 : ℝ), (13571315132959/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677353147/5000000000 : ℝ)|^531 ≤ (43911396825903/100000000000000 : ℝ)^403
        have hw : |(2677353147/5000000000 : ℝ)|=(2677353147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5225183441/10000000000 : ℝ)|^531 ≤ (21258644012697/50000000000000 : ℝ)^403
        have hw : |(5225183441/10000000000 : ℝ)|=(5225183441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2196379693/10000000000 : ℝ)|^531 ≤ (13571315132959/100000000000000 : ℝ)^403
        have hw : |(-2196379693/10000000000 : ℝ)|=(2196379693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1288_s3_3 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4339488893/10000000000 : ℝ)*x 0 + (4129629383/10000000000 : ℝ)*x 1 + (113988459/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4339488893/10000000000 : ℝ)^531 ≤ (8321902162187/25000000000000 : ℝ)^403 := by
    have hnat : (4339488893 : ℕ)^531*25000000000000^403 ≤ 8321902162187^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4339488893 10000000000 8321902162187 25000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4129629383/10000000000 : ℝ)^531 ≤ (7795744230519/25000000000000 : ℝ)^403 := by
    have hnat : (4129629383 : ℕ)^531*25000000000000^403 ≤ 7795744230519^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4129629383 10000000000 7795744230519 25000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (113988459/250000000 : ℝ)^531 ≤ (88823536039/250000000000 : ℝ)^403 := by
    have hnat : (113988459 : ℕ)^531*250000000000^403 ≤ 88823536039^403*250000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113988459 250000000 88823536039 250000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4339488893/10000000000 : ℝ), (4129629383/10000000000 : ℝ), (113988459/250000000 : ℝ)] ![(8321902162187/25000000000000 : ℝ), (7795744230519/25000000000000 : ℝ), (88823536039/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4339488893/10000000000 : ℝ)|^531 ≤ (8321902162187/25000000000000 : ℝ)^403
        have hw : |(4339488893/10000000000 : ℝ)|=(4339488893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4129629383/10000000000 : ℝ)|^531 ≤ (7795744230519/25000000000000 : ℝ)^403
        have hw : |(4129629383/10000000000 : ℝ)|=(4129629383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(113988459/250000000 : ℝ)|^531 ≤ (88823536039/250000000000 : ℝ)^403
        have hw : |(113988459/250000000 : ℝ)|=(113988459/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1288_s3_4 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-417834269/2000000000 : ℝ)*x 0 + (522608807/1000000000 : ℝ)*x 1 + (1358442541/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (417834269/2000000000 : ℝ)^531 ≤ (12705321898399/100000000000000 : ℝ)^403 := by
    have hnat : (417834269 : ℕ)^531*100000000000000^403 ≤ 12705321898399^403*2000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417834269 2000000000 12705321898399 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (522608807/1000000000 : ℝ)^531 ≤ (4252698722583/10000000000000 : ℝ)^403 := by
    have hnat : (522608807 : ℕ)^531*10000000000000^403 ≤ 4252698722583^403*1000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522608807 1000000000 4252698722583 10000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1358442541/2500000000 : ℝ)^531 ≤ (44767690859949/100000000000000 : ℝ)^403 := by
    have hnat : (1358442541 : ℕ)^531*100000000000000^403 ≤ 44767690859949^403*2500000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358442541 2500000000 44767690859949 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-417834269/2000000000 : ℝ), (522608807/1000000000 : ℝ), (1358442541/2500000000 : ℝ)] ![(12705321898399/100000000000000 : ℝ), (4252698722583/10000000000000 : ℝ), (44767690859949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-417834269/2000000000 : ℝ)|^531 ≤ (12705321898399/100000000000000 : ℝ)^403
        have hw : |(-417834269/2000000000 : ℝ)|=(417834269/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(522608807/1000000000 : ℝ)|^531 ≤ (4252698722583/10000000000000 : ℝ)^403
        have hw : |(522608807/1000000000 : ℝ)|=(522608807/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1358442541/2500000000 : ℝ)|^531 ≤ (44767690859949/100000000000000 : ℝ)^403
        have hw : |(1358442541/2500000000 : ℝ)|=(1358442541/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1288_s3_5 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5301092467/10000000000 : ℝ)*x 0 + (-993896407/5000000000 : ℝ)*x 1 + (543377011/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5301092467/10000000000 : ℝ)^531 ≤ (21666507131567/50000000000000 : ℝ)^403 := by
    have hnat : (5301092467 : ℕ)^531*50000000000000^403 ≤ 21666507131567^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5301092467 10000000000 21666507131567 50000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (993896407/5000000000 : ℝ)^531 ≤ (5949647720113/50000000000000 : ℝ)^403 := by
    have hnat : (993896407 : ℕ)^531*50000000000000^403 ≤ 5949647720113^403*5000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      993896407 5000000000 5949647720113 50000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (543377011/1000000000 : ℝ)^531 ≤ (11191922568437/25000000000000 : ℝ)^403 := by
    have hnat : (543377011 : ℕ)^531*25000000000000^403 ≤ 11191922568437^403*1000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543377011 1000000000 11191922568437 25000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5301092467/10000000000 : ℝ), (-993896407/5000000000 : ℝ), (543377011/1000000000 : ℝ)] ![(21666507131567/50000000000000 : ℝ), (5949647720113/50000000000000 : ℝ), (11191922568437/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5301092467/10000000000 : ℝ)|^531 ≤ (21666507131567/50000000000000 : ℝ)^403
        have hw : |(5301092467/10000000000 : ℝ)|=(5301092467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-993896407/5000000000 : ℝ)|^531 ≤ (5949647720113/50000000000000 : ℝ)^403
        have hw : |(-993896407/5000000000 : ℝ)|=(993896407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(543377011/1000000000 : ℝ)|^531 ≤ (11191922568437/25000000000000 : ℝ)^403
        have hw : |(543377011/1000000000 : ℝ)|=(543377011/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1288_s3_6 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (662636561/1250000000 : ℝ)*x 0 + (5433770067/10000000000 : ℝ)*x 1 + (-397558569/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (662636561/1250000000 : ℝ)^531 ≤ (43333014489319/100000000000000 : ℝ)^403 := by
    have hnat : (662636561 : ℕ)^531*100000000000000^403 ≤ 43333014489319^403*1250000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      662636561 1250000000 43333014489319 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5433770067/10000000000 : ℝ)^531 ≤ (22383844903479/50000000000000 : ℝ)^403 := by
    have hnat : (5433770067 : ℕ)^531*50000000000000^403 ≤ 22383844903479^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433770067 10000000000 22383844903479 50000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (397558569/2000000000 : ℝ)^531 ≤ (11899295684739/100000000000000 : ℝ)^403 := by
    have hnat : (397558569 : ℕ)^531*100000000000000^403 ≤ 11899295684739^403*2000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397558569 2000000000 11899295684739 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(662636561/1250000000 : ℝ), (5433770067/10000000000 : ℝ), (-397558569/2000000000 : ℝ)] ![(43333014489319/100000000000000 : ℝ), (22383844903479/50000000000000 : ℝ), (11899295684739/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(662636561/1250000000 : ℝ)|^531 ≤ (43333014489319/100000000000000 : ℝ)^403
        have hw : |(662636561/1250000000 : ℝ)|=(662636561/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5433770067/10000000000 : ℝ)|^531 ≤ (22383844903479/50000000000000 : ℝ)^403
        have hw : |(5433770067/10000000000 : ℝ)|=(5433770067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-397558569/2000000000 : ℝ)|^531 ≤ (11899295684739/100000000000000 : ℝ)^403
        have hw : |(-397558569/2000000000 : ℝ)|=(397558569/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1288_s3_7 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (867907201/2000000000 : ℝ)*x 0 + (4557681261/10000000000 : ℝ)*x 1 + (1032874427/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (867907201/2000000000 : ℝ)^531 ≤ (1664404241143/5000000000000 : ℝ)^403 := by
    have hnat : (867907201 : ℕ)^531*5000000000000^403 ≤ 1664404241143^403*2000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      867907201 2000000000 1664404241143 5000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4557681261/10000000000 : ℝ)^531 ≤ (8877587059743/25000000000000 : ℝ)^403 := by
    have hnat : (4557681261 : ℕ)^531*25000000000000^403 ≤ 8877587059743^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4557681261 10000000000 8877587059743 25000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1032874427/2500000000 : ℝ)^531 ≤ (31201566930863/100000000000000 : ℝ)^403 := by
    have hnat : (1032874427 : ℕ)^531*100000000000000^403 ≤ 31201566930863^403*2500000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1032874427 2500000000 31201566930863 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(867907201/2000000000 : ℝ), (4557681261/10000000000 : ℝ), (1032874427/2500000000 : ℝ)] ![(1664404241143/5000000000000 : ℝ), (8877587059743/25000000000000 : ℝ), (31201566930863/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(867907201/2000000000 : ℝ)|^531 ≤ (1664404241143/5000000000000 : ℝ)^403
        have hw : |(867907201/2000000000 : ℝ)|=(867907201/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4557681261/10000000000 : ℝ)|^531 ≤ (8877587059743/25000000000000 : ℝ)^403
        have hw : |(4557681261/10000000000 : ℝ)|=(4557681261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1032874427/2500000000 : ℝ)|^531 ≤ (31201566930863/100000000000000 : ℝ)^403
        have hw : |(1032874427/2500000000 : ℝ)|=(1032874427/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1288_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152604817/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1021/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (379/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (133/1250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (471/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1021/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (379/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1021/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (379/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1021/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (379/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1021/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (379/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1021/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (379/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1021/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (379/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (379/4000 : ℝ) ^ (4247/1024 : ℝ) ≤ (1138760206099849/20000000000000000000 : ℝ) := by
    have hpowers : (379/4000 : ℝ)^4247 ≤ (1138760206099849/20000000000000000000 : ℝ)^1024 := by
      have hnat : (379 : ℕ)^4247*20000000000000000000^1024 ≤ 1138760206099849^1024*4000^4247 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        379 4000 1138760206099849 20000000000000000000 4247 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (379/4000 : ℝ)) (X := (1138760206099849/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4247 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1021/6250 : ℝ) ^ (4247/1024 : ℝ) ≤ (27259798055964041/50000000000000000000 : ℝ) := by
    have hpowers : (1021/6250 : ℝ)^4247 ≤ (27259798055964041/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1021 : ℕ)^4247*50000000000000000000^1024 ≤ 27259798055964041^1024*6250^4247 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1021 6250 27259798055964041 50000000000000000000 4247 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1021/6250 : ℝ)) (X := (27259798055964041/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4247 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001138760206099849/10000000000000000000 : ℝ) ≤ (5000137278086661/5000000000000000 : ℝ) ^ (4247/1024 : ℝ) := by
    have hpowers : (10001138760206099849/10000000000000000000 : ℝ)^1024 ≤ (5000137278086661/5000000000000000 : ℝ)^4247 := by
      have hnat : (10001138760206099849 : ℕ)^1024*5000000000000000^4247 ≤ 5000137278086661^4247*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001138760206099849 10000000000000000000 5000137278086661 5000000000000000 1024 4247 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000137278086661/5000000000000000 : ℝ)) (X := (10001138760206099849/10000000000000000000 : ℝ)) (by norm_num) 4247 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100060213397142427327/100000000000000000000 : ℝ) ≤ (500072574094813/500000000000000 : ℝ) ^ (4247/1024 : ℝ) := by
    have hpowers : (100060213397142427327/100000000000000000000 : ℝ)^1024 ≤ (500072574094813/500000000000000 : ℝ)^4247 := by
      have hnat : (100060213397142427327 : ℕ)^1024*500000000000000^4247 ≤ 500072574094813^4247*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100060213397142427327 100000000000000000000 500072574094813 500000000000000 1024 4247 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500072574094813/500000000000000 : ℝ)) (X := (100060213397142427327/100000000000000000000 : ℝ)) (by norm_num) 4247 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25027259798055964041/25000000000000000000 : ℝ) ≤ (5001314203809599/5000000000000000 : ℝ) ^ (4247/1024 : ℝ) := by
    have hpowers : (25027259798055964041/25000000000000000000 : ℝ)^1024 ≤ (5001314203809599/5000000000000000 : ℝ)^4247 := by
      have hnat : (25027259798055964041 : ℕ)^1024*5000000000000000^4247 ≤ 5001314203809599^4247*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25027259798055964041 25000000000000000000 5001314203809599 5000000000000000 1024 4247 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001314203809599/5000000000000000 : ℝ)) (X := (25027259798055964041/25000000000000000000 : ℝ)) (by norm_num) 4247 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1138760206099849/20000000000000000000 : ℝ) ≤ ((34294790493727743571/34305000000000000000 : ℝ)+2*(588462861469/343050000000000 : ℝ)*(379/4000 : ℝ))^(4247/1024 : ℝ) := by
    rw [show (34294790493727743571/34305000000000000000 : ℝ)+2*(588462861469/343050000000000 : ℝ)*(379/4000 : ℝ)=(5000137278086661/5000000000000000 : ℝ) by norm_num, show 1+2*(1138760206099849/20000000000000000000 : ℝ)=(10001138760206099849/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27259798055964041/50000000000000000000 : ℝ)+(1138760206099849/20000000000000000000 : ℝ) ≤ ((34294790493727743571/34305000000000000000 : ℝ)+(588462861469/343050000000000 : ℝ)*((1021/6250 : ℝ)+(379/4000 : ℝ)))^(4247/1024 : ℝ) := by
    rw [show (34294790493727743571/34305000000000000000 : ℝ)+(588462861469/343050000000000 : ℝ)*((1021/6250 : ℝ)+(379/4000 : ℝ))=(500072574094813/500000000000000 : ℝ) by norm_num, show 1+(27259798055964041/50000000000000000000 : ℝ)+(1138760206099849/20000000000000000000 : ℝ)=(100060213397142427327/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27259798055964041/50000000000000000000 : ℝ) ≤ ((34294790493727743571/34305000000000000000 : ℝ)+2*(588462861469/343050000000000 : ℝ)*(1021/6250 : ℝ))^(4247/1024 : ℝ) := by
    rw [show (34294790493727743571/34305000000000000000 : ℝ)+2*(588462861469/343050000000000 : ℝ)*(1021/6250 : ℝ)=(5001314203809599/5000000000000000 : ℝ) by norm_num, show 1+2*(27259798055964041/50000000000000000000 : ℝ)=(25027259798055964041/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (34294790493727743571/34305000000000000000 : ℝ)*(X 1 0+X 2 0)+(588462861469/343050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4247/1024 : ℝ)) (lo := (379/4000 : ℝ)) (hi := (1021/6250 : ℝ)) (c := (34294790493727743571/34305000000000000000 : ℝ)) (alpha := (588462861469/343050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (34294790493727743571/34305000000000000000 : ℝ)*(X 0 1+X 2 1)+(588462861469/343050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4247/1024 : ℝ)) (lo := (379/4000 : ℝ)) (hi := (1021/6250 : ℝ)) (c := (34294790493727743571/34305000000000000000 : ℝ)) (alpha := (588462861469/343050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (34294790493727743571/34305000000000000000 : ℝ)*(X 0 2+X 1 2)+(588462861469/343050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4247/1024 : ℝ)) (lo := (379/4000 : ℝ)) (hi := (1021/6250 : ℝ)) (c := (34294790493727743571/34305000000000000000 : ℝ)) (alpha := (588462861469/343050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-261143557/1250000000 : ℝ)*X 0 0+(2717340419/5000000000 : ℝ)*X 0 1+(5225183111/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5354706389/10000000000 : ℝ)*X 1 0+(-2196380027/10000000000 : ℝ)*X 1 1+(1306295773/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2677353147/5000000000 : ℝ)*X 2 0+(5225183441/10000000000 : ℝ)*X 2 1+(-2196379693/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4339488893/10000000000 : ℝ)*X 0 0+(4129629383/10000000000 : ℝ)*X 0 1+(113988459/250000000 : ℝ)*X 0 2+(4339488893/10000000000 : ℝ)*X 1 0+(4129629383/10000000000 : ℝ)*X 1 1+(113988459/250000000 : ℝ)*X 1 2+(4339488893/10000000000 : ℝ)*X 2 0+(4129629383/10000000000 : ℝ)*X 2 1+(113988459/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-417834269/2000000000 : ℝ)*X 0 0+(522608807/1000000000 : ℝ)*X 0 1+(1358442541/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5301092467/10000000000 : ℝ)*X 1 0+(-993896407/5000000000 : ℝ)*X 1 1+(543377011/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((662636561/1250000000 : ℝ)*X 2 0+(5433770067/10000000000 : ℝ)*X 2 1+(-397558569/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((867907201/2000000000 : ℝ)*X 0 0+(4557681261/10000000000 : ℝ)*X 0 1+(1032874427/2500000000 : ℝ)*X 0 2+(867907201/2000000000 : ℝ)*X 1 0+(4557681261/10000000000 : ℝ)*X 1 1+(1032874427/2500000000 : ℝ)*X 1 2+(867907201/2000000000 : ℝ)*X 2 0+(4557681261/10000000000 : ℝ)*X 2 1+(1032874427/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1741123735952713536659225533/285875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (945484233/100000000000000 : ℝ)*(base19) + (175463047/20000000000000 : ℝ)*(base23) + (7241071/100000000000000 : ℝ)*(upper4) + (36937967/20000000000000 : ℝ)*(upper5) + (3549728145920423/100000000000000 : ℝ)*(major0) + (3549728145920423/100000000000000 : ℝ)*(major1) + (3549728145920423/100000000000000 : ℝ)*(major2) + (37291719317767/781250000000 : ℝ)*(sp0) + (2386680167848713/50000000000000 : ℝ)*(sp1) + (1193340851029523/25000000000000 : ℝ)*(sp2) + (581520989095669/25000000000000 : ℝ)*(sp3) + (24208759151/100000000000000 : ℝ)*(sp4) + (750062917/25000000000000 : ℝ)*(sp5) + (7851007929/100000000000000 : ℝ)*(sp7) + (581522951847651/25000000000000 : ℝ)*(f.failure) + (4773364281433327/100000000000000 : ℝ)*(f.sum) + (66435037809659/8576250000000000000000000000 : ℝ)*base66 + (43584438854912949467/3430500000000000000000000000000000 : ℝ)*base68 + (29668392474901449467/3430500000000000000000000000000000 : ℝ)*base70 + (54119797827326949467/3430500000000000000000000000000000 : ℝ)*base72 + (135568530671741/34305000000000000000000000000 : ℝ)*base74 + (33827367287047449467/3430500000000000000000000000000000 : ℝ)*base76 + (35731053269555949467/3430500000000000000000000000000000 : ℝ)*base78 + (6988518678810050533/3430500000000000000000000000000000 : ℝ)*base79 + (112864623861853/17152500000000000000000000000 : ℝ)*base82 + (17734867/2500000000000000000000 : ℝ)*base89 + (17734867/2500000000000000000000 : ℝ)*base91 + (17734867/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2266392802418272209880763/228700000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2258433311/100000000000000 : ℝ)*(base19) + (2381348943/100000000000000 : ℝ)*(base23) + (229346787/100000000000000 : ℝ)*(upper3) + (26079759/50000000000000 : ℝ)*(lower4) + (50056717/20000000000000 : ℝ)*(upper5) + (1432291615553/40000000000 : ℝ)*(major0) + (1432291615553/40000000000 : ℝ)*(major1) + (1432291615553/40000000000 : ℝ)*(major2) + (37198120523/100000000000000 : ℝ)*(sp1) + (37736792397/100000000000000 : ℝ)*(sp2) + (4815051448292941/100000000000000 : ℝ)*(sp4) + (4815011991739107/100000000000000 : ℝ)*(sp5) + (4815011330151601/100000000000000 : ℝ)*(sp6) + (293300787392781/12500000000000 : ℝ)*(sp7) + (293300787392781/12500000000000 : ℝ)*(f.failure) + (4815051448292941/100000000000000 : ℝ)*(f.sum) + (6847245086341/1372200000000000000000000000 : ℝ)*base65 + (8088161827115837/1372200000000000000000000000000 : ℝ)*base68 + (3559148914697837/1372200000000000000000000000000 : ℝ)*base70 + (3171234457496563/1372200000000000000000000000000 : ℝ)*base71 + (12830096758249/6861000000000000000000000000 : ℝ)*base74 + (11730430533074237/1372200000000000000000000000000 : ℝ)*base76 + (15905627282301437/1372200000000000000000000000000 : ℝ)*base78 + (2176290088261363/1372200000000000000000000000000 : ℝ)*base79 + (14690639379451/3430500000000000000000000000 : ℝ)*base81 + (1626077/1250000000000000000000 : ℝ)*base89 + (1626077/1250000000000000000000 : ℝ)*base91 + (1626077/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1288_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152604817/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1021/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (379/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (133/1250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (471/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1288_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1288_s4_0 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2091110911/10000000000 : ℝ)*x 0 + (5419244847/10000000000 : ℝ)*x 1 + (1309833243/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2091110911/10000000000 : ℝ)^531 ≤ (12720866144457/100000000000000 : ℝ)^403 := by
    have hnat : (2091110911 : ℕ)^531*100000000000000^403 ≤ 12720866144457^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2091110911 10000000000 12720866144457 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5419244847/10000000000 : ℝ)^531 ≤ (22305038572663/50000000000000 : ℝ)^403 := by
    have hnat : (5419244847 : ℕ)^531*50000000000000^403 ≤ 22305038572663^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419244847 10000000000 22305038572663 50000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1309833243/2500000000 : ℝ)^531 ≤ (21334528350627/50000000000000 : ℝ)^403 := by
    have hnat : (1309833243 : ℕ)^531*50000000000000^403 ≤ 21334528350627^403*2500000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309833243 2500000000 21334528350627 50000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2091110911/10000000000 : ℝ), (5419244847/10000000000 : ℝ), (1309833243/2500000000 : ℝ)] ![(12720866144457/100000000000000 : ℝ), (22305038572663/50000000000000 : ℝ), (21334528350627/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2091110911/10000000000 : ℝ)|^531 ≤ (12720866144457/100000000000000 : ℝ)^403
        have hw : |(-2091110911/10000000000 : ℝ)|=(2091110911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5419244847/10000000000 : ℝ)|^531 ≤ (22305038572663/50000000000000 : ℝ)^403
        have hw : |(5419244847/10000000000 : ℝ)|=(5419244847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1309833243/2500000000 : ℝ)|^531 ≤ (21334528350627/50000000000000 : ℝ)^403
        have hw : |(1309833243/2500000000 : ℝ)|=(1309833243/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1288_s4_1 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (334425501/625000000 : ℝ)*x 0 + (-2182898299/10000000000 : ℝ)*x 1 + (5239332923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334425501/625000000 : ℝ)^531 ≤ (4386928019163/10000000000000 : ℝ)^403 := by
    have hnat : (334425501 : ℕ)^531*10000000000000^403 ≤ 4386928019163^403*625000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334425501 625000000 4386928019163 10000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2182898299/10000000000 : ℝ)^531 ≤ (6730831806677/50000000000000 : ℝ)^403 := by
    have hnat : (2182898299 : ℕ)^531*50000000000000^403 ≤ 6730831806677^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182898299 10000000000 6730831806677 50000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5239332923/10000000000 : ℝ)^531 ≤ (42669056175451/100000000000000 : ℝ)^403 := by
    have hnat : (5239332923 : ℕ)^531*100000000000000^403 ≤ 42669056175451^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239332923 10000000000 42669056175451 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334425501/625000000 : ℝ), (-2182898299/10000000000 : ℝ), (5239332923/10000000000 : ℝ)] ![(4386928019163/10000000000000 : ℝ), (6730831806677/50000000000000 : ℝ), (42669056175451/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334425501/625000000 : ℝ)|^531 ≤ (4386928019163/10000000000000 : ℝ)^403
        have hw : |(334425501/625000000 : ℝ)|=(334425501/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2182898299/10000000000 : ℝ)|^531 ≤ (6730831806677/50000000000000 : ℝ)^403
        have hw : |(-2182898299/10000000000 : ℝ)|=(2182898299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5239332923/10000000000 : ℝ)|^531 ≤ (42669056175451/100000000000000 : ℝ)^403
        have hw : |(5239332923/10000000000 : ℝ)|=(5239332923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1288_s4_2 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (668851003/1250000000 : ℝ)*x 0 + (5239332899/10000000000 : ℝ)*x 1 + (-2182898321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668851003/1250000000 : ℝ)^531 ≤ (43869280278051/100000000000000 : ℝ)^403 := by
    have hnat : (668851003 : ℕ)^531*100000000000000^403 ≤ 43869280278051^403*1250000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668851003 1250000000 43869280278051 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5239332899/10000000000 : ℝ)^531 ≤ (8533811183583/20000000000000 : ℝ)^403 := by
    have hnat : (5239332899 : ℕ)^531*20000000000000^403 ≤ 8533811183583^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239332899 10000000000 8533811183583 20000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2182898321/10000000000 : ℝ)^531 ≤ (13461663792117/100000000000000 : ℝ)^403 := by
    have hnat : (2182898321 : ℕ)^531*100000000000000^403 ≤ 13461663792117^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182898321 10000000000 13461663792117 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668851003/1250000000 : ℝ), (5239332899/10000000000 : ℝ), (-2182898321/10000000000 : ℝ)] ![(43869280278051/100000000000000 : ℝ), (8533811183583/20000000000000 : ℝ), (13461663792117/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668851003/1250000000 : ℝ)|^531 ≤ (43869280278051/100000000000000 : ℝ)^403
        have hw : |(668851003/1250000000 : ℝ)|=(668851003/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5239332899/10000000000 : ℝ)|^531 ≤ (8533811183583/20000000000000 : ℝ)^403
        have hw : |(5239332899/10000000000 : ℝ)|=(5239332899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2182898321/10000000000 : ℝ)|^531 ≤ (13461663792117/100000000000000 : ℝ)^403
        have hw : |(-2182898321/10000000000 : ℝ)|=(2182898321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1288_s4_3 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2170337891/5000000000 : ℝ)*x 0 + (831967147/2000000000 : ℝ)*x 1 + (4529032511/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2170337891/5000000000 : ℝ)^531 ≤ (33299605366959/100000000000000 : ℝ)^403 := by
    have hnat : (2170337891 : ℕ)^531*100000000000000^403 ≤ 33299605366959^403*5000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2170337891 5000000000 33299605366959 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (831967147/2000000000 : ℝ)^531 ≤ (15741929944973/50000000000000 : ℝ)^403 := by
    have hnat : (831967147 : ℕ)^531*50000000000000^403 ≤ 15741929944973^403*2000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      831967147 2000000000 15741929944973 50000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4529032511/10000000000 : ℝ)^531 ≤ (8804133681869/25000000000000 : ℝ)^403 := by
    have hnat : (4529032511 : ℕ)^531*25000000000000^403 ≤ 8804133681869^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4529032511 10000000000 8804133681869 25000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2170337891/5000000000 : ℝ), (831967147/2000000000 : ℝ), (4529032511/10000000000 : ℝ)] ![(33299605366959/100000000000000 : ℝ), (15741929944973/50000000000000 : ℝ), (8804133681869/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2170337891/5000000000 : ℝ)|^531 ≤ (33299605366959/100000000000000 : ℝ)^403
        have hw : |(2170337891/5000000000 : ℝ)|=(2170337891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(831967147/2000000000 : ℝ)|^531 ≤ (15741929944973/50000000000000 : ℝ)^403
        have hw : |(831967147/2000000000 : ℝ)|=(831967147/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4529032511/10000000000 : ℝ)|^531 ≤ (8804133681869/25000000000000 : ℝ)^403
        have hw : |(4529032511/10000000000 : ℝ)|=(4529032511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1288_s4_4 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2091125271/10000000000 : ℝ)*x 0 + (209600043/400000000 : ℝ)*x 1 + (5418573231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2091125271/10000000000 : ℝ)^531 ≤ (6360490623379/50000000000000 : ℝ)^403 := by
    have hnat : (2091125271 : ℕ)^531*50000000000000^403 ≤ 6360490623379^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2091125271 10000000000 6360490623379 50000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209600043/400000000 : ℝ)^531 ≤ (10669056508483/25000000000000 : ℝ)^403 := by
    have hnat : (209600043 : ℕ)^531*25000000000000^403 ≤ 10669056508483^403*400000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209600043 400000000 10669056508483 25000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5418573231/10000000000 : ℝ)^531 ≤ (4460279270547/10000000000000 : ℝ)^403 := by
    have hnat : (5418573231 : ℕ)^531*10000000000000^403 ≤ 4460279270547^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418573231 10000000000 4460279270547 10000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2091125271/10000000000 : ℝ), (209600043/400000000 : ℝ), (5418573231/10000000000 : ℝ)] ![(6360490623379/50000000000000 : ℝ), (10669056508483/25000000000000 : ℝ), (4460279270547/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2091125271/10000000000 : ℝ)|^531 ≤ (6360490623379/50000000000000 : ℝ)^403
        have hw : |(-2091125271/10000000000 : ℝ)|=(2091125271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(209600043/400000000 : ℝ)|^531 ≤ (10669056508483/25000000000000 : ℝ)^403
        have hw : |(209600043/400000000 : ℝ)|=(209600043/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5418573231/10000000000 : ℝ)|^531 ≤ (4460279270547/10000000000000 : ℝ)^403
        have hw : |(5418573231/10000000000 : ℝ)|=(5418573231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1288_s4_5 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2652384551/5000000000 : ℝ)*x 0 + (-2003657997/10000000000 : ℝ)*x 1 + (5418573079/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652384551/5000000000 : ℝ)^531 ≤ (5421577308939/12500000000000 : ℝ)^403 := by
    have hnat : (2652384551 : ℕ)^531*12500000000000^403 ≤ 5421577308939^403*5000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652384551 5000000000 5421577308939 12500000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2003657997/10000000000 : ℝ)^531 ≤ (187884225979/1562500000000 : ℝ)^403 := by
    have hnat : (2003657997 : ℕ)^531*1562500000000^403 ≤ 187884225979^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2003657997 10000000000 187884225979 1562500000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5418573079/10000000000 : ℝ)^531 ≤ (4460279105689/10000000000000 : ℝ)^403 := by
    have hnat : (5418573079 : ℕ)^531*10000000000000^403 ≤ 4460279105689^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418573079 10000000000 4460279105689 10000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652384551/5000000000 : ℝ), (-2003657997/10000000000 : ℝ), (5418573079/10000000000 : ℝ)] ![(5421577308939/12500000000000 : ℝ), (187884225979/1562500000000 : ℝ), (4460279105689/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652384551/5000000000 : ℝ)|^531 ≤ (5421577308939/12500000000000 : ℝ)^403
        have hw : |(2652384551/5000000000 : ℝ)|=(2652384551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2003657997/10000000000 : ℝ)|^531 ≤ (187884225979/1562500000000 : ℝ)^403
        have hw : |(-2003657997/10000000000 : ℝ)|=(2003657997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5418573079/10000000000 : ℝ)|^531 ≤ (4460279105689/10000000000000 : ℝ)^403
        have hw : |(5418573079/10000000000 : ℝ)|=(5418573079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1288_s4_6 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (33154807/62500000 : ℝ)*x 0 + (5418573209/10000000000 : ℝ)*x 1 + (-2003657793/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33154807/62500000 : ℝ)^531 ≤ (43372618665427/100000000000000 : ℝ)^403 := by
    have hnat : (33154807 : ℕ)^531*100000000000000^403 ≤ 43372618665427^403*62500000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33154807 62500000 43372618665427 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5418573209/10000000000 : ℝ)^531 ≤ (2230139623343/5000000000000 : ℝ)^403 := by
    have hnat : (5418573209 : ℕ)^531*5000000000000^403 ≤ 2230139623343^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418573209 10000000000 2230139623343 5000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2003657793/10000000000 : ℝ)^531 ≤ (12024588849537/100000000000000 : ℝ)^403 := by
    have hnat : (2003657793 : ℕ)^531*100000000000000^403 ≤ 12024588849537^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2003657793 10000000000 12024588849537 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33154807/62500000 : ℝ), (5418573209/10000000000 : ℝ), (-2003657793/10000000000 : ℝ)] ![(43372618665427/100000000000000 : ℝ), (2230139623343/5000000000000 : ℝ), (12024588849537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33154807/62500000 : ℝ)|^531 ≤ (43372618665427/100000000000000 : ℝ)^403
        have hw : |(33154807/62500000 : ℝ)|=(33154807/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5418573209/10000000000 : ℝ)|^531 ≤ (2230139623343/5000000000000 : ℝ)^403
        have hw : |(5418573209/10000000000 : ℝ)|=(5418573209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2003657793/10000000000 : ℝ)|^531 ≤ (12024588849537/100000000000000 : ℝ)^403
        have hw : |(-2003657793/10000000000 : ℝ)|=(2003657793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1288_s4_7 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (542588143/1250000000 : ℝ)*x 0 + (22638309/50000000 : ℝ)*x 1 + (4161214069/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (542588143/1250000000 : ℝ)^531 ≤ (33299902162461/100000000000000 : ℝ)^403 := by
    have hnat : (542588143 : ℕ)^531*100000000000000^403 ≤ 33299902162461^403*1250000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542588143 1250000000 33299902162461 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (22638309/50000000 : ℝ)^531 ≤ (17601245931919/50000000000000 : ℝ)^403 := by
    have hnat : (22638309 : ℕ)^531*50000000000000^403 ≤ 17601245931919^403*50000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22638309 50000000 17601245931919 50000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4161214069/10000000000 : ℝ)^531 ≤ (3149760596099/10000000000000 : ℝ)^403 := by
    have hnat : (4161214069 : ℕ)^531*10000000000000^403 ≤ 3149760596099^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4161214069 10000000000 3149760596099 10000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(542588143/1250000000 : ℝ), (22638309/50000000 : ℝ), (4161214069/10000000000 : ℝ)] ![(33299902162461/100000000000000 : ℝ), (17601245931919/50000000000000 : ℝ), (3149760596099/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(542588143/1250000000 : ℝ)|^531 ≤ (33299902162461/100000000000000 : ℝ)^403
        have hw : |(542588143/1250000000 : ℝ)|=(542588143/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(22638309/50000000 : ℝ)|^531 ≤ (17601245931919/50000000000000 : ℝ)^403
        have hw : |(22638309/50000000 : ℝ)|=(22638309/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4161214069/10000000000 : ℝ)|^531 ≤ (3149760596099/10000000000000 : ℝ)^403
        have hw : |(4161214069/10000000000 : ℝ)|=(4161214069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1288_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152604817/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (471/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (133/1250 : ℝ)*pair X i i ≤ pair X i h) :
    (5471/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14749/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (471/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (133/1250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (471/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (133/1250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (471/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (133/1250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (471/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (133/1250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (471/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (133/1250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (471/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (133/1250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (133/1250 : ℝ) ^ (4247/1024 : ℝ) ≤ (2302599577959417/25000000000000000000 : ℝ) := by
    have hpowers : (133/1250 : ℝ)^4247 ≤ (2302599577959417/25000000000000000000 : ℝ)^1024 := by
      have hnat : (133 : ℕ)^4247*25000000000000000000^1024 ≤ 2302599577959417^1024*1250^4247 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        133 1250 2302599577959417 25000000000000000000 4247 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (133/1250 : ℝ)) (X := (2302599577959417/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4247 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (471/3125 : ℝ) ^ (4247/1024 : ℝ) ≤ (3903874521421931/10000000000000000000 : ℝ) := by
    have hpowers : (471/3125 : ℝ)^4247 ≤ (3903874521421931/10000000000000000000 : ℝ)^1024 := by
      have hnat : (471 : ℕ)^4247*10000000000000000000^1024 ≤ 3903874521421931^1024*3125^4247 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        471 3125 3903874521421931 10000000000000000000 4247 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (471/3125 : ℝ)) (X := (3903874521421931/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4247 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502302599577959417/12500000000000000000 : ℝ) ≤ (5000222057657541/5000000000000000 : ℝ) ^ (4247/1024 : ℝ) := by
    have hpowers : (12502302599577959417/12500000000000000000 : ℝ)^1024 ≤ (5000222057657541/5000000000000000 : ℝ)^4247 := by
      have hnat : (12502302599577959417 : ℕ)^1024*5000000000000000^4247 ≤ 5000222057657541^4247*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502302599577959417 12500000000000000000 5000222057657541 5000000000000000 1024 4247 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000222057657541/5000000000000000 : ℝ)) (X := (12502302599577959417/12500000000000000000 : ℝ)) (by norm_num) 4247 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024124571763028489/50000000000000000000 : ℝ) ≤ (5000581564400049/5000000000000000 : ℝ) ^ (4247/1024 : ℝ) := by
    have hpowers : (50024124571763028489/50000000000000000000 : ℝ)^1024 ≤ (5000581564400049/5000000000000000 : ℝ)^4247 := by
      have hnat : (50024124571763028489 : ℕ)^1024*5000000000000000^4247 ≤ 5000581564400049^4247*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024124571763028489 50000000000000000000 5000581564400049 5000000000000000 1024 4247 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000581564400049/5000000000000000 : ℝ)) (X := (50024124571763028489/50000000000000000000 : ℝ)) (by norm_num) 4247 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003903874521421931/5000000000000000000 : ℝ) ≤ (5000941071142557/5000000000000000 : ℝ) ^ (4247/1024 : ℝ) := by
    have hpowers : (5003903874521421931/5000000000000000000 : ℝ)^1024 ≤ (5000941071142557/5000000000000000 : ℝ)^4247 := by
      have hnat : (5003903874521421931 : ℕ)^1024*5000000000000000^4247 ≤ 5000941071142557^4247*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003903874521421931 5000000000000000000 5000941071142557 5000000000000000 1024 4247 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000941071142557/5000000000000000 : ℝ)) (X := (5003903874521421931/5000000000000000000 : ℝ)) (by norm_num) 4247 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2302599577959417/25000000000000000000 : ℝ) ≤ ((1384583366003603217/1385000000000000000 : ℝ)+2*(89876685627/55400000000000 : ℝ)*(133/1250 : ℝ))^(4247/1024 : ℝ) := by
    rw [show (1384583366003603217/1385000000000000000 : ℝ)+2*(89876685627/55400000000000 : ℝ)*(133/1250 : ℝ)=(5000222057657541/5000000000000000 : ℝ) by norm_num, show 1+2*(2302599577959417/25000000000000000000 : ℝ)=(12502302599577959417/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3903874521421931/10000000000000000000 : ℝ)+(2302599577959417/25000000000000000000 : ℝ) ≤ ((1384583366003603217/1385000000000000000 : ℝ)+(89876685627/55400000000000 : ℝ)*((471/3125 : ℝ)+(133/1250 : ℝ)))^(4247/1024 : ℝ) := by
    rw [show (1384583366003603217/1385000000000000000 : ℝ)+(89876685627/55400000000000 : ℝ)*((471/3125 : ℝ)+(133/1250 : ℝ))=(5000581564400049/5000000000000000 : ℝ) by norm_num, show 1+(3903874521421931/10000000000000000000 : ℝ)+(2302599577959417/25000000000000000000 : ℝ)=(50024124571763028489/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3903874521421931/10000000000000000000 : ℝ) ≤ ((1384583366003603217/1385000000000000000 : ℝ)+2*(89876685627/55400000000000 : ℝ)*(471/3125 : ℝ))^(4247/1024 : ℝ) := by
    rw [show (1384583366003603217/1385000000000000000 : ℝ)+2*(89876685627/55400000000000 : ℝ)*(471/3125 : ℝ)=(5000941071142557/5000000000000000 : ℝ) by norm_num, show 1+2*(3903874521421931/10000000000000000000 : ℝ)=(5003903874521421931/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1384583366003603217/1385000000000000000 : ℝ)*(X 1 0+X 2 0)+(89876685627/55400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4247/1024 : ℝ)) (lo := (133/1250 : ℝ)) (hi := (471/3125 : ℝ)) (c := (1384583366003603217/1385000000000000000 : ℝ)) (alpha := (89876685627/55400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1384583366003603217/1385000000000000000 : ℝ)*(X 0 1+X 2 1)+(89876685627/55400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4247/1024 : ℝ)) (lo := (133/1250 : ℝ)) (hi := (471/3125 : ℝ)) (c := (1384583366003603217/1385000000000000000 : ℝ)) (alpha := (89876685627/55400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1384583366003603217/1385000000000000000 : ℝ)*(X 0 2+X 1 2)+(89876685627/55400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4247/1024 : ℝ)) (lo := (133/1250 : ℝ)) (hi := (471/3125 : ℝ)) (c := (1384583366003603217/1385000000000000000 : ℝ)) (alpha := (89876685627/55400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2091110911/10000000000 : ℝ)*X 0 0+(5419244847/10000000000 : ℝ)*X 0 1+(1309833243/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334425501/625000000 : ℝ)*X 1 0+(-2182898299/10000000000 : ℝ)*X 1 1+(5239332923/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668851003/1250000000 : ℝ)*X 2 0+(5239332899/10000000000 : ℝ)*X 2 1+(-2182898321/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2170337891/5000000000 : ℝ)*X 0 0+(831967147/2000000000 : ℝ)*X 0 1+(4529032511/10000000000 : ℝ)*X 0 2+(2170337891/5000000000 : ℝ)*X 1 0+(831967147/2000000000 : ℝ)*X 1 1+(4529032511/10000000000 : ℝ)*X 1 2+(2170337891/5000000000 : ℝ)*X 2 0+(831967147/2000000000 : ℝ)*X 2 1+(4529032511/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2091125271/10000000000 : ℝ)*X 0 0+(209600043/400000000 : ℝ)*X 0 1+(5418573231/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652384551/5000000000 : ℝ)*X 1 0+(-2003657997/10000000000 : ℝ)*X 1 1+(5418573079/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((33154807/62500000 : ℝ)*X 2 0+(5418573209/10000000000 : ℝ)*X 2 1+(-2003657793/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((542588143/1250000000 : ℝ)*X 0 0+(22638309/50000000 : ℝ)*X 0 1+(4161214069/10000000000 : ℝ)*X 0 2+(542588143/1250000000 : ℝ)*X 1 0+(22638309/50000000 : ℝ)*X 1 1+(4161214069/10000000000 : ℝ)*X 1 2+(542588143/1250000000 : ℝ)*X 2 0+(22638309/50000000 : ℝ)*X 2 1+(4161214069/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10410729112004768955279/1385000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1684844771/100000000000000 : ℝ)*(base19) + (414142063/25000000000000 : ℝ)*(base23) + (19576893/100000000000000 : ℝ)*(lower2) + (42641103/20000000000000 : ℝ)*(upper3) + (32486769/20000000000000 : ℝ)*(upper5) + (2066739183882059/50000000000000 : ℝ)*(major0) + (2066739183882059/50000000000000 : ℝ)*(major1) + (2066739183882059/50000000000000 : ℝ)*(major2) + (555830922965681/10000000000000 : ℝ)*(sp0) + (2779169440122727/50000000000000 : ℝ)*(sp1) + (2779169454260987/50000000000000 : ℝ)*(sp2) + (2708598807333493/100000000000000 : ℝ)*(sp3) + (3916929177/12500000000000 : ℝ)*(sp4) + (4278136361/25000000000000 : ℝ)*(sp7) + (1354307959939469/50000000000000 : ℝ)*(f.failure) + (2779170282545113/50000000000000 : ℝ)*(f.sum) + (4674707635833/1385000000000000000000000000 : ℝ)*base65 + (263637176729558803/69250000000000000000000000000000 : ℝ)*base67 + (432476090907941197/69250000000000000000000000000000 : ℝ)*base70 + (559653372085308803/69250000000000000000000000000000 : ℝ)*base71 + (612354866809/173125000000000000000000000 : ℝ)*base74 + (477091106991558803/69250000000000000000000000000000 : ℝ)*base75 + (212398265670691197/69250000000000000000000000000000 : ℝ)*base78 + (237784231423441197/69250000000000000000000000000000 : ℝ)*base80 + (229247955929/173125000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (97822173/5000000000000000000000 : ℝ)*base89 + (97822173/5000000000000000000000 : ℝ)*base91 + (97822173/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (262927711061846437776267/135253906250000000000000000000 : ℝ) := by norm_num
    linear_combination (664668409/100000000000000 : ℝ)*(base19) + (852897701/100000000000000 : ℝ)*(base23) + (3029823/6250000000000 : ℝ)*(upper2) + (21021681/100000000000000 : ℝ)*(upper3) + (130138769918801/3125000000000 : ℝ)*(major0) + (130138769918801/3125000000000 : ℝ)*(major1) + (130138769918801/3125000000000 : ℝ)*(major2) + (276684171/2500000000000 : ℝ)*(sp1) + (20036776693/100000000000000 : ℝ)*(sp2) + (1306013223/100000000000000 : ℝ)*(sp3) + (174999253367143/3125000000000 : ℝ)*(sp4) + (2799982187856663/50000000000000 : ℝ)*(sp5) + (2799977609037091/50000000000000 : ℝ)*(sp6) + (682225949060727/25000000000000 : ℝ)*(sp7) + (2728905102256131/100000000000000 : ℝ)*(f.failure) + (174999253367143/3125000000000 : ℝ)*(f.sum) + (5405634556731/692500000000000000000000000 : ℝ)*base65 + (203746035432423/1082031250000000000000000000000 : ℝ)*base67 + (1119752173552149/541015625000000000000000000000 : ℝ)*base69 + (6057774719464067/4328125000000000000000000000000 : ℝ)*base71 + (3419600176277/1385000000000000000000000000 : ℝ)*base73 + (4860630256817971/2164062500000000000000000000000 : ℝ)*base75 + (23004973265401567/4328125000000000000000000000000 : ℝ)*base77 + (49976451406339067/4328125000000000000000000000000 : ℝ)*base79 + (2797116703811/692500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (41616973/10000000000000000000000 : ℝ)*base90 + (41616973/10000000000000000000000 : ℝ)*base92 + (41616973/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1288_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152604817/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (471/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (133/1250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5471/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14749/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1288_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1288_s5_0 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-83659321/400000000 : ℝ)*x 0 + (2708058263/5000000000 : ℝ)*x 1 + (81909633/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83659321/400000000 : ℝ)^531 ≤ (3180962224503/25000000000000 : ℝ)^403 := by
    have hnat : (83659321 : ℕ)^531*25000000000000^403 ≤ 3180962224503^403*400000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83659321 400000000 3180962224503 25000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2708058263/5000000000 : ℝ)^531 ≤ (891522987741/2000000000000 : ℝ)^403 := by
    have hnat : (2708058263 : ℕ)^531*2000000000000^403 ≤ 891522987741^403*5000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708058263 5000000000 891522987741 2000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (81909633/156250000 : ℝ)^531 ≤ (42700001698573/100000000000000 : ℝ)^403 := by
    have hnat : (81909633 : ℕ)^531*100000000000000^403 ≤ 42700001698573^403*156250000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81909633 156250000 42700001698573 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-83659321/400000000 : ℝ), (2708058263/5000000000 : ℝ), (81909633/156250000 : ℝ)] ![(3180962224503/25000000000000 : ℝ), (891522987741/2000000000000 : ℝ), (42700001698573/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-83659321/400000000 : ℝ)|^531 ≤ (3180962224503/25000000000000 : ℝ)^403
        have hw : |(-83659321/400000000 : ℝ)|=(83659321/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2708058263/5000000000 : ℝ)|^531 ≤ (891522987741/2000000000000 : ℝ)^403
        have hw : |(2708058263/5000000000 : ℝ)|=(2708058263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(81909633/156250000 : ℝ)|^531 ≤ (42700001698573/100000000000000 : ℝ)^403
        have hw : |(81909633/156250000 : ℝ)|=(81909633/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1288_s5_1 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1337503621/2500000000 : ℝ)*x 0 + (-2180144303/10000000000 : ℝ)*x 1 + (5242216501/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337503621/2500000000 : ℝ)^531 ≤ (21930354069483/50000000000000 : ℝ)^403 := by
    have hnat : (1337503621 : ℕ)^531*50000000000000^403 ≤ 21930354069483^403*2500000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337503621 2500000000 21930354069483 50000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2180144303/10000000000 : ℝ)^531 ≤ (3359822566517/25000000000000 : ℝ)^403 := by
    have hnat : (2180144303 : ℕ)^531*25000000000000^403 ≤ 3359822566517^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180144303 10000000000 3359822566517 25000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242216501/10000000000 : ℝ)^531 ≤ (8540000316103/20000000000000 : ℝ)^403 := by
    have hnat : (5242216501 : ℕ)^531*20000000000000^403 ≤ 8540000316103^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242216501 10000000000 8540000316103 20000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337503621/2500000000 : ℝ), (-2180144303/10000000000 : ℝ), (5242216501/10000000000 : ℝ)] ![(21930354069483/50000000000000 : ℝ), (3359822566517/25000000000000 : ℝ), (8540000316103/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337503621/2500000000 : ℝ)|^531 ≤ (21930354069483/50000000000000 : ℝ)^403
        have hw : |(1337503621/2500000000 : ℝ)|=(1337503621/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2180144303/10000000000 : ℝ)|^531 ≤ (3359822566517/25000000000000 : ℝ)^403
        have hw : |(-2180144303/10000000000 : ℝ)|=(2180144303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242216501/10000000000 : ℝ)|^531 ≤ (8540000316103/20000000000000 : ℝ)^403
        have hw : |(5242216501/10000000000 : ℝ)|=(5242216501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1288_s5_2 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (267500723/500000000 : ℝ)*x 0 + (2621108267/5000000000 : ℝ)*x 1 + (-545036073/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267500723/500000000 : ℝ)^531 ≤ (8772141575943/20000000000000 : ℝ)^403 := by
    have hnat : (267500723 : ℕ)^531*20000000000000^403 ≤ 8772141575943^403*500000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267500723 500000000 8772141575943 20000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621108267/5000000000 : ℝ)^531 ≤ (42700001934689/100000000000000 : ℝ)^403 := by
    have hnat : (2621108267 : ℕ)^531*100000000000000^403 ≤ 42700001934689^403*5000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621108267 5000000000 42700001934689 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (545036073/2500000000 : ℝ)^531 ≤ (13439290176723/100000000000000 : ℝ)^403 := by
    have hnat : (545036073 : ℕ)^531*100000000000000^403 ≤ 13439290176723^403*2500000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545036073 2500000000 13439290176723 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267500723/500000000 : ℝ), (2621108267/5000000000 : ℝ), (-545036073/2500000000 : ℝ)] ![(8772141575943/20000000000000 : ℝ), (42700001934689/100000000000000 : ℝ), (13439290176723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267500723/500000000 : ℝ)|^531 ≤ (8772141575943/20000000000000 : ℝ)^403
        have hw : |(267500723/500000000 : ℝ)|=(267500723/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621108267/5000000000 : ℝ)|^531 ≤ (42700001934689/100000000000000 : ℝ)^403
        have hw : |(2621108267/5000000000 : ℝ)|=(2621108267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-545036073/2500000000 : ℝ)|^531 ≤ (13439290176723/100000000000000 : ℝ)^403
        have hw : |(-545036073/2500000000 : ℝ)|=(545036073/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1288_s5_3 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (434089473/1000000000 : ℝ)*x 0 + (4165976799/10000000000 : ℝ)*x 1 + (2261418161/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (434089473/1000000000 : ℝ)^531 ≤ (16650909270773/50000000000000 : ℝ)^403 := by
    have hnat : (434089473 : ℕ)^531*50000000000000^403 ≤ 16650909270773^403*1000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434089473 1000000000 16650909270773 50000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4165976799/10000000000 : ℝ)^531 ≤ (31545115611569/100000000000000 : ℝ)^403 := by
    have hnat : (4165976799 : ℕ)^531*100000000000000^403 ≤ 31545115611569^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4165976799 10000000000 31545115611569 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2261418161/5000000000 : ℝ)^531 ≤ (3515306583571/10000000000000 : ℝ)^403 := by
    have hnat : (2261418161 : ℕ)^531*10000000000000^403 ≤ 3515306583571^403*5000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2261418161 5000000000 3515306583571 10000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(434089473/1000000000 : ℝ), (4165976799/10000000000 : ℝ), (2261418161/5000000000 : ℝ)] ![(16650909270773/50000000000000 : ℝ), (31545115611569/100000000000000 : ℝ), (3515306583571/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(434089473/1000000000 : ℝ)|^531 ≤ (16650909270773/50000000000000 : ℝ)^403
        have hw : |(434089473/1000000000 : ℝ)|=(434089473/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4165976799/10000000000 : ℝ)|^531 ≤ (31545115611569/100000000000000 : ℝ)^403
        have hw : |(4165976799/10000000000 : ℝ)|=(4165976799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2261418161/5000000000 : ℝ)|^531 ≤ (3515306583571/10000000000000 : ℝ)^403
        have hw : |(2261418161/5000000000 : ℝ)|=(2261418161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1288_s5_4 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1045748089/5000000000 : ℝ)*x 0 + (5242840797/10000000000 : ℝ)*x 1 + (5415488933/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1045748089/5000000000 : ℝ)^531 ≤ (1590494291447/12500000000000 : ℝ)^403 := by
    have hnat : (1045748089 : ℕ)^531*12500000000000^403 ≤ 1590494291447^403*5000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045748089 5000000000 1590494291447 12500000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242840797/10000000000 : ℝ)^531 ≤ (10676675496859/25000000000000 : ℝ)^403 := by
    have hnat : (5242840797 : ℕ)^531*25000000000000^403 ≤ 10676675496859^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242840797 10000000000 10676675496859 25000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5415488933/10000000000 : ℝ)^531 ≤ (22284671833157/50000000000000 : ℝ)^403 := by
    have hnat : (5415488933 : ℕ)^531*50000000000000^403 ≤ 22284671833157^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415488933 10000000000 22284671833157 50000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1045748089/5000000000 : ℝ), (5242840797/10000000000 : ℝ), (5415488933/10000000000 : ℝ)] ![(1590494291447/12500000000000 : ℝ), (10676675496859/25000000000000 : ℝ), (22284671833157/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1045748089/5000000000 : ℝ)|^531 ≤ (1590494291447/12500000000000 : ℝ)^403
        have hw : |(-1045748089/5000000000 : ℝ)|=(1045748089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242840797/10000000000 : ℝ)|^531 ≤ (10676675496859/25000000000000 : ℝ)^403
        have hw : |(5242840797/10000000000 : ℝ)|=(5242840797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5415488933/10000000000 : ℝ)|^531 ≤ (22284671833157/50000000000000 : ℝ)^403
        have hw : |(5415488933/10000000000 : ℝ)|=(5415488933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1288_s5_5 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5305514231/10000000000 : ℝ)*x 0 + (-2006871843/10000000000 : ℝ)*x 1 + (5415488943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305514231/10000000000 : ℝ)^531 ≤ (43380645961733/100000000000000 : ℝ)^403 := by
    have hnat : (5305514231 : ℕ)^531*100000000000000^403 ≤ 43380645961733^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305514231 10000000000 43380645961733 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2006871843/10000000000 : ℝ)^531 ≤ (12050010243959/100000000000000 : ℝ)^403 := by
    have hnat : (2006871843 : ℕ)^531*100000000000000^403 ≤ 12050010243959^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2006871843 10000000000 12050010243959 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5415488943/10000000000 : ℝ)^531 ≤ (22284671887377/50000000000000 : ℝ)^403 := by
    have hnat : (5415488943 : ℕ)^531*50000000000000^403 ≤ 22284671887377^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415488943 10000000000 22284671887377 50000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305514231/10000000000 : ℝ), (-2006871843/10000000000 : ℝ), (5415488943/10000000000 : ℝ)] ![(43380645961733/100000000000000 : ℝ), (12050010243959/100000000000000 : ℝ), (22284671887377/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305514231/10000000000 : ℝ)|^531 ≤ (43380645961733/100000000000000 : ℝ)^403
        have hw : |(5305514231/10000000000 : ℝ)|=(5305514231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2006871843/10000000000 : ℝ)|^531 ≤ (12050010243959/100000000000000 : ℝ)^403
        have hw : |(-2006871843/10000000000 : ℝ)|=(2006871843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5415488943/10000000000 : ℝ)|^531 ≤ (22284671887377/50000000000000 : ℝ)^403
        have hw : |(5415488943/10000000000 : ℝ)|=(5415488943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1288_s5_6 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2652757093/5000000000 : ℝ)*x 0 + (5415488987/10000000000 : ℝ)*x 1 + (-1003435923/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652757093/5000000000 : ℝ)^531 ≤ (10845161369231/25000000000000 : ℝ)^403 := by
    have hnat : (2652757093 : ℕ)^531*25000000000000^403 ≤ 10845161369231^403*5000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652757093 5000000000 10845161369231 25000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5415488987/10000000000 : ℝ)^531 ≤ (2785584015743/6250000000000 : ℝ)^403 := by
    have hnat : (5415488987 : ℕ)^531*6250000000000^403 ≤ 2785584015743^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415488987 10000000000 2785584015743 6250000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1003435923/5000000000 : ℝ)^531 ≤ (6025005133847/50000000000000 : ℝ)^403 := by
    have hnat : (1003435923 : ℕ)^531*50000000000000^403 ≤ 6025005133847^403*5000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1003435923 5000000000 6025005133847 50000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652757093/5000000000 : ℝ), (5415488987/10000000000 : ℝ), (-1003435923/5000000000 : ℝ)] ![(10845161369231/25000000000000 : ℝ), (2785584015743/6250000000000 : ℝ), (6025005133847/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652757093/5000000000 : ℝ)|^531 ≤ (10845161369231/25000000000000 : ℝ)^403
        have hw : |(2652757093/5000000000 : ℝ)|=(2652757093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5415488987/10000000000 : ℝ)|^531 ≤ (2785584015743/6250000000000 : ℝ)^403
        have hw : |(5415488987/10000000000 : ℝ)|=(5415488987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1003435923/5000000000 : ℝ)|^531 ≤ (6025005133847/50000000000000 : ℝ)^403
        have hw : |(-1003435923/5000000000 : ℝ)|=(1003435923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1288_s5_7 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (868184321/2000000000 : ℝ)*x 0 + (4521555187/10000000000 : ℝ)*x 1 + (4167264467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (868184321/2000000000 : ℝ)^531 ≤ (16651045101203/50000000000000 : ℝ)^403 := by
    have hnat : (868184321 : ℕ)^531*50000000000000^403 ≤ 16651045101203^403*2000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      868184321 2000000000 16651045101203 50000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4521555187/10000000000 : ℝ)^531 ≤ (35139946339173/100000000000000 : ℝ)^403 := by
    have hnat : (4521555187 : ℕ)^531*100000000000000^403 ≤ 35139946339173^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4521555187 10000000000 35139946339173 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4167264467/10000000000 : ℝ)^531 ≤ (31557963447161/100000000000000 : ℝ)^403 := by
    have hnat : (4167264467 : ℕ)^531*100000000000000^403 ≤ 31557963447161^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4167264467 10000000000 31557963447161 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(868184321/2000000000 : ℝ), (4521555187/10000000000 : ℝ), (4167264467/10000000000 : ℝ)] ![(16651045101203/50000000000000 : ℝ), (35139946339173/100000000000000 : ℝ), (31557963447161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(868184321/2000000000 : ℝ)|^531 ≤ (16651045101203/50000000000000 : ℝ)^403
        have hw : |(868184321/2000000000 : ℝ)|=(868184321/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4521555187/10000000000 : ℝ)|^531 ≤ (35139946339173/100000000000000 : ℝ)^403
        have hw : |(4521555187/10000000000 : ℝ)|=(4521555187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4167264467/10000000000 : ℝ)|^531 ≤ (31557963447161/100000000000000 : ℝ)^403
        have hw : |(4167264467/10000000000 : ℝ)|=(4167264467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1288_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152604817/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14749/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5471/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2751/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3671/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14749/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5471/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14749/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5471/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14749/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5471/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14749/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5471/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14749/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5471/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14749/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5471/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5471/50000 : ℝ) ^ (4247/1024 : ℝ) ≤ (10344062640618003/100000000000000000000 : ℝ) := by
    have hpowers : (5471/50000 : ℝ)^4247 ≤ (10344062640618003/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5471 : ℕ)^4247*100000000000000000000^1024 ≤ 10344062640618003^1024*50000^4247 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5471 50000 10344062640618003 100000000000000000000 4247 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5471/50000 : ℝ)) (X := (10344062640618003/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4247 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14749/100000 : ℝ) ^ (4247/1024 : ℝ) ≤ (4460517685205301/12500000000000000000 : ℝ) := by
    have hpowers : (14749/100000 : ℝ)^4247 ≤ (4460517685205301/12500000000000000000 : ℝ)^1024 := by
      have hnat : (14749 : ℕ)^4247*12500000000000000000^1024 ≤ 4460517685205301^1024*100000^4247 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14749 100000 4460517685205301 12500000000000000000 4247 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14749/100000 : ℝ)) (X := (4460517685205301/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4247 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010344062640618003/50000000000000000000 : ℝ) ≤ (10000498775076459/10000000000000000 : ℝ) ^ (4247/1024 : ℝ) := by
    have hpowers : (50010344062640618003/50000000000000000000 : ℝ)^1024 ≤ (10000498775076459/10000000000000000 : ℝ)^4247 := by
      have hnat : (50010344062640618003 : ℕ)^1024*10000000000000000^4247 ≤ 10000498775076459^4247*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010344062640618003 50000000000000000000 10000498775076459 10000000000000000 1024 4247 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000498775076459/10000000000000000 : ℝ)) (X := (50010344062640618003/50000000000000000000 : ℝ)) (by norm_num) 4247 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046028204122260411/100000000000000000000 : ℝ) ≤ (5000554799286769/5000000000000000 : ℝ) ^ (4247/1024 : ℝ) := by
    have hpowers : (100046028204122260411/100000000000000000000 : ℝ)^1024 ≤ (5000554799286769/5000000000000000 : ℝ)^4247 := by
      have hnat : (100046028204122260411 : ℕ)^1024*5000000000000000^4247 ≤ 5000554799286769^4247*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046028204122260411 100000000000000000000 5000554799286769 5000000000000000 1024 4247 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000554799286769/5000000000000000 : ℝ)) (X := (100046028204122260411/100000000000000000000 : ℝ)) (by norm_num) 4247 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254460517685205301/6250000000000000000 : ℝ) ≤ (10001720422070617/10000000000000000 : ℝ) ^ (4247/1024 : ℝ) := by
    have hpowers : (6254460517685205301/6250000000000000000 : ℝ)^1024 ≤ (10001720422070617/10000000000000000 : ℝ)^4247 := by
      have hnat : (6254460517685205301 : ℕ)^1024*10000000000000000^4247 ≤ 10001720422070617^4247*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254460517685205301 6250000000000000000 10001720422070617 10000000000000000 1024 4247 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001720422070617/10000000000000000 : ℝ)) (X := (6254460517685205301/6250000000000000000 : ℝ)) (by norm_num) 4247 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10344062640618003/100000000000000000000 : ℝ) ≤ ((38058531575306002577/38070000000000000000 : ℝ)+2*(610823497079/380700000000000 : ℝ)*(5471/50000 : ℝ))^(4247/1024 : ℝ) := by
    rw [show (38058531575306002577/38070000000000000000 : ℝ)+2*(610823497079/380700000000000 : ℝ)*(5471/50000 : ℝ)=(10000498775076459/10000000000000000 : ℝ) by norm_num, show 1+2*(10344062640618003/100000000000000000000 : ℝ)=(50010344062640618003/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4460517685205301/12500000000000000000 : ℝ)+(10344062640618003/100000000000000000000 : ℝ) ≤ ((38058531575306002577/38070000000000000000 : ℝ)+(610823497079/380700000000000 : ℝ)*((14749/100000 : ℝ)+(5471/50000 : ℝ)))^(4247/1024 : ℝ) := by
    rw [show (38058531575306002577/38070000000000000000 : ℝ)+(610823497079/380700000000000 : ℝ)*((14749/100000 : ℝ)+(5471/50000 : ℝ))=(5000554799286769/5000000000000000 : ℝ) by norm_num, show 1+(4460517685205301/12500000000000000000 : ℝ)+(10344062640618003/100000000000000000000 : ℝ)=(100046028204122260411/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4460517685205301/12500000000000000000 : ℝ) ≤ ((38058531575306002577/38070000000000000000 : ℝ)+2*(610823497079/380700000000000 : ℝ)*(14749/100000 : ℝ))^(4247/1024 : ℝ) := by
    rw [show (38058531575306002577/38070000000000000000 : ℝ)+2*(610823497079/380700000000000 : ℝ)*(14749/100000 : ℝ)=(10001720422070617/10000000000000000 : ℝ) by norm_num, show 1+2*(4460517685205301/12500000000000000000 : ℝ)=(6254460517685205301/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (38058531575306002577/38070000000000000000 : ℝ)*(X 1 0+X 2 0)+(610823497079/380700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4247/1024 : ℝ)) (lo := (5471/50000 : ℝ)) (hi := (14749/100000 : ℝ)) (c := (38058531575306002577/38070000000000000000 : ℝ)) (alpha := (610823497079/380700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (38058531575306002577/38070000000000000000 : ℝ)*(X 0 1+X 2 1)+(610823497079/380700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4247/1024 : ℝ)) (lo := (5471/50000 : ℝ)) (hi := (14749/100000 : ℝ)) (c := (38058531575306002577/38070000000000000000 : ℝ)) (alpha := (610823497079/380700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (38058531575306002577/38070000000000000000 : ℝ)*(X 0 2+X 1 2)+(610823497079/380700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4247/1024 : ℝ)) (lo := (5471/50000 : ℝ)) (hi := (14749/100000 : ℝ)) (c := (38058531575306002577/38070000000000000000 : ℝ)) (alpha := (610823497079/380700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-83659321/400000000 : ℝ)*X 0 0+(2708058263/5000000000 : ℝ)*X 0 1+(81909633/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337503621/2500000000 : ℝ)*X 1 0+(-2180144303/10000000000 : ℝ)*X 1 1+(5242216501/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((267500723/500000000 : ℝ)*X 2 0+(2621108267/5000000000 : ℝ)*X 2 1+(-545036073/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((434089473/1000000000 : ℝ)*X 0 0+(4165976799/10000000000 : ℝ)*X 0 1+(2261418161/5000000000 : ℝ)*X 0 2+(434089473/1000000000 : ℝ)*X 1 0+(4165976799/10000000000 : ℝ)*X 1 1+(2261418161/5000000000 : ℝ)*X 1 2+(434089473/1000000000 : ℝ)*X 2 0+(4165976799/10000000000 : ℝ)*X 2 1+(2261418161/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1045748089/5000000000 : ℝ)*X 0 0+(5242840797/10000000000 : ℝ)*X 0 1+(5415488933/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305514231/10000000000 : ℝ)*X 1 0+(-2006871843/10000000000 : ℝ)*X 1 1+(5415488943/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652757093/5000000000 : ℝ)*X 2 0+(5415488987/10000000000 : ℝ)*X 2 1+(-1003435923/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((868184321/2000000000 : ℝ)*X 0 0+(4521555187/10000000000 : ℝ)*X 0 1+(4167264467/10000000000 : ℝ)*X 0 2+(868184321/2000000000 : ℝ)*X 1 0+(4521555187/10000000000 : ℝ)*X 1 1+(4167264467/10000000000 : ℝ)*X 1 2+(868184321/2000000000 : ℝ)*X 2 0+(4521555187/10000000000 : ℝ)*X 2 1+(4167264467/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (262707624106434140554678861/63450000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (91340197/12500000000000 : ℝ)*(base19) + (673321087/100000000000000 : ℝ)*(base23) + (16908237/100000000000000 : ℝ)*(lower2) + (35086263/50000000000000 : ℝ)*(upper3) + (13827071/25000000000000 : ℝ)*(upper5) + (427635030253231/10000000000000 : ℝ)*(major0) + (427635030253231/10000000000000 : ℝ)*(major1) + (427635030253231/10000000000000 : ℝ)*(major2) + (2875223365920719/50000000000000 : ℝ)*(sp0) + (5750461650665799/100000000000000 : ℝ)*(sp1) + (359403856754143/6250000000000 : ℝ)*(sp2) + (280223044545213/10000000000000 : ℝ)*(sp3) + (15649545937/100000000000000 : ℝ)*(sp4) + (7640212171/100000000000000 : ℝ)*(sp7) + (1401119042832151/50000000000000 : ℝ)*(f.failure) + (46003699051099/800000000000 : ℝ)*(f.sum) + (73847799593/761400000000000000000000000 : ℝ)*base65 + (738351677563323713/380700000000000000000000000000000 : ℝ)*base68 + (3087508299082323713/380700000000000000000000000000000 : ℝ)*base70 + (3031784812556223713/380700000000000000000000000000000 : ℝ)*base72 + (930659392031/475875000000000000000000000 : ℝ)*base73 + (2480714308317723713/380700000000000000000000000000000 : ℝ)*base76 + (1716501247111023713/380700000000000000000000000000000 : ℝ)*base78 + (4670605637993823713/380700000000000000000000000000000 : ℝ)*base80 + (5196804394649/3807000000000000000000000000 : ℝ)*base82 + (65071367/5000000000000000000000 : ℝ)*base89 + (65071367/5000000000000000000000 : ℝ)*base91 + (65071367/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (474189159335124628782080437/79312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (639091021/50000000000000 : ℝ)*(base19) + (620467313/50000000000000 : ℝ)*(base23) + (3166241/100000000000000 : ℝ)*(upper2) + (79791383/50000000000000 : ℝ)*(upper3) + (32360101/25000000000000 : ℝ)*(upper5) + (1076833386307181/25000000000000 : ℝ)*(major0) + (1076833386307181/25000000000000 : ℝ)*(major1) + (1076833386307181/25000000000000 : ℝ)*(major2) + (24942992993/100000000000000 : ℝ)*(sp1) + (25647842399/100000000000000 : ℝ)*(sp2) + (36200786748407/625000000000 : ℝ)*(sp4) + (2896049829285043/50000000000000 : ℝ)*(sp5) + (181003093467753/3125000000000 : ℝ)*(sp6) + (1411270505710421/50000000000000 : ℝ)*(sp7) + (1411270505710421/50000000000000 : ℝ)*(f.failure) + (36200786748407/625000000000 : ℝ)*(f.sum) + (22511721477277/9517500000000000000000000000 : ℝ)*base66 + (6562362897865005437/951750000000000000000000000000000 : ℝ)*base67 + (8049483745774994563/951750000000000000000000000000000 : ℝ)*base70 + (1975907980074494563/951750000000000000000000000000000 : ℝ)*base72 + (88208041681501/19035000000000000000000000000 : ℝ)*base73 + (9890910259579244563/951750000000000000000000000000000 : ℝ)*base76 + (13785312318280994563/951750000000000000000000000000000 : ℝ)*base78 + (3642988886796494563/951750000000000000000000000000000 : ℝ)*base80 + (12202550497477/9517500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (51697957/5000000000000000000000 : ℝ)*base89 + (51697957/5000000000000000000000 : ℝ)*base91 + (51697957/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1288_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152604817/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14749/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5471/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2751/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3671/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1288_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1288_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152604817/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1021/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (379/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2751/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3671/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1288_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1288_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1288_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152604817/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1021/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (379/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2751/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3671/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1288_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
