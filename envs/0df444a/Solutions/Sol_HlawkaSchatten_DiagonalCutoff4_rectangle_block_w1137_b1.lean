-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1137_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:29:58.105464+00:00
-- url     : https://prove2.me/submissions/0368f70e-1a53-43cf-8cae-e0a92b05fc36

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
theorem support_rectangle_w1137_s3_0 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2165422543/10000000000 : ℝ)*x 0 + (5429689309/10000000000 : ℝ)*x 1 + (5231617969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2165422543/10000000000 : ℝ)^4165 ≤ (3287474364851/25000000000000 : ℝ)^3141 := by
    have hnat : (2165422543 : ℕ)^4165*25000000000000^3141 ≤ 3287474364851^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2165422543 10000000000 3287474364851 25000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5429689309/10000000000 : ℝ)^4165 ≤ (2224737403073/5000000000000 : ℝ)^3141 := by
    have hnat : (5429689309 : ℕ)^4165*5000000000000^3141 ≤ 2224737403073^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429689309 10000000000 2224737403073 5000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5231617969/10000000000 : ℝ)^4165 ≤ (10588838614359/25000000000000 : ℝ)^3141 := by
    have hnat : (5231617969 : ℕ)^4165*25000000000000^3141 ≤ 10588838614359^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5231617969 10000000000 10588838614359 25000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2165422543/10000000000 : ℝ), (5429689309/10000000000 : ℝ), (5231617969/10000000000 : ℝ)] ![(3287474364851/25000000000000 : ℝ), (2224737403073/5000000000000 : ℝ), (10588838614359/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2165422543/10000000000 : ℝ)|^4165 ≤ (3287474364851/25000000000000 : ℝ)^3141
        have hw : |(-2165422543/10000000000 : ℝ)|=(2165422543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5429689309/10000000000 : ℝ)|^4165 ≤ (2224737403073/5000000000000 : ℝ)^3141
        have hw : |(5429689309/10000000000 : ℝ)|=(5429689309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5231617969/10000000000 : ℝ)|^4165 ≤ (10588838614359/25000000000000 : ℝ)^3141
        have hw : |(5231617969/10000000000 : ℝ)|=(5231617969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s3_1 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353913247/10000000000 : ℝ)*x 0 + (-283335109/1250000000 : ℝ)*x 1 + (163488057/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353913247/10000000000 : ℝ)^4165 ≤ (43673223304019/100000000000000 : ℝ)^3141 := by
    have hnat : (5353913247 : ℕ)^4165*100000000000000^3141 ≤ 43673223304019^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353913247 10000000000 43673223304019 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (283335109/1250000000 : ℝ)^4165 ≤ (13971423781823/100000000000000 : ℝ)^3141 := by
    have hnat : (283335109 : ℕ)^4165*100000000000000^3141 ≤ 13971423781823^3141*1250000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283335109 1250000000 13971423781823 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (163488057/312500000 : ℝ)^4165 ≤ (42355352900799/100000000000000 : ℝ)^3141 := by
    have hnat : (163488057 : ℕ)^4165*100000000000000^3141 ≤ 42355352900799^3141*312500000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163488057 312500000 42355352900799 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353913247/10000000000 : ℝ), (-283335109/1250000000 : ℝ), (163488057/312500000 : ℝ)] ![(43673223304019/100000000000000 : ℝ), (13971423781823/100000000000000 : ℝ), (42355352900799/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353913247/10000000000 : ℝ)|^4165 ≤ (43673223304019/100000000000000 : ℝ)^3141
        have hw : |(5353913247/10000000000 : ℝ)|=(5353913247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-283335109/1250000000 : ℝ)|^4165 ≤ (13971423781823/100000000000000 : ℝ)^3141
        have hw : |(-283335109/1250000000 : ℝ)|=(283335109/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(163488057/312500000 : ℝ)|^4165 ≤ (42355352900799/100000000000000 : ℝ)^3141
        have hw : |(163488057/312500000 : ℝ)|=(163488057/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s3_2 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338478333/2500000000 : ℝ)*x 0 + (5231617911/10000000000 : ℝ)*x 1 + (-566670161/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338478333/2500000000 : ℝ)^4165 ≤ (43673224223431/100000000000000 : ℝ)^3141 := by
    have hnat : (1338478333 : ℕ)^4165*100000000000000^3141 ≤ 43673224223431^3141*2500000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338478333 2500000000 43673224223431 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5231617911/10000000000 : ℝ)^4165 ≤ (42355353834781/100000000000000 : ℝ)^3141 := by
    have hnat : (5231617911 : ℕ)^4165*100000000000000^3141 ≤ 42355353834781^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5231617911 10000000000 42355353834781 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (566670161/2500000000 : ℝ)^4165 ≤ (13971421918311/100000000000000 : ℝ)^3141 := by
    have hnat : (566670161 : ℕ)^4165*100000000000000^3141 ≤ 13971421918311^3141*2500000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      566670161 2500000000 13971421918311 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338478333/2500000000 : ℝ), (5231617911/10000000000 : ℝ), (-566670161/2500000000 : ℝ)] ![(43673224223431/100000000000000 : ℝ), (42355353834781/100000000000000 : ℝ), (13971421918311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338478333/2500000000 : ℝ)|^4165 ≤ (43673224223431/100000000000000 : ℝ)^3141
        have hw : |(1338478333/2500000000 : ℝ)|=(1338478333/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5231617911/10000000000 : ℝ)|^4165 ≤ (42355353834781/100000000000000 : ℝ)^3141
        have hw : |(5231617911/10000000000 : ℝ)|=(5231617911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-566670161/2500000000 : ℝ)|^4165 ≤ (13971421918311/100000000000000 : ℝ)^3141
        have hw : |(-566670161/2500000000 : ℝ)|=(566670161/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s3_3 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (272693043/625000000 : ℝ)*x 0 + (4170670371/10000000000 : ℝ)*x 1 + (1141085361/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (272693043/625000000 : ℝ)^4165 ≤ (33293771853739/100000000000000 : ℝ)^3141 := by
    have hnat : (272693043 : ℕ)^4165*100000000000000^3141 ≤ 33293771853739^3141*625000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272693043 625000000 33293771853739 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4170670371/10000000000 : ℝ)^4165 ≤ (31360925312307/100000000000000 : ℝ)^3141 := by
    have hnat : (4170670371 : ℕ)^4165*100000000000000^3141 ≤ 31360925312307^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4170670371 10000000000 31360925312307 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1141085361/2500000000 : ℝ)^4165 ≤ (17672651412347/50000000000000 : ℝ)^3141 := by
    have hnat : (1141085361 : ℕ)^4165*50000000000000^3141 ≤ 17672651412347^3141*2500000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1141085361 2500000000 17672651412347 50000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(272693043/625000000 : ℝ), (4170670371/10000000000 : ℝ), (1141085361/2500000000 : ℝ)] ![(33293771853739/100000000000000 : ℝ), (31360925312307/100000000000000 : ℝ), (17672651412347/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(272693043/625000000 : ℝ)|^4165 ≤ (33293771853739/100000000000000 : ℝ)^3141
        have hw : |(272693043/625000000 : ℝ)|=(272693043/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4170670371/10000000000 : ℝ)|^4165 ≤ (31360925312307/100000000000000 : ℝ)^3141
        have hw : |(4170670371/10000000000 : ℝ)|=(4170670371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1141085361/2500000000 : ℝ)|^4165 ≤ (17672651412347/50000000000000 : ℝ)^3141
        have hw : |(1141085361/2500000000 : ℝ)|=(1141085361/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s3_4 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1082720429/5000000000 : ℝ)*x 0 + (654048623/1250000000 : ℝ)*x 1 + (542891397/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1082720429/5000000000 : ℝ)^4165 ≤ (13150044939803/100000000000000 : ℝ)^3141 := by
    have hnat : (1082720429 : ℕ)^4165*100000000000000^3141 ≤ 13150044939803^3141*5000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082720429 5000000000 13150044939803 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (654048623/1250000000 : ℝ)^4165 ≤ (1059090795809/2500000000000 : ℝ)^3141 := by
    have hnat : (654048623 : ℕ)^4165*2500000000000^3141 ≤ 1059090795809^3141*1250000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654048623 1250000000 1059090795809 2500000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (542891397/1000000000 : ℝ)^4165 ≤ (44486323207871/100000000000000 : ℝ)^3141 := by
    have hnat : (542891397 : ℕ)^4165*100000000000000^3141 ≤ 44486323207871^3141*1000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542891397 1000000000 44486323207871 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1082720429/5000000000 : ℝ), (654048623/1250000000 : ℝ), (542891397/1000000000 : ℝ)] ![(13150044939803/100000000000000 : ℝ), (1059090795809/2500000000000 : ℝ), (44486323207871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1082720429/5000000000 : ℝ)|^4165 ≤ (13150044939803/100000000000000 : ℝ)^3141
        have hw : |(-1082720429/5000000000 : ℝ)|=(1082720429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(654048623/1250000000 : ℝ)|^4165 ≤ (1059090795809/2500000000000 : ℝ)^3141
        have hw : |(654048623/1250000000 : ℝ)|=(654048623/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(542891397/1000000000 : ℝ)|^4165 ≤ (44486323207871/100000000000000 : ℝ)^3141
        have hw : |(542891397/1000000000 : ℝ)|=(542891397/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s3_5 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (212150039/400000000 : ℝ)*x 0 + (-2069385167/10000000000 : ℝ)*x 1 + (2714456873/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212150039/400000000 : ℝ)^4165 ≤ (43131468213277/100000000000000 : ℝ)^3141 := by
    have hnat : (212150039 : ℕ)^4165*100000000000000^3141 ≤ 43131468213277^3141*400000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212150039 400000000 43131468213277 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2069385167/10000000000 : ℝ)^4165 ≤ (12382210996801/100000000000000 : ℝ)^3141 := by
    have hnat : (2069385167 : ℕ)^4165*100000000000000^3141 ≤ 12382210996801^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069385167 10000000000 12382210996801 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2714456873/5000000000 : ℝ)^4165 ≤ (22243160386969/50000000000000 : ℝ)^3141 := by
    have hnat : (2714456873 : ℕ)^4165*50000000000000^3141 ≤ 22243160386969^3141*5000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714456873 5000000000 22243160386969 50000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212150039/400000000 : ℝ), (-2069385167/10000000000 : ℝ), (2714456873/5000000000 : ℝ)] ![(43131468213277/100000000000000 : ℝ), (12382210996801/100000000000000 : ℝ), (22243160386969/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212150039/400000000 : ℝ)|^4165 ≤ (43131468213277/100000000000000 : ℝ)^3141
        have hw : |(212150039/400000000 : ℝ)|=(212150039/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2069385167/10000000000 : ℝ)|^4165 ≤ (12382210996801/100000000000000 : ℝ)^3141
        have hw : |(-2069385167/10000000000 : ℝ)|=(2069385167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2714456873/5000000000 : ℝ)|^4165 ≤ (22243160386969/50000000000000 : ℝ)^3141
        have hw : |(2714456873/5000000000 : ℝ)|=(2714456873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s3_6 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (662968947/1250000000 : ℝ)*x 0 + (339307083/625000000 : ℝ)*x 1 + (-1034692461/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (662968947/1250000000 : ℝ)^4165 ≤ (21565737347069/50000000000000 : ℝ)^3141 := by
    have hnat : (662968947 : ℕ)^4165*50000000000000^3141 ≤ 21565737347069^3141*1250000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      662968947 1250000000 21565737347069 50000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (339307083/625000000 : ℝ)^4165 ≤ (8897263246409/20000000000000 : ℝ)^3141 := by
    have hnat : (339307083 : ℕ)^4165*20000000000000^3141 ≤ 8897263246409^3141*625000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339307083 625000000 8897263246409 20000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1034692461/5000000000 : ℝ)^4165 ≤ (12382209052919/100000000000000 : ℝ)^3141 := by
    have hnat : (1034692461 : ℕ)^4165*100000000000000^3141 ≤ 12382209052919^3141*5000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034692461 5000000000 12382209052919 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(662968947/1250000000 : ℝ), (339307083/625000000 : ℝ), (-1034692461/5000000000 : ℝ)] ![(21565737347069/50000000000000 : ℝ), (8897263246409/20000000000000 : ℝ), (12382209052919/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(662968947/1250000000 : ℝ)|^4165 ≤ (21565737347069/50000000000000 : ℝ)^3141
        have hw : |(662968947/1250000000 : ℝ)|=(662968947/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(339307083/625000000 : ℝ)|^4165 ≤ (8897263246409/20000000000000 : ℝ)^3141
        have hw : |(339307083/625000000 : ℝ)|=(339307083/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1034692461/5000000000 : ℝ)|^4165 ≤ (12382209052919/100000000000000 : ℝ)^3141
        have hw : |(-1034692461/5000000000 : ℝ)|=(1034692461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s3_7 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4363124869/10000000000 : ℝ)*x 0 + (2281404563/5000000000 : ℝ)*x 1 + (13038161/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4363124869/10000000000 : ℝ)^4165 ≤ (33294137951591/100000000000000 : ℝ)^3141 := by
    have hnat : (4363124869 : ℕ)^4165*100000000000000^3141 ≤ 33294137951591^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4363124869 10000000000 33294137951591 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2281404563/5000000000 : ℝ)^4165 ≤ (17664784654353/50000000000000 : ℝ)^3141 := by
    have hnat : (2281404563 : ℕ)^4165*50000000000000^3141 ≤ 17664784654353^3141*5000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2281404563 5000000000 17664784654353 50000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13038161/31250000 : ℝ)^4165 ≤ (3137629272859/10000000000000 : ℝ)^3141 := by
    have hnat : (13038161 : ℕ)^4165*10000000000000^3141 ≤ 3137629272859^3141*31250000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13038161 31250000 3137629272859 10000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4363124869/10000000000 : ℝ), (2281404563/5000000000 : ℝ), (13038161/31250000 : ℝ)] ![(33294137951591/100000000000000 : ℝ), (17664784654353/50000000000000 : ℝ), (3137629272859/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4363124869/10000000000 : ℝ)|^4165 ≤ (33294137951591/100000000000000 : ℝ)^3141
        have hw : |(4363124869/10000000000 : ℝ)|=(4363124869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2281404563/5000000000 : ℝ)|^4165 ≤ (17664784654353/50000000000000 : ℝ)^3141
        have hw : |(2281404563/5000000000 : ℝ)|=(2281404563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(13038161/31250000 : ℝ)|^4165 ≤ (3137629272859/10000000000000 : ℝ)^3141
        have hw : |(13038161/31250000 : ℝ)|=(13038161/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1137_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149376161/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16517/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1131/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (531/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14811/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16517/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1131/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16517/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1131/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16517/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1131/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16517/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1131/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16517/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1131/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16517/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1131/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1131/12500 : ℝ) ^ (8329/2048 : ℝ) ≤ (570702062950681/10000000000000000000 : ℝ) := by
    have hpowers : (1131/12500 : ℝ)^8329 ≤ (570702062950681/10000000000000000000 : ℝ)^2048 := by
      have hnat : (1131 : ℕ)^8329*10000000000000000000^2048 ≤ 570702062950681^2048*12500^8329 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1131 12500 570702062950681 10000000000000000000 8329 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1131/12500 : ℝ)) (X := (570702062950681/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8329 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (16517/100000 : ℝ) ^ (8329/2048 : ℝ) ≤ (16494857042053633/25000000000000000000 : ℝ) := by
    have hpowers : (16517/100000 : ℝ)^8329 ≤ (16494857042053633/25000000000000000000 : ℝ)^2048 := by
      have hnat : (16517 : ℕ)^8329*25000000000000000000^2048 ≤ 16494857042053633^2048*100000^8329 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16517 100000 16494857042053633 25000000000000000000 8329 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16517/100000 : ℝ)) (X := (16494857042053633/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8329 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000570702062950681/5000000000000000000 : ℝ) ≤ (10000280645341899/10000000000000000 : ℝ) ^ (8329/2048 : ℝ) := by
    have hpowers : (5000570702062950681/5000000000000000000 : ℝ)^2048 ≤ (10000280645341899/10000000000000000 : ℝ)^8329 := by
      have hnat : (5000570702062950681 : ℕ)^2048*10000000000000000^8329 ≤ 10000280645341899^8329*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000570702062950681 5000000000000000000 10000280645341899 10000000000000000 2048 8329 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000280645341899/10000000000000000 : ℝ)) (X := (5000570702062950681/5000000000000000000 : ℝ)) (by norm_num) 8329 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50035843224398860671/50000000000000000000 : ℝ) ≤ (2500440551627621/2500000000000000 : ℝ) ^ (8329/2048 : ℝ) := by
    have hpowers : (50035843224398860671/50000000000000000000 : ℝ)^2048 ≤ (2500440551627621/2500000000000000 : ℝ)^8329 := by
      have hnat : (50035843224398860671 : ℕ)^2048*2500000000000000^8329 ≤ 2500440551627621^8329*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035843224398860671 50000000000000000000 2500440551627621 2500000000000000 2048 8329 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500440551627621/2500000000000000 : ℝ)) (X := (50035843224398860671/50000000000000000000 : ℝ)) (by norm_num) 8329 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12516494857042053633/12500000000000000000 : ℝ) ≤ (10003243767679069/10000000000000000 : ℝ) ^ (8329/2048 : ℝ) := by
    have hpowers : (12516494857042053633/12500000000000000000 : ℝ)^2048 ≤ (10003243767679069/10000000000000000 : ℝ)^8329 := by
      have hnat : (12516494857042053633 : ℕ)^2048*10000000000000000^8329 ≤ 10003243767679069^8329*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12516494857042053633 12500000000000000000 10003243767679069 10000000000000000 2048 8329 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003243767679069/10000000000000000 : ℝ)) (X := (12516494857042053633/12500000000000000000 : ℝ)) (by norm_num) 8329 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(570702062950681/10000000000000000000 : ℝ) ≤ ((74665285809151929471/74690000000000000000 : ℝ)+2*(296312233717/149380000000000 : ℝ)*(1131/12500 : ℝ))^(8329/2048 : ℝ) := by
    rw [show (74665285809151929471/74690000000000000000 : ℝ)+2*(296312233717/149380000000000 : ℝ)*(1131/12500 : ℝ)=(10000280645341899/10000000000000000 : ℝ) by norm_num, show 1+2*(570702062950681/10000000000000000000 : ℝ)=(5000570702062950681/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16494857042053633/25000000000000000000 : ℝ)+(570702062950681/10000000000000000000 : ℝ) ≤ ((74665285809151929471/74690000000000000000 : ℝ)+(296312233717/149380000000000 : ℝ)*((16517/100000 : ℝ)+(1131/12500 : ℝ)))^(8329/2048 : ℝ) := by
    rw [show (74665285809151929471/74690000000000000000 : ℝ)+(296312233717/149380000000000 : ℝ)*((16517/100000 : ℝ)+(1131/12500 : ℝ))=(2500440551627621/2500000000000000 : ℝ) by norm_num, show 1+(16494857042053633/25000000000000000000 : ℝ)+(570702062950681/10000000000000000000 : ℝ)=(50035843224398860671/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16494857042053633/25000000000000000000 : ℝ) ≤ ((74665285809151929471/74690000000000000000 : ℝ)+2*(296312233717/149380000000000 : ℝ)*(16517/100000 : ℝ))^(8329/2048 : ℝ) := by
    rw [show (74665285809151929471/74690000000000000000 : ℝ)+2*(296312233717/149380000000000 : ℝ)*(16517/100000 : ℝ)=(10003243767679069/10000000000000000 : ℝ) by norm_num, show 1+2*(16494857042053633/25000000000000000000 : ℝ)=(12516494857042053633/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (74665285809151929471/74690000000000000000 : ℝ)*(X 1 0+X 2 0)+(296312233717/149380000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8329/2048 : ℝ)) (lo := (1131/12500 : ℝ)) (hi := (16517/100000 : ℝ)) (c := (74665285809151929471/74690000000000000000 : ℝ)) (alpha := (296312233717/149380000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (74665285809151929471/74690000000000000000 : ℝ)*(X 0 1+X 2 1)+(296312233717/149380000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8329/2048 : ℝ)) (lo := (1131/12500 : ℝ)) (hi := (16517/100000 : ℝ)) (c := (74665285809151929471/74690000000000000000 : ℝ)) (alpha := (296312233717/149380000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (74665285809151929471/74690000000000000000 : ℝ)*(X 0 2+X 1 2)+(296312233717/149380000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8329/2048 : ℝ)) (lo := (1131/12500 : ℝ)) (hi := (16517/100000 : ℝ)) (c := (74665285809151929471/74690000000000000000 : ℝ)) (alpha := (296312233717/149380000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2165422543/10000000000 : ℝ)*X 0 0+(5429689309/10000000000 : ℝ)*X 0 1+(5231617969/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5353913247/10000000000 : ℝ)*X 1 0+(-283335109/1250000000 : ℝ)*X 1 1+(163488057/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338478333/2500000000 : ℝ)*X 2 0+(5231617911/10000000000 : ℝ)*X 2 1+(-566670161/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((272693043/625000000 : ℝ)*X 0 0+(4170670371/10000000000 : ℝ)*X 0 1+(1141085361/2500000000 : ℝ)*X 0 2+(272693043/625000000 : ℝ)*X 1 0+(4170670371/10000000000 : ℝ)*X 1 1+(1141085361/2500000000 : ℝ)*X 1 2+(272693043/625000000 : ℝ)*X 2 0+(4170670371/10000000000 : ℝ)*X 2 1+(1141085361/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1082720429/5000000000 : ℝ)*X 0 0+(654048623/1250000000 : ℝ)*X 0 1+(542891397/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((212150039/400000000 : ℝ)*X 1 0+(-2069385167/10000000000 : ℝ)*X 1 1+(2714456873/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((662968947/1250000000 : ℝ)*X 2 0+(339307083/625000000 : ℝ)*X 2 1+(-1034692461/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4363124869/10000000000 : ℝ)*X 0 0+(2281404563/5000000000 : ℝ)*X 0 1+(13038161/31250000 : ℝ)*X 0 2+(4363124869/10000000000 : ℝ)*X 1 0+(2281404563/5000000000 : ℝ)*X 1 1+(13038161/31250000 : ℝ)*X 1 2+(4363124869/10000000000 : ℝ)*X 2 0+(2281404563/5000000000 : ℝ)*X 2 1+(13038161/31250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (612079062369506592674250951/84875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (28580523/1562500000000 : ℝ)*(base19) + (431799437/25000000000000 : ℝ)*(base23) + (12187571/12500000000000 : ℝ)*(lower2) + (1691609/1562500000000 : ℝ)*(upper3) + (55853317/25000000000000 : ℝ)*(upper5) + (948621473883897/25000000000000 : ℝ)*(major0) + (948621473883897/25000000000000 : ℝ)*(major1) + (948621473883897/25000000000000 : ℝ)*(major2) + (1009742936040253/20000000000000 : ℝ)*(sp0) + (5048747861409477/100000000000000 : ℝ)*(sp1) + (5048747963365201/100000000000000 : ℝ)*(sp2) + (317525878265161/12500000000000 : ℝ)*(sp3) + (8752590421/25000000000000 : ℝ)*(sp4) + (7417001211/50000000000000 : ℝ)*(sp7) + (254022186012371/10000000000000 : ℝ)*(f.failure) + (1262187422640737/25000000000000 : ℝ)*(f.sum) + (3600266114731/679000000000000000000000000 : ℝ)*base65 + (159917775392374683/169750000000000000000000000000000 : ℝ)*base68 + (1109786427208374683/169750000000000000000000000000000 : ℝ)*base70 + (173487373112374683/169750000000000000000000000000000 : ℝ)*base72 + (162115896023/42437500000000000000000000 : ℝ)*base74 + (109086714872624683/169750000000000000000000000000000 : ℝ)*base76 + (129156861155875317/169750000000000000000000000000000 : ℝ)*base77 + (921449108250125317/169750000000000000000000000000000 : ℝ)*base79 + (265604792517/84875000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1512269/1000000000000000000000 : ℝ)*base90 + (1512269/1000000000000000000000 : ℝ)*base92 + (1512269/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (47257794557699851751155527/33343750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (262733439/100000000000000 : ℝ)*(base19) + (114840597/12500000000000 : ℝ)*(base23) + (25051/6250000000000 : ℝ)*(upper2) + (23277009/100000000000000 : ℝ)*(upper5) + (478037588739347/12500000000000 : ℝ)*(major0) + (478037588739347/12500000000000 : ℝ)*(major1) + (478037588739347/12500000000000 : ℝ)*(major2) + (52245599/3125000000000 : ℝ)*(sp0) + (1981907447/100000000000000 : ℝ)*(sp1) + (2059272727/20000000000000 : ℝ)*(sp2) + (5088418287365963/100000000000000 : ℝ)*(sp4) + (1017683542916849/20000000000000 : ℝ)*(sp5) + (5088408744136719/100000000000000 : ℝ)*(sp6) + (320022676670173/12500000000000 : ℝ)*(sp7) + (320022676670173/12500000000000 : ℝ)*(f.failure) + (5088419959225131/100000000000000 : ℝ)*(f.sum) + (23272771051/21340000000000000000000000 : ℝ)*base66 + (426163491698156491/133375000000000000000000000000000 : ℝ)*base67 + (2423155010906491/133375000000000000000000000000000 : ℝ)*base69 + (1214500291052656491/133375000000000000000000000000000 : ℝ)*base71 + (5495151158839/1067000000000000000000000000 : ℝ)*base74 + (1547350890880593509/133375000000000000000000000000000 : ℝ)*base76 + (581961126982656491/133375000000000000000000000000000 : ℝ)*base77 + (1113395409514281491/133375000000000000000000000000000 : ℝ)*base79 + (675338414009/533500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (5945853/1250000000000000000000 : ℝ)*base89 + (5945853/1250000000000000000000 : ℝ)*base91 + (5945853/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1137_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149376161/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16517/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1131/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (531/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14811/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1137_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1137_s4_0 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2168466549/10000000000 : ℝ)*x 0 + (33763301/62500000 : ℝ)*x 1 + (210287513/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2168466549/10000000000 : ℝ)^4165 ≤ (205850229837/1562500000000 : ℝ)^3141 := by
    have hnat : (2168466549 : ℕ)^4165*1562500000000^3141 ≤ 205850229837^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2168466549 10000000000 205850229837 1562500000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (33763301/62500000 : ℝ)^4165 ≤ (1726387071/3906250000 : ℝ)^3141 := by
    have hnat : (33763301 : ℕ)^4165*3906250000^3141 ≤ 1726387071^3141*62500000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33763301 62500000 1726387071 3906250000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210287513/400000000 : ℝ)^4165 ≤ (42630076264641/100000000000000 : ℝ)^3141 := by
    have hnat : (210287513 : ℕ)^4165*100000000000000^3141 ≤ 42630076264641^3141*400000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210287513 400000000 42630076264641 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2168466549/10000000000 : ℝ), (33763301/62500000 : ℝ), (210287513/400000000 : ℝ)] ![(205850229837/1562500000000 : ℝ), (1726387071/3906250000 : ℝ), (42630076264641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2168466549/10000000000 : ℝ)|^4165 ≤ (205850229837/1562500000000 : ℝ)^3141
        have hw : |(-2168466549/10000000000 : ℝ)|=(2168466549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(33763301/62500000 : ℝ)|^4165 ≤ (1726387071/3906250000 : ℝ)^3141
        have hw : |(33763301/62500000 : ℝ)|=(33763301/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210287513/400000000 : ℝ)|^4165 ≤ (42630076264641/100000000000000 : ℝ)^3141
        have hw : |(210287513/400000000 : ℝ)|=(210287513/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s4_1 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (16709477/31250000 : ℝ)*x 0 + (-56053211/250000000 : ℝ)*x 1 + (5257188291/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16709477/31250000 : ℝ)^4165 ≤ (8719762817771/20000000000000 : ℝ)^3141 := by
    have hnat : (16709477 : ℕ)^4165*20000000000000^3141 ≤ 8719762817771^3141*31250000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16709477 31250000 8719762817771 20000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (56053211/250000000 : ℝ)^4165 ≤ (13771104616483/100000000000000 : ℝ)^3141 := by
    have hnat : (56053211 : ℕ)^4165*100000000000000^3141 ≤ 13771104616483^3141*250000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56053211 250000000 13771104616483 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5257188291/10000000000 : ℝ)^4165 ≤ (42630081275309/100000000000000 : ℝ)^3141 := by
    have hnat : (5257188291 : ℕ)^4165*100000000000000^3141 ≤ 42630081275309^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257188291 10000000000 42630081275309 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(16709477/31250000 : ℝ), (-56053211/250000000 : ℝ), (5257188291/10000000000 : ℝ)] ![(8719762817771/20000000000000 : ℝ), (13771104616483/100000000000000 : ℝ), (42630081275309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(16709477/31250000 : ℝ)|^4165 ≤ (8719762817771/20000000000000 : ℝ)^3141
        have hw : |(16709477/31250000 : ℝ)|=(16709477/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-56053211/250000000 : ℝ)|^4165 ≤ (13771104616483/100000000000000 : ℝ)^3141
        have hw : |(-56053211/250000000 : ℝ)|=(56053211/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5257188291/10000000000 : ℝ)|^4165 ≤ (42630081275309/100000000000000 : ℝ)^3141
        have hw : |(5257188291/10000000000 : ℝ)|=(5257188291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s4_2 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336758317/2500000000 : ℝ)*x 0 + (2628593653/5000000000 : ℝ)*x 1 + (-2242128907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336758317/2500000000 : ℝ)^4165 ≤ (10899705219709/25000000000000 : ℝ)^3141 := by
    have hnat : (1336758317 : ℕ)^4165*25000000000000^3141 ≤ 10899705219709^3141*2500000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336758317 2500000000 10899705219709 25000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2628593653/5000000000 : ℝ)^4165 ≤ (42630070684091/100000000000000 : ℝ)^3141 := by
    have hnat : (2628593653 : ℕ)^4165*100000000000000^3141 ≤ 42630070684091^3141*5000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628593653 5000000000 42630070684091 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2242128907/10000000000 : ℝ)^4165 ≤ (6885554209943/50000000000000 : ℝ)^3141 := by
    have hnat : (2242128907 : ℕ)^4165*50000000000000^3141 ≤ 6885554209943^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242128907 10000000000 6885554209943 50000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336758317/2500000000 : ℝ), (2628593653/5000000000 : ℝ), (-2242128907/10000000000 : ℝ)] ![(10899705219709/25000000000000 : ℝ), (42630070684091/100000000000000 : ℝ), (6885554209943/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336758317/2500000000 : ℝ)|^4165 ≤ (10899705219709/25000000000000 : ℝ)^3141
        have hw : |(1336758317/2500000000 : ℝ)|=(1336758317/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2628593653/5000000000 : ℝ)|^4165 ≤ (42630070684091/100000000000000 : ℝ)^3141
        have hw : |(2628593653/5000000000 : ℝ)|=(2628593653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2242128907/10000000000 : ℝ)|^4165 ≤ (6885554209943/50000000000000 : ℝ)^3141
        have hw : |(-2242128907/10000000000 : ℝ)|=(2242128907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s4_3 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4364904139/10000000000 : ℝ)*x 0 + (4223233041/10000000000 : ℝ)*x 1 + (4511307549/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4364904139/10000000000 : ℝ)^4165 ≤ (8328035683977/25000000000000 : ℝ)^3141 := by
    have hnat : (4364904139 : ℕ)^4165*25000000000000^3141 ≤ 8328035683977^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4364904139 10000000000 8328035683977 25000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4223233041/10000000000 : ℝ)^4165 ≤ (389234508/1220703125 : ℝ)^3141 := by
    have hnat : (4223233041 : ℕ)^4165*1220703125^3141 ≤ 389234508^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4223233041 10000000000 389234508 1220703125 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4511307549/10000000000 : ℝ)^4165 ≤ (8700441590133/25000000000000 : ℝ)^3141 := by
    have hnat : (4511307549 : ℕ)^4165*25000000000000^3141 ≤ 8700441590133^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4511307549 10000000000 8700441590133 25000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4364904139/10000000000 : ℝ), (4223233041/10000000000 : ℝ), (4511307549/10000000000 : ℝ)] ![(8328035683977/25000000000000 : ℝ), (389234508/1220703125 : ℝ), (8700441590133/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4364904139/10000000000 : ℝ)|^4165 ≤ (8328035683977/25000000000000 : ℝ)^3141
        have hw : |(4364904139/10000000000 : ℝ)|=(4364904139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4223233041/10000000000 : ℝ)|^4165 ≤ (389234508/1220703125 : ℝ)^3141
        have hw : |(4223233041/10000000000 : ℝ)|=(4223233041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4511307549/10000000000 : ℝ)|^4165 ≤ (8700441590133/25000000000000 : ℝ)^3141
        have hw : |(4511307549/10000000000 : ℝ)|=(4511307549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s4_4 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1084237047/5000000000 : ℝ)*x 0 + (5257601273/10000000000 : ℝ)*x 1 + (5401712747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1084237047/5000000000 : ℝ)^4165 ≤ (13174475492993/100000000000000 : ℝ)^3141 := by
    have hnat : (1084237047 : ℕ)^4165*100000000000000^3141 ≤ 13174475492993^3141*5000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084237047 5000000000 13174475492993 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5257601273/10000000000 : ℝ)^4165 ≤ (666164405057/1562500000000 : ℝ)^3141 := by
    have hnat : (5257601273 : ℕ)^4165*1562500000000^3141 ≤ 666164405057^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257601273 10000000000 666164405057 1562500000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5401712747/10000000000 : ℝ)^4165 ≤ (44191002563357/100000000000000 : ℝ)^3141 := by
    have hnat : (5401712747 : ℕ)^4165*100000000000000^3141 ≤ 44191002563357^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401712747 10000000000 44191002563357 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1084237047/5000000000 : ℝ), (5257601273/10000000000 : ℝ), (5401712747/10000000000 : ℝ)] ![(13174475492993/100000000000000 : ℝ), (666164405057/1562500000000 : ℝ), (44191002563357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1084237047/5000000000 : ℝ)|^4165 ≤ (13174475492993/100000000000000 : ℝ)^3141
        have hw : |(-1084237047/5000000000 : ℝ)|=(1084237047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5257601273/10000000000 : ℝ)|^4165 ≤ (666164405057/1562500000000 : ℝ)^3141
        have hw : |(5257601273/10000000000 : ℝ)|=(5257601273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5401712747/10000000000 : ℝ)|^4165 ≤ (44191002563357/100000000000000 : ℝ)^3141
        have hw : |(5401712747/10000000000 : ℝ)|=(5401712747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s4_5 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1327582021/2500000000 : ℝ)*x 0 + (-419520603/2000000000 : ℝ)*x 1 + (2700856249/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327582021/2500000000 : ℝ)^4165 ≤ (10800601636679/25000000000000 : ℝ)^3141 := by
    have hnat : (1327582021 : ℕ)^4165*25000000000000^3141 ≤ 10800601636679^3141*2500000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327582021 2500000000 10800601636679 25000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (419520603/2000000000 : ℝ)^4165 ≤ (12606593576627/100000000000000 : ℝ)^3141 := by
    have hnat : (419520603 : ℕ)^4165*100000000000000^3141 ≤ 12606593576627^3141*2000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419520603 2000000000 12606593576627 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2700856249/5000000000 : ℝ)^4165 ≤ (22095499931103/50000000000000 : ℝ)^3141 := by
    have hnat : (2700856249 : ℕ)^4165*50000000000000^3141 ≤ 22095499931103^3141*5000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700856249 5000000000 22095499931103 50000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327582021/2500000000 : ℝ), (-419520603/2000000000 : ℝ), (2700856249/5000000000 : ℝ)] ![(10800601636679/25000000000000 : ℝ), (12606593576627/100000000000000 : ℝ), (22095499931103/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327582021/2500000000 : ℝ)|^4165 ≤ (10800601636679/25000000000000 : ℝ)^3141
        have hw : |(1327582021/2500000000 : ℝ)|=(1327582021/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-419520603/2000000000 : ℝ)|^4165 ≤ (12606593576627/100000000000000 : ℝ)^3141
        have hw : |(-419520603/2000000000 : ℝ)|=(419520603/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2700856249/5000000000 : ℝ)|^4165 ≤ (22095499931103/50000000000000 : ℝ)^3141
        have hw : |(2700856249/5000000000 : ℝ)|=(2700856249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s4_6 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2655163803/5000000000 : ℝ)*x 0 + (1350428271/2500000000 : ℝ)*x 1 + (-419520573/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655163803/5000000000 : ℝ)^4165 ≤ (43202401390139/100000000000000 : ℝ)^3141 := by
    have hnat : (2655163803 : ℕ)^4165*100000000000000^3141 ≤ 43202401390139^3141*5000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655163803 5000000000 43202401390139 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1350428271/2500000000 : ℝ)^4165 ≤ (44191006219131/100000000000000 : ℝ)^3141 := by
    have hnat : (1350428271 : ℕ)^4165*100000000000000^3141 ≤ 44191006219131^3141*2500000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350428271 2500000000 44191006219131 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (419520573/2000000000 : ℝ)^4165 ≤ (12606592381229/100000000000000 : ℝ)^3141 := by
    have hnat : (419520573 : ℕ)^4165*100000000000000^3141 ≤ 12606592381229^3141*2000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419520573 2000000000 12606592381229 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655163803/5000000000 : ℝ), (1350428271/2500000000 : ℝ), (-419520573/2000000000 : ℝ)] ![(43202401390139/100000000000000 : ℝ), (44191006219131/100000000000000 : ℝ), (12606592381229/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655163803/5000000000 : ℝ)|^4165 ≤ (43202401390139/100000000000000 : ℝ)^3141
        have hw : |(2655163803/5000000000 : ℝ)|=(2655163803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1350428271/2500000000 : ℝ)|^4165 ≤ (44191006219131/100000000000000 : ℝ)^3141
        have hw : |(1350428271/2500000000 : ℝ)|=(1350428271/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-419520573/2000000000 : ℝ)|^4165 ≤ (12606592381229/100000000000000 : ℝ)^3141
        have hw : |(-419520573/2000000000 : ℝ)|=(419520573/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s4_7 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4364917801/10000000000 : ℝ)*x 0 + (902097099/2000000000 : ℝ)*x 1 + (4224059109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4364917801/10000000000 : ℝ)^4165 ≤ (33312280993641/100000000000000 : ℝ)^3141 := by
    have hnat : (4364917801 : ℕ)^4165*100000000000000^3141 ≤ 33312280993641^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4364917801 10000000000 33312280993641 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (902097099/2000000000 : ℝ)^4165 ≤ (4349169696653/12500000000000 : ℝ)^3141 := by
    have hnat : (902097099 : ℕ)^4165*12500000000000^3141 ≤ 4349169696653^3141*2000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      902097099 2000000000 4349169696653 12500000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4224059109/10000000000 : ℝ)^4165 ≤ (1594718070893/5000000000000 : ℝ)^3141 := by
    have hnat : (4224059109 : ℕ)^4165*5000000000000^3141 ≤ 1594718070893^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4224059109 10000000000 1594718070893 5000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4364917801/10000000000 : ℝ), (902097099/2000000000 : ℝ), (4224059109/10000000000 : ℝ)] ![(33312280993641/100000000000000 : ℝ), (4349169696653/12500000000000 : ℝ), (1594718070893/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4364917801/10000000000 : ℝ)|^4165 ≤ (33312280993641/100000000000000 : ℝ)^3141
        have hw : |(4364917801/10000000000 : ℝ)|=(4364917801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(902097099/2000000000 : ℝ)|^4165 ≤ (4349169696653/12500000000000 : ℝ)^3141
        have hw : |(902097099/2000000000 : ℝ)|=(902097099/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4224059109/10000000000 : ℝ)|^4165 ≤ (1594718070893/5000000000000 : ℝ)^3141
        have hw : |(4224059109/10000000000 : ℝ)|=(4224059109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1137_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149376161/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14811/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (531/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (5583/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2847/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14811/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (531/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14811/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (531/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14811/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (531/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14811/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (531/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14811/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (531/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14811/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (531/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base29 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0, f.sum]
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
  have hpowlo : (531/5000 : ℝ) ^ (8329/2048 : ℝ) ≤ (10948411774125541/100000000000000000000 : ℝ) := by
    have hpowers : (531/5000 : ℝ)^8329 ≤ (10948411774125541/100000000000000000000 : ℝ)^2048 := by
      have hnat : (531 : ℕ)^8329*100000000000000000000^2048 ≤ 10948411774125541^2048*5000^8329 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        531 5000 10948411774125541 100000000000000000000 8329 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (531/5000 : ℝ)) (X := (10948411774125541/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8329 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14811/100000 : ℝ) ^ (8329/2048 : ℝ) ≤ (21175036280704481/50000000000000000000 : ℝ) := by
    have hpowers : (14811/100000 : ℝ)^8329 ≤ (21175036280704481/50000000000000000000 : ℝ)^2048 := by
      have hnat : (14811 : ℕ)^8329*50000000000000000000^2048 ≤ 21175036280704481^2048*100000^8329 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14811 100000 21175036280704481 50000000000000000000 8329 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14811/100000 : ℝ)) (X := (21175036280704481/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8329 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010948411774125541/50000000000000000000 : ℝ) ≤ (10000538371864267/10000000000000000 : ℝ) ^ (8329/2048 : ℝ) := by
    have hpowers : (50010948411774125541/50000000000000000000 : ℝ)^2048 ≤ (10000538371864267/10000000000000000 : ℝ)^8329 := by
      have hnat : (50010948411774125541 : ℕ)^2048*10000000000000000^8329 ≤ 10000538371864267^8329*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010948411774125541 50000000000000000000 10000538371864267 10000000000000000 2048 8329 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000538371864267/10000000000000000 : ℝ)) (X := (50010948411774125541/50000000000000000000 : ℝ)) (by norm_num) 8329 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100053298484335534503/100000000000000000000 : ℝ) ≤ (1000131028174259/1000000000000000 : ℝ) ^ (8329/2048 : ℝ) := by
    have hpowers : (100053298484335534503/100000000000000000000 : ℝ)^2048 ≤ (1000131028174259/1000000000000000 : ℝ)^8329 := by
      have hnat : (100053298484335534503 : ℕ)^2048*1000000000000000^8329 ≤ 1000131028174259^8329*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100053298484335534503 100000000000000000000 1000131028174259 1000000000000000 2048 8329 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000131028174259/1000000000000000 : ℝ)) (X := (100053298484335534503/100000000000000000000 : ℝ)) (by norm_num) 8329 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25021175036280704481/25000000000000000000 : ℝ) ≤ (10002082191620913/10000000000000000 : ℝ) ^ (8329/2048 : ℝ) := by
    have hpowers : (25021175036280704481/25000000000000000000 : ℝ)^2048 ≤ (10002082191620913/10000000000000000 : ℝ)^8329 := by
      have hnat : (25021175036280704481 : ℕ)^2048*10000000000000000^8329 ≤ 10002082191620913^8329*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25021175036280704481 25000000000000000000 10002082191620913 10000000000000000 2048 8329 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002082191620913/10000000000000000 : ℝ)) (X := (25021175036280704481/25000000000000000000 : ℝ)) (by norm_num) 8329 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10948411774125541/100000000000000000000 : ℝ) ≤ ((13965286983555854159/13970000000000000000 : ℝ)+2*(771909878323/419100000000000 : ℝ)*(531/5000 : ℝ))^(8329/2048 : ℝ) := by
    rw [show (13965286983555854159/13970000000000000000 : ℝ)+2*(771909878323/419100000000000 : ℝ)*(531/5000 : ℝ)=(10000538371864267/10000000000000000 : ℝ) by norm_num, show 1+2*(10948411774125541/100000000000000000000 : ℝ)=(50010948411774125541/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(21175036280704481/50000000000000000000 : ℝ)+(10948411774125541/100000000000000000000 : ℝ) ≤ ((13965286983555854159/13970000000000000000 : ℝ)+(771909878323/419100000000000 : ℝ)*((14811/100000 : ℝ)+(531/5000 : ℝ)))^(8329/2048 : ℝ) := by
    rw [show (13965286983555854159/13970000000000000000 : ℝ)+(771909878323/419100000000000 : ℝ)*((14811/100000 : ℝ)+(531/5000 : ℝ))=(1000131028174259/1000000000000000 : ℝ) by norm_num, show 1+(21175036280704481/50000000000000000000 : ℝ)+(10948411774125541/100000000000000000000 : ℝ)=(100053298484335534503/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(21175036280704481/50000000000000000000 : ℝ) ≤ ((13965286983555854159/13970000000000000000 : ℝ)+2*(771909878323/419100000000000 : ℝ)*(14811/100000 : ℝ))^(8329/2048 : ℝ) := by
    rw [show (13965286983555854159/13970000000000000000 : ℝ)+2*(771909878323/419100000000000 : ℝ)*(14811/100000 : ℝ)=(10002082191620913/10000000000000000 : ℝ) by norm_num, show 1+2*(21175036280704481/50000000000000000000 : ℝ)=(25021175036280704481/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13965286983555854159/13970000000000000000 : ℝ)*(X 1 0+X 2 0)+(771909878323/419100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8329/2048 : ℝ)) (lo := (531/5000 : ℝ)) (hi := (14811/100000 : ℝ)) (c := (13965286983555854159/13970000000000000000 : ℝ)) (alpha := (771909878323/419100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13965286983555854159/13970000000000000000 : ℝ)*(X 0 1+X 2 1)+(771909878323/419100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8329/2048 : ℝ)) (lo := (531/5000 : ℝ)) (hi := (14811/100000 : ℝ)) (c := (13965286983555854159/13970000000000000000 : ℝ)) (alpha := (771909878323/419100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13965286983555854159/13970000000000000000 : ℝ)*(X 0 2+X 1 2)+(771909878323/419100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8329/2048 : ℝ)) (lo := (531/5000 : ℝ)) (hi := (14811/100000 : ℝ)) (c := (13965286983555854159/13970000000000000000 : ℝ)) (alpha := (771909878323/419100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2168466549/10000000000 : ℝ)*X 0 0+(33763301/62500000 : ℝ)*X 0 1+(210287513/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((16709477/31250000 : ℝ)*X 1 0+(-56053211/250000000 : ℝ)*X 1 1+(5257188291/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336758317/2500000000 : ℝ)*X 2 0+(2628593653/5000000000 : ℝ)*X 2 1+(-2242128907/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4364904139/10000000000 : ℝ)*X 0 0+(4223233041/10000000000 : ℝ)*X 0 1+(4511307549/10000000000 : ℝ)*X 0 2+(4364904139/10000000000 : ℝ)*X 1 0+(4223233041/10000000000 : ℝ)*X 1 1+(4511307549/10000000000 : ℝ)*X 1 2+(4364904139/10000000000 : ℝ)*X 2 0+(4223233041/10000000000 : ℝ)*X 2 1+(4511307549/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1084237047/5000000000 : ℝ)*X 0 0+(5257601273/10000000000 : ℝ)*X 0 1+(5401712747/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1327582021/2500000000 : ℝ)*X 1 0+(-419520603/2000000000 : ℝ)*X 1 1+(2700856249/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2655163803/5000000000 : ℝ)*X 2 0+(1350428271/2500000000 : ℝ)*X 2 1+(-419520573/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4364917801/10000000000 : ℝ)*X 0 0+(902097099/2000000000 : ℝ)*X 0 1+(4224059109/10000000000 : ℝ)*X 0 2+(4364917801/10000000000 : ℝ)*X 1 0+(902097099/2000000000 : ℝ)*X 1 1+(4224059109/10000000000 : ℝ)*X 1 2+(4364917801/10000000000 : ℝ)*X 2 0+(902097099/2000000000 : ℝ)*X 2 1+(4224059109/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2886110182624527162997161339/349250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (306167/2000000000000 : ℝ)*(base21) + (337673253/100000000000000 : ℝ)*(base29) + (456379281/100000000000000 : ℝ)*(lower2) + (28922393/20000000000000 : ℝ)*(upper3) + (123643909/100000000000000 : ℝ)*(lower4) + (129634113580737/2500000000000 : ℝ)*(major0) + (5185364880902733/100000000000000 : ℝ)*(major1) + (5185364880902733/100000000000000 : ℝ)*(major2) + (6899382488145621/100000000000000 : ℝ)*(sp0) + (6899382150472367/100000000000000 : ℝ)*(sp1) + (215604775067473/3125000000000 : ℝ)*(sp2) + (3471331199412097/100000000000000 : ℝ)*(sp3) + (14666502441/50000000000000 : ℝ)*(sp6) + (78993949/500000000000 : ℝ)*(sp7) + (3471346998201897/100000000000000 : ℝ)*(f.failure) + (6899382488145621/100000000000000 : ℝ)*(f.sum) + (44296302584563/6985000000000000000000000000 : ℝ)*base65 + (306736291113528777/127000000000000000000000000000000 : ℝ)*base67 + (9119794936106528777/127000000000000000000000000000000 : ℝ)*base69 + (226131274168407317/34925000000000000000000000000000 : ℝ)*base72 + (36181243529843/13970000000000000000000000000 : ℝ)*base73 + (1158495154630516547/1397000000000000000000000000000000 : ℝ)*base75 + (5690931592513907317/34925000000000000000000000000000 : ℝ)*base78 + (231729729116523516547/1397000000000000000000000000000000 : ℝ)*base79 + (74630222494063/13970000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (23222583/10000000000000000000000 : ℝ)*base90 + (23222583/10000000000000000000000 : ℝ)*base92 + (23222583/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (77096199396271476782654741/13970000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (158828777/20000000000000 : ℝ)*(base19) + (422350411/100000000000000 : ℝ)*(base23) + (9016607/20000000000000 : ℝ)*(upper3) + (48724121/50000000000000 : ℝ)*(lower4) + (208607508089033/4000000000000 : ℝ)*(major0) + (208607508089033/4000000000000 : ℝ)*(major1) + (208607508089033/4000000000000 : ℝ)*(major2) + (10192374049/100000000000000 : ℝ)*(sp1) + (808759023/4000000000000 : ℝ)*(sp2) + (249703823/3125000000000 : ℝ)*(sp3) + (6939063308799977/100000000000000 : ℝ)*(sp4) + (6939052322282043/100000000000000 : ℝ)*(sp5) + (6939042667473993/100000000000000 : ℝ)*(sp6) + (3491303921172747/100000000000000 : ℝ)*(sp7) + (1745655955847541/50000000000000 : ℝ)*(f.failure) + (6939063308799977/100000000000000 : ℝ)*(f.sum) + (5309313040903/1047750000000000000000000000 : ℝ)*base65 + (86158324719069569/15240000000000000000000000000000 : ℝ)*base68 + (83117098045629569/15240000000000000000000000000000 : ℝ)*base70 + (198175974363290431/15240000000000000000000000000000 : ℝ)*base71 + (10692389705119/4191000000000000000000000000 : ℝ)*base73 + (241840583300589569/15240000000000000000000000000000 : ℝ)*base76 + (56570148899349569/15240000000000000000000000000000 : ℝ)*base78 + (410073927447909569/15240000000000000000000000000000 : ℝ)*base80 + (3120298516331/523875000000000000000000000 : ℝ)*base81 + (1/50000000000000 : ℝ)*base87 + (74129899/5000000000000000000000 : ℝ)*base90 + (74129899/5000000000000000000000 : ℝ)*base92 + (74129899/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1137_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149376161/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14811/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (531/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5583/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1137_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1137_s5_0 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1084556723/5000000000 : ℝ)*x 0 + (2697521233/5000000000 : ℝ)*x 1 + (2631924509/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1084556723/5000000000 : ℝ)^4165 ≤ (1647453304973/12500000000000 : ℝ)^3141 := by
    have hnat : (1084556723 : ℕ)^4165*12500000000000^3141 ≤ 1647453304973^3141*5000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084556723 5000000000 1647453304973 12500000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697521233/5000000000 : ℝ)^4165 ≤ (44118657963713/100000000000000 : ℝ)^3141 := by
    have hnat : (2697521233 : ℕ)^4165*100000000000000^3141 ≤ 44118657963713^3141*5000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697521233 5000000000 44118657963713 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2631924509/5000000000 : ℝ)^4165 ≤ (42701715570003/100000000000000 : ℝ)^3141 := by
    have hnat : (2631924509 : ℕ)^4165*100000000000000^3141 ≤ 42701715570003^3141*5000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631924509 5000000000 42701715570003 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1084556723/5000000000 : ℝ), (2697521233/5000000000 : ℝ), (2631924509/5000000000 : ℝ)] ![(1647453304973/12500000000000 : ℝ), (44118657963713/100000000000000 : ℝ), (42701715570003/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1084556723/5000000000 : ℝ)|^4165 ≤ (1647453304973/12500000000000 : ℝ)^3141
        have hw : |(-1084556723/5000000000 : ℝ)|=(1084556723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697521233/5000000000 : ℝ)|^4165 ≤ (44118657963713/100000000000000 : ℝ)^3141
        have hw : |(2697521233/5000000000 : ℝ)|=(2697521233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2631924509/5000000000 : ℝ)|^4165 ≤ (42701715570003/100000000000000 : ℝ)^3141
        have hw : |(2631924509/5000000000 : ℝ)|=(2631924509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s5_1 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534525773/1000000000 : ℝ)*x 0 + (-2235685973/10000000000 : ℝ)*x 1 + (1315962257/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534525773/1000000000 : ℝ)^4165 ≤ (21789812336703/50000000000000 : ℝ)^3141 := by
    have hnat : (534525773 : ℕ)^4165*50000000000000^3141 ≤ 21789812336703^3141*1000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534525773 1000000000 21789812336703 50000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2235685973/10000000000 : ℝ)^4165 ≤ (6859329815459/50000000000000 : ℝ)^3141 := by
    have hnat : (2235685973 : ℕ)^4165*50000000000000^3141 ≤ 6859329815459^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2235685973 10000000000 6859329815459 50000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1315962257/2500000000 : ℝ)^4165 ≤ (42701715677573/100000000000000 : ℝ)^3141 := by
    have hnat : (1315962257 : ℕ)^4165*100000000000000^3141 ≤ 42701715677573^3141*2500000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315962257 2500000000 42701715677573 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534525773/1000000000 : ℝ), (-2235685973/10000000000 : ℝ), (1315962257/2500000000 : ℝ)] ![(21789812336703/50000000000000 : ℝ), (6859329815459/50000000000000 : ℝ), (42701715677573/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534525773/1000000000 : ℝ)|^4165 ≤ (21789812336703/50000000000000 : ℝ)^3141
        have hw : |(534525773/1000000000 : ℝ)|=(534525773/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2235685973/10000000000 : ℝ)|^4165 ≤ (6859329815459/50000000000000 : ℝ)^3141
        have hw : |(-2235685973/10000000000 : ℝ)|=(2235685973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1315962257/2500000000 : ℝ)|^4165 ≤ (42701715677573/100000000000000 : ℝ)^3141
        have hw : |(1315962257/2500000000 : ℝ)|=(1315962257/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s5_2 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069051539/2000000000 : ℝ)*x 0 + (2631924531/5000000000 : ℝ)*x 1 + (-279460747/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069051539/2000000000 : ℝ)^4165 ≤ (2723726518439/6250000000000 : ℝ)^3141 := by
    have hnat : (1069051539 : ℕ)^4165*6250000000000^3141 ≤ 2723726518439^3141*2000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069051539 2000000000 2723726518439 6250000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2631924531/5000000000 : ℝ)^4165 ≤ (42701716043309/100000000000000 : ℝ)^3141 := by
    have hnat : (2631924531 : ℕ)^4165*100000000000000^3141 ≤ 42701716043309^3141*5000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631924531 5000000000 42701716043309 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (279460747/1250000000 : ℝ)^4165 ≤ (428708114229/3125000000000 : ℝ)^3141 := by
    have hnat : (279460747 : ℕ)^4165*3125000000000^3141 ≤ 428708114229^3141*1250000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      279460747 1250000000 428708114229 3125000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069051539/2000000000 : ℝ), (2631924531/5000000000 : ℝ), (-279460747/1250000000 : ℝ)] ![(2723726518439/6250000000000 : ℝ), (42701716043309/100000000000000 : ℝ), (428708114229/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069051539/2000000000 : ℝ)|^4165 ≤ (2723726518439/6250000000000 : ℝ)^3141
        have hw : |(1069051539/2000000000 : ℝ)|=(1069051539/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2631924531/5000000000 : ℝ)|^4165 ≤ (42701716043309/100000000000000 : ℝ)^3141
        have hw : |(2631924531/5000000000 : ℝ)|=(2631924531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-279460747/1250000000 : ℝ)|^4165 ≤ (428708114229/3125000000000 : ℝ)^3141
        have hw : |(-279460747/1250000000 : ℝ)|=(279460747/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s5_3 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2182640949/5000000000 : ℝ)*x 0 + (2118423213/5000000000 : ℝ)*x 1 + (1124399093/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2182640949/5000000000 : ℝ)^4165 ≤ (16657982830879/50000000000000 : ℝ)^3141 := by
    have hnat : (2182640949 : ℕ)^4165*50000000000000^3141 ≤ 16657982830879^3141*5000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182640949 5000000000 16657982830879 50000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2118423213/5000000000 : ℝ)^4165 ≤ (8005613540793/25000000000000 : ℝ)^3141 := by
    have hnat : (2118423213 : ℕ)^4165*25000000000000^3141 ≤ 8005613540793^3141*5000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118423213 5000000000 8005613540793 25000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1124399093/2500000000 : ℝ)^4165 ≤ (8665395037241/25000000000000 : ℝ)^3141 := by
    have hnat : (1124399093 : ℕ)^4165*25000000000000^3141 ≤ 8665395037241^3141*2500000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124399093 2500000000 8665395037241 25000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2182640949/5000000000 : ℝ), (2118423213/5000000000 : ℝ), (1124399093/2500000000 : ℝ)] ![(16657982830879/50000000000000 : ℝ), (8005613540793/25000000000000 : ℝ), (8665395037241/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2182640949/5000000000 : ℝ)|^4165 ≤ (16657982830879/50000000000000 : ℝ)^3141
        have hw : |(2182640949/5000000000 : ℝ)|=(2182640949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2118423213/5000000000 : ℝ)|^4165 ≤ (8005613540793/25000000000000 : ℝ)^3141
        have hw : |(2118423213/5000000000 : ℝ)|=(2118423213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1124399093/2500000000 : ℝ)|^4165 ≤ (8665395037241/25000000000000 : ℝ)^3141
        have hw : |(1124399093/2500000000 : ℝ)|=(1124399093/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s5_4 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-542279691/2500000000 : ℝ)*x 0 + (5264188187/10000000000 : ℝ)*x 1 + (5394702051/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (542279691/2500000000 : ℝ)^4165 ≤ (13179669286389/100000000000000 : ℝ)^3141 := by
    have hnat : (542279691 : ℕ)^4165*100000000000000^3141 ≤ 13179669286389^3141*2500000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542279691 2500000000 13179669286389 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264188187/10000000000 : ℝ)^4165 ≤ (1708214561231/4000000000000 : ℝ)^3141 := by
    have hnat : (5264188187 : ℕ)^4165*4000000000000^3141 ≤ 1708214561231^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264188187 10000000000 1708214561231 4000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394702051/10000000000 : ℝ)^4165 ≤ (22057483334517/50000000000000 : ℝ)^3141 := by
    have hnat : (5394702051 : ℕ)^4165*50000000000000^3141 ≤ 22057483334517^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394702051 10000000000 22057483334517 50000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-542279691/2500000000 : ℝ), (5264188187/10000000000 : ℝ), (5394702051/10000000000 : ℝ)] ![(13179669286389/100000000000000 : ℝ), (1708214561231/4000000000000 : ℝ), (22057483334517/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-542279691/2500000000 : ℝ)|^4165 ≤ (13179669286389/100000000000000 : ℝ)^3141
        have hw : |(-542279691/2500000000 : ℝ)|=(542279691/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264188187/10000000000 : ℝ)|^4165 ≤ (1708214561231/4000000000000 : ℝ)^3141
        have hw : |(5264188187/10000000000 : ℝ)|=(5264188187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394702051/10000000000 : ℝ)|^4165 ≤ (22057483334517/50000000000000 : ℝ)^3141
        have hw : |(5394702051/10000000000 : ℝ)|=(5394702051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s5_5 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312032071/10000000000 : ℝ)*x 0 + (-1052416477/5000000000 : ℝ)*x 1 + (2697351019/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312032071/10000000000 : ℝ)^4165 ≤ (8644157962329/20000000000000 : ℝ)^3141 := by
    have hnat : (5312032071 : ℕ)^4165*20000000000000^3141 ≤ 8644157962329^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312032071 10000000000 8644157962329 20000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052416477/5000000000 : ℝ)^4165 ≤ (2532848731027/20000000000000 : ℝ)^3141 := by
    have hnat : (1052416477 : ℕ)^4165*20000000000000^3141 ≤ 2532848731027^3141*5000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052416477 5000000000 2532848731027 20000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697351019/5000000000 : ℝ)^4165 ≤ (4411496652807/10000000000000 : ℝ)^3141 := by
    have hnat : (2697351019 : ℕ)^4165*10000000000000^3141 ≤ 4411496652807^3141*5000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697351019 5000000000 4411496652807 10000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312032071/10000000000 : ℝ), (-1052416477/5000000000 : ℝ), (2697351019/5000000000 : ℝ)] ![(8644157962329/20000000000000 : ℝ), (2532848731027/20000000000000 : ℝ), (4411496652807/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312032071/10000000000 : ℝ)|^4165 ≤ (8644157962329/20000000000000 : ℝ)^3141
        have hw : |(5312032071/10000000000 : ℝ)|=(5312032071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1052416477/5000000000 : ℝ)|^4165 ≤ (2532848731027/20000000000000 : ℝ)^3141
        have hw : |(-1052416477/5000000000 : ℝ)|=(1052416477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697351019/5000000000 : ℝ)|^4165 ≤ (4411496652807/10000000000000 : ℝ)^3141
        have hw : |(2697351019/5000000000 : ℝ)|=(2697351019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s5_6 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1062406413/2000000000 : ℝ)*x 0 + (5394702041/10000000000 : ℝ)*x 1 + (-2104832957/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062406413/2000000000 : ℝ)^4165 ≤ (43220789746911/100000000000000 : ℝ)^3141 := by
    have hnat : (1062406413 : ℕ)^4165*100000000000000^3141 ≤ 43220789746911^3141*2000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062406413 2000000000 43220789746911 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394702041/10000000000 : ℝ)^4165 ≤ (220574832803/500000000000 : ℝ)^3141 := by
    have hnat : (5394702041 : ℕ)^4165*500000000000^3141 ≤ 220574832803^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394702041 10000000000 220574832803 500000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2104832957/10000000000 : ℝ)^4165 ≤ (12664243679069/100000000000000 : ℝ)^3141 := by
    have hnat : (2104832957 : ℕ)^4165*100000000000000^3141 ≤ 12664243679069^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2104832957 10000000000 12664243679069 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062406413/2000000000 : ℝ), (5394702041/10000000000 : ℝ), (-2104832957/10000000000 : ℝ)] ![(43220789746911/100000000000000 : ℝ), (220574832803/500000000000 : ℝ), (12664243679069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062406413/2000000000 : ℝ)|^4165 ≤ (43220789746911/100000000000000 : ℝ)^3141
        have hw : |(1062406413/2000000000 : ℝ)|=(1062406413/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394702041/10000000000 : ℝ)|^4165 ≤ (220574832803/500000000000 : ℝ)^3141
        have hw : |(5394702041/10000000000 : ℝ)|=(5394702041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2104832957/10000000000 : ℝ)|^4165 ≤ (12664243679069/100000000000000 : ℝ)^3141
        have hw : |(-2104832957/10000000000 : ℝ)|=(2104832957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s5_7 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1746117/4000000 : ℝ)*x 0 + (2248461163/5000000000 : ℝ)*x 1 + (2118761493/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1746117/4000000 : ℝ)^4165 ≤ (4164509119461/12500000000000 : ℝ)^3141 := by
    have hnat : (1746117 : ℕ)^4165*12500000000000^3141 ≤ 4164509119461^3141*4000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1746117 4000000 4164509119461 12500000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2248461163/5000000000 : ℝ)^4165 ≤ (4331836517161/12500000000000 : ℝ)^3141 := by
    have hnat : (2248461163 : ℕ)^4165*12500000000000^3141 ≤ 4331836517161^3141*5000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248461163 5000000000 4331836517161 12500000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2118761493/5000000000 : ℝ)^4165 ≤ (6405846979039/20000000000000 : ℝ)^3141 := by
    have hnat : (2118761493 : ℕ)^4165*20000000000000^3141 ≤ 6405846979039^3141*5000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118761493 5000000000 6405846979039 20000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1746117/4000000 : ℝ), (2248461163/5000000000 : ℝ), (2118761493/5000000000 : ℝ)] ![(4164509119461/12500000000000 : ℝ), (4331836517161/12500000000000 : ℝ), (6405846979039/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1746117/4000000 : ℝ)|^4165 ≤ (4164509119461/12500000000000 : ℝ)^3141
        have hw : |(1746117/4000000 : ℝ)|=(1746117/4000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2248461163/5000000000 : ℝ)|^4165 ≤ (4331836517161/12500000000000 : ℝ)^3141
        have hw : |(2248461163/5000000000 : ℝ)|=(2248461163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2118761493/5000000000 : ℝ)|^4165 ≤ (6405846979039/20000000000000 : ℝ)^3141
        have hw : |(2118761493/5000000000 : ℝ)|=(2118761493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1137_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149376161/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5583/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2827/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14087/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5583/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5583/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5583/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5583/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5583/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5583/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5583/50000 : ℝ) ^ (8329/2048 : ℝ) ≤ (13424559740420473/100000000000000000000 : ℝ) := by
    have hpowers : (5583/50000 : ℝ)^8329 ≤ (13424559740420473/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5583 : ℕ)^8329*100000000000000000000^2048 ≤ 13424559740420473^2048*50000^8329 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5583 50000 13424559740420473 100000000000000000000 8329 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5583/50000 : ℝ)) (X := (13424559740420473/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8329 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2847/20000 : ℝ) ^ (8329/2048 : ℝ) ≤ (36040775798783507/100000000000000000000 : ℝ) := by
    have hpowers : (2847/20000 : ℝ)^8329 ≤ (36040775798783507/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2847 : ℕ)^8329*100000000000000000000^2048 ≤ 36040775798783507^2048*20000^8329 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2847 20000 36040775798783507 100000000000000000000 8329 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2847/20000 : ℝ)) (X := (36040775798783507/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8329 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013424559740420473/50000000000000000000 : ℝ) ≤ (5000330060216677/5000000000000000 : ℝ) ^ (8329/2048 : ℝ) := by
    have hpowers : (50013424559740420473/50000000000000000000 : ℝ)^2048 ≤ (5000330060216677/5000000000000000 : ℝ)^8329 := by
      have hnat : (50013424559740420473 : ℕ)^2048*5000000000000000^8329 ≤ 5000330060216677^8329*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013424559740420473 50000000000000000000 5000330060216677 5000000000000000 2048 8329 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000330060216677/5000000000000000 : ℝ)) (X := (50013424559740420473/50000000000000000000 : ℝ)) (by norm_num) 8329 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (5002473266776960199/5000000000000000000 : ℝ) ≤ (5000608032885357/5000000000000000 : ℝ) ^ (8329/2048 : ℝ) := by
    have hpowers : (5002473266776960199/5000000000000000000 : ℝ)^2048 ≤ (5000608032885357/5000000000000000 : ℝ)^8329 := by
      have hnat : (5002473266776960199 : ℕ)^2048*5000000000000000^8329 ≤ 5000608032885357^8329*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002473266776960199 5000000000000000000 5000608032885357 5000000000000000 2048 8329 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000608032885357/5000000000000000 : ℝ)) (X := (5002473266776960199/5000000000000000000 : ℝ)) (by norm_num) 8329 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036040775798783507/50000000000000000000 : ℝ) ≤ (5000886005554037/5000000000000000 : ℝ) ^ (8329/2048 : ℝ) := by
    have hpowers : (50036040775798783507/50000000000000000000 : ℝ)^2048 ≤ (5000886005554037/5000000000000000 : ℝ)^8329 := by
      have hnat : (50036040775798783507 : ℕ)^2048*5000000000000000^8329 ≤ 5000886005554037^8329*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036040775798783507 50000000000000000000 5000886005554037 5000000000000000 2048 8329 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000886005554037/5000000000000000 : ℝ)) (X := (50036040775798783507/50000000000000000000 : ℝ)) (by norm_num) 8329 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13424559740420473/100000000000000000000 : ℝ) ≤ ((164944142679226021/165000000000000000 : ℝ)+2*(224171507/123750000000 : ℝ)*(5583/50000 : ℝ))^(8329/2048 : ℝ) := by
    rw [show (164944142679226021/165000000000000000 : ℝ)+2*(224171507/123750000000 : ℝ)*(5583/50000 : ℝ)=(5000330060216677/5000000000000000 : ℝ) by norm_num, show 1+2*(13424559740420473/100000000000000000000 : ℝ)=(50013424559740420473/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36040775798783507/100000000000000000000 : ℝ)+(13424559740420473/100000000000000000000 : ℝ) ≤ ((164944142679226021/165000000000000000 : ℝ)+(224171507/123750000000 : ℝ)*((2847/20000 : ℝ)+(5583/50000 : ℝ)))^(8329/2048 : ℝ) := by
    rw [show (164944142679226021/165000000000000000 : ℝ)+(224171507/123750000000 : ℝ)*((2847/20000 : ℝ)+(5583/50000 : ℝ))=(5000608032885357/5000000000000000 : ℝ) by norm_num, show 1+(36040775798783507/100000000000000000000 : ℝ)+(13424559740420473/100000000000000000000 : ℝ)=(5002473266776960199/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36040775798783507/100000000000000000000 : ℝ) ≤ ((164944142679226021/165000000000000000 : ℝ)+2*(224171507/123750000000 : ℝ)*(2847/20000 : ℝ))^(8329/2048 : ℝ) := by
    rw [show (164944142679226021/165000000000000000 : ℝ)+2*(224171507/123750000000 : ℝ)*(2847/20000 : ℝ)=(5000886005554037/5000000000000000 : ℝ) by norm_num, show 1+2*(36040775798783507/100000000000000000000 : ℝ)=(50036040775798783507/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (164944142679226021/165000000000000000 : ℝ)*(X 1 0+X 2 0)+(224171507/123750000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8329/2048 : ℝ)) (lo := (5583/50000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (164944142679226021/165000000000000000 : ℝ)) (alpha := (224171507/123750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (164944142679226021/165000000000000000 : ℝ)*(X 0 1+X 2 1)+(224171507/123750000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8329/2048 : ℝ)) (lo := (5583/50000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (164944142679226021/165000000000000000 : ℝ)) (alpha := (224171507/123750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (164944142679226021/165000000000000000 : ℝ)*(X 0 2+X 1 2)+(224171507/123750000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8329/2048 : ℝ)) (lo := (5583/50000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (164944142679226021/165000000000000000 : ℝ)) (alpha := (224171507/123750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1084556723/5000000000 : ℝ)*X 0 0+(2697521233/5000000000 : ℝ)*X 0 1+(2631924509/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534525773/1000000000 : ℝ)*X 1 0+(-2235685973/10000000000 : ℝ)*X 1 1+(1315962257/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069051539/2000000000 : ℝ)*X 2 0+(2631924531/5000000000 : ℝ)*X 2 1+(-279460747/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2182640949/5000000000 : ℝ)*X 0 0+(2118423213/5000000000 : ℝ)*X 0 1+(1124399093/2500000000 : ℝ)*X 0 2+(2182640949/5000000000 : ℝ)*X 1 0+(2118423213/5000000000 : ℝ)*X 1 1+(1124399093/2500000000 : ℝ)*X 1 2+(2182640949/5000000000 : ℝ)*X 2 0+(2118423213/5000000000 : ℝ)*X 2 1+(1124399093/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-542279691/2500000000 : ℝ)*X 0 0+(5264188187/10000000000 : ℝ)*X 0 1+(5394702051/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312032071/10000000000 : ℝ)*X 1 0+(-1052416477/5000000000 : ℝ)*X 1 1+(2697351019/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062406413/2000000000 : ℝ)*X 2 0+(5394702041/10000000000 : ℝ)*X 2 1+(-2104832957/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1746117/4000000 : ℝ)*X 0 0+(2248461163/5000000000 : ℝ)*X 0 1+(2118761493/5000000000 : ℝ)*X 0 2+(1746117/4000000 : ℝ)*X 1 0+(2248461163/5000000000 : ℝ)*X 1 1+(2118761493/5000000000 : ℝ)*X 1 2+(1746117/4000000 : ℝ)*X 2 0+(2248461163/5000000000 : ℝ)*X 2 1+(2118761493/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (29832313498883379711/5500000000000000000000000 : ℝ) := by norm_num
    linear_combination (222796867/20000000000000 : ℝ)*(base19) + (40640019/4000000000000 : ℝ)*(base23) + (25696523/100000000000000 : ℝ)*(lower2) + (35532799/25000000000000 : ℝ)*(upper3) + (23344243/25000000000000 : ℝ)*(upper5) + (5728758092661873/100000000000000 : ℝ)*(major0) + (5728758092661873/100000000000000 : ℝ)*(major1) + (5728758092661873/100000000000000 : ℝ)*(major2) + (3811181955360909/50000000000000 : ℝ)*(sp0) + (7622392837386143/100000000000000 : ℝ)*(sp1) + (7622392935370003/100000000000000 : ℝ)*(sp2) + (191755322701047/5000000000000 : ℝ)*(sp3) + (1502032433/5000000000000 : ℝ)*(sp4) + (7799565207/50000000000000 : ℝ)*(sp7) + (1917561026575677/50000000000000 : ℝ)*(f.failure) + (3811196975685239/50000000000000 : ℝ)*(f.sum) + (84357671219/8250000000000000000000000 : ℝ)*base65 + (342281009753802667/16500000000000000000000000000000 : ℝ)*base68 + (212183727977802667/16500000000000000000000000000000 : ℝ)*base70 + (140205580029197333/16500000000000000000000000000000 : ℝ)*base71 + (117766408847/33000000000000000000000000 : ℝ)*base73 + (116688618792197333/16500000000000000000000000000000 : ℝ)*base75 + (101557833061697333/16500000000000000000000000000000 : ℝ)*base77 + (347270355290802667/16500000000000000000000000000000 : ℝ)*base80 + (50612449511/8250000000000000000000000 : ℝ)*base81 + (43764003/5000000000000000000000 : ℝ)*base90 + (43764003/5000000000000000000000 : ℝ)*base92 + (43764003/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9491854494515020246999513/1031250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1749586583/100000000000000 : ℝ)*(base19) + (1883585409/100000000000000 : ℝ)*(base23) + (184425559/100000000000000 : ℝ)*(upper3) + (32714777/50000000000000 : ℝ)*(lower4) + (11606667/6250000000000 : ℝ)*(upper5) + (719817448769033/12500000000000 : ℝ)*(major0) + (719817448769033/12500000000000 : ℝ)*(major1) + (719817448769033/12500000000000 : ℝ)*(major2) + (46720405459/100000000000000 : ℝ)*(sp1) + (49834988273/100000000000000 : ℝ)*(sp2) + (1915504892782013/25000000000000 : ℝ)*(sp4) + (766197110113601/10000000000000 : ℝ)*(sp5) + (7661967852554369/100000000000000 : ℝ)*(sp6) + (1927529651184523/50000000000000 : ℝ)*(sp7) + (1927529651184523/50000000000000 : ℝ)*(f.failure) + (1915504892782013/25000000000000 : ℝ)*(f.sum) + (3125431759/2475000000000000000000000 : ℝ)*base66 + (34258055741823079/6187500000000000000000000000000 : ℝ)*base67 + (36872996647323079/6187500000000000000000000000000 : ℝ)*base69 + (4385195183073079/6187500000000000000000000000000 : ℝ)*base71 + (774919105517/99000000000000000000000000 : ℝ)*base73 + (50007836621073079/6187500000000000000000000000000 : ℝ)*base75 + (74520953554323079/6187500000000000000000000000000 : ℝ)*base77 + (99121028381260579/6187500000000000000000000000000 : ℝ)*base79 + (86190015157/99000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (51643797/5000000000000000000000 : ℝ)*base90 + (51643797/5000000000000000000000 : ℝ)*base92 + (51643797/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1137_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149376161/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5583/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2827/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14087/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1137_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1137_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149376161/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16517/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1131/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2827/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14087/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1137_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1137_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1137_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149376161/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16517/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1131/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2827/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14087/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1137_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
